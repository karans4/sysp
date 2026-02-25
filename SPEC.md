# sysp Language Specification

**Draft — February 2026**

sysp is a systems Lisp that compiles to readable C99. The programmer writes s-expressions; the compiler produces a single C file with no runtime dependency. Type inference handles most annotations. Memory is managed automatically via escape analysis and reference counting — the programmer doesn't think about allocation.

```
sbcl --script sysp.lisp input.sysp output.c
cc -std=c99 output.c -o program
```

---

## 1. Philosophy

Write Lisp, get readable C, don't think about types, don't think about memory.

**Guiding principles:**

- **The programmer doesn't manage memory.** Escape analysis decides stack vs heap. ARC handles shared ownership. Drop cleans up at scope exit. Manual `ptr-alloc`/`ptr-free` exists for C interop, not for normal programming.
- **The programmer doesn't write types.** HM inference resolves everything. Annotations are accepted but rarely needed. A 1600-line Apple II emulator compiles with zero type annotations.
- **The output is readable C.** Not compiler soup. C you could read, debug, and hand to any C compiler. The output is the product.
- **The compiler is dumb. Libraries are smart.** The compiler provides general mechanisms: generic structs, traits, field-walking, monomorphization. Collections, strings, printing — all library code. No type name is special in the compiler (except Cons).
- **Small enough to self-host.** The compiler targets ~4000 lines. Every special case is a special case that has to be reimplemented in the self-hosted version. General mechanisms replace special cases.
- **Minimize special forms, maximize functions.** `if` and `let` are special. Most everything else is a function or a macro. If it can be expressed as a transformation on s-expressions, it's a macro.
- **C is always there.** `c-expr`, `c-tmpl`, `extern`, `include` — you can drop to C at any granularity. sysp doesn't hide the machine.

---

## 2. Lexical Structure

### 2.1 Tokens

```
integer    ::= [0-9]+ | '0x' [0-9a-fA-F]+
float      ::= [0-9]+ '.' [0-9]+
string     ::= '"' (char | escape)* '"'
character  ::= '#\' char | '#\' name
keyword    ::= ':' symbol
symbol     ::= anything else
```

A symbol is any token that isn't a number, string, character literal, keyword, or delimiter. There is no restricted character set — `+`, `hello-world`, `str-eq?`, `<=>` are all valid symbols. The compiler mangles symbols to valid C identifiers (`?` → `_p`, `!` → `_bang`, `-` → `_`, etc.).

Escape sequences: `\n` `\t` `\r` `\\` `\"` `\0`.
Character names: `#\space` `#\newline` `#\tab` `#\nul`.
Commas are whitespace.

### 2.2 Delimiters

`()` and `[]` are interchangeable. Both produce lists. Convention: `[]` for binding specs and parameter lists.

### 2.3 Comments

`;` to end of line. Comments on top-level forms are preserved in generated C.

### 2.4 Quasiquote

`` ` `` for templates, `~` for unquote, `~@` for splice-unquote. Used in macros. Since commas are whitespace, sysp uses `~` where traditional Lisps use `,`.

---

## 3. Types

### 3.1 Primitives

| Type | C | Notes |
|---|---|---|
| `:int` | `int` | Default numeric type |
| `:float` | `float` | |
| `:double` | `double` | |
| `:bool` | `int` | Printed as true/false |
| `:char` | `char` | |
| `:void` | `void` | |
| `:i8` ... `:i64` | `int8_t` ... `int64_t` | C99 fixed-width |
| `:u8` ... `:u64` | `uint8_t` ... `uint64_t` | |
| `:short` `:long` `:long-long` | C equivalents | Plus unsigned variants |
| `:size` `:ptrdiff` `:intptr` `:uintptr` | `size_t` etc. | |

There is no string primitive. String literals are `char*` (`:ptr-char`). The library provides a `String` struct for heap-allocated, length-tracked strings.

### 3.2 Compound Types

| Syntax | Shorthand | Description |
|---|---|---|
| `(:ptr T)` | `:ptr-int` | Pointer |
| `(:fn (T...) R)` | | Function type |
| `(:array T N)` | | Fixed-size C array |
| `(:tuple T...)` | | Heterogeneous product |
| `(:struct "Name")` | | Named struct |
| `(:enum "Name")` | | Named enum |
| `(:union T...)` | | Tagged union (sum type) |
| `(:rc T)` | | ARC-managed heap object |
| `(:volatile T)` | `:volatile-int` | Volatile-qualified |

The shorthand `:ptr-int` means `(:ptr :int)`. Works for any type: `:ptr-float`, `:ptr-Node`, `:volatile-u32`.

Collections (Vector, HashMap) and String are NOT compiler types. They are generic structs defined in library code. `(:Vector :int)` is just `(:generic "Vector" :int)` — an ordinary monomorphized struct.

### 3.3 Type Inference

The compiler uses Hindley-Milner unification. Types flow forward from literals and backward from usage:

```lisp
(let x 5)           ; x is :int (from literal)
(let y (+ x 1.0))   ; y is :float (numeric promotion)
(let v (Vector 1 2)) ; v is (:Vector :int) — library type, inferred
```

No annotations needed. Annotations are accepted anywhere and act as constraints — if your annotation contradicts inference, it's a compile error.

When inference encounters two incompatible types in branches, it produces a union type `(:union :int :ptr-char)` rather than erroring. When inference can't resolve a type at all, it falls back to the `Value` type.

### 3.4 Polymorphism and Monomorphization

`:?` marks a type variable. The compiler generates a specialized copy for each concrete instantiation.

```lisp
(defn id [x] x)
(id 42)       ; emits int id_int(int x) { return x; }
(id "hello")  ; emits char* id_str(char* x) { return x; }
```

Instances are deduped by mangled name. No runtime dispatch, no vtables — just stamped-out C functions.

### 3.5 Union Types

```lisp
(deftype NumOrStr (:union :int :ptr-char))
```

Compiled to a C tagged struct with an enum tag and a union body.

- `(runtype expr)` — runtime tag (enum value)
- `(as expr :type)` — extract variant
- `(match expr ...)` — pattern match on variants (section 8)

### 3.6 Type Aliases

```lisp
(deftype Name TypeExpr)
```

Emits a C `typedef`.

---

## 4. Declarations

### 4.1 Functions

```lisp
(defn name [param1, param2]
  body...)
```

Type annotations are optional. The last expression is the return value.

**Qualified functions** (for CUDA, static inline, etc.):

```lisp
(defn "__global__" kernel [data :ptr-float, n :int] :void ...)
```

**Variadic:**

```lisp
(defn log [fmt, & args] :void ...)
```

### 4.2 Structs

```lisp
(struct Point [x :float, y :float])
```

Generates a C `typedef struct`. Field access via `get`:

```lisp
(let p (Point 1.0 2.0))
(get p x)                   ; 1.0 — dispatches to Gettable trait
(set! (get p x) 3.0)        ; dispatches to Settable trait
```

Generic structs are monomorphized:

```lisp
(struct (Pair :A :B) [first :A, second :B])
(let p (Pair 1 "hello"))   ; monomorphizes to Pair_int_str
```

With C attributes: `(struct "__attribute__((packed))" Header [magic :u32, len :u16])`.

Foreign structs (from C headers, no code emitted): `(foreign-struct SDL_Event [type :u32])`.

### 4.3 Enums

```lisp
(enum Color Red Green Blue)
(enum Flags [A 1] [B 2] [C 4])   ; explicit values
```

### 4.4 External Declarations (FFI)

sysp compiles to C. "FFI" is just declaring what already exists.

```lisp
(extern printf [fmt :ptr-char, & args] :int)
(extern-var errno :int)
(include "SDL2/SDL.h")
(foreign-struct SDL_Rect [x :int, y :int, w :int, h :int])
```

For inline C:

```lisp
(c-expr "SDL_GetTicks()" :u32)            ; expression with type
(c-tmpl "memcpy(~, ~, ~)" :void dst src n) ; template, ~ = hole
(c-stmt "SDL_Quit();")                      ; raw statement
(c-decl "#define MAX_SIZE 1024")            ; top-level
```

### 4.5 Modules

```lisp
(use collections)             ; resolves to lib/collections.sysp
(use "path/to/file.sysp")    ; relative to source file
(export name1 name2)          ; restrict what's visible
```

Files are deduplicated by absolute path. The compiler can emit `.sysph` header files (`--emit-header`).

### 4.6 Compile-Time Functions

```lisp
(defmacro name [params] body...)   ; macro — receives and returns s-expressions
(defn-ct name [params] body...)    ; compile-time helper — callable from macros
```

See section 9 for details.

---

## 5. Traits

Traits are the universal dispatch mechanism. HM inference resolves concrete types at every call site, so trait dispatch is always static — no vtables, no runtime overhead.

### 5.1 Defining Traits

```lisp
(deftrait Printable [:T]
  (show [self] (:rc String))
  :default (defn show [self :?] (:rc String)
             ;; field-walking auto-derive
             ...))
```

Traits can have a `:default` impl that applies when a type has no explicit impl. The compiler monomorphizes the default for the concrete type.

### 5.2 Implementing Traits

```lisp
(impl Printable :int
  (defn show [x :int] (:rc String) (String (str-from-int x))))

(impl Printable (:Vector :T)
  (defn show [v (:Vector :T)] (:rc String) ...))
```

Primitives can impl traits. Generic types can impl traits. Resolution: explicit impl > default impl > compile error.

### 5.3 Built-in Traits

Three traits the compiler has special knowledge of:

**Drop** — compiler inserts calls at scope exit:
```lisp
(deftrait Drop [:T]
  (drop [self] :void)
  :default (defn drop [self :?] :void
             (for-fields [name type val] self
               (when (impl? Drop type)
                 (drop val)))))
```

**Gettable** — `(get x key)` dispatches to this trait:
```lisp
(deftrait Gettable [:K :V]
  (get [self key] :V)
  :default ...)  ;; struct field access
```

**Settable** — `(set! (get x key) val)` dispatches to this trait:
```lisp
(deftrait Settable [:K :V]
  (set [self key val] :void)
  :default ...)  ;; struct field assignment
```

Default impls handle struct field access. Library overrides for collections:

```lisp
(impl Gettable (:Vector :T)    ;; (get v 0) → index access
  (defn get [v (:Vector :T) i :int] :T ...))
(impl Gettable (:HashMap :K :V) ;; (get m "foo") → key lookup
  (defn get [m (:HashMap :K :V) key :K] :V ...))
```

One syntax for structs, vectors, hashmaps, and any user-defined type.

### 5.4 Library Traits

These are pure library — no compiler magic:

- **Printable** — `(show x)` returns `(:rc String)`. println/fmt use this.
- **Hashable** — `(hash-key x)` and `(key-eq a b)` for HashMap keys
- **Sized** — `(len x)` for any collection
- **Indexed** — `(nth x i)` for sequential collections
- **Keyed** — `(kget m k)` and `(has? m k)` for key-value collections
- **Iterable** — `(iter-len x)` and `(iter-nth x i)` for iteration. One trait gives you for-each, map, filter, reduce for any collection.
- **Comparable** — `(cmp a b)` for ordering. Enables sorting, min/max on custom types.

### 5.5 Field-Walking Intrinsic

The compiler provides a way for library code to iterate over a struct's fields at compile time:

```lisp
(for-fields [name type val] self body...)
```

Expands at monomorphization time to per-field code. `(impl? TraitName type)` is a compile-time check. This enables generic Drop and Printable in library code without the compiler knowing any specific type.

---

## 6. Statements and Control Flow

### 6.1 Bindings

```lisp
(let x 5)              ; immutable
(let x :int 5)         ; with annotation (rarely needed)
(let-mut x 5)          ; mutable
```

`set!` on a `let`-bound variable is a compile error. Use `let-mut`.

Arrays:

```lisp
(let-array buf :int 256)
(let-array "__shared__" smem :float 1024)  ; CUDA shared memory
```

### 6.2 Assignment

```lisp
(set! x 42)                  ; variable
(set! (get point x) 3.0)     ; struct field — Settable trait
(set! (get v 0) 10)           ; collection element — Settable trait
(set! (array-ref a i) 0)      ; array element
```

Generalized `set!` — any `get` expression on the left dispatches to the Settable trait, like CL's `setf`.

### 6.3 Conditionals

`if` is the only conditional form. No distinction between statement and expression — the compiler infers from context.

```lisp
(if (< x 0)
  (println "negative")
 elif (== x 0)
  (println "zero")
 else
  (println "positive"))

(let sign (if (< x 0) -1 elif (== x 0) 0 else 1))
```

`when` and `unless` are macros. No `cond` — use `if`/`elif` chains or pattern matching.

### 6.4 Pattern Matching

```lisp
(match expr
  ((:int n) (show n))         ; union variant
  ((Point x y) (+ x y))      ; struct destructuring
  (42 "the answer")           ; literal equality
  (_ "default"))              ; wildcard
```

### 6.5 Loops

```lisp
(for [i 0 10] (println i))              ; counted
(while (< i 10) (inc! i))               ; while
(for-each [x vec] (println x))          ; iterate elements
(for-each [k v table] (println k v))    ; iterate key-value pairs
(dotimes [i 100] (println i))           ; repeat n times
```

`break` and `continue` work inside loops.

### 6.6 Tail Recursion

```lisp
(defn factorial [n, acc]
  (if (== n 0) acc
   else (recur (- n 1) (* acc n))))
```

`recur` compiles to parameter reassignment + `goto`. Zero stack growth.

### 6.7 Blocks

`do` is a sequential block. Value is the last form:

```lisp
(let result (do
  (let a (compute-x))
  (let b (compute-y))
  (+ a b)))
```

### 6.8 Multiple Return Values

```lisp
(defn divmod [a, b] (values (/ a b) (% a b)))
(let-values [(q r) (divmod 17 5)])
```

---

## 7. Expressions and Operations

### 7.1 Arithmetic

```lisp
(+ a b)    (- a b)    (* a b)    (/ a b)    (% a b)
(- x)      ; unary negation
```

Type follows operands with numeric promotion.

### 7.2 Comparison and Logical

```lisp
(< a b)  (> a b)  (<= a b)  (>= a b)  (== a b)  (!= a b)
(and a b)  (or a b)  (not x)   ; short-circuit
```

### 7.3 Bitwise

```lisp
(bit-and a b)  (bit-or a b)  (bit-xor a b)  (bit-not x)  (shl a n)  (shr a n)
```

### 7.4 Strings

String literals are `char*`. The library provides `String` as a heap-allocated, length-tracked struct:

```lisp
(struct String [data :ptr-char, len :int])
(defn String [s :ptr-char] (:rc String)
  (new String (strdup s) (strlen s)))
```

`String` is just a normal function — convention, not special syntax. `(new String ...)` creates an ARC object internally.

String operations are library functions:

```lisp
(str-len s)  (str-eq? a b)  (str-contains? s sub)
(str-concat a b)  (str-slice s start end)
(str-upper s)  (str-lower s)  (str-split s delim)
```

Allocating ops return `(:rc String)` — ARC-managed, auto-freed at scope exit. No manual memory management for strings.

### 7.5 Collections

Collections are library types, not compiler primitives.

**Vectors:**

```lisp
(let v (Vector 1 2 3))
(get v 0)                  ; Gettable trait → 1
(set! (get v 0) 42)        ; Settable trait
(vector-push! v 4)         ; macro → library poly-fn
(len v)                    ; Sized trait → 4
```

**Hash maps:**

```lisp
(let m (HashMap "a" 1 "b" 2))
(get m "a")                ; Gettable trait → 1
(set! (get m "a") 99)      ; Settable trait
(hash-del! m "b")          ; macro → library poly-fn
(hash-keys m)              ; returns Vector
```

**Conses:**

Conses are the one built-in compound data structure. The compiler can construct and destructure them.

```lisp
(cons 1 (cons 2 (cons 3 nil)))
(list 1 2 3)                       ; shorthand
(car xs)                            ; head
(cdr xs)                            ; tail
(nil? xs)                           ; empty check
```

Conses participate in the trait system like any other type — library impls Gettable, Printable, Drop for conses.

### 7.6 Printing

`println` uses the Printable trait:

```lisp
(println x)
;; expands to:
;;   (let _s (show x))          ;; Printable trait → (:rc String)
;;   (printf "%s\n" (. _s data))
;;   ;; _s auto-dropped at scope exit
```

`fmt` builds a String by concatenating `show` results:

```lisp
(fmt "hello {name}, age {age}")
```

All intermediate strings are ARC — no manual tracking, no pending-string-frees.

Any type can be printed. Printable has a default impl that uses `for-fields` to build `"TypeName{f1: v1, f2: v2}"`. Define a custom `(impl Printable MyType ...)` to override.

### 7.7 Collection Operations

Higher-order operations dispatch through the Iterable trait:

```lisp
(map f vec)               ; apply f to each element
(filter pred vec)         ; keep elements where pred is true
(reduce f init vec)       ; fold left
(for-each [x vec] ...)   ; iterate
```

**Predicates:** `some`, `every?`, `not-any?`, `not-every?`
**Selection:** `remove`, `take`, `drop`, `take-while`, `drop-while`
**Construction:** `range`, `repeat`, `reverse`, `concat`, `distinct`, `frequencies`
**Access:** `first`, `last`, `nth`, `count`, `empty?`
**Threading:** `->` (thread-first), `->>` (thread-last)

These work on any type that impls Iterable — Vector, Cons lists, HashMap (iterate keys), user-defined collections.

### 7.8 Pointers and Low-Level

For C interop. Not the normal path.

```lisp
(addr-of x)            ; &x
(deref p)              ; *p
(cast expr :type)      ; type cast
(sizeof :type)         ; C sizeof
(ptr+ p n)             ; pointer arithmetic
(null? p)              ; NULL check
(ptr-alloc :int)       ; malloc(sizeof(int))
(ptr-free p)           ; free(p)
```

### 7.9 Lambdas and Closures

```lisp
(lambda [x] (* x x))              ; no capture → plain C function
(lambda [x] (+ x captured-var))   ; captures from enclosing scope
```

Compiled as fat pointer: `Fn = {fn, env}`. Non-capturing lambdas have `env = NULL` and can be passed as C function pointers directly.

---

## 8. Memory Model

The programmer doesn't think about memory. The compiler decides:

1. **Escape analysis** determines stack vs heap
2. **ARC** handles shared ownership for heap objects
3. **Drop trait** cleans up at scope exit
4. **Manual control** exists for C interop

| Allocation | When | Lifetime |
|---|---|---|
| Stack (default) | Locals, non-escaping values | Scope |
| ARC heap | Values that escape, `(:rc T)` | Refcount reaches zero |
| Manual heap | `(ptr-alloc ...)` | `(ptr-free ...)` |
| Static | String literals, top-level constants | Program |

The key: escape analysis is automatic. The user writes `(let v (Vector 1 2 3))` and the compiler decides. If `v` doesn't escape, it's stack. If it does, ARC. The user doesn't write `new`, doesn't choose allocation strategy.

Thread-safe via platform-detected atomics. Opt out: `-DSYSP_NO_THREADS`.

---

## 9. Concurrency

### 9.1 Spawn / Await

```lisp
(let f (spawn (expensive-computation x)))
(let result (await f))
```

`spawn` creates a pthread. Captured variables are copied. `await` does `pthread_join`.

### 9.2 Thread Safety

Atomic refcounting, thread-local gensym counters. Mutable data is NOT thread-safe — synchronization is the programmer's responsibility (same as C).

---

## 10. Macros and Compile-Time Evaluation

### 10.1 defmacro

```lisp
(defmacro swap! [a b]
  (let g (gensym))
  `(do (let-mut ~g ~a)
       (set! ~a ~b)
       (set! ~b ~g)))
```

### 10.2 defn-ct (Compile-Time Functions)

```lisp
(defn-ct double [x] (* x 2))

(defmacro emit-constant [n]
  (double n))                 ; evaluates at compile time
```

Full Lisp at compile time. Homoiconic metaprogramming: the code you generate is the same data structure as the code you write.

### 10.3 Built-in Macros

- `->`, `->>` — threading
- `when`, `unless` — conditional
- `when-let` — conditional binding
- `dotimes`, `for-each` — loop bindings
- `inc!`, `dec!` — mutation sugar
- `vector-push!`, `hash-set!`, `hash-del!` — collection mutation

---

## 11. Condition System

CL-style restartable conditions. Handlers run in the signaler's stack frame (no unwinding). All stack-allocated, zero malloc.

```lisp
(handler-bind
  (("parse-error" (lambda [line :int]
    (println "skipping bad line")
    (invoke-restart "skip" 0))))
  (process-file input))

(defn process-line [line] :void
  (restart-case
    (do
      (when (bad? line) (signal "parse-error" line-num))
      (handle line))
    ("skip" val (println "skipped"))))
```

---

## 12. C Interop

sysp's output IS C. Interop isn't a bridge — it's the same language at a different abstraction level.

```lisp
(extern SDL_Init [flags :u32] :int)
(foreign-struct SDL_Rect [x :int, y :int, w :int, h :int])
(include "SDL2/SDL.h")
(c-expr "SDL_GetTicks()" :u32)
(c-tmpl "memcpy(~, ~, ~)" :void dst src n)
```

Generated C properties:
- Valid C99 (`-std=c99 -pedantic`)
- No GNU extensions required
- Single-file output, no external runtime
- Readable variable names, structured control flow

---

## 13. Compiler Architecture

The compiler is a single Common Lisp file (`sysp.lisp`, targeting ~4000 lines).

```
source.sysp
  -> [Parse]         Custom tokenizer + recursive descent, source locations
  -> [Expand uses]   Splice imported modules, dedup by path
  -> [Infer]         HM type inference, constraint gen, unification
  -> [Escape]        Mark non-escaping allocations for stack
  -> [Compile]       AST -> C strings, macro expansion, monomorphization
  -> [Emit]          Assemble C: includes, preamble, types, decls, functions
```

The compiler provides:
1. **Conses** — the one built-in compound data structure
2. **Generic structs** — monomorphized C structs, no name is special
3. **Traits + impl** — static dispatch, HM resolves concrete types
4. **Drop/Gettable/Settable** — three built-in traits with compiler-magic dispatch
5. **Field-walking intrinsic** — `(for-fields ...)` for generic struct iteration
6. **Poly-fns** — monomorphized per call site
7. **Macros** — syntactic expansion
8. **Module system** — `(use mod)` loads `lib/mod.sysp`
9. **FFI** — `(include ...)` / `(extern ...)`

Everything else is library.

### 13.1 Self-Hosting

The end goal is for sysp to compile itself. The bootstrap compiler (`sysp.lisp`, Common Lisp) gets replaced by `sysp.sysp`, which compiles to `bootstrap.c` — a checked-in generated C file. New contributors need only a C compiler, not SBCL.

The dumber the compiler, the easier this is. Every special case in the CL compiler is a special case that has to be reimplemented. General mechanisms (traits, generics, field-walking) replace hundreds of lines of bespoke codegen.

---

## 14. Standard Library

Located in `lib/`. Imported via `(use name)`.

### Core

| Module | Contents |
|---|---|
| `collections` | Vector, HashMap — structs, traits (Indexed, Keyed, Hashable, Sized), mutation ops |
| `strings` | String struct, char* helpers, Printable impls |
| `core` | Predicates, arithmetic, HOFs (map, filter, reduce) |
| `math` | sqrt, sin, cos, pow, log, fabs, floor, ceil |
| `io` | File I/O |
| `mem` | Memory utilities |
| `fmt` | String interpolation |

### Bindings

sysp ships with bindings for major C libraries. Since sysp's output IS C, bindings are just `extern` + `foreign-struct` + `include` with ergonomic wrappers and macros on top.

| Module | Library | Domain |
|---|---|---|
| `sdl2` | SDL2 | Graphics, audio, input, windowing |
| `raylib` | raylib | Simple games and graphics |
| `gtk2` | GTK 2 | GUI toolkit (legacy) |
| `gtk3` | GTK 3 | GUI toolkit |
| `gtk4` | GTK 4 | GUI toolkit (modern) |
| `sqlite` | SQLite | Embedded database |
| `curl` | libcurl | HTTP, FTP, network transfers |
| `ssl` | OpenSSL | TLS, cryptography |
| `z` | zlib | Compression |
| `ffmpeg` | FFmpeg | Video/audio encode, decode, transcode |
| `ncurses` | ncurses | Terminal UI |
| `png` | libpng | PNG image read/write |
| `jpeg` | libjpeg | JPEG image read/write |
| `lua` | Lua | Embeddable scripting engine |
| `cuda` | CUDA | GPU kernel support |

```lisp
(use gtk4)
(use sqlite)
(use curl)
;; That's it. Full access to these ecosystems from sysp.
```

The litmus test: define a new `(struct (Deque :T) ...)` in pure library code, impl Sized/Indexed/Drop/Printable/Gettable/Settable, and it works identically to Vector — println, auto-drop, for-each, uniform access. Zero compiler changes.

---

## Appendix: Grammar

```
program     ::= form*
form        ::= literal | symbol | keyword | list | quoted
literal     ::= integer | float | string | character
list        ::= '(' form* ')' | '[' form* ']'
quoted      ::= "'" form | '`' form | '~' form | '~@' form

toplevel    ::= defn | struct | enum | deftype | deftrait | impl
              | extern | extern-var | defmacro | defn-ct
              | use | export | include | c-decl | foreign-struct
              | let | let-mut

defn        ::= '(' 'defn' [string] name params [type] body+ ')'
struct      ::= '(' 'struct' [string] name fields ')'
enum        ::= '(' 'enum' name variant+ ')'
deftype     ::= '(' 'deftype' name type-expr ')'
deftrait    ::= '(' 'deftrait' name type-params method+ [':default' defn] ')'
impl        ::= '(' 'impl' trait-name type defn+ ')'
extern      ::= '(' 'extern' name params [type] ')'

params      ::= '[' (name [type] ','?)* ['&' name] ']'
fields      ::= '[' (name type ','?)* ']'
variant     ::= name | '[' name [integer] ']'
type        ::= keyword | '(' keyword type* ')'
```

---

## License

MIT
