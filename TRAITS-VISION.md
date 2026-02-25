# sysp Vision

## The Language

Write Lisp, get readable C, don't think about types, don't think about memory.

- **S-expressions** with HM inference — you almost never write type annotations
- **Readable C output** — not compiler soup, C you can read and debug
- **Automatic memory** — escape analysis decides stack vs heap, ARC handles
  lifetime, Drop cleans up at scope exit. The user doesn't think about
  allocation. It just works.
- **Traits + generics** — static dispatch, monomorphized, zero runtime cost
- **Conses + macros** — it's a real Lisp, with metaprogramming
- **Compiles to C** — runs everywhere, FFI to any C library
- **Small enough to self-host** — that's the whole point of the diet

## Core Architecture Principle

The compiler knows NOTHING about Vector, HashMap, String, or any collection.
They are ordinary generic structs. The compiler provides:
1. Conses — the only built-in compound data structure
2. Generic structs + monomorphization
3. Traits + static dispatch (Drop, Gettable, Settable are compiler-magic)
4. A field-walking intrinsic so libraries can implement Drop and Printable
5. That's it.

No type name is special (except Cons). No collection gets bespoke codegen.

## Conses: The One Built-in

Conses are the only non-C-primitive data structure the compiler knows about.
The compiler can construct and destructure them. Everything else — Vector,
HashMap, String — is pure library built on top of generic structs + C FFI.

But conses still participate in the trait system like any other type.
Libraries impl Gettable, Printable, Drop, etc. for conses alongside
their impls for Vector, HashMap, and everything else. Conses are not
above the law — they just happen to be the one type that exists before
any library is loaded.

## Built-in Traits: Drop, Gettable, Settable

Three traits the compiler has special knowledge of:

### Drop
Compiler inserts calls at scope exit.
Does this type have a Drop impl? If yes, call it.
If no, recurse into struct fields (using the generic field-walk mechanism).

### Gettable / Settable (CL-style uniform access)
`(get x key)` dispatches to the Gettable trait.
`(set! (get x key) val)` dispatches to the Settable trait.

Default impl: struct field access. `(get p x)` on a plain struct reads
field `x`. `(set! (get p x) 42)` writes it. No explicit impl needed.

Library overrides for collections:
```lisp
(deftrait Gettable [:K :V]
  (get [self key] :V)
  :default ...)  ;; struct field access

(deftrait Settable [:K :V]
  (set [self key val] :void)
  :default ...)  ;; struct field assignment

(impl Gettable (:Vector :T)   ;; (get v 0) → index access
  (defn get [v (:Vector :T) i :int] :T (array-ref (. v data) i)))
(impl Settable (:Vector :T)   ;; (set! (get v 0) 42)
  (defn set [v (:Vector :T) i :int val :T] :void (array-set! (. v data) i val)))
(impl Gettable (:HashMap :K :V)   ;; (get m "foo") → key lookup
  ...)
(impl Settable (:HashMap :K :V)   ;; (set! (get m "foo") 99)
  ...)
```

One syntax for structs, vectors, hashmaps, and any user-defined type.
The compiler just calls the trait method — it doesn't know what types exist.

### Printable (NOT built-in)
Printable is a library trait. `println` compiles to a call to the
Printable trait's `show` method. The library implements `show` for
primitives, structs (via field-walking), and collections.

`show` returns `(:rc String)` — a refcounted String. This means println,
fmt, and all string formatting use the library String type. The compiler
doesn't know about any of this.

## Trait Defaults

Traits can specify a default impl that applies when a type has no explicit
impl. This is how Printable works for arbitrary structs without requiring
every type to manually impl it.

```lisp
(deftrait Printable [:T]
  (show [self] (:rc String))
  :default (defn show [self :?] (:rc String)
             ;; Use field-walking intrinsic to build "TypeName{f1: v1, f2: v2}"
             ...))
```

The compiler resolves trait calls: if an explicit impl exists, use it.
Otherwise, if the trait has a `:default`, monomorphize the default for
this type. Otherwise, compile error.

This also enables a default Drop that recursively drops fields:
```lisp
(deftrait Drop [:T]
  (drop [self] :void)
  :default (defn drop [self :?] :void
             (for-fields [name type val] self
               (when (impl? Drop type)
                 (drop val)))))
```

## Field-Walking Intrinsic

The compiler provides a way for library code to iterate over a struct's
fields at compile time. This enables generic Drop and Printable without
the compiler knowing any specific type.

```lisp
(for-fields [name type val] self body...)
```
Expands at monomorphization time to per-field code. `name` is a string
literal, `type` is the field's type, `val` is the field's value.
`(impl? TraitName type)` is a compile-time check: does this type have
an impl for that trait?

The key: the LIBRARY writes the generic Drop/Printable logic using this
intrinsic. The compiler just provides the field iteration primitive.

## Type Shorthands

Pointer types have a shorthand: `:ptr-char` instead of `(:ptr :char)`,
`:ptr-int` instead of `(:ptr :int)`, etc. The compiler expands these
automatically. Use the shorthand — it's cleaner.

## Strings

There is no `:str` or `:String` in the compiler. Strings are `:ptr-char`
aka `char*`. String literals produce `char*`. The compiler has zero string
awareness beyond what C gives you.

If the user wants a heap-allocated, length-tracked string type:
```lisp
(struct String [data :ptr-char, len :int])
```
This is a library type in lib/strings.sysp, not a compiler concept.

Printf/println for `char*` just uses `%s`. Printf/println for `String`
uses the Printable trait (library-provided).

## What the Compiler Provides

1. **Conses**: the one built-in compound data structure
2. **Generic structs**: monomorphized C structs, nothing special about any name
3. **Traits + impl**: static dispatch, HM inference resolves concrete types
4. **Drop/Gettable/Settable (built-in traits)**: compiler-magic dispatch
5. **Field-walking intrinsic**: lets library code iterate struct fields generically
6. **Poly-fns**: monomorphized per call site
7. **Macros**: syntactic expansion
8. **Module system**: `(use collections)` loads `lib/collections.sysp`
9. **`(include ...)` / `(extern ...)`**: FFI to C headers

## What the Library Provides

### lib/collections.sysp

**Struct definitions** (just ordinary generic structs):
```lisp
(struct (Vector :T) [data (:ptr :T), len :int, cap :int])
(struct (HashMap :K :V) [keys (:ptr :K), vals (:ptr :V),
                         occ (:ptr :char), len :int, cap :int])
```

**C runtime headers** (included by library):
```lisp
(include "runtime/vector.h")
(include "runtime/hashmap.h")
```

**Traits + impls**:
```lisp
;; Sized
(deftrait Sized [:T] (len [self] :int))
(impl Sized (:Vector :T) ...)
(impl Sized (:HashMap :K :V) ...)

;; Indexed
(deftrait Indexed [:T] (nth [self i] :?))
(impl Indexed (:Vector :T) ...)

;; Keyed
(deftrait Keyed [:K :V]
  (kget [self k] :V)
  (has? [self k] :bool))
(impl Keyed (:HashMap :K :V) ...)

;; Hashable — key types
(deftrait Hashable [:T]
  (hash-key [self] :uint)
  (key-eq [a b] :bool))
(impl Hashable :int ...)
(impl Hashable (:ptr :char) ...)

;; Drop — library provides impls, compiler provides auto-call
(impl Drop (:Vector :T)
  (defn drop [v (:Vector :T)] :void
    (when (> (. v cap) 0) (free (cast (:ptr :void) (. v data))))))
(impl Drop (:HashMap :K :V) ...)

;; Printable — pure library trait, returns (:rc String)
;; Has a default impl that uses for-fields to build "TypeName{f1: v1, ...}"
(deftrait Printable [:T]
  (show [self] (:rc String))
  :default ...)  ;; field-walk auto-derive
(impl Printable :int ...)
(impl Printable (:ptr :char) ...)  ;; char* → String(s)
(impl Printable (:Vector :T) ...)  ;; "[1, 2, 3]"
(impl Printable (:HashMap :K :V) ...)
```

**Mutation ops** (poly-fns + macros):
```lisp
(defn _vector-push-impl [vp (:ptr :?) elem :?] :void ...)
(defn _hash-set-impl [mp (:ptr :?) key :? val :?] :void ...)
(defn _hash-del-impl [mp (:ptr :?) key :?] :void ...)
(defn hash-keys [m :?] :? ...)
(defn hash-vals [m :?] :? ...)
```

**Macros**:
```lisp
(vector-push! v x)   → (_vector-push-impl (addr-of v) x)
(hash-set! m k v)     → (_hash-set-impl (addr-of m) k v)
(hash-del! m k)       → (_hash-del-impl (addr-of m) k)
(Vector 1 2 3)        → (do (let-mut _v (Vector)) (vector-push! _v 1) ... _v)
(HashMap "a" 1 "b" 2) → (do (let-mut _m (HashMap)) (hash-set! _m "a" 1) ... _m)
```

### println / print / fmt — all library, all use Printable + String

```lisp
;; println is a macro or builtin that expands to:
;;   (let _s (show x))        ;; calls Printable trait → (:rc String)
;;   (printf "%s\n" (. _s data))
;;   ;; _s auto-dropped at scope exit (ARC decrement)

;; fmt builds a String by concatenating show results:
;;   (fmt "hello {name}, age {age}")
;;   → String(str-concat (show "hello ") (show name) (show ", age ") (show age))
;;
;; All intermediate Strings are ARC — no manual free, no pending-string-frees.
;; The compiler's *pending-string-frees* mechanism is deleted entirely.
```

### lib/strings.sysp

Low-level `char*` helpers:
```lisp
(extern strlen [s (:ptr :char)] :int)
(extern strcmp [a (:ptr :char) b (:ptr :char)] :int)
(defn str-len [s (:ptr :char)] :int (cast :int (strlen s)))
(defn str-eq? [a (:ptr :char) b (:ptr :char)] :bool (== (strcmp a b) 0))
;; etc.
```

String as a library struct:
```lisp
(struct String [data (:ptr :char), len :int])

;; Just a normal function that happens to share the type's name.
;; No special semantics — it's a convention, not a language feature.
(defn String [s (:ptr :char)] (:rc String)
  (let len (cast :int (strlen s)))
  (new String (strdup s) len))

(impl Printable String
  (defn show [s String] (:ptr :char) (strdup (. s data))))
(impl Drop String
  (defn drop [s String] :void (free (cast (:ptr :void) (. s data)))))
```

### Object Lifetime Model

- `(struct Foo ...)` — plain C struct, stack-allocated, value semantics
- `(new Foo ...)` — ARC heap object, refcounted, shared ownership
- `(Foo ...)` — if there's a function named `Foo`, it's just a function call.
  No special semantics. Convention is to define `(defn Foo [...] :Foo ...)`
  as a factory, but the compiler doesn't know or care.
- Almost never call `(new ...)` directly. User writes
  `(let s (String "hello"))` — that's just calling the function `String`.

## What Gets Deleted from Compiler

EVERYTHING that references "Vector", "HashMap", or "str"/"String" by name:
- `compile-vector`, `compile-hash-map` and ALL hash/vector compile-* functions
- `vector-type-p`, `hashmap-type-p`, `vector-elem-type`, etc.
- `generate-collection-helpers` (library handles C helper emission)
- `ensure-str-split-helper` (str-split becomes library function)
- `ensure-show-helper` Vector/HashMap branches (Printable trait handles it)
- `emit-drop`/`type-needs-drop-p` Vector/HashMap branches (Drop trait)
- `str-type-p` and all `:str` remnants
- `*printf-formats*` string entry, `format-print-arg` string case
- All `*expr-dispatch*` and `*stmt-dispatch*` collection entries
- All `infer-list` collection branches
- `compile-set-expr` vector-ref/hash-get branches
- `compile-nth` vector branch
- String builtin compilers (str-concat etc.) — move to library using
  regular malloc + the field-walk/trait system

## Why: Self-Hosting

The dumber the compiler, the easier it is to rewrite in sysp itself.
Every special case in the CL compiler is a special case that has to be
reimplemented in the self-hosted version. Traits, generics, field-walking,
and a module system are general mechanisms — implement them once, and
Vector/HashMap/String/Printable/Drop all fall out as library code that
doesn't need to be in the compiler at all. The self-hosted compiler
only needs to handle: conses, generic structs, traits, poly-fns, macros,
HM inference, field-walking, and C emission. That's it.

## Future Traits

### Iterable
```lisp
(deftrait Iterable [:T]
  (iter-len [self] :int)
  (iter-nth [self i] :T))
```
One trait gives you for-each, map, filter, reduce, some, every? for
any collection. Impl it for Vector, HashMap (iterate keys), Cons lists,
Deque, whatever.

### Comparable
```lisp
(deftrait Comparable [:T]
  (cmp [a b] :int))   ;; -1, 0, 1
```
Enables ==, <, > for user-defined types. Sorting and min/max on
collections of custom types.

### Design Note
No Into/From conversion traits. HM inference resolves types — the user
should rarely if ever have to write type annotations or explicit casts.
The type system works *for* you, not against you.

## The Litmus Test

After refactoring, define this in pure library code:
```lisp
(struct (Deque :T) [data (:ptr :T), front :int, back :int, cap :int])
(impl Sized (:Deque :T) ...)
(impl Indexed (:Deque :T) ...)
(impl Drop (:Deque :T) ...)
(impl Printable (:Deque :T) ...)
```
It should work identically to Vector: println, auto-drop, for-each, len.
Zero compiler changes needed. If it needs compiler changes, the architecture
is wrong.

## Current State (Session 158)

- Phase 1 DONE: `:str` → `(:ptr :char)` alias throughout compiler
- Phase 4 partially done: removed most dispatch entries + compile functions
  for hash/vector ops, added macros for vector-push!/hash-set!/hash-del!
- Tests currently broken — need to fix trait resolution for hash-get etc.
- Key remaining work:
  1. Field-walking intrinsic (enables generic Drop + Printable)
  2. Move generate-collection-helpers to library
  3. Move all string builtins to library
  4. Make println use Printable trait instead of hardcoded format dispatch
  5. Delete all collection/string names from compiler
