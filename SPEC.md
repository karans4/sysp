# sysp — Language Specification

Status: working specification. This document is the **target**. Where the
current implementation diverges, the spec wins and the gap is a bug or a
roadmap item (see §17 Conformance). This supersedes the design statements
in `TRAITS-VISION.md`; that file remains as motivation only.

---

## 1. Thesis & principles

sysp is a systems Lisp that compiles to readable C.

1. **Write Lisp, get C you can read.** Generated C is structured, named,
   and debuggable — not an SSA dump. This is a hard requirement, not a
   nicety (§16).
2. **Inference, not annotation.** Hindley–Milner with monomorphization.
   Annotations are optional everywhere they can be inferred.
3. **Traits are the spine.** Generic structs + monomorphized trait
   dispatch are the only abstraction mechanism. There is **no bespoke
   codegen for any type** except Cons.
4. **Deterministic memory.** No GC, no tracing, no pauses. Memory is
   governed by one axis: **mutability**. Deeply immutable data is shared
   and reference-counted (acyclic by construction, so RC is complete);
   mutable data uses value semantics and is borrowed only at call
   boundaries (§9). No borrow checker, no cycle collector, no lifetime
   annotations. The programmer rarely thinks about it; the model is still
   exact and predictable.
5. **Small enough to self-host.** The accepted subset (§16.3) is a
   fixed point: the compiler can be written in it.

The only compound data structure the compiler knows intrinsically is
the **Cons cell**. `String`, `Vec`, `HashMap`, everything else, is
library code over generic structs + traits + FFI.

---

## 2. Lexical structure

- **S-expressions.** `(` `)` delimit forms. `[` `]` are read identically
  to `( )` (sugar) and conventionally used for binding/parameter lists.
- **Comments.** `;` to end of line. `;;` by convention for prose.
- **Identifiers.** Letters, digits, and `- ? ! * + / < > = % & | ^ ~ _`.
  Case is preserved by the parser. Name resolution and trait/method
  mangling are **case-insensitive-canonical** (a name is identified by
  its upper-cased spelling) so identical source read by different front
  ends agrees.
- **Keywords.** A token beginning `:` is a keyword, used for type forms
  (`:int`, `:ptr-void`, `:Point`) and option markers (`:only`, `:as`).
- **Literals.**
  - Integers: `42`, `0xFF`, `0b1010`, `-7`. Default type `:int`
    (32-bit signed) unless inferred narrower/wider.
  - Floats: `3.14`, `1e9`. Type `:f64` (`:f32` by inference/annotation).
  - Chars: `#\a`, `#\newline`, `#\space`. Type `:char`.
  - C-strings: `(cstr "…")` → `:cstr` (`const char*`, not owned, not
    rc'd). A bare `"…"` is sugar for a `String` library value (§13),
    **not** a builtin string type.
  - Booleans: `true`, `false`. Type `:bool`.
  - Nil/unit: `()` in value position is `:unit`.

---

## 3. Program & module structure

A program is a sequence of top-level forms:

```
(use "path.sysp" [:only (a b)] [:as p])   ; import
(include "<stdio.h>")                       ; raw C include
(extern name (params) :ret)                 ; FFI declaration
(extern-struct Name (fields))               ; FFI struct (layout only)
(define NAME value)                          ; compile-time constant
(enum Name (A 0) (B 1) …)                    ; → constants
(defstruct Name (fields))                    ; struct (§6)
(deftype Name …)                             ; tagged union (§7)
(deftrait …) (impl …)                        ; traits (§8)
(defmacro …) (defn-ct …)                     ; compile-time (§10)
(defn name (params) [:ret] body…)            ; function (§5)
```

### 3.1 Modules

- `(use "path")` makes the module's public definitions available.
  `:only (a b)` restricts; `:as p` qualifies references as `p/name`.
- A name is **public** unless prefixed `-` (e.g. `-helper`) which makes
  it module-private.
- **Separate compilation.** `--emit-header path.sysph` emits declarations
  (types, signatures, trait impl externs) for a module so dependents
  compile without its source. Mangled names are stable across separate
  compilation (§16.2).
- **Trait impls are global and coherent** across all `use`d modules
  (§8.4). `use` is transitive for impls (you cannot "not import" an
  impl — coherence requires one global answer).

---

## 4. Type system

### 4.1 Type forms

```
:int :i8 :i16 :i32 :i64 :u8 :u16 :u32 :u64 :f32 :f64 :bool :char :unit
:cstr :ptr-void :ptr-T            ; pointer to T (e.g. :ptr-int, :ptr-Node)
:Name                             ; struct / union / enum type
(Name :A :B)                      ; generic instantiation
(:fn (:int :int) :int)            ; function type
(Cons :T)                         ; homogeneous cons; (Cons :Value) if mixed
:Value                            ; dynamic tagged value (Lisp datum)
(:tvar n)                         ; inference variable (internal)
(:forall (ids) ty)                ; generalized scheme (internal)
```

### 4.2 Inference

Hindley–Milner with:
- struct-field reverse lookup (a value used as `(get-field x f)` is
  inferred to a struct having field `f`),
- pointer element tracking, numeric promotion, `:unit` (void) detection,
- let-polymorphism: a binding's type is generalized; each use site is
  monomorphized.

Annotations are optional wherever a type is inferable and **mandatory**
at FFI boundaries (`extern`, `extern-struct`) and where a type param is
constrained (§8.5).

### 4.3 Numeric rules

Integer arithmetic does not implicitly wrap silently in a way the C
backend leaves UB: `+ - *` on signed types are specified as two's
complement wrapping (compiled with `-fwrapv` semantics). Mixed-width
arithmetic requires an explicit `(cast :T x)`; inference will not
silently widen across annotated boundaries.

---

## 5. Bindings, functions, control flow

### 5.1 Functions

```
(defn name ((p :T) (q :U)) :Ret body…)     ; annotated
(defn name (p q) body…)                     ; inferred
(defn name (p q) :Ret where ((Ord :T)) …)   ; with trait bounds (§8.5)
```

- Last expression is the return value. `(return e)` exits early.
- **Tail calls.** `(recur args…)` is a self tail-call; compiles to a
  loop (`goto`), no stack growth. Mutual tail recursion is not TCO'd
  (documented limitation; use `recur` or a trampoline).

### 5.2 Multiple return values

```
(defn divmod ((a :int) (b :int)) (values :int :int)
  (values (/ a b) (% a b)))
(let-values (((q r) (divmod 17 5))) (+ q r))
```
Compiles to an out-param or a small by-value struct (backend choice;
not observable).

### 5.3 Bindings

```
(let ((x 1) (y (f x))) body…)        ; sequential, scoped
(let-mut ((c 0)) (set! c (+ c 1)) c) ; mutable binding
```
A `let` binding owns its initializer's value; its Drop (§9) runs at the
end of the `let` body in reverse binding order.

### 5.4 Control flow

```
(if c a b)          (if c a elif d e else f)   ; elif/else chains
(cond (p1 e1) (p2 e2) (else e3))
(when c body…)      (while c body…)
(for ((i 0 n)) body…)                          ; i in [0,n)
(do e1 e2 … eN)                                ; value = eN
```
All control forms run pending Drops for any value whose owning scope
they exit, including on early `return` and condition unwinding (§9.4,
§11.3).

---

## 6. Structs & generics

```
(defstruct Point ((x :int) (y :int)))
(defstruct (Box :T) ((value :T)))
(defstruct (Pair :A :B) ((fst :A) (snd :B)))
```

- Construction: `(Point 3 4)`, `(Box 5)`, `(Pair "a" 1)`.
- Field access is via the `Gettable`/`Settable` traits (§8.6):
  `(get p x)` / `(set! (get p x) v)`. The lower-level `get-field` /
  `set-field!` are the trait's compiler-provided default and are also
  directly callable.
- Generic structs are **monomorphized** per concrete instantiation:
  one C `struct` per distinct `(Box :int)`, `(Box :f64)`, … A generic
  struct never appears in emitted C un-instantiated.
- Fields are **immutable by default.** `(mut name :T)` marks a mutable
  field; a struct with any reachable `mut` is mutable and obeys MVS
  (§9.2). `(defstruct Name (fields) :move)` marks a move-only type
  (§9.7), needed only for mutable owners of external resources.

Tuples are sugar: `(tuple a b)` ≡ an anonymous generic struct;
`(:tuple :A :B)` its type; `(get t 0)` indexed access.

---

## 7. Tagged unions & pattern matching

```
(deftype (Opt :T)
  (None)
  (Some :T))

(deftype Expr
  (Lit :int)
  (Add Expr Expr))

(match e
  ((None)      0)
  ((Some v)    v)
  (_           -1))
```

- A `deftype` is a tagged union: a discriminant + payload. Emitted as a
  tagged `struct { tag; union { … }; }`.
- `match` is exhaustive: non-exhaustive match is a compile error listing
  missing constructors. `_` is the wildcard. Patterns bind payload
  fields by position. Nested patterns allowed.
- Payloads obey the memory model (§9): a bound payload is moved out of
  the scrutinee if mutable, or shared (a reference-count bump) if
  immutable; the un-taken arms' payloads are Dropped.

---

## 8. Traits — the core

### 8.1 Declaration

```
(deftrait Show ()
  (show ((self :Self)) :cstr))

(deftrait Keyed (:K :V)
  (kget ((self :Self) (k :K)) :V)
  (khas ((self :Self) (k :K)) :bool))

(deftrait Drop ()
  (drop ((self :Self)) :unit)
  :default
  (defn drop ((self :Self)) :unit
    (for-fields (_n ty v) self
      (when (impl? Drop ty) (drop v)))))
```

- `:Self` is the implementing type. Method signatures may use the
  trait's type params (`:K :V`) and `:Self`.
- `:default` gives a default method body, used when an `impl` omits it.
  The default is type-checked generically (as if for an abstract
  `:Self`) and monomorphized per implementing type.

### 8.2 Implementation

```
(impl Show (Point)
  (defn show ((self :Point)) :cstr (fmt "({} {})" (get self x) (get self y))))

(impl (Keyed :K :V) (HashMap :K :V)
  (defn kget ((self (HashMap :K :V)) (k :K)) :V …)
  (defn khas ((self (HashMap :K :V)) (k :K)) :bool …))
```

- An `impl` provides each method (or inherits `:default`).
- Generic impls (`impl Trait (Vec :T)`) define **generic** methods:
  inference generalizes them; each concrete element type is
  monomorphized at the call site (the impl method is an ordinary poly
  function in the pipeline).

### 8.3 Dispatch

- **Static, monomorphized, zero runtime cost.** A trait call lowers to
  a direct C call to the resolved impl method. No vtables.
- **Receiver = the parameter typed `:Self`** (first parameter by
  default). Resolution uses that argument's concrete type after
  inference.
- **Return-type dispatch** (e.g. a `Default` trait, `(parse :int s)`)
  is resolved from the unification target (the type the result is
  required to have). If the target is ambiguous, it is a compile error
  demanding an annotation.
- **Cons** dispatches under type `(Cons :T)` when the element type is
  known, else `(Cons :Value)`. Because `(Cons :Value)` is a single
  concrete type, static dispatch over heterogeneous lists is well
  defined (the methods are monomorphic over `:Value`).

### 8.4 Coherence, overlap, orphans

- **At most one impl per `(Trait, Type)`** across the whole program
  (all `use`d modules included). A second impl is a compile error
  citing both source locations.
- **Orphan rule.** `(impl Trait Type …)` is permitted only if `Trait`
  **or** `Type` is declared in the current module. Prevents two
  modules giving incompatible impls for a foreign pair.
- Resolution is therefore total and order-independent: `impl?` and
  dispatch have a unique answer regardless of `use` order.

### 8.5 Bounds on generics

```
(defn maxv ((v (Vec :T))) :T where ((Ord :T))
  (reduce vmax v))

(deftrait Ord () (cmp ((self :Self) (o :Self)) :int))
```

- `where ((Trait :T) …)` constrains a type parameter.
- A constrained `:T` unifies only with a type that has the required
  impl; trait calls inside the body resolve through the bound and are
  monomorphized per concrete `:T`.
- Instantiating with a type lacking the impl is a compile error at the
  call site, naming the missing `(Trait, Type)`.
- This is the mechanism HOFs (`map`/`filter`/`reduce`) and the
  collection toolkit are written against.

### 8.6 Compiler-magic traits

Three traits the compiler has intrinsic knowledge of. All three have a
compiler-provided default; an `impl` overrides it.

- **`Drop`** — destruction. The compiler inserts `(drop x)` at the end
  of the scope owning `x` (§9). Default = field-walk: recurse `drop`
  into each field whose type `(impl? Drop ty)`. An `impl Drop` replaces
  the default for that type (and is then responsible for its fields).
- **`Gettable`** — `(get x k)`. Default = struct field access (`k` is a
  field name). An impl (e.g. `Vec` indexing) overrides; `k` is then a
  value.
- **`Settable`** — `(set! (get x k) v)`. Default = struct field store.

### 8.7 Compile-time reflection

Available inside `:default` bodies, trait method bodies, `defn-ct`, and
macros — never at runtime:

- **`(for-fields (name type val) expr body…)`** — unrolled at
  monomorphization over the **statically known** fields of `expr`'s
  concrete type, in declaration order. `name` = field-name symbol,
  `type` = the field's concrete type (usable in type position and in
  `impl?`), `val` = an lvalue for the field. Error if `expr`'s type is
  opaque/extern (no known fields). Terminates: field types are
  structurally smaller than the aggregate (no infinitely-sized struct).
- **`(impl? Trait Type)`** — compile-time `:bool`, true iff a coherent
  impl exists for the concrete `(Trait, Type)`. Resolved after all
  impls (including `use`d) are registered; total by §8.4.

---

## 9. Memory model

The central design decision. Memory is governed by a single axis,
**mutability**, and each value's discipline follows from whether its
type is deeply immutable or mutable. There is no borrow checker, no
cycle collector, no lifetime annotations, and no GC.

### 9.1 The rule

- **Deeply immutable data is reference-shared and reference-counted.** A
  value whose type is transitively immutable (no mutable field anywhere
  reachable) may be freely stored, aliased, and shared. Aliasing
  immutable data is unobservable — no write can distinguish a shared
  reference from a copy — and immutable data is **acyclic by
  construction** — a value can only reference values that already
  existed when it was built — so reference counting is **complete**: no
  cycle can ever form. `String` and `(Cons :T)` are the built-in
  instances; any immutable struct joins them.

- **Mutable data uses mutable value semantics (MVS).** Every binding
  owns its value; a reference to a *mutable* value may **never** be
  stored in a field or a variable. A mutable value is shared only as an
  `inout` borrow for the duration of a call (§9.3). The forbidden
  pairing is mutation *and* aliasing together: immutability removes the
  first, MVS removes the second.

- **Perceus reuse** turns value-semantics and immutable code into
  in-place mutation when a value is uniquely owned (refcount 1): an
  operation that logically allocates reuses the dying cells. This gives
  mutation-grade performance without mutable aliasing.

### 9.2 Mutability as a type property

- Bindings and struct fields are **immutable by default.** `mut` marks a
  mutable binding (`(let-mut …)`) or a mutable field
  (`(defstruct … ((mut count :int)))`).
- A type is **deeply immutable** (shareable) iff it has no `mut` field
  and every field type is itself deeply immutable. The compiler computes
  this by SCC over the type-reference graph; recursive immutable types
  (like `Cons`) are shareable.
- A type with any reachable `mut` is **mutable** and obeys MVS. This is
  the precise replacement for the old "struct has rc fields" test:
  shareable-immutable is rc-managed, mutable is value-semantics.

### 9.3 `inout` — borrowing mutable values

A function that mutates an argument takes it `inout`:

```
(defn translate ((p inout Point) (dx :int)) :unit
  (set! (get p x) (+ (get p x) dx)))
```

- An `inout` parameter is a **second-class reference**: valid only for
  the call, never stored. It compiles to a `T*` parameter.
- The caller must own the value for the call's duration; the callee's
  mutations are reflected in the caller.
- This is the only way to share a mutable value. There is no first-class
  mutable reference in the safe language.

### 9.4 Drop & deterministic destruction

- A value not moved out of its owning scope is **Dropped** (§8.6) at
  scope end, bindings in reverse order.
- For reference-shared immutable values, Drop is a release; the
  underlying object's destructor runs when the **last** reference is
  released.
- `return`, `match`-arm exit, loop `break`, and **condition unwinding**
  (§11.3) run all pending Drops for the scopes they exit, innermost
  first, before transferring control.
- Release of an immutable recursive value (e.g. a long `Cons` list) is
  **iterative** along the spine, not recursive, so dropping a large
  structure cannot overflow the stack.

### 9.5 Allocation

A value that does **not** escape its creating scope is stack-allocated
or held inline; a value that **escapes** (returned, or stored into an
escaping aggregate) is heap-allocated. Escape is computed by backward
analysis. This keeps allocation deterministic while letting the
programmer not think about it. `(new T args…)` forces heap allocation
explicitly; plain `(T args…)` lets escape analysis decide.

### 9.6 Graphs, cycles, and shared mutable structure

Because mutable references cannot be stored, genuinely graph-shaped or
cyclic mutable structure is expressed with **handles**, not pointers:

- The nodes live in an owned container (a `Vec`, an arena); cross-edges
  between them are **indices** (`:int`), which are primitives, not
  managed references. (A slot's generation can be carried alongside the
  index as plain data for stale-handle detection — still a primitive,
  not a language-level reference kind.)
- Indices keep nothing alive and form no cycle in the managed graph, so
  the structure may be arbitrarily cyclic in index space with no
  consequence for memory management.
- This is the same mechanism FFI uses for opaque C pointers (§14): an
  opaque token the memory model passes through but does not own.

### 9.7 Owned external resources

A struct that owns a C resource (a file handle, a socket) holds it as an
opaque primitive (§14) and gets an `impl Drop` that releases it.

- If the wrapper is **immutable and reference-shared**, there is one
  refcounted object and its `Drop` runs exactly once — the natural, safe
  default.
- If the wrapper is **mutable** and value-copied, it must be
  **move-only** (`(defstruct … :move)`): it cannot be duplicated, so the
  resource has exactly one owner and one `Drop`. Move-only is required
  only for this case.

---

## 10. Macros & compile-time evaluation

- `(defmacro name (params) body…)` — operates on s-expressions;
  `quasiquote` with `~` (unquote) and `~@` (splice); `(gensym)` for
  hygiene.
- `(defn-ct name (params) body…)` — a function evaluated **at compile
  time**. Usable from macros and `for-fields`/trait defaults. The
  compile-time evaluator accepts the self-hostable subset (§16.3).
- Macro and compile-time errors carry source locations (§15).

---

## 11. Condition system

CL-style, already part of the language:

- `(signal c)` / `(error c)` raise; `(handler-bind ((Type h)) body)`
  installs handlers; `(restart-case body (name args…) …)` /
  `(invoke-restart 'name args…)` for resumable control.
- Handlers run without unwinding; `invoke-restart` performs the
  transfer.

### 11.3 Interaction with Drop

Condition unwinding is a non-local exit (§9.4): every scope unwound
runs its pending Drops innermost-first before control reaches the
handler/restart. A handler that does not transfer control (returns
normally) does **not** trigger unwinding. This makes the condition
system memory-safe by construction.

---

## 12. Concurrency

```
(let ((h (spawn (fn () (work)))))
  (await h))
```

- `spawn` starts an OS thread; `await` joins and yields its result.
- Values crossing a `spawn` boundary: a **mutable** value is *moved* in
  (single owner, no aliasing, trivially thread-safe). A **deeply
  immutable shared** value may cross only if its refcount is atomic; the
  type system forbids sending a shared value with a non-atomic refcount
  across `spawn`.
- Atomicity is a property of the shared object's header, selected per
  type, not a separate `Arc` type. Safety is by the move-or-atomic rule,
  not by making all refcounts atomic.

> Concurrency is **deferred** (§17): it is downstream of the mutability
> model, not parallel to it, and is specified only in outline here.

---

## 13. Strings & formatting

- `String` is a **library type** (`lib/string.sysp`): a struct over a
  byte buffer, **immutable and reference-shared** (§9.1), with
  `impl Drop`, `impl Show`, `impl Iterable`, `impl Gettable` (byte/char
  index). Refcounted buffer, copy-on-write under Perceus reuse so a
  unique string mutates in place. The compiler has **no `:string`
  type**.
- `"…"` literal is sugar for a `String` constructed from a static
  buffer. `(cstr "…")` is the raw non-owning `const char*` for FFI.
- `(fmt "x={} sum={}" x (+ a b))` — compile-time-parsed format string;
  each `{}` consumes an argument and calls its `Show` impl. Field
  access `{x}` and expression `{(f x)}` interpolation supported. `fmt`
  returns a `String`.
- `Printable`/`Show` is the formatting trait; the field-walk default
  (§8.7) gives every struct a derivable `show`.

---

## 14. FFI

- `(extern name (params) :ret)` — declare a C function.
- `(extern-struct Name (fields))` — declare a C struct's layout for
  field access; the compiler emits no definition for it.
- `(include "<h>")` / `(include "rel.h")`.
- Pointer types `:ptr-T`, `(cast :T e)`, `:ptr-void`.
- `(asm! "template" (:out o) (:in i) (:clobber …))` — GCC extended
  inline asm; simple form `(asm! "…")`.
- **C pointers are opaque primitives.** A `:ptr-T`/`:ptr-void` is an
  address-sized token the memory model does not own, refcount, or reason
  about for cycles. It may be **stored in fields freely** (it is a
  primitive, not a managed reference — §9.6), and its lifetime is
  managed manually via `extern` calls.
- Lending sysp data to C (passing `(addr-of x)`) is an `inout` borrow
  (§9.3): valid for the call's duration. If C stores the pointer past
  the call, that is an unchecked escape and the programmer's
  responsibility.
- **Owning a C resource:** wrap the opaque pointer in a struct with an
  `impl Drop` that calls the C cleanup. Make it immutable + reference-
  shared (one `Drop` on last release) or `:move` (move-only) if mutable
  (§9.7). FFI values are otherwise unmanaged (no Drop, no rc).

---

## 15. Diagnostics

A spec for the failure UX, because the language's premise is
ergonomics:

- Every error carries `file:line:col` and a source caret. This holds
  for parse, inference, trait resolution, ownership/borrow, and
  macro/compile-time errors — not just the parser.
- Inference failure reports the conflicting types and both origin
  locations.
- Trait errors name the missing `(Trait, Type)` and the call site.
- Ownership errors ("use after move", "double drop") name the move
  site and the use site.
- No error is silently swallowed; a compiler that cannot prove a
  required property fails loudly rather than emitting unsound C.

---

## 16. Codegen contract

### 16.1 Readability

Generated C must read like hand-written C: source variable names
preserved where possible, single-use temporaries folded, no redundant
parentheses or `!= 0` boolification, control flow as `if/while/for`
not a CFG dump. This is testable and is a conformance requirement.

### 16.2 Mangling & ABI

- Monomorphized names: `name_<typesuffix>` (e.g. `id_int`,
  `show_Point`, `kget_HashMap_int_cstr`). Trait impl methods:
  `<method>_<selftypesuffix>`. Stable across separate compilation.
- Calling convention: immutable shared params passed by value (a
  refcounted handle); `inout` params passed as `T*` (a borrow valid for
  the call); returned/escaping values transfer ownership and their Drop
  obligation to the caller. Function ownership is **specialized** per
  call site where it pays (Lobster-style), not chosen globally.

### 16.3 Runtime & self-hosting

- The only runtime is `runtime/value.{c,h}` (Cons/Value/Fn, rc
  primitives, symbol intern) and the header-only library substrate.
  No GC, no scheduler beyond pthreads for `spawn`.
- The **self-hostable subset** = §§2–11 minus `asm!`, minus the CUDA
  backend, plus `defn-ct`. The compiler must be expressible in it.
  This subset is frozen; additions outside it are non-bootstrap.

### 16.4 Targets

C is the primary target. A CUDA target emits `__device__`/`__global__`
for functions annotated `(defn … :gpu …)`; trait monomorphization and
the no-special-types rule apply unchanged. CUDA is out of the
self-hosting subset.

---

## 17. Conformance status (roadmap)

Grounded in the current `karan/stage-16` engine.

| Area | Status |
|---|---|
| S-expr syntax, `:keyword` types, inference (HM, let-poly) | **Present** |
| `[ ]` sugar, comma params, `elif/else` | Planned (parser) |
| Functions, `recur` TCO, closures, `let`/`let-mut` | **Present** |
| Multiple return values (`values`/`let-values`) | Planned |
| `if/cond/when/while/for/do` | **Present** (no `elif/else` kw) |
| Structs, generic structs, monomorphization | **Present** |
| Tuples | Planned |
| Tagged unions + `match` (→ `Opt`/`Result`) | Planned |
| Traits: `deftrait`/`impl`, static dispatch (concrete) | **Present** |
| `:default` methods, `for-fields`, `impl?` | Planned (keystone) |
| Trait bounds (`where`) + generic impls end-to-end | Partial (concrete only; bounds Planned) |
| Coherence/orphan/overlap enforcement | Planned (currently silent-stacks) |
| Gettable/Settable (default + override) | **Present** |
| Drop (override of rc release) | **Present** for rc'd types |
| `set-field!` releases overwritten rc field | **Present** (fixed 2026-06-28) |
| `recur` over ref-typed accumulator | Rejected loudly; needs Phase 2 owned-param ARC |
| **Mutability axis: immutable-by-default + `mut`** | Planned (Phase 1, the spine) |
| **Deep-immutability (`val`) analysis** | Planned (Phase 1) |
| **Perceus reuse (FBIP) + drop specialization** | Partial (drop present; reuse Planned, Phase 2) |
| **Iterative `Cons` drop (no stack overflow)** | Planned (Phase 2) |
| **Owned-param ARC / ownership specialization** | Planned (Phase 2) |
| **MVS: `inout` borrow, no stored mutable refs** | Planned (Phase 3) |
| **Move-only (`:move`) types** | Planned (Phase 3) |
| Macros, quasiquote, gensym | **Present** (interp subprocess) |
| `defn-ct` | Planned |
| Condition system | **Present** (frozen); Drop-unwind interaction Planned |
| Concurrency (`spawn`/`await`, move-or-atomic) | Deferred (downstream of §9) |
| `String` as library type | **Present** (demo); default-`"…"` Planned |
| `fmt` / `Printable` derive | Planned |
| FFI extern/extern-struct/cast/include | **Present**; `asm!` Planned |
| FFI opaque-pointer primitives + RAII wrappers | Planned (Phase 5) |
| Diagnostics with locations below parser | Partial (parser only) |
| Readable-C contract | **Present** (paren-strip, coalesce, ARC-aware inlining) |
| Memory-safety gate (ASan/UBSan + alloc audit) | **Present** |
| Standalone compiler driver / CLI | **Absent** (all compilation in-process today) |
| Separate compilation / `--emit-header` | Planned |
| Self-hosting | Goal; subset frozen by §16.3 |
| CUDA target | Deferred |

**Cut** (resolved by the §9 mutability model, no longer roadmap items):
a borrow checker / linear ownership as a separate system, `weak`
references, generational references, age/region ordering, a cycle
collector, and `Rc`/`Arc` as a distinct feature (immutable data is
reference-counted by default; sharing *is* reference-sharing).

### 17.1 Critical path

The memory model is now the spine, so the sequencing follows it:

1. **Phase 1 — the mutability axis (§9.1–9.2).** Immutable-by-default
   plus `mut`, and the deep-immutability (`val`) analysis. *Highest
   leverage:* what is shareable, where MVS applies, and where `Drop`
   fires all derive from this split. Reuse the existing `tarjan-sccs`
   (currently the call graph) on the type-reference graph.
2. **Phase 2 — Perceus completion (§9.4).** Reuse analysis (FBIP), drop
   specialization, the iterative `Cons` drop, and owned-parameter ARC
   via ownership specialization (which fixes `recur` over ref types and
   makes the managed half correct and fast).
3. **Phase 3 — MVS for the mutable half (§9.3, §9.7).** `inout`
   borrows, the no-stored-mutable-references rule, and `:move` types.
4. **Phase 4 — features the model unblocks.** Tagged unions + `match`
   (§7), `for-fields`/`impl?` (§8.7) → `fmt`/`Printable`, trait bounds
   (§8.5), and tightening HM to require signatures at boundaries.
5. **Phase 5 — FFI hardening (§14).** RAII resource wrappers, the
   opaque-pointer-as-primitive story.
6. **Phase 6 — shipping.** A standalone compiler driver/CLI (still
   absent), separate compilation, then the self-hosting subset.

Everything hangs off Phases 1–2. Concurrency (§12) and CUDA (§16.4) are
deferred until the model is solid.
