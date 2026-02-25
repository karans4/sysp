# sysp

A systems Lisp that compiles to readable C. Hindley-Milner type inference with monomorphization, homoiconic macros for compile-time code generation, and direct C output with no runtime. The inference engine resolves pointer types, struct fields, and numeric promotions — a 1600-line Apple II emulator compiles with zero type annotations.

## Prior Art

sysp draws inspiration from [Carp](https://github.com/carp-lang/Carp), Zig, and other systems Lisps.

## Why

Most numerical computing is either written in C/CUDA (fast but verbose) or Python/JAX (expressive but slow). sysp targets the middle: write Lisp macros that generate specialized C or CUDA code at compile time. You get homoiconic code generation for kernel specialization, gradual typing without annotation burden, and readable generated code you can inspect and debug. The type system infers precise types where possible and falls back to a boxed `Value` type (tagged union) where it can't.

## Features

- **S-expression syntax** with `[]` array literals and custom parser (not CL's reader)
- **Compile-time macros** — `defmacro` over s-expressions, quasiquote with `~` and `~@`
- **Compile-time evaluation** — `defn-ct` for real homoiconic metaprogramming with `gensym`
- **Tail-call optimization** — `recur` compiles to `goto`
- **Cons cells** with automatic refcounting (`val_retain`/`val_release`)
- **Symbols** as interned integers with compile-time symbol table
- **Structs, enums, tuples, vectors, hash maps** with generated C type definitions
- **Foreign function interface** — `extern` declarations, pointer types, casts
- **Type inference** — Hindley-Milner with struct field reverse lookup, pointer element tracking, numeric promotion, void detection
- **Tagged unions** — `deftype`, `(:union ...)`, pattern matching with `match`
- **Closures** — fat pointers (`Fn = {fn, env}`), free variable analysis, C-compatible non-capturing lambdas
- **Monomorphization** — auto-polymorphic functions stamped per concrete call site (`:?` explicit or inferred)
- **Threads** — `spawn`/`await` via pthreads, TLS-safe refcounting
- **Condition system** — CL-style `restart-case`, `handler-bind`, `signal`, `invoke-restart`
- **ARC memory** — `(new T args)` for RC-managed heap objects, escape analysis for stack promotion
- **Multiple return values** — `(values a b)` + `(let-values [(q r) (f)] ...)`
- **Inline assembly** — `(asm! ...)` for GCC extended asm, simple and extended forms
- **Module system** — `(use mod)` with qualified imports, `:only`, `:as` aliases, `--emit-header`
- **String interpolation** — `(fmt "x is {x}, sum is {(+ a b)}")`
- **HOFs as real functions** — `map`, `filter`, `reduce` are polymorphic functions, not macros
- **Collection toolkit** — `first`, `last`, `count`, `some`, `every?`, `take`, `drop`, `reverse`, `concat`, `distinct`, `frequencies`, etc.

## Examples

Types are inferred — annotations are optional. These are equivalent:

```lisp
;; Fully annotated
(defn clamp [x :int, lo :int, hi :int] :int
  (if (< x lo) lo
  elif (> x hi) hi
  else x))

;; No annotations — same generated C
(defn clamp [x, lo, hi]
  (if (< x lo) lo
  elif (> x hi) hi
  else x))
```

```c
int clamp(int x, int lo, int hi) {
  if ((x < lo)) { return lo; }
  else if ((x > hi)) { return hi; }
  else { return x; }
}
```

Struct field access infers struct types via reverse lookup:

```lisp
(struct Point [x :int, y :int])

(defn manhattan [p]        ;; p inferred as Point from field access
  (+ p.x p.y))
```

Closures capture their environment as fat pointers. Non-capturing lambdas compile to plain C functions — directly passable to C APIs like `qsort`:

```lisp
(defn make-adder [n :int] :fn (:int) :int
  (lambda [x :int] :int (+ x n)))

(defn main [] :int
  (let add5 (make-adder 5))
  (println (add5 10))  ;; 15
  0)
```

```c
typedef struct { int y; } _env_1;

// Capturing lambda — env struct, void* ctx
static int _lambda_1(void* _ctx, int x) {
    _env_1* _env = (_env_1*)_ctx;
    return (x + _env->y);
}

// Non-capturing — plain C function, no void*
static int _lambda_2(int x) {
    return (x * 2);
}

// Thin wrapper lets it work with sysp's Fn fat pointers too
static int _lambda_2_wrap(void* _ctx, int x) {
    return _lambda_2(x);
}
```

Any `defn` passed to a HOF gets the same treatment — auto-wrapped into a `Fn` struct. `recur` inside lambdas compiles to `goto`.

Polymorphic functions auto-generalize and monomorphize:

```lisp
(defn identity [x] x)     ;; unconstrained → auto-poly
(identity 42)              ;; instantiates identity_int
(identity 3.14)            ;; instantiates identity_float
```

Macros operate on s-expressions at compile time:

```lisp
(defmacro swap! [a b]
  (let tmp (gensym))
  `(do (let ~tmp ~a)
       (set! ~a ~b)
       (set! ~b ~tmp)))
```

## Building

Requires SBCL (Steel Bank Common Lisp) and a C compiler.

```sh
# Compile a .sysp file to C
sbcl --script sysp.lisp input.sysp output.c

# Then compile the C
cc -std=c99 output.c -o program

# Run tests
bash run-tests.sh
```

## Architecture

The compiler is a single Common Lisp file (`sysp.lisp`, ~7400 lines, targeting ~4000). The design principle: keep the compiler dumb, push everything into libraries via traits. The compiler knows nothing about Vector, HashMap, or String — they're ordinary generic structs defined in library code. Three built-in traits (Drop, Gettable, Settable) plus a field-walking intrinsic provide the general mechanisms; everything else is library. See `TRAITS-VISION.md` for the full architectural vision.

1. **Parse** — hand-written tokenizer + recursive descent (not CL's reader)
2. **Macro-expand** — recursive expansion of `defmacro` + built-in macros
3. **Infer** — Hindley-Milner type inference with unification
4. **Compile** — AST → C code generation with type tracking, monomorphization
5. **Emit** — headers, type declarations, forward decls, function bodies

Standard library in `lib/`:

| Module | Contents |
|--------|----------|
| `core` | Predicates (`zero?`, `even?`, `odd?`), arithmetic (`inc`, `dec`, `abs`, `min`, `max`, `clamp`), HOFs (`map`, `filter`, `reduce`) |
| `collections` | Vector, HashMap — structs, traits (Indexed, Keyed, Hashable), mutation ops |
| `string` | String operations |
| `io` | File I/O |
| `mem` | Memory utilities |
| `math` | Math functions |
| `fmt` | String interpolation |
| `cuda` | CUDA kernel support |
| `raylib` | Raylib game library bindings |

## Type System

Hindley-Milner inference with monomorphization — annotations are optional:

- **Inference**: pointer element types from `ptr-deref`/`ptr-set!`, struct types from field access (reverse lookup), numeric promotion across arithmetic/bitwise/branches, void detection for statement-ending functions
- **Auto-polymorphism**: functions with unconstrained type variables auto-generalize; each call site instantiates a concrete monomorphized version
- **Implicit coercion**: widening numeric conversions (int→float, u8→int) inserted automatically; narrowing (float→int) requires explicit `(cast :int ...)`
- Unresolved types box into `Value` (tagged union: int, float, string, symbol, cons)
- Resolved types generate specialized C: `Vector_int`, `Fn_int_int`, `Cons_int_symbol`
- `deftype` for named type aliases and union types, `match` for pattern matching

## Roadmap

- [x] Core language (functions, control flow, operators)
- [x] Macro system (defmacro + compile-time eval)
- [x] Cons cells with refcounting
- [x] Symbols, quasiquote, splice
- [x] Type inference (HM unification, constraint generation)
- [x] Tagged unions (sum types, deftype, match)
- [x] Monomorphization (specialized C output per concrete type)
- [x] Closures (fat pointers, free variable analysis)
- [x] Threads (spawn/await, TLS-safe RC)
- [x] Condition system (restart-case, handler-bind)
- [x] ARC memory (new, escape analysis)
- [x] Module system (use, emit-header, namespacing)
- [x] Multiple return values
- [x] Inline assembly
- [x] HOFs as real polymorphic functions
- [x] CUDA backend (lib/cuda.sysp — untested, needs GPU hardware)
- [ ] Self-hosting (bootstrap compiler ships as generated C)

## Status

Alpha. 39 tests, valgrind clean. Actively refactoring toward ~4000 line compiler via trait-based architecture. Expect breaking changes.

## Self-Hosting

The end goal is for sysp to compile itself. The bootstrap compiler (`sysp.lisp`, Common Lisp) would be replaced by `sysp.sysp`, which compiles to `bootstrap.c` — a checked-in generated C file that can build the compiler with just `cc bootstrap.c -o sysp`. New contributors need only a C compiler, not SBCL.

## License

MIT
