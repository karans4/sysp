# sysp

A systems Lisp that compiles to readable C. Designed for numerical computing and GPU work, where you want to generate specialized kernels at compile time using homoiconic macros. Manual memory management, Hindley-Milner type inference with monomorphization, and direct C generation with no runtime.

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
- **Type inference** — Hindley-Milner unification with constraint generation
- **Tagged unions** — `deftype`, `(:union ...)`, pattern matching with `match`
- **Closures** — fat pointers (`Fn = {fn, env}`), free variable analysis, direct call optimization
- **Monomorphization** — polymorphic functions (`:?` type vars) stamped per concrete call site
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

```lisp
(defn clamp [x :int, lo :int, hi :int] :int
  (if (< x lo) lo
  elif (> x hi) hi
  else x))
```

Compiles to:
```c
int clamp(int x, int lo, int hi) {
  if ((x < lo)) {
    return lo;
  } else if ((x > hi)) {
    return hi;
  } else {
    return x;
  }
}
```

Higher-order functions work as real values — `defn` functions are automatically wrapped into `Fn` structs when passed to polymorphic HOFs:

```lisp
(use core)

(defn double [x :int] :int (* x 2))
(defn add [a :int, b :int] :int (+ a b))

(defn main [] :int
  (let v (vector 1 2 3 4 5))
  (let doubled (map double v))        ;; (2 4 6 8 10)
  (let evens (filter even? v))        ;; (2 4)
  (let sum (reduce add 0 v))          ;; 15
  (println sum)
  0)
```

Closures capture their environment:

```lisp
(defn make-adder [n :int] :fn (:int) :int
  (lambda [x :int] :int (+ x n)))

(defn main [] :int
  (let add5 (make-adder 5))
  (println (add5 10))  ;; 15
  0)
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

The compiler is a single Common Lisp file (`sysp.lisp`, ~7200 lines):

1. **Parse** — hand-written tokenizer + recursive descent (not CL's reader)
2. **Macro-expand** — recursive expansion of `defmacro` + built-in macros
3. **Infer** — Hindley-Milner type inference with unification
4. **Compile** — AST → C code generation with type tracking, monomorphization
5. **Emit** — headers, type declarations, forward decls, function bodies

Standard library in `lib/`:

| Module | Contents |
|--------|----------|
| `core` | Predicates (`zero?`, `even?`, `odd?`), arithmetic (`inc`, `dec`, `abs`, `min`, `max`, `clamp`), HOFs (`map`, `filter`, `reduce`) |
| `string` | String operations |
| `io` | File I/O |
| `mem` | Memory utilities |
| `math` | Math functions |
| `fmt` | String interpolation |
| `cuda` | CUDA kernel support |
| `raylib` | Raylib game library bindings |

## Type System

Gradual typing with Hindley-Milner inference and tagged unions:

- Unresolved types box into `Value` (tagged union: int, float, string, symbol, cons)
- Resolved types generate specialized C: `Vector_int`, `Fn_int_int`, `Cons_int_symbol`
- Polymorphic functions use `:?` type variables, monomorphized at call site
- `deftype` for named type aliases and union types: `(deftype NumVal (:union :int :float))`
- if/cond branches with different types automatically produce union types
- `match` for pattern matching on unions and structs

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

Alpha. 35 tests, valgrind clean. Expect breaking changes.

## Self-Hosting

The end goal is for sysp to compile itself. The bootstrap compiler (`sysp.lisp`, Common Lisp) would be replaced by `sysp.sysp`, which compiles to `bootstrap.c` — a checked-in generated C file that can build the compiler with just `cc bootstrap.c -o sysp`. New contributors need only a C compiler, not SBCL.

## License

MIT
