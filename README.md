# sysp

A systems Lisp that compiles to readable C. Designed for numerical computing and GPU work, where you want to generate specialized kernels at compile time using homoiconic macros. Manual memory management, Hindley-Milner type inference with monomorphization, and direct C generation with no runtime.

## Prior Art

sysp draws inspiration from [Carp](https://github.com/carp-lang/Carp), Zig, and other systems Lisps.

## Why

Most numerical computing is either written in C/CUDA (fast but verbose) or Python/JAX (expressive but slow). sysp targets the middle: write Lisp macros that generate specialized C or CUDA code at compile time. You get homoiconic code generation for kernel specialization, gradual typing without annotation burden, and readable generated code you can inspect and debug. The type system infers precise types where possible and falls back to a boxed `Value` type (tagged union) where it can't.

## Features

- **S-expression syntax** with `[]` array literals
- **Compile-time macros** - `defmacro` over s-expressions, quasiquote with `~` and `~@`
- **Compile-time evaluation** - `defn-ct` for real homoiconic metaprogramming with `gensym`
- **Tail-call optimization** - `recur` compiles to `goto`
- **Cons cells** with automatic refcounting (`val_retain`/`val_release`)
- **Symbols** as interned integers with compile-time symbol table
- **Structs, enums, tuples, vectors** with generated C type definitions
- **Foreign function interface** - `extern` declarations, pointer types, casts
- **Type inference** - Hindley-Milner unification with constraint generation
- **Tagged unions** - `deftype`, `(:union ...)`, `runtype`/`as` for runtime dispatch

## Examples

```lisp
(defn clamp [x :int, lo :int, hi :int] :int
  (if (< x lo) lo
  else (if (> x hi) hi
  else x)))
```

Compiles to:
```c
int clamp(int x, int lo, int hi) {
  int _tmp1;
  if ((x < lo)) {
    _tmp1 = lo;
  } else {
    if ((x > hi)) {
      _tmp1 = hi;
    } else {
      _tmp1 = x;
    }
  }
  return _tmp1;
}
```

The more Lisp features you use (recursion, lambdas, closures, polymorphism, cons cells), the less the output resembles "normal" C. But it's always the same algorithm you'd write by hand; the compiler just does the mechanical work for you.

```lisp
(defn factorial [n :int, acc :int] :int
  (if (== n 0)
    acc
  else
    (recur (- n 1) (* acc n))))

(defn main [] :int
  (println (factorial 12 1))
  0)
```

Compiles to:
```c
int factorial(int n, int acc) {
  _recur_top: ;
  int _tmp1;
  if ((n == 0)) {
    _tmp1 = acc;
  } else {
    int __recur_0 = (n - 1);
    int __recur_1 = (acc * n);
    n = __recur_0;
    acc = __recur_1;
    goto _recur_top;
  }
  return _tmp1;
}

int main(void) {
  printf("%d\n", factorial(12, 1));
  return 0;
}
```

## Building

Requires SBCL (Steel Bank Common Lisp) and a C compiler.

```sh
# Compile a .sysp file to C
sbcl --script sysp.lisp input.sysp output.c

# Then compile the C
cc output.c -o program
```

For the raylib demo (tic-tac-toe):
```sh
sbcl --script sysp.lisp tictactoe.sysp tictactoe.c
cc tictactoe.c -lraylib -lm -o tictactoe
```

## Architecture

The compiler is a single Common Lisp file (`sysp.lisp`, ~3600 lines):

1. **Read** - custom readtable for `[]` arrays and backquote syntax
2. **Macro-expand** - recursive expansion of `defmacro` + built-in macros (`->`, `->>`, `when-let`, `dotimes`, etc.)
3. **Infer** - Hindley-Milner type inference with unification, generalize/instantiate for let-polymorphism
4. **Compile** - AST → C code generation with type tracking
5. **Emit** - headers, type declarations, forward decls, function bodies

## Type System

Gradual typing with Hindley-Milner inference and tagged unions:

- Unresolved types box into `Value` (tagged union: int, float, string, symbol, cons)
- Resolved types generate specialized C: `Vector_int`, `Fn_int_int`, `Cons_int_symbol`
- The inference engine supports type variables, structural unification, occurs check, and let-polymorphism
- `Value` acts as the "any" type, unifies with everything, zero annotation burden
- `deftype` for named type aliases and union types: `(deftype NumVal (:union :int :float))`
- if/cond branches with different types automatically produce union types
- `runtype` for runtime tag query, `as` for variant extraction

## Roadmap

- [x] Core language (functions, control flow, operators)
- [x] Macro system (defmacro + compile-time eval)
- [x] Cons cells with refcounting
- [x] Symbols, quasiquote, splice
- [x] Type inference (HM unification, constraint generation)
- [x] Tagged unions (sum types, deftype, runtype/as)
- [ ] Monomorphization (specialized C output per concrete type)
- [ ] Pattern matching / destructuring
- [ ] Borrow checker (linear types)
- [ ] CUDA backend (GPU kernels from Lisp)
- [ ] HPC primitives (SIMD, parallel loops)
- [ ] Self-hosting

## License

MIT

## Status

Alpha software. Expect breaking changes. All tests pass on master.

Threading is planned but not yet implemented. C99 does not have standard threads, so when threads land they will require C11 or compiler-specific extensions (pthreads, Windows threads, etc.).

