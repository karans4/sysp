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
- **Type inference** - Hindley-Milner unification engine (WIP: constraint generation, monomorphization)

## Example

```lisp
(defn factorial [n :int, acc :int] :int
  (if (== n 0) (return acc)
  else (recur (- n 1) (* acc n)))
  0)

(defn main []
  (println (factorial 12 1)))
```

Compiles to:
```c
int factorial(int n, int acc) {
_recur_top:
    if ((n == 0)) { return acc; }
    else { int _t0 = (n - 1); int _t1 = (acc * n); n = _t0; acc = _t1; goto _recur_top; }
    return 0;
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

The compiler is a single Common Lisp file (`sysp.lisp`, ~1900 lines):

1. **Read** - custom readtable for `[]` arrays and backquote syntax
2. **Macro-expand** - recursive expansion of `defmacro` + built-in macros (`->`, `->>`, `when-let`, `dotimes`, etc.)
3. **Infer** *(WIP)* - Hindley-Milner type inference with unification, generalize/instantiate for let-polymorphism
4. **Compile** - AST → C code generation with type tracking
5. **Emit** - headers, type declarations, forward decls, function bodies

## Type System (in progress)

The goal is gradual typing with aggressive monomorphization:

- Unresolved types box into `Value` (tagged union: int, float, string, symbol, cons)
- Resolved types generate specialized C: `Vector_int`, `Fn_int_int`, `Cons_int_symbol`
- The inference engine supports type variables, structural unification, occurs check, and let-polymorphism
- `Value` acts as the "any" type - unifies with everything, zero annotation burden

## Roadmap

- [x] Core language (functions, control flow, operators)
- [x] Macro system (defmacro + compile-time eval)
- [x] Cons cells with refcounting
- [x] Symbols, quasiquote, splice
- [ ] Type inference (constraint generation from AST)
- [ ] Monomorphization (specialized C output per concrete type)
- [ ] Pattern matching / destructuring
- [ ] Tagged unions (sum types)
- [ ] Borrow checker (linear types)
- [ ] CUDA backend (GPU kernels from Lisp)
- [ ] HPC primitives (SIMD, parallel loops)
- [ ] Self-hosting

## License

MIT

## Warnings:

This is a personal project and alpha software. Do expect dramatic changes between versions. Don't expect it to run on every commit. The following version [runs](https://github.com/karans4/sysp/tree/1521ee6dae988c2aef5e8c84f2c72ebacd6759f8).

Due to the way closures and reference counting are implemented, threads (not yet implemented) will only be supported in C11 or higher. For those using C99, you will have to rely on compiler extensions. No specific compilers will be supported, but I will probably make it work in the top 3 or 4 compilers from 2006 for C99.

