# sysp

A systems Lisp that compiles to C. Homoiconic macros, manual memory management with refcounted cons cells, and Hindley-Milner type inference (in progress) with monomorphization to specialized C types.

## Prior Art

sysp draws inspiration from [Carp](https://github.com/carp-lang/Carp), Zig, and other systems Lisps.

## Why

Most Lisps are interpreted or compile to bytecode. sysp compiles directly to C — you get Lisp's macro system and expressiveness with C's performance and zero-runtime-cost abstractions. The type system infers precise types where possible and falls back to a boxed `Value` type (tagged union) where it can't, giving you gradual typing without annotations everywhere.

## Features

- **S-expression syntax** with `[]` array literals
- **Compile-time macros** — `defmacro` over s-expressions, quasiquote with `~` and `~@`
- **Compile-time evaluation** — `defn-ct` for real homoiconic metaprogramming with `gensym`
- **Tail-call optimization** — `recur` compiles to `goto`
- **Cons cells** with automatic refcounting (`val_retain`/`val_release`)
- **Symbols** as interned integers with compile-time symbol table
- **Structs, enums, tuples, vectors** with generated C type definitions
- **Foreign function interface** — `extern` declarations, pointer types, casts
- **Type inference** — Hindley-Milner unification engine (WIP: constraint generation, monomorphization)

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

1. **Read** — custom readtable for `[]` arrays and backquote syntax
2. **Macro-expand** — recursive expansion of `defmacro` + built-in macros (`->`, `->>`, `when-let`, `dotimes`, etc.)
3. **Infer** *(WIP)* — Hindley-Milner type inference with unification, generalize/instantiate for let-polymorphism
4. **Compile** — AST → C code generation with type tracking
5. **Emit** — headers, type declarations, forward decls, function bodies

## Type System (in progress)

The goal is gradual typing with aggressive monomorphization:

- Unresolved types box into `Value` (tagged union: int, float, string, symbol, cons)
- Resolved types generate specialized C: `Vector_int`, `Fn_int_int`, `Cons_int_symbol`
- The inference engine supports type variables, structural unification, occurs check, and let-polymorphism
- `Value` acts as the "any" type — unifies with everything, zero annotation burden

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
