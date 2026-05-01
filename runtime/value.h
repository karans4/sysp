/* Value, Cons, Fn — the Lisp data model.
 *
 * Used at three deployment targets:
 *   - sysp-ir's compile-time macro expansion (linked into the macro
 *     expansion subprocess).
 *   - User programs that import the runtime to manipulate code as data
 *     or use the embedded interpreter.
 *   - On-device REPLs / hot-swap loops on embedded targets.
 *
 * The compiler treats Value, Cons, Symbol, Fn as opaque struct kinds.
 * It knows their layout enough to pass them by value (Value, Fn) or as
 * pointers (Cons*). All operations go through these helpers. */

#ifndef SYSP_VALUE_H
#define SYSP_VALUE_H

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>

typedef enum {
    VAL_NIL = 0,
    VAL_INT,
    VAL_FLOAT,
    VAL_STR,
    VAL_SYM,
    VAL_CONS,
    VAL_FN
} ValTag;

struct Cons;
struct Fn;

typedef struct Value {
    ValTag tag;
    union {
        int32_t       i;
        double        f;
        const char*   s;       /* interned literal; not rc'd at runtime */
        uint32_t      sym;
        struct Cons*  cons;
        struct Fn*    fn;
    } as;
} Value;

typedef struct Cons {
    Value car;
    Value cdr;
    int   rc;
} Cons;

/* Fn: universal callable. Compiled lambdas and interpreted closures
 * both wrap into this struct; the call site dispatches via invoke. */
typedef struct Fn {
    void* invoke;     /* compiled: function ptr.  interp: trampoline. */
    void* state;      /* compiled: env struct ptr. interp: Closure*.  */
    int   rc;
} Fn;

/* ---------- Constructors ---------- */

Value val_nil(void);
Value val_int(int32_t i);
Value val_float(double f);
Value val_str(const char* s);
Value val_sym(uint32_t sym);
Value val_cons(Value car, Value cdr);
Value val_fn(Fn* fn);

/* ---------- Predicates ---------- */

int is_nil(Value v);
int is_int(Value v);
int is_float(Value v);
int is_str(Value v);
int is_sym(Value v);
int is_cons(Value v);
int is_fn(Value v);

/* ---------- Accessors ---------- */

int32_t      val_int_of(Value v);
double       val_float_of(Value v);
const char*  val_str_of(Value v);
uint32_t     val_sym_of(Value v);
Value        val_car(Value v);
Value        val_cdr(Value v);
Fn*          val_fn_of(Value v);

/* ---------- Equality ---------- */

int val_eq(Value a, Value b);
int sym_eq(Value a, Value b);

/* ---------- Refcounting ----------
 * Primitives (int, float, str, sym, nil) are no-op. cons/fn are rc'd.
 * Caller responsible for one retain per held reference; one release per drop. */

void val_retain(Value v);
void val_release(Value v);

/* ---------- Symbol interning ---------- */

uint32_t    intern_sym(const char* name);
const char* sym_name(uint32_t id);

/* Free interned-symbol and read-string-literal pools. Optional: call at
 * end-of-process for valgrind cleanliness. */
void runtime_shutdown(void);

/* ---------- I/O ---------- */

/* Parse one s-expression from f. Returns val_nil() at EOF.
 * On parse error, prints to stderr and returns val_nil(). */
Value read_sexp(FILE* f);

/* Print v to f. No trailing newline. */
void  write_sexp(FILE* f, Value v);

/* Convenience: print to stdout with trailing newline. */
void val_println(Value v);

#endif
