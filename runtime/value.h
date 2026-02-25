/* sysp Value Type System — runtime support */
/* Tagged union for dynamic values: nil, int, float, string, symbol, cons */

#ifndef SYSP_VALUE_H
#define SYSP_VALUE_H

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

typedef uint32_t Symbol;
typedef struct Cons Cons;

typedef enum {
    VAL_NIL,
    VAL_INT,
    VAL_FLOAT,
    VAL_STR,
    VAL_SYM,
    VAL_CONS
} ValueTag;

typedef struct {
    ValueTag tag;
    union {
        int as_int;
        double as_float;
        const char* as_str;
        Symbol as_sym;
        Cons* as_cons;
    };
} Value;

struct Cons {
    Value car;
    Value cdr;
    int refcount;
};

/* Value constructors */
static Value val_nil(void) { return (Value){.tag = VAL_NIL}; }
static Value val_int(int x) { Value v = {.tag = VAL_INT}; v.as_int = x; return v; }
static Value val_float(double x) { Value v = {.tag = VAL_FLOAT}; v.as_float = x; return v; }
static Value val_str(const char* x) { Value v = {.tag = VAL_STR}; v.as_str = x; return v; }
static Value val_sym(Symbol x) { Value v = {.tag = VAL_SYM}; v.as_sym = x; return v; }
static Value val_cons(Cons* x) { Value v = {.tag = VAL_CONS}; v.as_cons = x; return v; }

static Cons* make_cons(Value car, Value cdr) {
    Cons* c = malloc(sizeof(Cons));
    c->car = car;
    c->cdr = cdr;
    c->refcount = 1;
    return c;
}

/* Reference counting */
static Value val_retain(Value v) {
    if (v.tag == VAL_CONS && v.as_cons)
        RC_INC(v.as_cons->refcount);
    return v;
}

static void val_release(Value v) {
    if (v.tag == VAL_CONS && v.as_cons && RC_DEC(v.as_cons->refcount) == 1) {
        val_release(v.as_cons->car);
        val_release(v.as_cons->cdr);
        free(v.as_cons);
    }
}

/* Accessors (borrow semantics - caller retains if storing) */
static Value sysp_car(Value v) { return v.as_cons->car; }
static Value sysp_cdr(Value v) { return v.as_cons->cdr; }
static int sysp_nilp(Value v) { return v.tag == VAL_NIL; }

static int sysp_sym_eq(Value a, Value b) {
    return a.tag == VAL_SYM && b.tag == VAL_SYM && a.as_sym == b.as_sym;
}

/* List operations */
static Value sysp_append(Value lst, Value tail) {
    if (lst.tag == VAL_NIL)
        return val_retain(tail);
    return val_cons(make_cons(val_retain(lst.as_cons->car),
                              sysp_append(lst.as_cons->cdr, tail)));
}

static Value sysp_list(int n, ...) {
    va_list args;
    va_start(args, n);
    Value result = val_nil();
    Value* values = malloc(n * sizeof(Value));
    for (int i = 0; i < n; i++)
        values[i] = va_arg(args, Value);
    va_end(args);
    for (int i = n - 1; i >= 0; i--)
        result = val_cons(make_cons(val_retain(values[i]), result));
    free(values);
    return result;
}

/* Print function */
static void sysp_print_value(Value v) {
    switch (v.tag) {
    case VAL_NIL:
        printf("nil");
        break;
    case VAL_INT:
        printf("%d", v.as_int);
        break;
    case VAL_FLOAT:
        printf("%f", v.as_float);
        break;
    case VAL_STR:
        printf("%s", v.as_str);
        break;
    case VAL_SYM:
        if (v.as_sym < sizeof(_sym_names)/sizeof(_sym_names[0]))
            printf("%s", _sym_names[v.as_sym]);
        else
            printf("g%u", v.as_sym);
        break;
    case VAL_CONS: {
        printf("(");
        sysp_print_value(v.as_cons->car);
        Value tail = v.as_cons->cdr;
        while (tail.tag == VAL_CONS) {
            printf(" ");
            sysp_print_value(tail.as_cons->car);
            tail = tail.as_cons->cdr;
        }
        if (tail.tag != VAL_NIL) {
            printf(" . ");
            sysp_print_value(tail);
        }
        printf(")");
        break;
    }
    }
}

#endif /* SYSP_VALUE_H */
