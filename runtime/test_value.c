/* Standalone unit test for runtime/value.c */
#include "value.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>

static int ok = 0, fail = 0;

#define CHECK(label, cond) do {                              \
    if (cond) { ok++; printf("%s: ok\n", label); }           \
    else      { fail++; printf("%s: FAIL\n", label); }       \
} while (0)

static void test_basics(void) {
    Value n = val_nil();
    CHECK("nil is nil", is_nil(n));
    CHECK("int is int", is_int(val_int(42)));
    CHECK("int_of",     val_int_of(val_int(42)) == 42);
    CHECK("sym_eq",     sym_eq(val_sym(7), val_sym(7)));
    CHECK("sym_neq",    !sym_eq(val_sym(1), val_sym(2)));
}

static void test_intern(void) {
    uint32_t a = intern_sym("foo");
    uint32_t b = intern_sym("bar");
    uint32_t c = intern_sym("foo");
    CHECK("intern unique", a != b);
    CHECK("intern same",   a == c);
    CHECK("sym_name foo",  strcmp(sym_name(a), "foo") == 0);
}

/* val_cons borrows its args; caller must release intermediates. Helper
 * to build (a b c) without leaking. */
static Value mk3(Value a, Value b, Value c) {
    Value t2 = val_cons(c, val_nil());
    Value t1 = val_cons(b, t2); val_release(t2);
    Value t0 = val_cons(a, t1); val_release(t1);
    return t0;
}

static void test_cons(void) {
    Value lst = mk3(val_int(1), val_int(2), val_int(3));
    CHECK("car = 1", val_int_of(val_car(lst)) == 1);
    CHECK("cadr = 2", val_int_of(val_car(val_cdr(lst))) == 2);
    CHECK("caddr = 3", val_int_of(val_car(val_cdr(val_cdr(lst)))) == 3);
    CHECK("cdddr = nil", is_nil(val_cdr(val_cdr(val_cdr(lst)))));
    val_release(lst);
}

static void test_write(void) {
    /* Build (1 (2 3) "hi" foo) and print to a memstream */
    char buf[256];
    FILE* f = fmemopen(buf, sizeof(buf), "w");
    Value inner_t1 = val_cons(val_int(3), val_nil());
    Value inner    = val_cons(val_int(2), inner_t1); val_release(inner_t1);
    Value t3 = val_cons(val_sym(intern_sym("foo")), val_nil());
    Value t2 = val_cons(val_str("hi"), t3); val_release(t3);
    Value t1 = val_cons(inner, t2); val_release(inner); val_release(t2);
    Value lst = val_cons(val_int(1), t1); val_release(t1);
    write_sexp(f, lst);
    fclose(f);
    CHECK("write_sexp", strcmp(buf, "(1 (2 3) \"hi\" foo)") == 0);
    val_release(lst);
}

static void test_read_basic(void) {
    FILE* f = fmemopen("(1 2 3)", 7, "r");
    Value v = read_sexp(f);
    fclose(f);
    CHECK("read 3-list cons",  is_cons(v));
    CHECK("read car=1",        val_int_of(val_car(v)) == 1);
    CHECK("read cadr=2",       val_int_of(val_car(val_cdr(v))) == 2);
    val_release(v);
}

static void test_read_nested(void) {
    const char* src = "(if (> x 0) (foo x) nil)";
    FILE* f = fmemopen((char*)src, strlen(src), "r");
    Value v = read_sexp(f);
    fclose(f);
    CHECK("read nested cons", is_cons(v));
    CHECK("head is 'if",      sym_eq(val_car(v), val_sym(intern_sym("if"))));
    val_release(v);
}

static void test_read_quoted(void) {
    FILE* f = fmemopen("'foo", 4, "r");
    Value v = read_sexp(f);
    fclose(f);
    CHECK("'foo head = quote",
          sym_eq(val_car(v), val_sym(intern_sym("quote"))));
    CHECK("'foo arg = foo",
          sym_eq(val_car(val_cdr(v)), val_sym(intern_sym("foo"))));
    val_release(v);
}

static void test_quasiquote_unquote(void) {
    const char* src = "`(a ~b ~@c)";
    FILE* f = fmemopen((char*)src, strlen(src), "r");
    Value v = read_sexp(f);
    fclose(f);
    /* (quasiquote (a (unquote b) (splice c))) */
    CHECK("qq head", sym_eq(val_car(v), val_sym(intern_sym("quasiquote"))));
    Value inner = val_car(val_cdr(v));   /* (a (unquote b) (splice c)) */
    CHECK("qq inner is cons", is_cons(inner));
    CHECK("qq elem 0 = a",
          sym_eq(val_car(inner), val_sym(intern_sym("a"))));
    Value uq = val_car(val_cdr(inner));
    CHECK("uq head = unquote",
          sym_eq(val_car(uq), val_sym(intern_sym("unquote"))));
    Value sp = val_car(val_cdr(val_cdr(inner)));
    CHECK("splice head = splice",
          sym_eq(val_car(sp), val_sym(intern_sym("splice"))));
    val_release(v);
}

static void test_round_trip(void) {
    const char* src = "(defn f (x) (+ x 1))";
    FILE* in = fmemopen((char*)src, strlen(src), "r");
    Value v = read_sexp(in);
    fclose(in);
    char buf[256];
    FILE* out = fmemopen(buf, sizeof(buf), "w");
    write_sexp(out, v);
    fclose(out);
    CHECK("round-trip", strcmp(buf, src) == 0);
    val_release(v);
}

int main(void) {
    test_basics();
    test_intern();
    test_cons();
    test_write();
    test_read_basic();
    test_read_nested();
    test_read_quoted();
    test_quasiquote_unquote();
    test_round_trip();
    printf("\n%d passed, %d failed\n", ok, fail);
    runtime_shutdown();
    return fail ? 1 : 0;
}
