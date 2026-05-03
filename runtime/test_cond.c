/* Standalone test: signal_cond / with_handler / with_restart / invoke_restart */
#include "conditions.h"
#include "value.h"
#include <stdio.h>
#include <string.h>

static int ok = 0, fail = 0;

#define CHECK(label, cond) do {                              \
    if (cond) { ok++; printf("%s: ok\n", label); }           \
    else      { fail++; printf("%s: FAIL\n", label); }       \
} while (0)

static Fn make_test_fn(void* invoke) {
    return (Fn){ .invoke = invoke, .state = NULL, .rc = 1 };
}

/* ---------- Test 1: handler returns a normal value ---------- */
static Value sentinel_handler(void* env, Value cond) {
    (void)env; val_release(cond);
    return val_int(42);
}
static Value signal_body(void* env) {
    (void)env;
    Value tag  = val_sym(intern_sym("parse-error"));
    Value cond = val_cons(tag, val_nil());
    val_release(tag);
    Value r = signal_cond(cond);
    val_release(cond);
    return r;
}
static void test_handler_returns_normally(void) {
    Fn h = make_test_fn((void*)sentinel_handler);
    Fn b = make_test_fn((void*)signal_body);
    Value r = with_handler(intern_sym("parse-error"), &h, &b);
    CHECK("handler returns normally", val_int_of(r) == 42);
    val_release(r);
}

/* ---------- Test 2: restart invoked directly from body ---------- */
static Value direct_invoke_body(void* env) {
    (void)env;
    invoke_restart(intern_sym("use-default"), val_int(7));
    return val_nil();   /* unreachable */
}
static Value identity_fallback(void* env, Value arg) {
    (void)env; return arg;
}
static void test_restart_direct(void) {
    Fn b  = make_test_fn((void*)direct_invoke_body);
    Fn fb = make_test_fn((void*)identity_fallback);
    Value r = with_restart(intern_sym("use-default"), &b, &fb);
    CHECK("restart direct invoke", val_int_of(r) == 7);
    val_release(r);
}

/* ---------- Test 3: full CL flow: signal → handler → invoke-restart ---------- */

/* Handler invokes a restart with arg=99. Doesn't return. */
static Value invoking_handler(void* env, Value cond) {
    (void)env; val_release(cond);
    invoke_restart(intern_sym("use-default"), val_int(99));
    return val_nil();   /* unreachable */
}

/* The body of with_restart: install handler-bind, then signal. */
static Value handler_bind_body(void* env) {
    (void)env;
    Fn h = make_test_fn((void*)invoking_handler);
    Fn inner = make_test_fn((void*)signal_body);
    return with_handler(intern_sym("parse-error"), &h, &inner);
}

static void test_full_cl_flow(void) {
    Fn body = make_test_fn((void*)handler_bind_body);
    Fn fb   = make_test_fn((void*)identity_fallback);
    Value r = with_restart(intern_sym("use-default"), &body, &fb);
    CHECK("CL flow: signal → handler → restart", val_int_of(r) == 99);
    val_release(r);
}

/* ---------- Test 4: nested restarts ---------- */
static Value invoke_outer_body(void* env) {
    (void)env;
    invoke_restart(intern_sym("outer"), val_int(11));
    return val_nil();
}
static Value invoke_outer_via_inner_body(void* env) {
    (void)env;
    Fn inner = make_test_fn((void*)invoke_outer_body);
    Fn fb    = make_test_fn((void*)identity_fallback);
    /* Inner restart-case for "inner". Body invokes outer (skipping inner). */
    return with_restart(intern_sym("inner"), &inner, &fb);
}
static void test_nested_restart_skips(void) {
    Fn body = make_test_fn((void*)invoke_outer_via_inner_body);
    Fn fb   = make_test_fn((void*)identity_fallback);
    Value r = with_restart(intern_sym("outer"), &body, &fb);
    CHECK("nested restarts: invoke skips inner", val_int_of(r) == 11);
    val_release(r);
}

int main(void) {
    test_handler_returns_normally();
    test_restart_direct();
    test_full_cl_flow();
    test_nested_restart_skips();
    printf("\n%d passed, %d failed\n", ok, fail);
    runtime_shutdown();
    return fail ? 1 : 0;
}
