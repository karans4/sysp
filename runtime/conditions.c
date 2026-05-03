#include "conditions.h"
#include <stdio.h>
#include <stdlib.h>

static CondHandler* g_handlers = NULL;
static Restart*     g_restarts = NULL;

/* signal: walk handler stack, call each matching one. Handler runs in
 * the signaling frame (no unwind). If handler returns normally, signal
 * continues to the next match — like CL. If handler longjmps via
 * invoke_restart, control transfers to the restart-case. */
Value signal_cond(Value cond) {
    /* Convention: cond is a list whose car is the type symbol. */
    if (!is_cons(cond) || !is_sym(val_car(cond))) {
        fprintf(stderr, "signal_cond: bad condition (not (TYPE-SYM ...))\n");
        write_sexp(stderr, cond);
        fprintf(stderr, "\n");
        abort();
    }
    uint32_t tag;
    {
        Value head = val_car(cond);
        tag = val_sym_of(head);
        val_release(head);
    }
    for (CondHandler* h = g_handlers; h; h = h->next) {
        if (h->type_sym == tag) {
            /* Call handler with the condition. Signature (Value)->Value. */
            Value (*fn)(void*, Value) = (Value(*)(void*, Value))h->handler->invoke;
            return fn(h->handler->state, cond);
        }
    }
    fprintf(stderr, "Unhandled condition: ");
    write_sexp(stderr, cond);
    fprintf(stderr, "\n");
    abort();
}

Value with_handler(uint32_t type_sym, Fn* handler, Fn* body) {
    CondHandler h = { .type_sym = type_sym,
                      .handler  = handler,
                      .next     = g_handlers };
    g_handlers = &h;
    Value (*body_fn)(void*) = (Value(*)(void*))body->invoke;
    Value result = body_fn(body->state);
    g_handlers = h.next;
    return result;
}

Value with_restart(uint32_t name_sym, Fn* body, Fn* fallback) {
    Restart r;
    r.name_sym = name_sym;
    r.next     = g_restarts;
    g_restarts = &r;
    Value result;
    if (setjmp(r.jb) == 0) {
        Value (*body_fn)(void*) = (Value(*)(void*))body->invoke;
        result = body_fn(body->state);
        g_restarts = r.next;
    } else {
        Value arg = r.arg;
        g_restarts = r.next;
        Value (*fb_fn)(void*, Value) = (Value(*)(void*, Value))fallback->invoke;
        result = fb_fn(fallback->state, arg);
    }
    return result;
}

void invoke_restart(uint32_t name_sym, Value arg) {
    for (Restart* r = g_restarts; r; r = r->next) {
        if (r->name_sym == name_sym) {
            r->arg = arg;
            longjmp(r->jb, 1);
        }
    }
    fprintf(stderr, "No such restart: %s\n", sym_name(name_sym));
    abort();
}
