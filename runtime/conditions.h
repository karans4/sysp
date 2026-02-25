/* sysp Condition System Runtime */
/* CL-style conditions: restart-case, handler-bind, signal, invoke-restart */

#ifndef SYSP_CONDITIONS_H
#define SYSP_CONDITIONS_H

#include <setjmp.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct _sysp_restart {
    const char* name;
    jmp_buf buf;
    void* value;
    char _vbuf[16];
    struct _sysp_restart* next;
} _sysp_restart;

typedef struct _sysp_handler {
    const char* type;
    void (*fn)(void*, void*);
    void* env;
    struct _sysp_handler* next;
} _sysp_handler;

static SYSP_TLS _sysp_restart* _restart_stack = NULL;
static SYSP_TLS _sysp_handler* _handler_stack = NULL;

static void _sysp_signal(const char* type, void* val) {
    _sysp_handler* h = _handler_stack;
    while (h) {
        if (strcmp(h->type, type) == 0) {
            h->fn(h->env, val);
        }
        h = h->next;
    }
    fprintf(stderr, "Unhandled condition: %s\n", type);
    abort();
}

static void _sysp_invoke_restart(const char* name, void* val, size_t vsize) {
    _sysp_restart* r = _restart_stack;
    while (r) {
        if (strcmp(r->name, name) == 0) {
            if (val && vsize <= sizeof(r->_vbuf)) {
                memcpy(r->_vbuf, val, vsize);
                r->value = r->_vbuf;
            } else {
                r->value = val;
            }
            longjmp(r->buf, 1);
        }
        r = r->next;
    }
    fprintf(stderr, "No restart: %s\n", name);
    abort();
}

#endif /* SYSP_CONDITIONS_H */
