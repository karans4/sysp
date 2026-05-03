/* CL-style condition system on the sysp runtime.
 *
 * Two parallel stacks: handlers (registered by type) and restarts
 * (registered by name with a jmp_buf).
 *
 * signal_cond walks the handler stack and invokes each matching handler
 * in the SIGNALING frame — no unwind unless the handler invokes a restart.
 * If the handler returns normally, signal_cond returns its result and
 * execution continues at the signal site.
 *
 * invoke_restart longjmps back to the matching restart-case, where the
 * caller's setjmp returns nonzero and runs the recovery arm. */

#ifndef SYSP_CONDITIONS_H
#define SYSP_CONDITIONS_H

#include "value.h"
#include <setjmp.h>

typedef struct CondHandler {
    uint32_t type_sym;
    Fn*      handler;            /* invoke: Value(*)(void*, Value cond) */
    struct CondHandler* next;
} CondHandler;

typedef struct Restart {
    uint32_t name_sym;
    jmp_buf  jb;
    Value    arg;                /* populated by invoke_restart */
    struct Restart* next;
} Restart;

/* Public entry points. */
Value signal_cond(Value cond);
Value with_handler(uint32_t type_sym, Fn* handler, Fn* body);
Value with_restart(uint32_t name_sym, Fn* body, Fn* fallback);
void  invoke_restart(uint32_t name_sym, Value arg);

#endif
