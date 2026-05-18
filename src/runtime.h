#ifndef SYSP_RUNTIME_H
#define SYSP_RUNTIME_H

#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

typedef struct {
    size_t rc;
    size_t len;
    size_t cap;
    char data[];
} sysp_str_buf;

typedef struct { sysp_str_buf *b; } String;

/* ---- allocation audit (test-only, -DSYSP_ALLOC_AUDIT) ----
 * A deterministic leak gate for the refcounting runtime: every rc'd
 * object alloc bumps a counter, every free drops it, and an atexit
 * handler fails the process if it isn't zero. Catches forgotten
 * releases — the #1 ARC bug — which macOS `leaks` (reachability-based)
 * cannot. No-op unless the flag is set, so shipped builds are untouched.
 * Weak so the single counter coalesces across value.c + this header. */
#ifdef SYSP_ALLOC_AUDIT
__attribute__((weak)) long sysp_live_objs = 0;
static inline void sysp_audit_inc(void) { sysp_live_objs++; }
static inline void sysp_audit_dec(void) { sysp_live_objs--; }
__attribute__((weak)) void sysp_audit_report(void) {
    if (sysp_live_objs != 0) {
        fflush(NULL);
        fprintf(stderr, "SYSP_LEAK: %ld live object(s) at exit\n",
                sysp_live_objs);
        _Exit(77);
    }
}
__attribute__((constructor)) static void sysp_audit_install(void) {
    atexit(sysp_audit_report);
}
#else
#define sysp_audit_inc() ((void)0)
#define sysp_audit_dec() ((void)0)
#endif

static inline String sysp_str_lit(const char *s, size_t n) {
    sysp_str_buf *b = (sysp_str_buf*)malloc(sizeof(sysp_str_buf) + n + 1);
    sysp_audit_inc();
    b->rc = 1; b->len = n; b->cap = n;
    memcpy(b->data, s, n); b->data[n] = '\0';
    return (String){b};
}

static inline String sysp_str_retain(String s) {
    if (s.b) s.b->rc++;
    return s;
}

static inline void sysp_str_release(String s) {
    if (s.b && --s.b->rc == 0) { sysp_audit_dec(); free(s.b); }
}

static inline String sysp_str_concat(String a, String b) {
    size_t n = a.b->len + b.b->len;
    sysp_str_buf *nb = (sysp_str_buf*)malloc(sizeof(sysp_str_buf) + n + 1);
    sysp_audit_inc();
    nb->rc = 1; nb->len = n; nb->cap = n;
    memcpy(nb->data, a.b->data, a.b->len);
    memcpy(nb->data + a.b->len, b.b->data, b.b->len);
    nb->data[n] = '\0';
    return (String){nb};
}

static inline int sysp_str_len(String s) { return (int)s.b->len; }

static inline void sysp_str_print(String s) {
    fwrite(s.b->data, 1, s.b->len, stdout);
    fputc('\n', stdout);
}

#endif
