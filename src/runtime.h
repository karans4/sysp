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

static inline String sysp_str_lit(const char *s, size_t n) {
    sysp_str_buf *b = (sysp_str_buf*)malloc(sizeof(sysp_str_buf) + n + 1);
    b->rc = 1; b->len = n; b->cap = n;
    memcpy(b->data, s, n); b->data[n] = '\0';
    return (String){b};
}

static inline String sysp_str_retain(String s) {
    if (s.b) s.b->rc++;
    return s;
}

static inline void sysp_str_release(String s) {
    if (s.b && --s.b->rc == 0) free(s.b);
}

static inline String sysp_str_concat(String a, String b) {
    size_t n = a.b->len + b.b->len;
    sysp_str_buf *nb = (sysp_str_buf*)malloc(sizeof(sysp_str_buf) + n + 1);
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
