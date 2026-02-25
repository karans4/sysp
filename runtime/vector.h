/* sysp Vector Runtime — macro-based generic vector helpers */
/* Usage: SYSP_VECTOR_PUSH(Vec_int, int, int) generates sysp_vecpush_int */
/*        SYSP_VECTOR_MAKE(Vec_int, int, int) generates sysp_mkvec_int  */
/*        SYSP_VECTOR_SHOW(Vec_int, int, show_int) generates show_Vec_int */

#ifndef SYSP_VECTOR_H
#define SYSP_VECTOR_H

#include <stdlib.h>
#include <string.h>

#define SYSP_VECTOR_PUSH(VEC_T, ELEM_T, MANGLED) \
static void sysp_vecpush_##MANGLED(VEC_T* v, ELEM_T val) { \
    if (v->len >= v->cap) { \
        int _nc = (v->cap > 0) ? v->cap * 2 : (v->len > 0 ? v->len * 2 : 4); \
        ELEM_T* _nd = malloc(sizeof(ELEM_T) * _nc); \
        if (v->len > 0) memcpy(_nd, v->data, sizeof(ELEM_T) * v->len); \
        if (v->cap > 0) free(v->data); \
        v->data = _nd; v->cap = _nc; \
    } \
    v->data[v->len++] = val; \
}

/* VA_PROMOTE: type used in va_arg (char/short promote to int, float to double) */
#define SYSP_VECTOR_MAKE(VEC_T, ELEM_T, VA_PROMOTE, MANGLED) \
static VEC_T sysp_mkvec_##MANGLED(int n, ...) { \
    va_list ap; va_start(ap, n); \
    ELEM_T* d = malloc(sizeof(ELEM_T) * n); \
    for (int i = 0; i < n; i++) d[i] = va_arg(ap, VA_PROMOTE); \
    va_end(ap); \
    return (VEC_T){d, n, n}; \
}

#define SYSP_VECTOR_SHOW(VEC_T, SHOW_ELEM, FN_NAME) \
static const char* FN_NAME(VEC_T self) { \
    if (self.len == 0) { char* r = malloc(3); memcpy(r, "[]", 3); return r; } \
    const char** parts = malloc(sizeof(const char*) * self.len); \
    int total = 2; \
    for (int i = 0; i < self.len; i++) { \
        parts[i] = SHOW_ELEM(self.data[i]); \
        total += strlen(parts[i]); \
        if (i > 0) total += 2; \
    } \
    char* buf = malloc(total + 1); \
    char* p = buf; *p++ = '['; \
    for (int i = 0; i < self.len; i++) { \
        if (i > 0) { *p++ = ','; *p++ = ' '; } \
        int n = strlen(parts[i]); memcpy(p, parts[i], n); p += n; \
        free((char*)parts[i]); \
    } \
    *p++ = ']'; *p = '\0'; free(parts); \
    return buf; \
}

#endif /* SYSP_VECTOR_H */
