/* sysp String Runtime — helper functions for string operations */

#ifndef SYSP_STRING_H
#define SYSP_STRING_H

#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>

static const char* _sysp_str_concat(const char* a, const char* b) {
    int la = strlen(a), lb = strlen(b);
    char* r = malloc(la + lb + 1);
    memcpy(r, a, la); memcpy(r + la, b, lb + 1);
    return r;
}

static const char* _sysp_str_slice(const char* s, int start, int end) {
    int slen = strlen(s);
    if (start < 0) start = 0;
    if (end > slen) end = slen;
    if (start >= end) { char* r = malloc(1); r[0] = 0; return r; }
    int n = end - start;
    char* r = malloc(n + 1);
    memcpy(r, s + start, n); r[n] = 0;
    return r;
}

static const char* _sysp_str_upper(const char* s) {
    int n = strlen(s);
    char* r = malloc(n + 1);
    for (int i = 0; i <= n; i++) r[i] = toupper((unsigned char)s[i]);
    return r;
}

static const char* _sysp_str_lower(const char* s) {
    int n = strlen(s);
    char* r = malloc(n + 1);
    for (int i = 0; i <= n; i++) r[i] = tolower((unsigned char)s[i]);
    return r;
}

static const char* _sysp_str_from_int(int v) {
    char buf[32];
    snprintf(buf, sizeof(buf), "%d", v);
    int n = strlen(buf);
    char* r = malloc(n + 1);
    memcpy(r, buf, n + 1);
    return r;
}

static const char* _sysp_str_from_float(double v) {
    char buf[64];
    snprintf(buf, sizeof(buf), "%g", v);
    int n = strlen(buf);
    char* r = malloc(n + 1);
    memcpy(r, buf, n + 1);
    return r;
}

static const char* _sysp_str_trim(const char* s) {
    while (*s && (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r')) s++;
    int n = strlen(s);
    while (n > 0 && (s[n-1] == ' ' || s[n-1] == '\t' || s[n-1] == '\n' || s[n-1] == '\r')) n--;
    char* r = malloc(n + 1);
    memcpy(r, s, n); r[n] = 0;
    return r;
}

static const char* _sysp_str_replace(const char* s, const char* old, const char* new_s) {
    int slen = strlen(s), olen = strlen(old), nlen = strlen(new_s);
    if (olen == 0) { char* r = malloc(slen + 1); memcpy(r, s, slen + 1); return r; }
    int count = 0;
    const char* p = s;
    while ((p = strstr(p, old))) { count++; p += olen; }
    char* r = malloc(slen + count * (nlen - olen) + 1);
    char* w = r;
    p = s;
    while (1) {
        const char* f = strstr(p, old);
        if (!f) { strcpy(w, p); break; }
        memcpy(w, p, f - p); w += f - p;
        memcpy(w, new_s, nlen); w += nlen;
        p = f + olen;
    }
    return r;
}

static const char* _sysp_str_join(const char** data, int len, const char* delim) {
    if (len == 0) { char* r = malloc(1); r[0] = 0; return r; }
    int dlen = strlen(delim), total = 0;
    for (int i = 0; i < len; i++) total += strlen(data[i]);
    total += dlen * (len - 1);
    char* r = malloc(total + 1);
    char* w = r;
    for (int i = 0; i < len; i++) {
        if (i > 0) { memcpy(w, delim, dlen); w += dlen; }
        int n = strlen(data[i]);
        memcpy(w, data[i], n); w += n;
    }
    *w = 0;
    return r;
}

#endif /* SYSP_STRING_H */
