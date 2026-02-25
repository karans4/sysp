/* sysp Show Primitives — show_char, show_str, show_bool */

#ifndef SYSP_SHOW_H
#define SYSP_SHOW_H

#include <stdlib.h>
#include <string.h>

static const char* show_char(char x) { char* b = malloc(2); b[0] = x; b[1] = 0; return b; }
static const char* show_str(const char* x) { int n = strlen(x); char* b = malloc(n+1); memcpy(b, x, n+1); return b; }
static const char* show_bool(int x) { return x ? strdup("true") : strdup("false"); }

/* Macro for generating show_TYPE via snprintf measure+fill */
#define SYSP_SHOW_SNPRINTF(FN_NAME, C_TYPE, FMT) \
static const char* FN_NAME(C_TYPE x) { \
    int n = snprintf(NULL, 0, FMT, x); \
    char* b = malloc(n+1); \
    snprintf(b, n+1, FMT, x); \
    return b; \
}

/* Macro for generating show_TYPE via PRIxNN inttypes macros */
#define SYSP_SHOW_PRI(FN_NAME, C_TYPE, PRI_MACRO) \
static const char* FN_NAME(C_TYPE x) { \
    char buf[64]; \
    snprintf(buf, sizeof(buf), PRI_MACRO, x); \
    char* b = malloc(strlen(buf)+1); \
    memcpy(b, buf, strlen(buf)+1); \
    return b; \
}

#endif /* SYSP_SHOW_H */
