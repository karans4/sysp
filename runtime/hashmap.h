/* sysp HashMap Runtime — macro-based generic hashmap helpers */
/* Open addressing, linear probing, 75% load factor */

#ifndef SYSP_HASHMAP_H
#define SYSP_HASHMAP_H

#include <stdlib.h>
#include <string.h>

/* Hash functions (shared by all hashmap instantiations) */
static unsigned int _sysp_hash_str(const char* s) {
    unsigned int h = 2166136261u;
    while (*s) { h ^= (unsigned char)*s++; h *= 16777619u; }
    return h;
}
static unsigned int _sysp_hash_int(unsigned int x) {
    x = ((x >> 16) ^ x) * 0x45d9f3b;
    x = ((x >> 16) ^ x) * 0x45d9f3b;
    x = (x >> 16) ^ x;
    return x;
}

/* KEY_EQ: expression comparing m->keys[h] to key (e.g. "==" or strcmp-based) */
/* HASH_EXPR: expression computing hash of 'key' variable */
/* REHASH_EXPR: expression computing hash of source[i] during grow */

#define SYSP_HASHMAP_GROW(MK, MV, HM_T, KEY_T, VAL_T, REHASH_EXPR) \
static void _hm_grow_##MK##_##MV(HM_T* m) { \
    int oc = m->cap; KEY_T* ok = m->keys; VAL_T* ov = m->vals; char* oo = m->occ; \
    m->cap = oc ? oc * 2 : 8; m->len = 0; \
    m->keys = calloc(m->cap, sizeof(KEY_T)); m->vals = calloc(m->cap, sizeof(VAL_T)); \
    m->occ = calloc(m->cap, 1); \
    for (int i = 0; i < oc; i++) { \
        if (oo[i] == 1) { \
            unsigned int h = (REHASH_EXPR) % m->cap; \
            while (m->occ[h]) h = (h + 1) % m->cap; \
            m->keys[h] = ok[i]; m->vals[h] = ov[i]; m->occ[h] = 1; m->len++; \
        } \
    } \
    free(ok); free(ov); free(oo); \
}

#define SYSP_HASHMAP_SET(MK, MV, HM_T, KEY_T, VAL_T, HASH_EXPR, KEY_EQ) \
static void _hm_set_##MK##_##MV(HM_T* m, KEY_T key, VAL_T val) { \
    if (m->len * 4 >= m->cap * 3) _hm_grow_##MK##_##MV(m); \
    unsigned int h = (HASH_EXPR) % m->cap; \
    while (m->occ[h] == 1) { if (KEY_EQ) { m->vals[h] = val; return; } h = (h + 1) % m->cap; } \
    m->keys[h] = key; m->vals[h] = val; m->occ[h] = 1; m->len++; \
}

#define SYSP_HASHMAP_GET(MK, MV, HM_T, KEY_T, VAL_T, HASH_EXPR, KEY_EQ) \
static VAL_T _hm_get_##MK##_##MV(HM_T* m, KEY_T key) { \
    if (!m->cap) return (VAL_T){0}; \
    unsigned int h = (HASH_EXPR) % m->cap; \
    while (m->occ[h]) { if (m->occ[h] == 1 && (KEY_EQ)) return m->vals[h]; h = (h + 1) % m->cap; } \
    return (VAL_T){0}; \
}

#define SYSP_HASHMAP_HAS(MK, MV, HM_T, KEY_T, HASH_EXPR, KEY_EQ) \
static int _hm_has_##MK##_##MV(HM_T* m, KEY_T key) { \
    if (!m->cap) return 0; \
    unsigned int h = (HASH_EXPR) % m->cap; \
    while (m->occ[h]) { if (m->occ[h] == 1 && (KEY_EQ)) return 1; h = (h + 1) % m->cap; } \
    return 0; \
}

#define SYSP_HASHMAP_DEL(MK, MV, HM_T, KEY_T, HASH_EXPR, KEY_EQ) \
static void _hm_del_##MK##_##MV(HM_T* m, KEY_T key) { \
    if (!m->cap) return; \
    unsigned int h = (HASH_EXPR) % m->cap; \
    while (m->occ[h]) { if (m->occ[h] == 1 && (KEY_EQ)) { m->occ[h] = 2; m->len--; return; } h = (h + 1) % m->cap; } \
}

#define SYSP_HASHMAP_KEYS(MK, MV, HM_T, VEC_K_T, PUSH_K_FN) \
static VEC_K_T _hm_keys_##MK##_##MV(HM_T* m) { \
    VEC_K_T r = {NULL, 0, 0}; \
    for (int i = 0; i < m->cap; i++) { if (m->occ[i] == 1) PUSH_K_FN(&r, m->keys[i]); } \
    return r; \
}

#define SYSP_HASHMAP_VALS(MK, MV, HM_T, VEC_V_T, PUSH_V_FN) \
static VEC_V_T _hm_vals_##MK##_##MV(HM_T* m) { \
    VEC_V_T r = {NULL, 0, 0}; \
    for (int i = 0; i < m->cap; i++) { if (m->occ[i] == 1) PUSH_V_FN(&r, m->vals[i]); } \
    return r; \
}

#define SYSP_HASHMAP_SHOW(HM_T, SHOW_K, SHOW_V, FN_NAME) \
static const char* FN_NAME(HM_T self) { \
    if (self.len == 0) { char* r = malloc(3); memcpy(r, "{}", 3); return r; } \
    const char** parts = malloc(sizeof(const char*) * self.len); \
    int total = 2, idx = 0; \
    for (int i = 0; i < self.cap; i++) { \
        if (!self.occ[i]) continue; \
        const char* ks = SHOW_K(self.keys[i]); \
        const char* vs = SHOW_V(self.vals[i]); \
        int kn = strlen(ks), vn = strlen(vs); \
        char* entry = malloc(kn + 2 + vn + 1); \
        memcpy(entry, ks, kn); entry[kn] = ':'; entry[kn+1] = ' '; \
        memcpy(entry + kn + 2, vs, vn + 1); \
        free((char*)ks); free((char*)vs); \
        parts[idx] = entry; \
        total += strlen(entry); \
        if (idx > 0) total += 2; \
        idx++; \
    } \
    char* buf = malloc(total + 1); \
    char* p = buf; *p++ = '{'; \
    for (int i = 0; i < idx; i++) { \
        if (i > 0) { *p++ = ','; *p++ = ' '; } \
        int n = strlen(parts[i]); memcpy(p, parts[i], n); p += n; \
        free((char*)parts[i]); \
    } \
    *p++ = '}'; *p = '\0'; free(parts); \
    return buf; \
}

#endif /* SYSP_HASHMAP_H */
