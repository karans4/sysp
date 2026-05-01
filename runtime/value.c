#include "value.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>

/* ---------- Constructors ---------- */

Value val_nil(void)         { Value v = {0}; v.tag = VAL_NIL; return v; }
Value val_int(int32_t i)    { Value v = {0}; v.tag = VAL_INT;   v.as.i = i;   return v; }
Value val_float(double f)   { Value v = {0}; v.tag = VAL_FLOAT; v.as.f = f;   return v; }
Value val_str(const char* s){ Value v = {0}; v.tag = VAL_STR;   v.as.s = s;   return v; }
Value val_sym(uint32_t s)   { Value v = {0}; v.tag = VAL_SYM;   v.as.sym = s; return v; }
Value val_fn(Fn* fn)        { Value v = {0}; v.tag = VAL_FN;    v.as.fn = fn; return v; }

Value val_cons(Value car, Value cdr) {
    Cons* c = malloc(sizeof(Cons));
    c->car = car;
    c->cdr = cdr;
    c->rc = 1;
    val_retain(car);
    val_retain(cdr);
    Value v = {0};
    v.tag = VAL_CONS;
    v.as.cons = c;
    return v;
}

/* ---------- Predicates ---------- */

int is_nil(Value v)  { return v.tag == VAL_NIL; }
int is_int(Value v)  { return v.tag == VAL_INT; }
int is_float(Value v){ return v.tag == VAL_FLOAT; }
int is_str(Value v)  { return v.tag == VAL_STR; }
int is_sym(Value v)  { return v.tag == VAL_SYM; }
int is_cons(Value v) { return v.tag == VAL_CONS; }
int is_fn(Value v)   { return v.tag == VAL_FN; }

/* ---------- Accessors ---------- */

int32_t     val_int_of(Value v)   { return v.as.i; }
double      val_float_of(Value v) { return v.as.f; }
const char* val_str_of(Value v)   { return v.as.s; }
uint32_t    val_sym_of(Value v)   { return v.as.sym; }
/* car/cdr retain the inner Value: caller becomes a +1 owner so ARC's
 * release-at-last-use balances. The cons cell itself is unaffected. */
Value       val_car(Value v)      { Value r = v.as.cons->car; val_retain(r); return r; }
Value       val_cdr(Value v)      { Value r = v.as.cons->cdr; val_retain(r); return r; }
Fn*         val_fn_of(Value v)    { return v.as.fn; }

/* ---------- Equality ---------- */

int val_eq(Value a, Value b) {
    if (a.tag != b.tag) return 0;
    switch (a.tag) {
        case VAL_NIL:   return 1;
        case VAL_INT:   return a.as.i == b.as.i;
        case VAL_FLOAT: return a.as.f == b.as.f;
        case VAL_STR:   return strcmp(a.as.s, b.as.s) == 0;
        case VAL_SYM:   return a.as.sym == b.as.sym;
        case VAL_CONS:  return val_eq(a.as.cons->car, b.as.cons->car)
                              && val_eq(a.as.cons->cdr, b.as.cons->cdr);
        case VAL_FN:    return a.as.fn == b.as.fn;
    }
    return 0;
}

int sym_eq(Value a, Value b) {
    return a.tag == VAL_SYM && b.tag == VAL_SYM && a.as.sym == b.as.sym;
}

/* ---------- Refcounting ---------- */

void val_retain(Value v) {
    switch (v.tag) {
        case VAL_CONS: v.as.cons->rc++; break;
        case VAL_FN:   v.as.fn->rc++; break;
        default: break;
    }
}

void val_release(Value v) {
    switch (v.tag) {
        case VAL_CONS:
            if (--v.as.cons->rc == 0) {
                val_release(v.as.cons->car);
                val_release(v.as.cons->cdr);
                free(v.as.cons);
            }
            break;
        case VAL_FN:
            if (--v.as.fn->rc == 0) {
                /* If state is a Closure (interp's lambda value), recurse
                 * into its fields. Compiled-lambda Fns set invoke != NULL
                 * and state to an env pointer (caller responsible). */
                Fn* fn = v.as.fn;
                if (fn->invoke == NULL && fn->state) {
                    Closure* c = (Closure*)fn->state;
                    if (--c->rc == 0) {
                        val_release(c->params);
                        val_release(c->body);
                        val_release(c->env);
                        free(c);
                    }
                }
                free(fn);
            }
            break;
        default: break;
    }
}

/* ---------- Symbol interning ---------- */

#define SYM_TAB_INIT 64

typedef struct {
    char**   names;     /* index = id */
    size_t   count;
    size_t   cap;
    /* Simple linear search. Replace with hash if it ever matters. */
} SymTab;

static SymTab g_symtab = {0};

/* Forward decls — defined later in this file. */
static char** g_str_pool;
static size_t g_str_pool_count, g_str_pool_cap;

static void symtab_grow(void) {
    size_t newcap = g_symtab.cap == 0 ? SYM_TAB_INIT : g_symtab.cap * 2;
    g_symtab.names = realloc(g_symtab.names, newcap * sizeof(char*));
    g_symtab.cap = newcap;
}

uint32_t intern_sym(const char* name) {
    /* Case-insensitive lookup but preserve the FIRST seen form's case for
     * printing — matches CL's reader behavior where 'inc' and 'INC' are
     * the same symbol but the printed form depends on the readtable. */
    for (uint32_t j = 0; j < g_symtab.count; j++) {
        if (strcasecmp(g_symtab.names[j], name) == 0) return j;
    }
    if (g_symtab.count >= g_symtab.cap) symtab_grow();
    g_symtab.names[g_symtab.count] = strdup(name);
    return g_symtab.count++;
}

const char* sym_name(uint32_t id) {
    if (id < g_symtab.count) return g_symtab.names[id];
    return "<bad-sym>";
}

void runtime_shutdown(void) {
    for (size_t i = 0; i < g_symtab.count; i++) free(g_symtab.names[i]);
    free(g_symtab.names);
    g_symtab.names = NULL;
    g_symtab.count = g_symtab.cap = 0;
    for (size_t i = 0; i < g_str_pool_count; i++) free(g_str_pool[i]);
    free(g_str_pool);
    g_str_pool = NULL;
    g_str_pool_count = g_str_pool_cap = 0;
}

/* ---------- Reader ---------- */

static int peek_skip_ws(FILE* f) {
    int c;
    for (;;) {
        c = fgetc(f);
        if (c == EOF) return EOF;
        if (c == ';') {
            while ((c = fgetc(f)) != EOF && c != '\n') ;
            continue;
        }
        if (!isspace(c) && c != ',') {
            ungetc(c, f);
            return c;
        }
    }
}

static int is_atom_char(int c) {
    return c != EOF && c != '(' && c != ')' && c != '[' && c != ']'
        && c != '"' && c != ';' && c != '\'' && c != '`' && c != '~'
        && !isspace(c) && c != ',';
}

/* Pool for read-string literals so they outlive a single read but are
 * reclaimable at runtime_shutdown. (declared above, defined here.) */

static const char* str_intern(const char* s) {
    for (size_t i = 0; i < g_str_pool_count; i++) {
        if (strcmp(g_str_pool[i], s) == 0) return g_str_pool[i];
    }
    if (g_str_pool_count >= g_str_pool_cap) {
        g_str_pool_cap = g_str_pool_cap == 0 ? 32 : g_str_pool_cap * 2;
        g_str_pool = realloc(g_str_pool, g_str_pool_cap * sizeof(char*));
    }
    g_str_pool[g_str_pool_count] = strdup(s);
    return g_str_pool[g_str_pool_count++];
}

static Value read_string_lit(FILE* f) {
    /* Opening " already consumed. */
    char buf[4096];
    size_t n = 0;
    int c;
    while ((c = fgetc(f)) != EOF && c != '"') {
        if (c == '\\') {
            int esc = fgetc(f);
            switch (esc) {
                case 'n': c = '\n'; break;
                case 't': c = '\t'; break;
                case 'r': c = '\r'; break;
                case '\\': c = '\\'; break;
                case '"': c = '"'; break;
                default:  c = esc; break;
            }
        }
        if (n + 1 >= sizeof(buf)) break;
        buf[n++] = (char)c;
    }
    buf[n] = 0;
    return val_str(str_intern(buf));
}

static Value read_atom(FILE* f, int first) {
    char buf[256];
    size_t n = 0;
    buf[n++] = (char)first;
    int c;
    while (n + 1 < sizeof(buf) && is_atom_char((c = fgetc(f)))) {
        buf[n++] = (char)c;
    }
    if (c != EOF) ungetc(c, f);
    buf[n] = 0;

    /* Try integer */
    char* endp;
    long iv = strtol(buf, &endp, 0);
    if (*endp == 0 && endp != buf) return val_int((int32_t)iv);
    /* Try float */
    double fv = strtod(buf, &endp);
    if (*endp == 0 && endp != buf) return val_float(fv);
    /* Special atoms */
    if (strcmp(buf, "nil") == 0) return val_nil();
    /* Symbol */
    return val_sym(intern_sym(buf));
}

static Value read_list(FILE* f, int closer) {
    /* Collect items into an array, build list right-to-left. */
    Value items[1024];
    size_t count = 0;
    for (;;) {
        int c = peek_skip_ws(f);
        if (c == EOF) {
            fprintf(stderr, "read_sexp: unclosed list\n");
            break;
        }
        if (c == closer) { fgetc(f); break; }
        items[count++] = read_sexp(f);
        if (count >= sizeof(items)/sizeof(items[0])) {
            fprintf(stderr, "read_sexp: list too long\n");
            break;
        }
    }
    Value lst = val_nil();
    for (size_t i = count; i > 0; i--) {
        Value tmp = val_cons(items[i-1], lst);
        val_release(items[i-1]);  /* drop local ref; cons retained */
        val_release(lst);
        lst = tmp;
    }
    return lst;
}

Value read_sexp(FILE* f) {
    int c = peek_skip_ws(f);
    if (c == EOF) return val_nil();
    fgetc(f);  /* consume */
    if (c == '(') return read_list(f, ')');
    if (c == '[') return read_list(f, ']');
    if (c == '"') return read_string_lit(f);
    if (c == '\'' || c == '`' || c == '~') {
        const char* head_name;
        if (c == '\'') head_name = "quote";
        else if (c == '`') head_name = "quasiquote";
        else {
            int next = fgetc(f);
            if (next == '@') head_name = "splice";
            else { ungetc(next, f); head_name = "unquote"; }
        }
        Value inner = read_sexp(f);
        Value tail  = val_cons(inner, val_nil());
        val_release(inner);
        Value q = val_cons(val_sym(intern_sym(head_name)), tail);
        val_release(tail);
        return q;
    }
    return read_atom(f, c);
}

/* ---------- Writer ---------- */

static void write_string_lit(FILE* f, const char* s) {
    fputc('"', f);
    for (; *s; s++) {
        if (*s == '"' || *s == '\\') fputc('\\', f);
        if (*s == '\n') { fputs("\\n", f); continue; }
        if (*s == '\t') { fputs("\\t", f); continue; }
        fputc(*s, f);
    }
    fputc('"', f);
}

void val_println(Value v) { write_sexp(stdout, v); fputc('\n', stdout); }

FILE* runtime_stdin(void)  { return stdin; }
FILE* runtime_stdout(void) { return stdout; }
FILE* runtime_stderr(void) { return stderr; }

/* ---------- Closure helpers ----------
 * A Value with VAL_FN tag whose state is a Closure*. The Fn's invoke
 * pointer is set by the interpreter at startup (interp_call trampoline).
 * For now, helpers don't set invoke — the interpreter does so before
 * the closure is ever called. */

Value val_closure(Value params, Value body, Value env) {
    Closure* c = malloc(sizeof(Closure));
    c->params = params; val_retain(params);
    c->body   = body;   val_retain(body);
    c->env    = env;    val_retain(env);
    c->rc = 1;

    Fn* fn = malloc(sizeof(Fn));
    fn->invoke = NULL;     /* interpreter sets this */
    fn->state  = c;
    fn->rc = 1;

    Value v = {0};
    v.tag = VAL_FN;
    v.as.fn = fn;
    return v;
}

Value closure_params(Value v) {
    Closure* c = (Closure*)v.as.fn->state;
    val_retain(c->params);
    return c->params;
}

Value closure_body(Value v) {
    Closure* c = (Closure*)v.as.fn->state;
    val_retain(c->body);
    return c->body;
}

Value closure_env(Value v) {
    Closure* c = (Closure*)v.as.fn->state;
    val_retain(c->env);
    return c->env;
}

void write_sexp(FILE* f, Value v) {
    switch (v.tag) {
        case VAL_NIL:   fputs("nil", f); break;
        case VAL_INT:   fprintf(f, "%d", v.as.i); break;
        case VAL_FLOAT: fprintf(f, "%g", v.as.f); break;
        case VAL_STR:   write_string_lit(f, v.as.s); break;
        case VAL_SYM:   fputs(sym_name(v.as.sym), f); break;
        case VAL_FN:    fprintf(f, "#<fn %p>", (void*)v.as.fn); break;
        case VAL_CONS: {
            fputc('(', f);
            Value cur = v;
            int first = 1;
            while (cur.tag == VAL_CONS) {
                if (!first) fputc(' ', f);
                write_sexp(f, cur.as.cons->car);
                first = 0;
                cur = cur.as.cons->cdr;
            }
            if (cur.tag != VAL_NIL) {
                fputs(" . ", f);
                write_sexp(f, cur);
            }
            fputc(')', f);
            break;
        }
    }
}
