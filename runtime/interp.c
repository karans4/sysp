#include <stdio.h>
#include <string.h>
#include "value.h"

Value env_lookup(Value env, uint32_t id);
Value env_bind(Value env, uint32_t id, Value v);
Value eval_form(Value form, Value env);
Value eval_args(Value args, Value env);
Value eval_call(Value form, Value env);
int name_is_p(uint32_t id, const char* s);
Value dispatch(uint32_t id, Value args, Value env, Value form);
Value eval_if(Value args, Value env);
int main();

Value env_lookup(Value env, uint32_t id) {
  int t1 = is_nil(env);
  if ((t1 != 0)) {
    Value t8 = val_nil();
    return t8;
  } else {
    Value t9 = val_car(env);
    Value pair = t9;
    Value t10 = val_car(pair);
    uint32_t t11 = val_sym_of(t10);
    if ((t11 == id)) {
      Value t17 = val_cdr(pair);
      return t17;
    } else {
      Value t18 = val_cdr(env);
      Value t19 = env_lookup(t18, id);
      return t19;
    }
  }
}

Value env_bind(Value env, uint32_t id, Value v) {
  Value t1 = val_sym(id);
  Value t2 = val_cons(t1, v);
  Value t3 = val_cons(t2, env);
  return t3;
}

Value eval_form(Value form, Value env) {
  int t1 = is_int(form);
  if ((t1 != 0)) {
    return form;
  } else {
    int t8 = is_str(form);
    if ((t8 != 0)) {
      return form;
    } else {
      int t15 = is_nil(form);
      if ((t15 != 0)) {
        return form;
      } else {
        int t22 = is_sym(form);
        if ((t22 != 0)) {
          uint32_t t29 = val_sym_of(form);
          Value t30 = env_lookup(env, t29);
          Value found = t30;
          int t31 = is_nil(found);
          if ((t31 != 0)) {
            return form;
          } else {
            return found;
          }
        } else {
          int t38 = is_cons(form);
          if ((t38 != 0)) {
            Value t45 = eval_call(form, env);
            return t45;
          } else {
            return form;
          }
        }
      }
    }
  }
}

Value eval_args(Value args, Value env) {
  int t1 = is_nil(args);
  if ((t1 != 0)) {
    Value t8 = val_nil();
    return t8;
  } else {
    Value t9 = val_car(args);
    Value t10 = eval_form(t9, env);
    Value t11 = val_cdr(args);
    Value t12 = eval_args(t11, env);
    Value t13 = val_cons(t10, t12);
    return t13;
  }
}

Value eval_call(Value form, Value env) {
  Value t1 = val_car(form);
  Value head = t1;
  Value t2 = val_cdr(form);
  int t3 = is_sym(head);
  if ((t3 != 0)) {
    uint32_t t10 = val_sym_of(head);
    Value t11 = dispatch(t10, t2, env, form);
    return t11;
  } else {
    Value t12 = val_nil();
    return t12;
  }
}

int name_is_p(uint32_t id, const char* s) {
  const char* t1 = sym_name(id);
  int t2 = strcmp(t1, s);
  return (t2 == 0);
}

Value dispatch(uint32_t id, Value args, Value env, Value form) {
  const char* t1 = "quote";
  int t2 = name_is_p(id, t1);
  if ((t2 != 0)) {
    Value t9 = val_car(args);
    return t9;
  } else {
    const char* t10 = "if";
    int t11 = name_is_p(id, t10);
    if ((t11 != 0)) {
      Value t18 = eval_if(args, env);
      return t18;
    } else {
      const char* t19 = "+";
      int t20 = name_is_p(id, t19);
      if ((t20 != 0)) {
        Value t27 = val_car(args);
        Value t28 = eval_form(t27, env);
        int t29 = val_int_of(t28);
        Value t30 = val_cdr(args);
        Value t31 = val_car(t30);
        Value t32 = eval_form(t31, env);
        int t33 = val_int_of(t32);
        Value t35 = val_int((t29 + t33));
        return t35;
      } else {
        const char* t36 = "-";
        int t37 = name_is_p(id, t36);
        if ((t37 != 0)) {
          Value t44 = val_car(args);
          Value t45 = eval_form(t44, env);
          int t46 = val_int_of(t45);
          Value t47 = val_cdr(args);
          Value t48 = val_car(t47);
          Value t49 = eval_form(t48, env);
          int t50 = val_int_of(t49);
          Value t52 = val_int((t46 - t50));
          return t52;
        } else {
          const char* t53 = "*";
          int t54 = name_is_p(id, t53);
          if ((t54 != 0)) {
            Value t61 = val_car(args);
            Value t62 = eval_form(t61, env);
            int t63 = val_int_of(t62);
            Value t64 = val_cdr(args);
            Value t65 = val_car(t64);
            Value t66 = eval_form(t65, env);
            int t67 = val_int_of(t66);
            Value t69 = val_int((t63 * t67));
            return t69;
          } else {
            const char* t70 = "=";
            int t71 = name_is_p(id, t70);
            if ((t71 != 0)) {
              Value t78 = val_car(args);
              Value t79 = eval_form(t78, env);
              Value t80 = val_cdr(args);
              Value t81 = val_car(t80);
              Value t82 = eval_form(t81, env);
              int t83 = val_eq(t79, t82);
              Value t84 = val_int(t83);
              return t84;
            } else {
              const char* t85 = "cons";
              int t86 = name_is_p(id, t85);
              if ((t86 != 0)) {
                Value t93 = val_car(args);
                Value t94 = eval_form(t93, env);
                Value t95 = val_cdr(args);
                Value t96 = val_car(t95);
                Value t97 = eval_form(t96, env);
                Value t98 = val_cons(t94, t97);
                return t98;
              } else {
                const char* t99 = "car";
                int t100 = name_is_p(id, t99);
                if ((t100 != 0)) {
                  Value t107 = val_car(args);
                  Value t108 = eval_form(t107, env);
                  Value t109 = val_car(t108);
                  return t109;
                } else {
                  const char* t110 = "cdr";
                  int t111 = name_is_p(id, t110);
                  if ((t111 != 0)) {
                    Value t118 = val_car(args);
                    Value t119 = eval_form(t118, env);
                    Value t120 = val_cdr(t119);
                    return t120;
                  } else {
                    const char* t121 = "nil?";
                    int t122 = name_is_p(id, t121);
                    if ((t122 != 0)) {
                      Value t129 = val_car(args);
                      Value t130 = eval_form(t129, env);
                      int t131 = is_nil(t130);
                      Value t132 = val_int(t131);
                      return t132;
                    } else {
                      const char* t133 = "println";
                      int t134 = name_is_p(id, t133);
                      if ((t134 != 0)) {
                        Value t141 = val_car(args);
                        Value t142 = eval_form(t141, env);
                        val_println(t142);
                        Value t144 = val_nil();
                        return t144;
                      } else {
                        return form;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

Value eval_if(Value args, Value env) {
  Value t1 = val_car(args);
  Value t2 = eval_form(t1, env);
  int t3 = is_nil(t2);
  if ((t3 == 1)) {
    Value t10 = val_cdr(args);
    Value t11 = val_cdr(t10);
    Value t12 = val_car(t11);
    Value t13 = eval_form(t12, env);
    return t13;
  } else {
    Value t14 = val_cdr(args);
    Value t15 = val_car(t14);
    Value t16 = eval_form(t15, env);
    return t16;
  }
}

int main() {
  void* t1 = runtime_stdin();
  void* in = t1;
  void* t2 = runtime_stdout();
  void* out = t2;
  Value t3 = val_nil();
  for (;;) {
    int t7 = feof(in);
    if (!((t7 == 0))) break;
    Value t10 = read_sexp(in);
    Value form = t10;
    int t14 = is_nil(form);
    if ((t14 == 0)) {
      Value t17 = eval_form(form, t3);
      write_sexp(out, t17);
      int t20 = fputc(10, out);
    } else {
    }
  }
  return 0;
}

