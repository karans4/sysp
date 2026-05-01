#include <stdio.h>
#include <string.h>
#include "value.h"

Value env_lookup(Value env, uint32_t id);
Value env_bind(Value env, uint32_t id, Value v);
Value bind_list(Value params, Value args, Value env);
int name_is_p(uint32_t id, const char* s);
Value eval_form(Value form, Value env, Value mac);
Value eval_args(Value args, Value env, Value mac);
Value eval_call(Value form, Value env, Value mac);
Value dispatch(uint32_t id, Value args, Value env, Value mac, Value form);
int is_falsy(Value v);
Value append_list(Value a, Value b);
int is_tagged_p(Value form, const char* tag);
Value eval_qq(Value form, Value env, Value mac);
Value eval_qq_list(Value items, Value env, Value mac);
Value eval_if(Value args, Value env, Value mac);
Value eval_let(Value args, Value env, Value mac);
Value eval_let_bindings(Value bindings, Value env, Value mac);
Value eval_body(Value body, Value env, Value mac);
Value apply_fn(Value fn, Value args, Value env, Value mac);
Value handle_form(Value form, Value env, Value mac);
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

Value bind_list(Value params, Value args, Value env) {
  int t1 = is_nil(params);
  if ((t1 != 0)) {
    return env;
  } else {
    Value t8 = val_cdr(params);
    Value t9 = val_cdr(args);
    Value t10 = val_car(params);
    uint32_t t11 = val_sym_of(t10);
    Value t12 = val_car(args);
    Value t13 = env_bind(env, t11, t12);
    Value t14 = bind_list(t8, t9, t13);
    return t14;
  }
}

int name_is_p(uint32_t id, const char* s) {
  const char* t1 = sym_name(id);
  int t2 = strcmp(t1, s);
  return (t2 == 0);
}

Value eval_form(Value form, Value env, Value mac) {
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
            Value t45 = eval_call(form, env, mac);
            return t45;
          } else {
            return form;
          }
        }
      }
    }
  }
}

Value eval_args(Value args, Value env, Value mac) {
  int t1 = is_nil(args);
  if ((t1 != 0)) {
    Value t8 = val_nil();
    return t8;
  } else {
    Value t9 = val_car(args);
    Value t10 = eval_form(t9, env, mac);
    Value t11 = val_cdr(args);
    Value t12 = eval_args(t11, env, mac);
    Value t13 = val_cons(t10, t12);
    return t13;
  }
}

Value eval_call(Value form, Value env, Value mac) {
  Value t1 = val_car(form);
  Value head = t1;
  Value t2 = val_cdr(form);
  Value args = t2;
  int t3 = is_sym(head);
  if ((t3 != 0)) {
    uint32_t t10 = val_sym_of(head);
    Value t11 = dispatch(t10, args, env, mac, form);
    return t11;
  } else {
    Value t12 = eval_form(head, env, mac);
    Value t13 = eval_args(args, env, mac);
    Value t14 = apply_fn(t12, t13, env, mac);
    return t14;
  }
}

Value dispatch(uint32_t id, Value args, Value env, Value mac, Value form) {
  int t134;
  int t157;
  const char* t1 = "quote";
  int t2 = name_is_p(id, t1);
  if ((t2 != 0)) {
    Value t9 = val_car(args);
    return t9;
  } else {
    const char* t10 = "if";
    int t11 = name_is_p(id, t10);
    if ((t11 != 0)) {
      Value t18 = eval_if(args, env, mac);
      return t18;
    } else {
      const char* t19 = "quasiquote";
      int t20 = name_is_p(id, t19);
      if ((t20 != 0)) {
        Value t27 = val_car(args);
        Value t28 = eval_qq(t27, env, mac);
        return t28;
      } else {
        const char* t29 = "let";
        int t30 = name_is_p(id, t29);
        if ((t30 != 0)) {
          Value t37 = eval_let(args, env, mac);
          return t37;
        } else {
          const char* t38 = "lambda";
          int t39 = name_is_p(id, t38);
          if ((t39 != 0)) {
            Value t46 = val_car(args);
            Value t47 = val_cdr(args);
            Value t48 = val_closure(t46, t47, env);
            return t48;
          } else {
            const char* t49 = "+";
            int t50 = name_is_p(id, t49);
            if ((t50 != 0)) {
              Value t57 = val_car(args);
              Value t58 = eval_form(t57, env, mac);
              int t59 = val_int_of(t58);
              Value t60 = val_cdr(args);
              Value t61 = val_car(t60);
              Value t62 = eval_form(t61, env, mac);
              int t63 = val_int_of(t62);
              Value t65 = val_int((t59 + t63));
              return t65;
            } else {
              const char* t66 = "-";
              int t67 = name_is_p(id, t66);
              if ((t67 != 0)) {
                Value t74 = val_car(args);
                Value t75 = eval_form(t74, env, mac);
                int t76 = val_int_of(t75);
                Value t77 = val_cdr(args);
                Value t78 = val_car(t77);
                Value t79 = eval_form(t78, env, mac);
                int t80 = val_int_of(t79);
                Value t82 = val_int((t76 - t80));
                return t82;
              } else {
                const char* t83 = "*";
                int t84 = name_is_p(id, t83);
                if ((t84 != 0)) {
                  Value t91 = val_car(args);
                  Value t92 = eval_form(t91, env, mac);
                  int t93 = val_int_of(t92);
                  Value t94 = val_cdr(args);
                  Value t95 = val_car(t94);
                  Value t96 = eval_form(t95, env, mac);
                  int t97 = val_int_of(t96);
                  Value t99 = val_int((t93 * t97));
                  return t99;
                } else {
                  const char* t100 = "=";
                  int t101 = name_is_p(id, t100);
                  if ((t101 != 0)) {
                    Value t108 = val_car(args);
                    Value t109 = eval_form(t108, env, mac);
                    Value t110 = val_cdr(args);
                    Value t111 = val_car(t110);
                    Value t112 = eval_form(t111, env, mac);
                    int t113 = val_eq(t109, t112);
                    Value t114 = val_int(t113);
                    return t114;
                  } else {
                    const char* t115 = "<";
                    int t116 = name_is_p(id, t115);
                    if ((t116 != 0)) {
                      Value t123 = val_car(args);
                      Value t124 = eval_form(t123, env, mac);
                      int t125 = val_int_of(t124);
                      Value t126 = val_cdr(args);
                      Value t127 = val_car(t126);
                      Value t128 = eval_form(t127, env, mac);
                      int t129 = val_int_of(t128);
                      if ((t125 < t129)) {
                        t134 = 1;
                      } else {
                        t134 = 0;
                      }
                      Value t137 = val_int(t134);
                      return t137;
                    } else {
                      const char* t138 = ">";
                      int t139 = name_is_p(id, t138);
                      if ((t139 != 0)) {
                        Value t146 = val_car(args);
                        Value t147 = eval_form(t146, env, mac);
                        int t148 = val_int_of(t147);
                        Value t149 = val_cdr(args);
                        Value t150 = val_car(t149);
                        Value t151 = eval_form(t150, env, mac);
                        int t152 = val_int_of(t151);
                        if ((t148 > t152)) {
                          t157 = 1;
                        } else {
                          t157 = 0;
                        }
                        Value t160 = val_int(t157);
                        return t160;
                      } else {
                        const char* t161 = "cons";
                        int t162 = name_is_p(id, t161);
                        if ((t162 != 0)) {
                          Value t169 = val_car(args);
                          Value t170 = eval_form(t169, env, mac);
                          Value t171 = val_cdr(args);
                          Value t172 = val_car(t171);
                          Value t173 = eval_form(t172, env, mac);
                          Value t174 = val_cons(t170, t173);
                          return t174;
                        } else {
                          const char* t175 = "car";
                          int t176 = name_is_p(id, t175);
                          if ((t176 != 0)) {
                            Value t183 = val_car(args);
                            Value t184 = eval_form(t183, env, mac);
                            Value t185 = val_car(t184);
                            return t185;
                          } else {
                            const char* t186 = "cdr";
                            int t187 = name_is_p(id, t186);
                            if ((t187 != 0)) {
                              Value t194 = val_car(args);
                              Value t195 = eval_form(t194, env, mac);
                              Value t196 = val_cdr(t195);
                              return t196;
                            } else {
                              const char* t197 = "nil?";
                              int t198 = name_is_p(id, t197);
                              if ((t198 != 0)) {
                                Value t205 = val_car(args);
                                Value t206 = eval_form(t205, env, mac);
                                int t207 = is_nil(t206);
                                Value t208 = val_int(t207);
                                return t208;
                              } else {
                                const char* t209 = "sym-eq?";
                                int t210 = name_is_p(id, t209);
                                if ((t210 != 0)) {
                                  Value t217 = val_car(args);
                                  Value t218 = eval_form(t217, env, mac);
                                  Value t219 = val_cdr(args);
                                  Value t220 = val_car(t219);
                                  Value t221 = eval_form(t220, env, mac);
                                  int t222 = sym_eq(t218, t221);
                                  Value t223 = val_int(t222);
                                  return t223;
                                } else {
                                  const char* t224 = "list";
                                  int t225 = name_is_p(id, t224);
                                  if ((t225 != 0)) {
                                    Value t232 = eval_args(args, env, mac);
                                    return t232;
                                  } else {
                                    const char* t233 = "println";
                                    int t234 = name_is_p(id, t233);
                                    if ((t234 != 0)) {
                                      Value t241 = val_car(args);
                                      Value t242 = eval_form(t241, env, mac);
                                      val_println(t242);
                                      Value t244 = val_nil();
                                      return t244;
                                    } else {
                                      Value t245 = env_lookup(mac, id);
                                      Value mfn = t245;
                                      int t246 = is_nil(mfn);
                                      if ((t246 == 0)) {
                                        Value t253 = apply_fn(mfn, args, env, mac);
                                        Value t254 = eval_form(t253, env, mac);
                                        return t254;
                                      } else {
                                        Value t255 = env_lookup(env, id);
                                        Value fn = t255;
                                        int t256 = is_nil(fn);
                                        if ((t256 == 0)) {
                                          Value t263 = eval_args(args, env, mac);
                                          Value t264 = apply_fn(fn, t263, env, mac);
                                          return t264;
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
                }
              }
            }
          }
        }
      }
    }
  }
}

int is_falsy(Value v) {
  int t1 = is_nil(v);
  if ((t1 != 0)) {
    return 1;
  } else {
    int t9 = is_int(v);
    if ((t9 != 0)) {
      int t16 = val_int_of(v);
      if ((t16 == 0)) {
        return 1;
      } else {
        return 0;
      }
    } else {
      return 0;
    }
  }
}

Value append_list(Value a, Value b) {
  int t1 = is_nil(a);
  if ((t1 != 0)) {
    return b;
  } else {
    Value t8 = val_car(a);
    Value t9 = val_cdr(a);
    Value t10 = append_list(t9, b);
    Value t11 = val_cons(t8, t10);
    return t11;
  }
}

int is_tagged_p(Value form, const char* tag) {
  int t1 = is_cons(form);
  if ((t1 == 0)) {
    return 0;
  } else {
    Value t9 = val_car(form);
    Value head = t9;
    int t10 = is_sym(head);
    if ((t10 == 0)) {
      return 0;
    } else {
      uint32_t t18 = val_sym_of(head);
      int t19 = name_is_p(t18, tag);
      return t19;
    }
  }
}

Value eval_qq(Value form, Value env, Value mac) {
  int t1 = is_cons(form);
  if ((t1 == 0)) {
    return form;
  } else {
    const char* t8 = "unquote";
    int t9 = is_tagged_p(form, t8);
    if ((t9 != 0)) {
      Value t16 = val_cdr(form);
      Value t17 = val_car(t16);
      Value t18 = eval_form(t17, env, mac);
      return t18;
    } else {
      Value t19 = eval_qq_list(form, env, mac);
      return t19;
    }
  }
}

Value eval_qq_list(Value items, Value env, Value mac) {
  int t1 = is_nil(items);
  if ((t1 != 0)) {
    Value t8 = val_nil();
    return t8;
  } else {
    Value t9 = val_car(items);
    Value first = t9;
    Value t10 = val_cdr(items);
    Value rest = t10;
    const char* t11 = "splice";
    int t12 = is_tagged_p(first, t11);
    if ((t12 != 0)) {
      Value t19 = val_cdr(first);
      Value t20 = val_car(t19);
      Value t21 = eval_form(t20, env, mac);
      Value t22 = eval_qq_list(rest, env, mac);
      Value t23 = append_list(t21, t22);
      return t23;
    } else {
      Value t24 = eval_qq(first, env, mac);
      Value t25 = eval_qq_list(rest, env, mac);
      Value t26 = val_cons(t24, t25);
      return t26;
    }
  }
}

Value eval_if(Value args, Value env, Value mac) {
  Value t1 = val_car(args);
  Value t2 = eval_form(t1, env, mac);
  int t3 = is_falsy(t2);
  if ((t3 == 1)) {
    Value t10 = val_cdr(args);
    Value t11 = val_cdr(t10);
    Value t12 = val_car(t11);
    Value t13 = eval_form(t12, env, mac);
    return t13;
  } else {
    Value t14 = val_cdr(args);
    Value t15 = val_car(t14);
    Value t16 = eval_form(t15, env, mac);
    return t16;
  }
}

Value eval_let(Value args, Value env, Value mac) {
  Value t1 = val_car(args);
  Value t2 = val_cdr(args);
  Value t3 = eval_let_bindings(t1, env, mac);
  Value t4 = eval_body(t2, t3, mac);
  return t4;
}

Value eval_let_bindings(Value bindings, Value env, Value mac) {
  int t1 = is_nil(bindings);
  if ((t1 != 0)) {
    return env;
  } else {
    Value t8 = val_car(bindings);
    Value b = t8;
    Value t9 = val_car(b);
    uint32_t t10 = val_sym_of(t9);
    Value t11 = val_cdr(b);
    Value t12 = val_car(t11);
    Value t13 = eval_form(t12, env, mac);
    Value t14 = val_cdr(bindings);
    Value t15 = env_bind(env, t10, t13);
    Value t16 = eval_let_bindings(t14, t15, mac);
    return t16;
  }
}

Value eval_body(Value body, Value env, Value mac) {
  int t1 = is_nil(body);
  if ((t1 != 0)) {
    Value t8 = val_nil();
    return t8;
  } else {
    Value t9 = val_car(body);
    Value t10 = eval_form(t9, env, mac);
    Value t11 = val_cdr(body);
    Value rest = t11;
    int t12 = is_nil(rest);
    if ((t12 != 0)) {
      return t10;
    } else {
      Value t19 = eval_body(rest, env, mac);
      return t19;
    }
  }
}

Value apply_fn(Value fn, Value args, Value env, Value mac) {
  Value t1 = closure_params(fn);
  Value t2 = closure_body(fn);
  Value t3 = bind_list(t1, args, env);
  Value t4 = eval_body(t2, t3, mac);
  return t4;
}

Value handle_form(Value form, Value env, Value mac) {
  int t1 = is_cons(form);
  if ((t1 == 0)) {
    Value t8 = eval_form(form, env, mac);
    Value t9 = val_cons(mac, t8);
    Value t10 = val_cons(env, t9);
    return t10;
  } else {
    Value t11 = val_car(form);
    Value head = t11;
    int t12 = is_sym(head);
    if ((t12 == 0)) {
      Value t19 = eval_form(form, env, mac);
      Value t20 = val_cons(mac, t19);
      Value t21 = val_cons(env, t20);
      return t21;
    } else {
      uint32_t t22 = val_sym_of(head);
      const char* t23 = "defn";
      int t24 = name_is_p(t22, t23);
      if ((t24 != 0)) {
        Value t31 = val_cdr(form);
        Value rest = t31;
        Value t32 = val_car(rest);
        uint32_t t33 = val_sym_of(t32);
        uint32_t name = t33;
        Value t34 = val_cdr(rest);
        Value t35 = val_car(t34);
        Value params = t35;
        Value t36 = val_cdr(rest);
        Value t37 = val_cdr(t36);
        Value body = t37;
        Value t38 = val_closure(params, body, env);
        Value closure = t38;
        Value t39 = env_bind(env, name, closure);
        Value t40 = val_nil();
        Value t41 = val_cons(mac, t40);
        Value t42 = val_cons(t39, t41);
        return t42;
      } else {
        uint32_t t43 = val_sym_of(head);
        const char* t44 = "defmacro";
        int t45 = name_is_p(t43, t44);
        if ((t45 != 0)) {
          Value t52 = val_cdr(form);
          Value rest = t52;
          Value t53 = val_car(rest);
          uint32_t t54 = val_sym_of(t53);
          uint32_t name = t54;
          Value t55 = val_cdr(rest);
          Value t56 = val_car(t55);
          Value params = t56;
          Value t57 = val_cdr(rest);
          Value t58 = val_cdr(t57);
          Value body = t58;
          Value t59 = val_closure(params, body, env);
          Value closure = t59;
          Value t60 = env_bind(mac, name, closure);
          Value t61 = val_nil();
          Value t62 = val_cons(t60, t61);
          Value t63 = val_cons(env, t62);
          return t63;
        } else {
          Value t64 = eval_form(form, env, mac);
          Value t65 = val_cons(mac, t64);
          Value t66 = val_cons(env, t65);
          return t66;
        }
      }
    }
  }
}

int main() {
  void* t1 = runtime_stdin();
  void* in = t1;
  void* t2 = runtime_stdout();
  void* out = t2;
  Value t3 = val_nil();
  Value env = t3;
  Value t4 = val_nil();
  Value mac = t4;
  for (;;) {
    int t8 = feof(in);
    if (!((t8 == 0))) break;
    Value t11 = read_sexp(in);
    Value form = t11;
    int t15 = is_cons(form);
    if ((t15 != 0)) {
      Value t18 = handle_form(form, env, mac);
      Value triple = t18;
      Value t19 = val_car(triple);
      Value t20 = val_cdr(triple);
      Value rest = t20;
      Value t21 = val_car(rest);
      Value t22 = val_cdr(rest);
      Value result = t22;
      env = t19;
      mac = t21;
      int t26 = is_nil(result);
      if ((t26 == 0)) {
        write_sexp(out, result);
        int t31 = fputc(10, out);
      } else {
      }
    } else {
    }
  }
  return 0;
}

