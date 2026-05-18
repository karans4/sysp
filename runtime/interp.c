#include <stdio.h>
#include <string.h>
#include "value.h"
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
Value macro_expand_once(Value form, Value env, Value mac);
Value macro_expand_all(Value form, Value env, Value mac);
Value handle_form(Value form, Value env, Value mac);
int main();

Value env_lookup(Value env, uint32_t id) {
  int t1 = is_nil(env);
  if (t1) {
    Value t8 = val_nil();
    return t8;
  } else {
    Value pair = val_car(env);
    Value t10 = val_car(pair);
    uint32_t t11 = val_sym_of(t10);
    val_release(t10);
    if (t11 == id) {
      Value t17 = val_cdr(pair);
      val_release(pair);
      return t17;
    } else {
      val_release(pair);
      Value t18 = val_cdr(env);
      Value t19 = env_lookup(t18, id);
      val_release(t18);
      return t19;
    }
  }
}

Value env_bind(Value env, uint32_t id, Value v) {
  Value t1 = val_sym(id);
  Value t2 = val_cons(t1, v);
  val_release(t1);
  Value t3 = val_cons(t2, env);
  val_release(t2);
  return t3;
}

Value bind_list(Value params, Value args, Value env) {
  int t1 = is_nil(params);
  if (t1) {
    val_retain(env);
    return env;
  } else {
    Value t8 = val_cdr(params);
    Value t9 = val_cdr(args);
    Value t10 = val_car(params);
    uint32_t t11 = val_sym_of(t10);
    val_release(t10);
    Value t12 = val_car(args);
    Value t13 = env_bind(env, t11, t12);
    val_release(t12);
    Value t14 = bind_list(t8, t9, t13);
    val_release(t8);
    val_release(t9);
    val_release(t13);
    return t14;
  }
}

int name_is_p(uint32_t id, const char* s) {
  int t2 = strcasecmp(sym_name(id), s);
  return (t2 == 0);
}

Value eval_form(Value form, Value env, Value mac) {
  int t1 = is_int(form);
  if (t1) {
    val_retain(form);
    return form;
  } else {
    int t8 = is_str(form);
    if (t8) {
      val_retain(form);
      return form;
    } else {
      int t15 = is_nil(form);
      if (t15) {
        val_retain(form);
        return form;
      } else {
        int t22 = is_sym(form);
        if (t22) {
          Value found = env_lookup(env, val_sym_of(form));
          int t31 = is_nil(found);
          if (t31) {
            val_release(found);
            val_retain(form);
            return form;
          } else {
            return found;
          }
        } else {
          int t38 = is_cons(form);
          if (t38) {
            Value t45 = eval_call(form, env, mac);
            return t45;
          } else {
            val_retain(form);
            return form;
          }
        }
      }
    }
  }
}

Value eval_args(Value args, Value env, Value mac) {
  int t1 = is_nil(args);
  if (t1) {
    Value t8 = val_nil();
    return t8;
  } else {
    Value t9 = val_car(args);
    Value t10 = eval_form(t9, env, mac);
    val_release(t9);
    Value t11 = val_cdr(args);
    Value t12 = eval_args(t11, env, mac);
    val_release(t11);
    Value t13 = val_cons(t10, t12);
    val_release(t10);
    val_release(t12);
    return t13;
  }
}

Value eval_call(Value form, Value env, Value mac) {
  Value head = val_car(form);
  Value args = val_cdr(form);
  int t3 = is_sym(head);
  if (t3) {
    uint32_t t10 = val_sym_of(head);
    val_release(head);
    Value t11 = dispatch(t10, args, env, mac, form);
    val_release(args);
    return t11;
  } else {
    Value t12 = eval_form(head, env, mac);
    val_release(head);
    Value t13 = eval_args(args, env, mac);
    val_release(args);
    Value t14 = apply_fn(t12, t13, env, mac);
    val_release(t12);
    val_release(t13);
    return t14;
  }
}

Value dispatch(uint32_t id, Value args, Value env, Value mac, Value form) {
  int t134;
  int t157;
  const char* t1 = "quote";
  int t2 = name_is_p(id, t1);
  if (t2) {
    Value t9 = val_car(args);
    return t9;
  } else {
    const char* t10 = "if";
    int t11 = name_is_p(id, t10);
    if (t11) {
      Value t18 = eval_if(args, env, mac);
      return t18;
    } else {
      const char* t19 = "quasiquote";
      int t20 = name_is_p(id, t19);
      if (t20) {
        Value t27 = val_car(args);
        Value t28 = eval_qq(t27, env, mac);
        val_release(t27);
        return t28;
      } else {
        const char* t29 = "let";
        int t30 = name_is_p(id, t29);
        if (t30) {
          Value t37 = eval_let(args, env, mac);
          return t37;
        } else {
          const char* t38 = "lambda";
          int t39 = name_is_p(id, t38);
          if (t39) {
            Value t46 = val_car(args);
            Value t47 = val_cdr(args);
            Value t48 = val_closure(t46, t47, env);
            val_release(t46);
            val_release(t47);
            return t48;
          } else {
            const char* t49 = "+";
            int t50 = name_is_p(id, t49);
            if (t50) {
              Value t57 = val_car(args);
              Value t58 = eval_form(t57, env, mac);
              val_release(t57);
              int t59 = val_int_of(t58);
              val_release(t58);
              Value t60 = val_cdr(args);
              Value t61 = val_car(t60);
              val_release(t60);
              Value t62 = eval_form(t61, env, mac);
              val_release(t61);
              int t63 = val_int_of(t62);
              val_release(t62);
              Value t65 = val_int((t59 + t63));
              return t65;
            } else {
              const char* t66 = "-";
              int t67 = name_is_p(id, t66);
              if (t67) {
                Value t74 = val_car(args);
                Value t75 = eval_form(t74, env, mac);
                val_release(t74);
                int t76 = val_int_of(t75);
                val_release(t75);
                Value t77 = val_cdr(args);
                Value t78 = val_car(t77);
                val_release(t77);
                Value t79 = eval_form(t78, env, mac);
                val_release(t78);
                int t80 = val_int_of(t79);
                val_release(t79);
                Value t82 = val_int((t76 - t80));
                return t82;
              } else {
                const char* t83 = "*";
                int t84 = name_is_p(id, t83);
                if (t84) {
                  Value t91 = val_car(args);
                  Value t92 = eval_form(t91, env, mac);
                  val_release(t91);
                  int t93 = val_int_of(t92);
                  val_release(t92);
                  Value t94 = val_cdr(args);
                  Value t95 = val_car(t94);
                  val_release(t94);
                  Value t96 = eval_form(t95, env, mac);
                  val_release(t95);
                  int t97 = val_int_of(t96);
                  val_release(t96);
                  Value t99 = val_int((t93 * t97));
                  return t99;
                } else {
                  const char* t100 = "=";
                  int t101 = name_is_p(id, t100);
                  if (t101) {
                    Value t108 = val_car(args);
                    Value t109 = eval_form(t108, env, mac);
                    val_release(t108);
                    Value t110 = val_cdr(args);
                    Value t111 = val_car(t110);
                    val_release(t110);
                    Value t112 = eval_form(t111, env, mac);
                    val_release(t111);
                    int t113 = val_eq(t109, t112);
                    val_release(t109);
                    val_release(t112);
                    Value t114 = val_int(t113);
                    return t114;
                  } else {
                    const char* t115 = "<";
                    int t116 = name_is_p(id, t115);
                    if (t116) {
                      Value t123 = val_car(args);
                      Value t124 = eval_form(t123, env, mac);
                      val_release(t123);
                      int t125 = val_int_of(t124);
                      val_release(t124);
                      Value t126 = val_cdr(args);
                      Value t127 = val_car(t126);
                      val_release(t126);
                      Value t128 = eval_form(t127, env, mac);
                      val_release(t127);
                      int t129 = val_int_of(t128);
                      val_release(t128);
                      if (t125 < t129) {
                        t134 = 1;
                      } else {
                        t134 = 0;
                      }
                      Value t137 = val_int(t134);
                      return t137;
                    } else {
                      const char* t138 = ">";
                      int t139 = name_is_p(id, t138);
                      if (t139) {
                        Value t146 = val_car(args);
                        Value t147 = eval_form(t146, env, mac);
                        val_release(t146);
                        int t148 = val_int_of(t147);
                        val_release(t147);
                        Value t149 = val_cdr(args);
                        Value t150 = val_car(t149);
                        val_release(t149);
                        Value t151 = eval_form(t150, env, mac);
                        val_release(t150);
                        int t152 = val_int_of(t151);
                        val_release(t151);
                        if (t148 > t152) {
                          t157 = 1;
                        } else {
                          t157 = 0;
                        }
                        Value t160 = val_int(t157);
                        return t160;
                      } else {
                        const char* t161 = "cons";
                        int t162 = name_is_p(id, t161);
                        if (t162) {
                          Value t169 = val_car(args);
                          Value t170 = eval_form(t169, env, mac);
                          val_release(t169);
                          Value t171 = val_cdr(args);
                          Value t172 = val_car(t171);
                          val_release(t171);
                          Value t173 = eval_form(t172, env, mac);
                          val_release(t172);
                          Value t174 = val_cons(t170, t173);
                          val_release(t170);
                          val_release(t173);
                          return t174;
                        } else {
                          const char* t175 = "car";
                          int t176 = name_is_p(id, t175);
                          if (t176) {
                            Value t183 = val_car(args);
                            Value t184 = eval_form(t183, env, mac);
                            val_release(t183);
                            Value t185 = val_car(t184);
                            val_release(t184);
                            return t185;
                          } else {
                            const char* t186 = "cdr";
                            int t187 = name_is_p(id, t186);
                            if (t187) {
                              Value t194 = val_car(args);
                              Value t195 = eval_form(t194, env, mac);
                              val_release(t194);
                              Value t196 = val_cdr(t195);
                              val_release(t195);
                              return t196;
                            } else {
                              const char* t197 = "nil?";
                              int t198 = name_is_p(id, t197);
                              if (t198) {
                                Value t205 = val_car(args);
                                Value t206 = eval_form(t205, env, mac);
                                val_release(t205);
                                int t207 = is_nil(t206);
                                val_release(t206);
                                Value t208 = val_int(t207);
                                return t208;
                              } else {
                                const char* t209 = "sym-eq?";
                                int t210 = name_is_p(id, t209);
                                if (t210) {
                                  Value t217 = val_car(args);
                                  Value t218 = eval_form(t217, env, mac);
                                  val_release(t217);
                                  Value t219 = val_cdr(args);
                                  Value t220 = val_car(t219);
                                  val_release(t219);
                                  Value t221 = eval_form(t220, env, mac);
                                  val_release(t220);
                                  int t222 = sym_eq(t218, t221);
                                  val_release(t218);
                                  val_release(t221);
                                  Value t223 = val_int(t222);
                                  return t223;
                                } else {
                                  const char* t224 = "list";
                                  int t225 = name_is_p(id, t224);
                                  if (t225) {
                                    Value t232 = eval_args(args, env, mac);
                                    return t232;
                                  } else {
                                    const char* t233 = "gensym";
                                    int t234 = name_is_p(id, t233);
                                    if (t234) {
                                      Value t241 = gensym();
                                      return t241;
                                    } else {
                                      const char* t242 = "println";
                                      int t243 = name_is_p(id, t242);
                                      if (t243) {
                                        Value t250 = val_car(args);
                                        Value t251 = eval_form(t250, env, mac);
                                        val_release(t250);
                                        val_println(t251);
                                        val_release(t251);
                                        Value t253 = val_nil();
                                        return t253;
                                      } else {
                                        const char* t254 = "macroexpand";
                                        int t255 = name_is_p(id, t254);
                                        if (t255) {
                                          Value t262 = val_car(args);
                                          Value t263 = eval_form(t262, env, mac);
                                          val_release(t262);
                                          Value t264 = macro_expand_all(t263, env, mac);
                                          val_release(t263);
                                          return t264;
                                        } else {
                                          Value mfn = env_lookup(mac, id);
                                          int t266 = is_nil(mfn);
                                          if (t266 == 0) {
                                            Value expanded = apply_fn(mfn, args, env, mac);
                                            val_release(mfn);
                                            Value t274 = eval_form(expanded, env, mac);
                                            val_release(expanded);
                                            return t274;
                                          } else {
                                            val_release(mfn);
                                            Value fn = env_lookup(env, id);
                                            int t276 = is_nil(fn);
                                            if (t276 == 0) {
                                              Value t283 = eval_args(args, env, mac);
                                              Value t284 = apply_fn(fn, t283, env, mac);
                                              val_release(fn);
                                              val_release(t283);
                                              return t284;
                                            } else {
                                              val_release(fn);
                                              val_retain(form);
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
  }
}

int is_falsy(Value v) {
  int t1 = is_nil(v);
  if (t1) {
    return 1;
  } else {
    int t9 = is_int(v);
    if (t9) {
      int t16 = val_int_of(v);
      if (t16 == 0) {
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
  if (t1) {
    val_retain(b);
    return b;
  } else {
    Value t8 = val_car(a);
    Value t9 = val_cdr(a);
    Value t10 = append_list(t9, b);
    val_release(t9);
    Value t11 = val_cons(t8, t10);
    val_release(t8);
    val_release(t10);
    return t11;
  }
}

int is_tagged_p(Value form, const char* tag) {
  int t1 = is_cons(form);
  if (t1 == 0) {
    return 0;
  } else {
    Value head = val_car(form);
    int t10 = is_sym(head);
    if (t10 == 0) {
      val_release(head);
      return 0;
    } else {
      uint32_t t18 = val_sym_of(head);
      val_release(head);
      return name_is_p(t18, tag);
    }
  }
}

Value eval_qq(Value form, Value env, Value mac) {
  int t1 = is_cons(form);
  if (t1 == 0) {
    val_retain(form);
    return form;
  } else {
    const char* t8 = "unquote";
    int t9 = is_tagged_p(form, t8);
    if (t9) {
      Value t16 = val_cdr(form);
      Value t17 = val_car(t16);
      val_release(t16);
      Value t18 = eval_form(t17, env, mac);
      val_release(t17);
      return t18;
    } else {
      Value t19 = eval_qq_list(form, env, mac);
      return t19;
    }
  }
}

Value eval_qq_list(Value items, Value env, Value mac) {
  int t1 = is_nil(items);
  if (t1) {
    Value t8 = val_nil();
    return t8;
  } else {
    Value first = val_car(items);
    Value rest = val_cdr(items);
    const char* t11 = "splice";
    int t12 = is_tagged_p(first, t11);
    if (t12) {
      Value t19 = val_cdr(first);
      val_release(first);
      Value t20 = val_car(t19);
      val_release(t19);
      Value t21 = eval_form(t20, env, mac);
      val_release(t20);
      Value t22 = eval_qq_list(rest, env, mac);
      val_release(rest);
      Value t23 = append_list(t21, t22);
      val_release(t21);
      val_release(t22);
      return t23;
    } else {
      Value t24 = eval_qq(first, env, mac);
      val_release(first);
      Value t25 = eval_qq_list(rest, env, mac);
      val_release(rest);
      Value t26 = val_cons(t24, t25);
      val_release(t24);
      val_release(t25);
      return t26;
    }
  }
}

Value eval_if(Value args, Value env, Value mac) {
  Value t1 = val_car(args);
  Value c = eval_form(t1, env, mac);
  val_release(t1);
  int t3 = is_falsy(c);
  val_release(c);
  if (t3 == 1) {
    Value t10 = val_cdr(args);
    Value t11 = val_cdr(t10);
    val_release(t10);
    Value t12 = val_car(t11);
    val_release(t11);
    Value t13 = eval_form(t12, env, mac);
    val_release(t12);
    return t13;
  } else {
    Value t14 = val_cdr(args);
    Value t15 = val_car(t14);
    val_release(t14);
    Value t16 = eval_form(t15, env, mac);
    val_release(t15);
    return t16;
  }
}

Value eval_let(Value args, Value env, Value mac) {
  Value bindings = val_car(args);
  Value body = val_cdr(args);
  Value new_env = eval_let_bindings(bindings, env, mac);
  val_release(bindings);
  Value t4 = eval_body(body, new_env, mac);
  val_release(body);
  val_release(new_env);
  return t4;
}

Value eval_let_bindings(Value bindings, Value env, Value mac) {
  int t1 = is_nil(bindings);
  if (t1) {
    val_retain(env);
    return env;
  } else {
    Value b = val_car(bindings);
    Value t9 = val_car(b);
    uint32_t name = val_sym_of(t9);
    val_release(t9);
    Value t11 = val_cdr(b);
    val_release(b);
    Value t12 = val_car(t11);
    val_release(t11);
    Value val = eval_form(t12, env, mac);
    val_release(t12);
    Value t14 = val_cdr(bindings);
    Value t15 = env_bind(env, name, val);
    val_release(val);
    Value t16 = eval_let_bindings(t14, t15, mac);
    val_release(t14);
    val_release(t15);
    return t16;
  }
}

Value eval_body(Value body, Value env, Value mac) {
  int t1 = is_nil(body);
  if (t1) {
    Value t8 = val_nil();
    return t8;
  } else {
    Value t9 = val_car(body);
    Value first = eval_form(t9, env, mac);
    val_release(t9);
    Value rest = val_cdr(body);
    int t12 = is_nil(rest);
    if (t12) {
      val_release(rest);
      return first;
    } else {
      val_release(first);
      Value t19 = eval_body(rest, env, mac);
      val_release(rest);
      return t19;
    }
  }
}

Value apply_fn(Value fn, Value args, Value env, Value mac) {
  Value params = closure_params(fn);
  Value body = closure_body(fn);
  Value new_env = bind_list(params, args, env);
  val_release(params);
  Value t4 = eval_body(body, new_env, mac);
  val_release(body);
  val_release(new_env);
  return t4;
}

Value macro_expand_once(Value form, Value env, Value mac) {
  int t1 = is_cons(form);
  if (t1 == 0) {
    val_retain(form);
    return form;
  } else {
    Value head = val_car(form);
    int t9 = is_sym(head);
    if (t9 == 0) {
      val_release(head);
      val_retain(form);
      return form;
    } else {
      uint32_t t16 = val_sym_of(head);
      val_release(head);
      Value mfn = env_lookup(mac, t16);
      int t18 = is_nil(mfn);
      if (t18) {
        val_release(mfn);
        val_retain(form);
        return form;
      } else {
        Value t25 = val_cdr(form);
        Value t26 = apply_fn(mfn, t25, env, mac);
        val_release(mfn);
        val_release(t25);
        return t26;
      }
    }
  }
}

Value macro_expand_all(Value form, Value env, Value mac) {
  Value once = macro_expand_once(form, env, mac);
  int t2 = val_eq(once, form);
  if (t2 == 0) {
    Value t9 = macro_expand_all(once, env, mac);
    val_release(once);
    return t9;
  } else {
    val_release(once);
    int t10 = is_cons(form);
    if (t10 == 0) {
      val_retain(form);
      return form;
    } else {
      Value t17 = val_car(form);
      Value t18 = macro_expand_all(t17, env, mac);
      val_release(t17);
      Value t19 = val_cdr(form);
      Value t20 = macro_expand_all(t19, env, mac);
      val_release(t19);
      Value t21 = val_cons(t18, t20);
      val_release(t18);
      val_release(t20);
      return t21;
    }
  }
}

Value handle_form(Value form, Value env, Value mac) {
  int t1 = is_cons(form);
  if (t1 == 0) {
    Value t8 = eval_form(form, env, mac);
    Value t9 = val_cons(mac, t8);
    val_release(t8);
    Value t10 = val_cons(env, t9);
    val_release(t9);
    return t10;
  } else {
    Value head = val_car(form);
    int t12 = is_sym(head);
    if (t12 == 0) {
      val_release(head);
      Value t19 = eval_form(form, env, mac);
      Value t20 = val_cons(mac, t19);
      val_release(t19);
      Value t21 = val_cons(env, t20);
      val_release(t20);
      return t21;
    } else {
      uint32_t t22 = val_sym_of(head);
      const char* t23 = "defn";
      int t24 = name_is_p(t22, t23);
      if (t24) {
        val_release(head);
        Value rest = val_cdr(form);
        Value t32 = val_car(rest);
        uint32_t name = val_sym_of(t32);
        val_release(t32);
        Value t34 = val_cdr(rest);
        Value params = val_car(t34);
        val_release(t34);
        Value t36 = val_cdr(rest);
        val_release(rest);
        Value body = val_cdr(t36);
        val_release(t36);
        Value closure = val_closure(params, body, env);
        val_release(params);
        val_release(body);
        Value t39 = env_bind(env, name, closure);
        val_release(closure);
        Value t40 = val_nil();
        Value t41 = val_cons(mac, t40);
        val_release(t40);
        Value t42 = val_cons(t39, t41);
        val_release(t39);
        val_release(t41);
        return t42;
      } else {
        uint32_t t43 = val_sym_of(head);
        val_release(head);
        const char* t44 = "defmacro";
        int t45 = name_is_p(t43, t44);
        if (t45) {
          Value rest = val_cdr(form);
          Value t53 = val_car(rest);
          uint32_t name = val_sym_of(t53);
          val_release(t53);
          Value t55 = val_cdr(rest);
          Value params = val_car(t55);
          val_release(t55);
          Value t57 = val_cdr(rest);
          val_release(rest);
          Value body = val_cdr(t57);
          val_release(t57);
          Value closure = val_closure(params, body, env);
          val_release(params);
          val_release(body);
          Value t60 = env_bind(mac, name, closure);
          val_release(closure);
          Value t61 = val_nil();
          Value t62 = val_cons(t60, t61);
          val_release(t60);
          val_release(t61);
          Value t63 = val_cons(env, t62);
          val_release(t62);
          return t63;
        } else {
          Value t64 = eval_form(form, env, mac);
          Value t65 = val_cons(mac, t64);
          val_release(t64);
          Value t66 = val_cons(env, t65);
          val_release(t65);
          return t66;
        }
      }
    }
  }
}

int main() {
  void* in = runtime_stdin();
  void* out = runtime_stdout();
  Value t3 = val_nil();
  Value env = t3;
  val_retain(env);
  val_release(t3);
  Value t4 = val_nil();
  Value mac = t4;
  val_retain(mac);
  val_release(t4);
  for (;;) {
    int t8 = feof(in);
    if (!(t8 == 0)) break;
    Value form = read_sexp(in);
    int t15 = is_cons(form);
    if (t15) {
      Value triple = handle_form(form, env, mac);
      val_release(form);
      Value new_env = val_car(triple);
      Value rest = val_cdr(triple);
      val_release(triple);
      Value new_mac = val_car(rest);
      Value result = val_cdr(rest);
      val_release(rest);
      val_release(env);
      env = new_env;
      val_retain(env);
      val_release(new_env);
      val_release(mac);
      mac = new_mac;
      val_retain(mac);
      val_release(new_mac);
      int t26 = is_nil(result);
      if (t26 == 0) {
        write_sexp(out, result);
        val_release(result);
        int t31 = fputc(10, out);
        int t32 = fflush(out);
      } else {
        val_release(result);
      }
    } else {
      val_release(form);
    }
  }
  return 0;
}

