(load "tests/common.lisp")
(in-package :sysp-ir)

(check-prog "literal-return"
            '((defn make () :string "hello"))
            "int main(){ String s = make(); sysp_str_print(s); sysp_str_release(s); return 0; }"
            "hello" :valgrind t)

(check-prog "concat-two-literals"
            '((defn greet () :string (string-concat "hello " "world")))
            "int main(){ String s = greet(); sysp_str_print(s); sysp_str_release(s); return 0; }"
            "hello world" :valgrind t)

(check-prog "concat-three"
            '((defn g () :string
                (string-concat (string-concat "a" "b") "c")))
            "int main(){ String s = g(); sysp_str_print(s); sysp_str_release(s); return 0; }"
            "abc" :valgrind t)

(check-prog "echo-transfer"
            '((defn echo ((s :string)) :string s))
            "int main(){ String a = sysp_str_lit(\"ping\", 4); String b = echo(a);
   sysp_str_print(b); sysp_str_release(b); sysp_str_release(a); return 0; }"
            "ping" :valgrind t)

(check-prog "use-and-drop-param"
            '((defn shout ((s :string)) :string (string-concat s "!")))
            "int main(){ String a = sysp_str_lit(\"hi\", 2); String b = shout(a);
   sysp_str_print(b); sysp_str_release(b); sysp_str_release(a); return 0; }"
            "hi!" :valgrind t)

(check-prog "param-len-only"
            '((defn lenfn ((s :string)) :int (string-len s)))
            "int main(){ String a = sysp_str_lit(\"abcd\", 4); int n = lenfn(a);
   printf(\"%d\\n\", n); sysp_str_release(a); return 0; }"
            "4" :valgrind t)

(check-prog "alias-via-let"
            '((defn id ((s :string)) :string (let ((x s)) x)))
            "int main(){ String a=sysp_str_lit(\"hi\",2); String b=id(a);
   sysp_str_print(b); sysp_str_release(b); sysp_str_release(a); return 0; }"
            "hi" :valgrind t)

(check-prog "alias-then-concat"
            '((defn dup-greet ((name :string)) :string
                (let ((copy name)) (string-concat copy "!"))))
            "int main(){ String n=sysp_str_lit(\"karan\",5); String r=dup_greet(n);
   sysp_str_print(r); sysp_str_release(r); sysp_str_release(n); return 0; }"
            "karan!" :valgrind t)

;; recur carrying a ref-typed (String) accumulator: owned-parameter ARC
;; (SPEC §9.3) retains the param at entry, so each iteration's release-old/
;; retain-new and the owned transfer at return balance. main owns `e` and
;; releases it (borrow discipline); the gate catches any imbalance.
(check-prog "recur-string-accumulator"
            '((defn rep ((n :int) (acc :string)) :string
                (if (= n 0) acc (recur (- n 1) (string-concat acc "x")))))
            "int main(){ String e = sysp_str_lit(\"\", 0); String r = rep(3, e);
   sysp_str_print(r); sysp_str_release(r); sysp_str_release(e); return 0; }"
            "xxx" :valgrind t)

;; recur where the owned accumulator is NOT returned: it must be released at
;; its last use in the exit arm, not transferred.
(check-prog "recur-string-not-returned"
            '((defn slen ((n :int) (acc :string)) :int
                (if (= n 0) (string-len acc) (recur (- n 1) (string-concat acc "x")))))
            "int main(){ String e = sysp_str_lit(\"\", 0); int r = slen(3, e);
   printf(\"%d\\n\", r); sysp_str_release(e); return 0; }"
            "3" :valgrind t)

(report-and-exit)
