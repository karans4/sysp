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

;; recur carrying a ref-typed (String) accumulator is rejected loudly until
;; owned-parameter ARC lands (a borrowed param can't be reassigned with
;; release-old without freeing the caller's value). Previously this silently
;; miscompiled (copy/set typed :int truncated the String).
(handler-case
    (progn
      (program-c '((defn rep ((n :int) (acc :string)) :string
                     (if (= n 0) acc (recur (- n 1) (string-concat acc "x"))))))
      (incf *fail*)
      (format t "recur-ref-accumulator-rejected: FAIL (no error raised)~%"))
  (error ()
    (incf *ok*)
    (format t "recur-ref-accumulator-rejected: ok (error raised)~%")))

(report-and-exit)
