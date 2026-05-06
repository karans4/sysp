(load "tests/common.lisp")
(in-package :sysp-ir)

;; Two int fns calling each other.
(check-prog "call-add"
            '((defn add ((x :int) (y :int)) :int (+ x y))
              (defn use-it ((n :int)) :int (add n (add n n))))
            "int main(){ printf(\"%d\\n\", use_it(5)); return 0; }"
            "15")

;; User fn returning string, called and used.
(check-prog "user-fn-string"
            '((defn make-greeting ((name :string)) :string
                (string-concat "hello " name))
              (defn loud ((name :string)) :string
                (string-concat (make-greeting name) "!")))
            "int main(){
  String n=sysp_str_lit(\"karan\",5);
  String r=loud(n); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(n); return 0;}"
            "hello karan!" :valgrind t)

;; Recursion (factorial)
(check-prog "fact-recursive"
            '((defn fact ((n :int)) :int
                (if (= n 0) 1 (* n (fact (- n 1))))))
            "int main(){ printf(\"%d\\n\", fact(6)); return 0; }"
            "720")

;; Mutual recursion (even/odd)
(check-prog "mutual-even-odd"
            '((defn is-even ((n :int)) :int
                (if (= n 0) 1 (is-odd (- n 1))))
              (defn is-odd ((n :int)) :int
                (if (= n 0) 0 (is-even (- n 1)))))
            "int main(){ printf(\"%d %d\\n\", is_even(8), is_odd(7)); return 0; }"
            "1 1")

;; User fn taking multiple ref args.
(check-prog "concat3"
            '((defn cat3 ((a :string) (b :string) (c :string)) :string
                (string-concat (string-concat a b) c)))
            "int main(){
  String x=sysp_str_lit(\"foo\",3); String y=sysp_str_lit(\"bar\",3); String z=sysp_str_lit(\"baz\",3);
  String r=cat3(x,y,z); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); sysp_str_release(z); return 0;}"
            "foobarbaz" :valgrind t)

(report-and-exit)
