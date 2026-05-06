(load "tests/common.lisp")
(in-package :sysp-ir)

;; pick: ifs select among params. The unchosen branch must release the param
;; that wasn't returned, but NOT the one that was. Symmetric.
(check-prog "pick-true"
            '((defn pick ((flag :bool) (a :string) (b :string)) :string
                (if flag a b)))
            "int main(){
  String x=sysp_str_lit(\"AAA\",3); String y=sysp_str_lit(\"BBB\",3);
  String r=pick(1,x,y); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); return 0;}"
            "AAA" :valgrind t)

(check-prog "pick-false"
            '((defn pick ((flag :bool) (a :string) (b :string)) :string
                (if flag a b)))
            "int main(){
  String x=sysp_str_lit(\"AAA\",3); String y=sysp_str_lit(\"BBB\",3);
  String r=pick(0,x,y); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); return 0;}"
            "BBB" :valgrind t)

;; if produces a freshly-allocated string in one branch, a literal in another.
;; Both should transfer to the join, exit cleanly.
(check-prog "if-build-vs-lit-true"
            '((defn maybe_greet ((flag :bool) (name :string)) :string
                (if flag (string-concat "hi " name) "anon")))
            "int main(){
  String n=sysp_str_lit(\"karan\",5);
  String r=maybe_greet(1,n); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(n); return 0;}"
            "hi karan" :valgrind t)

(check-prog "if-build-vs-lit-false"
            '((defn maybe_greet ((flag :bool) (name :string)) :string
                (if flag (string-concat "hi " name) "anon")))
            "int main(){
  String n=sysp_str_lit(\"karan\",5);
  String r=maybe_greet(0,n); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(n); return 0;}"
            "anon" :valgrind t)

;; if produces an int — the param must be released in BOTH branches.
(check-prog "discard-param-in-branch-true"
            '((defn lf ((flag :bool) (a :string)) :int
                (if flag (string-len a) 0)))
            "int main(){ String x=sysp_str_lit(\"abcdef\",6);
  int r=lf(1,x); printf(\"%d\\n\",r); sysp_str_release(x); return 0;}"
            "6" :valgrind t)

(check-prog "discard-param-in-branch-false"
            '((defn lf ((flag :bool) (a :string)) :int
                (if flag (string-len a) 0)))
            "int main(){ String x=sysp_str_lit(\"abcdef\",6);
  int r=lf(0,x); printf(\"%d\\n\",r); sysp_str_release(x); return 0;}"
            "0" :valgrind t)

;; Nested if returning string
(check-prog "nested-if-pick-1"
            '((defn three ((n :int) (a :string) (b :string) (c :string)) :string
                (if (= n 0) a (if (= n 1) b c))))
            "int main(){
  String x=sysp_str_lit(\"X\",1); String y=sysp_str_lit(\"Y\",1); String z=sysp_str_lit(\"Z\",1);
  String r=three(1,x,y,z); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); sysp_str_release(z); return 0;}"
            "Y" :valgrind t)

(check-prog "nested-if-pick-2"
            '((defn three ((n :int) (a :string) (b :string) (c :string)) :string
                (if (= n 0) a (if (= n 1) b c))))
            "int main(){
  String x=sysp_str_lit(\"X\",1); String y=sysp_str_lit(\"Y\",1); String z=sysp_str_lit(\"Z\",1);
  String r=three(2,x,y,z); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); sysp_str_release(z); return 0;}"
            "Z" :valgrind t)

(report-and-exit)
