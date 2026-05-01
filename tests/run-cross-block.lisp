(load "src/compiler.lisp")
(in-package :sysp-ir)

(defvar *ok* 0)
(defvar *fail* 0)

(defun compile-form-to-c (form)
  (with-output-to-string (s) (emit-c-fn (compile-defn form) s)))

(defun cc-and-run (preamble fns driver expected &key valgrind dump)
  (let ((c-file "/tmp/sysp-ir-cb.c") (exe "/tmp/sysp-ir-cb"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string preamble s) (terpri s)
      (dolist (f fns) (write-string f s) (terpri s))
      (write-string driver s))
    (when dump
      (with-open-file (s c-file :direction :input)
        (loop for l = (read-line s nil nil) while l do (format t "  | ~a~%" l))))
    (let ((ret (sb-ext:run-program "/usr/bin/cc"
                                   (list "-O0" "-Isrc" "-o" exe c-file)
                                   :output t :error t)))
      (unless (zerop (sb-ext:process-exit-code ret))
        (incf *fail*) (format t " [CC FAIL]~%") (return-from cc-and-run nil)))
    (let* ((p (sb-ext:run-program exe nil :output :stream))
           (out (with-output-to-string (s)
                  (loop for line = (read-line (sb-ext:process-output p) nil nil)
                        while line do (write-line line s)))))
      (sb-ext:process-wait p)
      (let ((got (string-trim '(#\Newline #\Space) out)))
        (if (string= got expected)
            (progn (incf *ok*) (format t " ok"))
            (progn (incf *fail*) (format t " FAIL out: got ~s want ~s" got expected)))))
    (when valgrind
      (let* ((p (sb-ext:run-program "/usr/bin/valgrind"
                                    (list "--error-exitcode=2" "--leak-check=full" "-q" exe)
                                    :output nil :error :stream))
             (errs (with-output-to-string (s)
                     (loop for line = (read-line (sb-ext:process-error p) nil nil)
                           while line do (write-line line s)))))
        (sb-ext:process-wait p)
        (if (zerop (sb-ext:process-exit-code p))
            (format t " (vg clean)~%")
            (progn (incf *fail*) (format t " VG FAIL:~%~a" errs)))))
    (terpri)))

(defun check (label fn-forms driver expected &key valgrind dump)
  (format t "~a:" label)
  (cc-and-run "#include \"runtime.h\""
              (mapcar #'compile-form-to-c fn-forms)
              driver expected :valgrind valgrind :dump dump))

;; pick: ifs select among params. The unchosen branch must release the param
;; that wasn't returned, but NOT the one that was. Symmetric.
(check "pick-true"
       (list '(defn pick ((flag :bool) (a :string) (b :string)) :string
                (if flag a b)))
       "int main(){
  String x=sysp_str_lit(\"AAA\",3); String y=sysp_str_lit(\"BBB\",3);
  String r=pick(1,x,y); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); return 0;}"
       "AAA" :valgrind t)

(check "pick-false"
       (list '(defn pick ((flag :bool) (a :string) (b :string)) :string
                (if flag a b)))
       "int main(){
  String x=sysp_str_lit(\"AAA\",3); String y=sysp_str_lit(\"BBB\",3);
  String r=pick(0,x,y); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); return 0;}"
       "BBB" :valgrind t)

;; if produces a freshly-allocated string in one branch, a literal in another.
;; Both should transfer to the join, exit cleanly.
(check "if-build-vs-lit-true"
       (list '(defn maybe_greet ((flag :bool) (name :string)) :string
                (if flag (string-concat "hi " name) "anon")))
       "int main(){
  String n=sysp_str_lit(\"karan\",5);
  String r=maybe_greet(1,n); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(n); return 0;}"
       "hi karan" :valgrind t)

(check "if-build-vs-lit-false"
       (list '(defn maybe_greet ((flag :bool) (name :string)) :string
                (if flag (string-concat "hi " name) "anon")))
       "int main(){
  String n=sysp_str_lit(\"karan\",5);
  String r=maybe_greet(0,n); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(n); return 0;}"
       "anon" :valgrind t)

;; if produces an int — the param must be released in BOTH branches.
(check "discard-param-in-branch-true"
       (list '(defn lf ((flag :bool) (a :string)) :int
                (if flag (string-len a) 0)))
       "#include <stdio.h>
int main(){ String x=sysp_str_lit(\"abcdef\",6);
  int r=lf(1,x); printf(\"%d\\n\",r); sysp_str_release(x); return 0;}"
       "6" :valgrind t)

(check "discard-param-in-branch-false"
       (list '(defn lf ((flag :bool) (a :string)) :int
                (if flag (string-len a) 0)))
       "#include <stdio.h>
int main(){ String x=sysp_str_lit(\"abcdef\",6);
  int r=lf(0,x); printf(\"%d\\n\",r); sysp_str_release(x); return 0;}"
       "0" :valgrind t)

;; Nested if returning string
(check "nested-if-pick-1"
       (list '(defn three ((n :int) (a :string) (b :string) (c :string)) :string
                (if (= n 0) a (if (= n 1) b c))))
       "int main(){
  String x=sysp_str_lit(\"X\",1); String y=sysp_str_lit(\"Y\",1); String z=sysp_str_lit(\"Z\",1);
  String r=three(1,x,y,z); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); sysp_str_release(z); return 0;}"
       "Y" :valgrind t)

(check "nested-if-pick-2"
       (list '(defn three ((n :int) (a :string) (b :string) (c :string)) :string
                (if (= n 0) a (if (= n 1) b c))))
       "int main(){
  String x=sysp_str_lit(\"X\",1); String y=sysp_str_lit(\"Y\",1); String z=sysp_str_lit(\"Z\",1);
  String r=three(2,x,y,z); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); sysp_str_release(z); return 0;}"
       "Z" :valgrind t)

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
