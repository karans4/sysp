(load "src/compiler.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (preamble program-c driver expected &key valgrind dump)
  (let ((c-file "/tmp/sysp-ir-mf.c") (exe "/tmp/sysp-ir-mf"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string preamble s) (terpri s)
      (write-string program-c s) (terpri s)
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

(defun program-c (defns)
  (with-output-to-string (s) (compile-program defns s)))

(defun check (label defns driver expected &key valgrind dump)
  (format t "~a:" label)
  (cc-and-run "#include \"runtime.h\"" (program-c defns) driver expected
              :valgrind valgrind :dump dump))

;; Two int fns calling each other.
(check "call-add"
       '((defn add ((x :int) (y :int)) :int (+ x y))
         (defn use-it ((n :int)) :int (add n (add n n))))
       "#include <stdio.h>
int main(){ printf(\"%d\\n\", use_it(5)); return 0; }"
       "15")

;; User fn returning string, called and used.
(check "user-fn-string"
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
(check "fact-recursive"
       '((defn fact ((n :int)) :int
            (if (= n 0) 1 (* n (fact (- n 1))))))
       "#include <stdio.h>
int main(){ printf(\"%d\\n\", fact(6)); return 0; }"
       "720")

;; Mutual recursion (even/odd)
(check "mutual-even-odd"
       '((defn is-even ((n :int)) :int
            (if (= n 0) 1 (is-odd (- n 1))))
         (defn is-odd ((n :int)) :int
            (if (= n 0) 0 (is-even (- n 1)))))
       "#include <stdio.h>
int main(){ printf(\"%d %d\\n\", is_even(8), is_odd(7)); return 0; }"
       "1 1")

;; User fn taking multiple ref args.
(check "concat3"
       '((defn cat3 ((a :string) (b :string) (c :string)) :string
            (string-concat (string-concat a b) c)))
       "int main(){
  String x=sysp_str_lit(\"foo\",3); String y=sysp_str_lit(\"bar\",3); String z=sysp_str_lit(\"baz\",3);
  String r=cat3(x,y,z); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(x); sysp_str_release(y); sysp_str_release(z); return 0;}"
       "foobarbaz" :valgrind t)

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
