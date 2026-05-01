(load "src/compiler.lisp")
(in-package :sysp-ir)

(defvar *ok* 0)
(defvar *fail* 0)

(defun compile-form-to-c (form)
  (with-output-to-string (s) (emit-c-fn (compile-defn form) s)))

(defun cc-and-run (preamble fns driver expected &key valgrind)
  (let ((c-file "/tmp/sysp-ir-str.c")
        (exe    "/tmp/sysp-ir-str"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string preamble s) (terpri s)
      (dolist (f fns) (write-string f s) (terpri s))
      (write-string driver s))
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
        (let ((code (sb-ext:process-exit-code p)))
          (if (zerop code)
              (format t " (valgrind clean)~%")
              (progn (incf *fail*) (format t " VALGRIND FAIL:~%~a" errs))))))
    (terpri)))

(defun preamble () "#include \"runtime.h\"")

(defun check (label fn-forms driver expected &key valgrind)
  (format t "~a:" label)
  (cc-and-run (preamble)
              (mapcar #'compile-form-to-c fn-forms)
              driver expected
              :valgrind valgrind))

(check "literal-return"
       (list '(defn make () :string "hello"))
       "int main(){ String s = make(); sysp_str_print(s); sysp_str_release(s); return 0; }"
       "hello"
       :valgrind t)

(check "concat-two-literals"
       (list '(defn greet () :string (string-concat "hello " "world")))
       "int main(){ String s = greet(); sysp_str_print(s); sysp_str_release(s); return 0; }"
       "hello world"
       :valgrind t)

(check "concat-three"
       (list '(defn g () :string
                (string-concat (string-concat "a" "b") "c")))
       "int main(){ String s = g(); sysp_str_print(s); sysp_str_release(s); return 0; }"
       "abc"
       :valgrind t)

(check "echo-transfer"
       (list '(defn echo ((s :string)) :string s))
       "int main(){ String a = sysp_str_lit(\"ping\", 4); String b = echo(a);
   sysp_str_print(b); sysp_str_release(b); sysp_str_release(a); return 0; }"
       "ping" :valgrind t)

(check "use-and-drop-param"
       (list '(defn shout ((s :string)) :string (string-concat s "!")))
       "int main(){ String a = sysp_str_lit(\"hi\", 2); String b = shout(a);
   sysp_str_print(b); sysp_str_release(b); sysp_str_release(a); return 0; }"
       "hi!" :valgrind t)

(check "param-len-only"
       (list '(defn lenfn ((s :string)) :int (string-len s)))
       "#include <stdio.h>
int main(){ String a = sysp_str_lit(\"abcd\", 4); int n = lenfn(a);
   printf(\"%d\\n\", n); sysp_str_release(a); return 0; }"
       "4" :valgrind t)

(check "alias-via-let"
       (list '(defn id ((s :string)) :string (let ((x s)) x)))
       "int main(){ String a=sysp_str_lit(\"hi\",2); String b=id(a);
   sysp_str_print(b); sysp_str_release(b); sysp_str_release(a); return 0; }"
       "hi" :valgrind t)

(check "alias-then-concat"
       (list '(defn dup-greet ((name :string)) :string
                (let ((copy name)) (string-concat copy "!"))))
       "int main(){ String n=sysp_str_lit(\"karan\",5); String r=dup_greet(n);
   sysp_str_print(r); sysp_str_release(r); sysp_str_release(n); return 0; }"
       "karan!" :valgrind t)

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
