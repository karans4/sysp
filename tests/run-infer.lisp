(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (preamble program-c driver expected &key valgrind)
  (let ((c-file "/tmp/sysp-ir-inf.c") (exe "/tmp/sysp-ir-inf"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string preamble s) (terpri s)
      (write-string program-c s) (terpri s)
      (write-string driver s))
    (let ((cc (sb-ext:run-program "/usr/bin/cc" (list "-O0" "-Isrc" "-o" exe c-file)
                                  :output t :error t)))
      (unless (zerop (sb-ext:process-exit-code cc))
        (incf *fail*) (format t " [CC FAIL]~%") (return-from cc-and-run nil)))
    (let* ((p (sb-ext:run-program exe nil :output :stream))
           (out (with-output-to-string (s)
                  (loop for line = (read-line (sb-ext:process-output p) nil nil)
                        while line do (write-line line s)))))
      (sb-ext:process-wait p)
      (let ((got (string-trim '(#\Newline #\Space) out)))
        (if (string= got expected)
            (progn (incf *ok*) (format t " ok"))
            (progn (incf *fail*) (format t " FAIL got ~s want ~s" got expected)))))
    (when valgrind
      (let ((p (sb-ext:run-program "/usr/bin/valgrind"
                                   (list "--error-exitcode=2" "--leak-check=full" "-q" exe)
                                   :output nil :error nil)))
        (sb-ext:process-wait p)
        (if (zerop (sb-ext:process-exit-code p))
            (format t " (vg clean)~%")
            (progn (incf *fail*) (format t " VG FAIL~%")))))
    (terpri)))

(defun program-c (defns)
  (with-output-to-string (s) (compile-program defns s)))

(defun check-prog (label defns driver expected &key valgrind)
  (format t "~a:" label)
  (cc-and-run "#include \"runtime.h\"" (program-c defns) driver expected :valgrind valgrind))

;; --- Naked params, no annotations ---
(check-prog "naked-add"
            '((defn add (x y) (+ x y)))
            "#include <stdio.h>
int main(){ printf(\"%d\\n\", add(3, 4)); return 0; }"
            "7")

(check-prog "naked-fact"
            '((defn fact (n) (if (= n 0) 1 (* n (fact (- n 1))))))
            "#include <stdio.h>
int main(){ printf(\"%d\\n\", fact(5)); return 0; }"
            "120")

;; --- String params inferred from string-concat usage ---
(check-prog "infer-string-shout"
            '((defn shout (s) (string-concat s "!")))
            "int main(){
  String a = sysp_str_lit(\"hi\", 2); String b = shout(a);
  sysp_str_print(b); sysp_str_release(b); sysp_str_release(a); return 0;}"
            "hi!" :valgrind t)

;; --- Mixed: some annotations, others inferred ---
(check-prog "mixed-annot"
            '((defn linear (x (m :int) (b :int)) (+ (* m x) b)))
            "#include <stdio.h>
int main(){ printf(\"%d\\n\", linear(3, 2, 5)); return 0; }"
            "11")

;; --- Mutual recursion with no annotations ---
(check-prog "mutual-naked"
            '((defn is-even (n) (if (= n 0) 1 (is-odd (- n 1))))
              (defn is-odd  (n) (if (= n 0) 0 (is-even (- n 1)))))
            "#include <stdio.h>
int main(){ printf(\"%d %d\\n\", is_even(8), is_odd(7)); return 0; }"
            "1 1")

;; --- while-loop body with naked params ---
(check-prog "naked-count-down"
            '((defn count-down (n)
                (while (> n 0) (set! n (- n 1)))
                n))
            "#include <stdio.h>
int main(){ printf(\"%d\\n\", count_down(7)); return 0; }"
            "0")

;; --- String composition with naked params, multi-fn ---
(check-prog "infer-multifn-string"
            '((defn make-greeting (name) (string-concat "hello " name))
              (defn loud (name) (string-concat (make-greeting name) "!")))
            "int main(){
  String n = sysp_str_lit(\"karan\", 5); String r = loud(n);
  sysp_str_print(r); sysp_str_release(r); sysp_str_release(n); return 0;}"
            "hello karan!" :valgrind t)

;; --- Type error: should fail at infer ---
(format t "~%Negative test: type-error catch~%")
(handler-case
    (progn
      (compile-program '((defn bad ((x :int)) (string-concat x "!"))))
      (incf *fail*) (format t "  FAIL: should have errored~%"))
  (error (e)
    (incf *ok*)
    (format t "  ok (got error: ~A)~%" (subseq (format nil "~A" e) 0 (min 60 (length (format nil "~A" e)))))))

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
