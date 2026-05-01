(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun compile-form-to-c (form)
  (with-output-to-string (s) (emit-c-fn (compile-defn form) s)))

(defun cc-and-run (preamble fns driver expected &key dump)
  (let ((c-file "/tmp/sysp-ir-loop.c") (exe "/tmp/sysp-ir-loop"))
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
            (progn (incf *ok*) (format t " ok (~a)~%" got))
            (progn (incf *fail*) (format t " FAIL: got ~s want ~s~%" got expected)))))))

(defun check (label fn-forms driver expected &key dump)
  (format t "~a:" label)
  (cc-and-run "#include \"runtime.h\"" (mapcar #'compile-form-to-c fn-forms)
              driver expected :dump dump))

(check "count-down"
       (list '(defn count-down ((n :int)) :int
                (while (> n 0) (set! n (- n 1)))
                n))
       "#include <stdio.h>
int main(){ printf(\"%d\\n\", count_down(7)); return 0; }"
       "0")

(check "factorial"
       (list '(defn fact ((n :int)) :int
                (let ((acc 1))
                  (while (> n 0)
                    (set! acc (* acc n))
                    (set! n (- n 1)))
                  acc)))
       "#include <stdio.h>
int main(){ printf(\"%d\\n\", fact(5)); return 0; }"
       "120")

(check "sum-to-n"
       (list '(defn sum ((n :int)) :int
                (let ((acc 0)
                      (i 1))
                  (while (< i (+ n 1))
                    (set! acc (+ acc i))
                    (set! i (+ i 1)))
                  acc)))
       "#include <stdio.h>
int main(){ printf(\"%d\\n\", sum(10)); return 0; }"
       "55")

(check "nested-loops"
       (list '(defn rect-sum ((rows :int) (cols :int)) :int
                (let ((sum 0)
                      (r 0))
                  (while (< r rows)
                    (let ((c 0))
                      (while (< c cols)
                        (set! sum (+ sum 1))
                        (set! c (+ c 1))))
                    (set! r (+ r 1)))
                  sum)))
       "#include <stdio.h>
int main(){ printf(\"%d\\n\", rect_sum(4, 5)); return 0; }"
       "20")

(check "loop-with-if"
       (list '(defn count-evens-to ((n :int)) :int
                (let ((count 0)
                      (i 0))
                  (while (< i n)
                    (if (= (- i (* (/ i 2) 2)) 0)
                        (set! count (+ count 1))
                        0)
                    (set! i (+ i 1)))
                  count)))
       "#include <stdio.h>
int main(){ printf(\"%d\\n\", count_evens_to(10)); return 0; }"
       "5")

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
