(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0)
(defvar *fail* 0)

(defun compile-form-to-c (form)
  (with-output-to-string (s) (emit-c-fn (compile-defn form) s)))

(defun cc-and-run (c-src driver expected)
  (let ((c-file "/tmp/sysp-ir-test.c")
        (exe    "/tmp/sysp-ir-test"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string c-src s)
      (write-string driver s))
    (let ((ret (sb-ext:run-program "/usr/bin/cc"
                                   (list "-O0" "-o" exe c-file)
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
            (progn (incf *fail*) (format t " FAIL: got ~s, want ~s~%" got expected)))))))

(defun check (label form driver expected)
  (format t "~a:" label)
  (cc-and-run (compile-form-to-c form) driver expected))

(check "add"
       '(defn add ((x :int) (y :int)) :int (+ x y))
       (format nil "~%#include <stdio.h>~%int main(){printf(\"%d\\n\",add(2,3));return 0;}~%")
       "5")

(check "let-add"
       '(defn f ((x :int)) :int
         (let ((a (+ x 1)) (b (+ x 2))) (* a b)))
       (format nil "~%#include <stdio.h>~%int main(){printf(\"%d\\n\",f(3));return 0;}~%")
       "20")

(check "abs-neg"
       '(defn myabs ((x :int)) :int (if (< x 0) (- 0 x) x))
       (format nil "~%#include <stdio.h>~%int main(){printf(\"%d\\n\",myabs(-7));return 0;}~%")
       "7")

(check "abs-pos"
       '(defn myabs ((x :int)) :int (if (< x 0) (- 0 x) x))
       (format nil "~%#include <stdio.h>~%int main(){printf(\"%d\\n\",myabs(7));return 0;}~%")
       "7")

(check "sgn-neg"
       '(defn sgn ((x :int)) :int
         (if (< x 0) (- 0 1) (if (= x 0) 0 1)))
       (format nil "~%#include <stdio.h>~%int main(){printf(\"%d\\n\",sgn(-5));return 0;}~%")
       "-1")

(check "sgn-zero"
       '(defn sgn ((x :int)) :int
         (if (< x 0) (- 0 1) (if (= x 0) 0 1)))
       (format nil "~%#include <stdio.h>~%int main(){printf(\"%d\\n\",sgn(0));return 0;}~%")
       "0")

(check "sgn-pos"
       '(defn sgn ((x :int)) :int
         (if (< x 0) (- 0 1) (if (= x 0) 0 1)))
       (format nil "~%#include <stdio.h>~%int main(){printf(\"%d\\n\",sgn(42));return 0;}~%")
       "1")

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
