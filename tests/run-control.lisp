(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (program-c driver expected)
  (let ((c-file "/tmp/sysp-ir-ctl.c") (exe "/tmp/sysp-ir-ctl"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string "#include <stdio.h>" s) (terpri s)
      (write-string program-c s) (terpri s)
      (write-string driver s))
    (let ((cc (sb-ext:run-program "/usr/bin/cc" (list "-O0" "-o" exe c-file)
                                  :output t :error t)))
      (unless (zerop (sb-ext:process-exit-code cc))
        (incf *fail*) (format t " [CC FAIL]~%") (return-from cc-and-run nil)))
    (let* ((p (sb-ext:run-program exe nil :output :stream))
           (out (with-output-to-string (s)
                  (loop for l = (read-line (sb-ext:process-output p) nil nil)
                        while l do (write-line l s)))))
      (sb-ext:process-wait p)
      (let ((got (string-trim '(#\Newline #\Space) out)))
        (if (string= got expected)
            (progn (incf *ok*) (format t " ok (~a)~%" got))
            (progn (incf *fail*) (format t " FAIL got ~s want ~s~%" got expected)))))))
(defun program-c (forms) (with-output-to-string (s) (compile-program forms s)))
(defun check (label forms driver expected)
  (format t "~a:" label)
  (cc-and-run (program-c forms) driver expected))

;; early-return short-circuits
(check "early-return"
       '((defn pos-or-neg ((x :int)) :int
            (when (< x 0) (return -1))
            (when (> x 0) (return 1))
            0))
       "int main(){ printf(\"%d %d %d\\n\", pos_or_neg(-5), pos_or_neg(0), pos_or_neg(7)); return 0; }"
       "-1 0 1")

;; do-block sequentially
(check "do-sequence"
       '((defn add3 ((x :int) (y :int) (z :int)) :int
            (do (+ x y) (+ x z) (+ x (+ y z)))))
       "int main(){ printf(\"%d\\n\", add3(1, 2, 3)); return 0; }"
       "6")

;; when as side-effect-only branch in a counting loop
(check "when-side-effect"
       '((extern putchar ((c :int)) :int)
         (defn print-evens ((n :int)) :unit
            (let ((i 0))
              (while (< i n)
                (when (= (band i 1) 0)
                  (putchar (+ #x30 i)))
                (set! i (+ i 1))))))
       "int main(){ print_evens(8); putchar(10); return 0; }"
       "0246")

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
