(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (program-c driver expected)
  (let ((c-file "/tmp/sysp-ir-bits.c") (exe "/tmp/sysp-ir-bits"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string "#include <stdint.h>" s) (terpri s)
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

(defun program-c (defns)
  (with-output-to-string (s) (compile-program defns s)))

(defun check (label defns driver expected)
  (format t "~a:" label)
  (cc-and-run (program-c defns) driver expected))

;; bitwise via named forms
(check "band-bor"
       '((defn f ((x :int) (y :int)) :int (bor (band x y) (bxor x y))))
       "int main(){ printf(\"%d\\n\", f(0xc, 0xa)); return 0; }"
       "14")

(check "shifts"
       '((defn shl ((x :int) (n :int)) :int (bshl x n))
         (defn shr ((x :int) (n :int)) :int (bshr x n)))
       "int main(){ printf(\"%d %d\\n\", shl(1, 8), shr(256, 4)); return 0; }"
       "256 16")

(check "bnot"
       '((defn f ((x :int)) :int (band (bnot x) #xff)))
       "int main(){ printf(\"%d\\n\", f(0x0f)); return 0; }"
       "240")

;; u8 storage roundtrip
(check "u8-arg"
       '((defn add1u8 ((x :u8)) :u8 (band (+ x 1) #xff)))
       "int main(){ printf(\"%d\\n\", add1u8(254)); return 0; }"
       "255")

;; comparison via named forms
(check "compares"
       '((defn lt ((x :int) (y :int)) :int (if (< x y) 1 0))
         (defn ne ((x :int) (y :int)) :int (if (!= x y) 1 0)))
       "int main(){ printf(\"%d %d\\n\", lt(3, 5), ne(7, 7)); return 0; }"
       "1 0")

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
