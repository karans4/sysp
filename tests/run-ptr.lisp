(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (program-c driver expected)
  (let ((c-file "/tmp/sysp-ir-ptr.c") (exe "/tmp/sysp-ir-ptr"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string "#include <stdint.h>" s) (terpri s)
      (write-string "#include <stdio.h>" s) (terpri s)
      (write-string "#include <stdlib.h>" s) (terpri s)
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

;; addr-of + deref via a helper that reads through a pointer
(check "addr-deref"
       '((defn read-via-ptr ((p :ptr-int)) :int (deref p)))
       "int main(){ int x = 42; printf(\"%d\\n\", read_via_ptr(&x)); return 0; }"
       "42")

;; ptr-ref (array indexing)
(check "ptr-ref"
       '((extern malloc ((n :size)) :ptr-void)
         (extern free ((p :ptr-void)) :unit)
         (defn array-third () :int
            (let ((arr (cast :ptr-int (malloc (cast :size 32)))))
              (ptr-set-at! arr 0 10)
              (ptr-set-at! arr 1 20)
              (ptr-set-at! arr 2 30)
              (ptr-set-at! arr 3 40)
              (let ((v (ptr-ref arr 2)))
                (free (cast :ptr-void arr))
                v))))
       "int main(){ printf(\"%d\\n\", array_third()); return 0; }"
       "30")

;; cast int to u8 on assign to u8 storage (via ptr)
(check "cast-narrow"
       '((extern malloc ((n :size)) :ptr-void)
         (extern free ((p :ptr-void)) :unit)
         (defn store-byte () :int
            (let ((mem (cast :ptr-u8 (malloc (cast :size 16)))))
              (ptr-set-at! mem 0 (cast :u8 (band #xff #xab)))
              (let ((b (ptr-ref mem 0)))
                (free (cast :ptr-void mem))
                b))))
       "int main(){ printf(\"%d\\n\", store_byte()); return 0; }"
       "171")

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
