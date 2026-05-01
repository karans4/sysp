(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (program-c driver expected)
  (let ((c-file "/tmp/sysp-ir-ext.c") (exe "/tmp/sysp-ir-ext"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
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

(defun program-c (forms)
  (with-output-to-string (s) (compile-program forms s)))

(defun check (label forms driver expected)
  (format t "~a:" label)
  (cc-and-run (program-c forms) driver expected))

;; include + use libc fn via extern. The defn calls puts and printf.
;; Note: printf is variadic — we declare just (fmt :cstr) :int and pass nothing
;; else; safe because C variadic is forgiving.
(check "puts-via-extern"
       '((include "<stdio.h>")
         (extern puts ((s :cstr)) :int)
         (defn say-hi () :int (puts (cstr "hello from sysp"))))
       "int main(){ return say_hi() < 0 ? 1 : 0; }"
       "hello from sysp")

(check "absint-libc"
       '((include "<stdlib.h>")
         (extern abs ((x :int)) :int)
         (defn neg-test () :int (abs -42)))
       "#include <stdio.h>
int main(){ printf(\"%d\\n\", neg_test()); return 0; }"
       "42")

;; Two externs called from two defns
(check "compose-libc"
       '((include "<stdlib.h>")
         (include "<string.h>")
         (extern abs ((x :int)) :int)
         (extern strlen ((s :cstr)) :size)
         (defn longest ((a :cstr) (b :cstr)) :int
            (if (> (strlen a) (strlen b)) (strlen a) (strlen b))))
       "#include <stdio.h>
int main(){ printf(\"%d\\n\", (int)longest(\"foo\", \"hello\")); return 0; }"
       "5")

;; Verify flat-syntax extern (a la old sysp `[x :int y :int]`) normalizes.
(let ((c (with-output-to-string (s)
           (compile-program '((extern flat-add (x :int y :int) :int)) s))))
  (format t "flat-params: ")
  (if (search "extern int flat_add(int x, int y);" c)
      (progn (incf *ok*) (format t "ok~%"))
      (progn (incf *fail*) (format t "FAIL: ~a~%" c))))

;; And the pair form too.
(let ((c (with-output-to-string (s)
           (compile-program '((extern pair-add ((x :int) (y :int)) :int)) s))))
  (format t "pair-params: ")
  (if (search "extern int pair_add(int x, int y);" c)
      (progn (incf *ok*) (format t "ok~%"))
      (progn (incf *fail*) (format t "FAIL: ~a~%" c))))

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
