;;;; Stage 16: let-polymorphism + monomorphization end-to-end.
;;;; A poly fn called with multiple types should get specialized C copies.

(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun program-c (defns)
  (with-output-to-string (s) (compile-program defns s)))

(defun cc-and-run (preamble program-c driver expected)
  (let ((c-file "/tmp/sysp-poly.c") (exe "/tmp/sysp-poly"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string preamble s) (terpri s)
      (write-string program-c s) (terpri s)
      (write-string driver s))
    (let ((cc (sb-ext:run-program "/usr/bin/cc"
                                  (list "-O0" "-Isrc" "-Iruntime" "-o" exe c-file
                                        "runtime/value.c")
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
            (progn (incf *ok*) (format t " ok~%"))
            (progn (incf *fail*) (format t " FAIL got ~s want ~s~%" got expected)))))))

(defun check-prog (label defns driver expected)
  (format t "~a:" label)
  (cc-and-run "#include \"runtime.h\"" (program-c defns) driver expected))

;; --- Identity fn used at two types ---
(check-prog "id-int-and-string"
            '((defn id (x) x)
              (defn use-int  () :int    (id 42))
              (defn use-str  () :string (id "hi")))
            "#include <stdio.h>
int main(){ printf(\"%d \", use_int());
            String s = use_str(); sysp_str_print(s); sysp_str_release(s); return 0; }"
            "42 hi")

;; --- Polymorphic fn defined and used only at one type ---
(check-prog "id-int-only"
            '((defn id (x) x)
              (defn use-int () :int (id 7)))
            "#include <stdio.h>
int main(){ printf(\"%d\\n\", use_int()); return 0; }"
            "7")

;; --- Polymorphic compose-like: poly fn that calls another poly fn ---
(check-prog "twice-int"
            '((defn id (x) x)
              (defn twice (x) (id (id x)))
              (defn use () :int (twice 10)))
            "#include <stdio.h>
int main(){ printf(\"%d\\n\", use()); return 0; }"
            "10")

;; --- Mutual recursion still infers correctly ---
(check-prog "mutual-naked-still-works"
            '((defn is-even (n) (if (= n 0) 1 (is-odd (- n 1))))
              (defn is-odd  (n) (if (= n 0) 0 (is-even (- n 1)))))
            "#include <stdio.h>
int main(){ printf(\"%d %d\\n\", is_even(8), is_odd(7)); return 0; }"
            "1 1")

;; --- Lambda with structural fn-type annotation: ret-type flows through ---
(check-prog "lambda-string-ret"
            '((defn pipe ((f (:fn (:int) :string)) (x :int)) :string (call f x))
              (defn run () :string (pipe (lambda ((x :int)) :string (string-concat "n=" "X")) 1)))
            "int main(){ String r = run(); sysp_str_print(r); sysp_str_release(r); return 0; }"
            "n=X")

;; --- Local lambda assigned to let binding, then called ---
(check-prog "local-lambda-call"
            '((defn run () :int
                (let ((f (lambda ((x :int)) :int (* x 3))))
                  (call f 7))))
            "#include <stdio.h>
int main(){ printf(\"%d\\n\", run()); return 0; }"
            "21")

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
