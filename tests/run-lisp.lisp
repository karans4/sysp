(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (program-c driver expected &key valgrind)
  (let ((c-file "/tmp/sysp-ir-lisp.c") (exe "/tmp/sysp-ir-lisp"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string program-c s) (terpri s)
      (write-string driver s))
    (let ((cc (sb-ext:run-program "/usr/bin/cc"
                  (list "-O0" "-Iruntime" "-o" exe c-file
                        "runtime/value.c")
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
            (progn (incf *ok*) (format t " ok (~a)" got))
            (progn (incf *fail*) (format t " FAIL got ~s want ~s" got expected)))))
    (when valgrind
      (let ((p (sb-ext:run-program "/usr/bin/valgrind"
                  (list "--error-exitcode=2" "--leak-check=full" "-q" exe)
                  :output nil :error nil)))
        (sb-ext:process-wait p)
        (if (zerop (sb-ext:process-exit-code p))
            (format t " (vg clean)")
            (progn (incf *fail*) (format t " VG FAIL")))))
    (terpri)))

(defun program-c (forms) (with-output-to-string (s) (compile-program forms s)))
(defun check (label forms driver expected &key valgrind)
  (format t "~a:" label)
  (cc-and-run (program-c forms) driver expected :valgrind valgrind))

;; Simplest cons + print
(check "cons-print"
       '((defn main () :int
            (val-print (cons 1 (cons 2 (cons 3 (val-nil)))))
            0))
       "" "(1 2 3)" :valgrind t)

;; Cons w/ nested list
(check "nested-cons"
       '((defn main () :int
            (val-print (cons (cons 1 (cons 2 (val-nil))) (cons 3 (val-nil))))
            0))
       "" "((1 2) 3)" :valgrind t)

;; (list ...) sugar
(check "list-sugar"
       '((defn main () :int
            (val-print (list 1 2 3 4 5))
            0))
       "" "(1 2 3 4 5)" :valgrind t)

;; car/cdr
(check "car-cdr"
       '((defn main () :int
            (let ((xs (list 10 20 30)))
              (val-print (car xs))
              (val-print (car (cdr xs)))
              (val-print (car (cdr (cdr xs)))))
            0))
       "" (format nil "10~%20~%30") :valgrind t)

;; nil?
(check "nil-test"
       '((defn main () :int
            (let ((xs (list 1 2)))
              (if (nil? xs)
                  (val-print (sym "empty"))
                  (val-print (sym "non-empty"))))
            0))
       "" "non-empty" :valgrind t)

;; symbols
(check "symbols"
       '((defn main () :int
            (let ((s (sym "hello")))
              (val-print s)
              (if (sym-eq? s (sym "hello"))
                  (val-print (sym "match"))
                  (val-print (sym "no-match"))))
            0))
       "" (format nil "hello~%match") :valgrind t)

;; build a typed-form-tree-as-data (this is what macros will manipulate)
(check "ast-shape"
       '((defn main () :int
            (let ((form (list (sym "if")
                              (list (sym ">") (sym "x") 0)
                              (list (sym "println") (sym "x"))
                              (sym "nil"))))
              (val-print form))
            0))
       "" "(if (> x 0) (println x) nil)" :valgrind t)

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
