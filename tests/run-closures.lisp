(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (program-c expected)
  (let ((c-file "/tmp/sysp-ir-cl.c") (exe "/tmp/sysp-ir-cl"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string program-c s) (terpri s))
    (let ((cc (sb-ext:run-program "/usr/bin/cc"
                  (list "-O0" "-Iruntime" "-o" exe c-file "runtime/value.c")
                  :output t :error t)))
      (unless (zerop (sb-ext:process-exit-code cc))
        (incf *fail*) (format t " [CC FAIL]~%") (return-from cc-and-run nil)))
    (let ((p (sb-ext:run-program exe nil :output nil)))
      (sb-ext:process-wait p)
      (let ((got (sb-ext:process-exit-code p)))
        (if (= got expected)
            (progn (incf *ok*) (format t " ok (exit ~a)~%" got))
            (progn (incf *fail*) (format t " FAIL exit ~a want ~a~%" got expected)))))))

(defun program-c (forms) (with-output-to-string (s) (compile-program forms s)))
(defun check (label forms expected)
  (format t "~a:" label)
  (cc-and-run (program-c forms) expected))

;; Non-capturing
(check "lambda-no-capture"
       '((defn main () :int
            (let ((f (lambda ((x :int)) :int (+ x 1))))
              (call f 9))))
       10)

;; Single capture
(check "lambda-1-capture"
       '((defn main () :int
            (let ((n 100))
              (let ((adder (lambda ((x :int)) :int (+ x n))))
                (call adder 7)))))
       107)

;; Multiple captures
(check "lambda-2-captures"
       '((defn main () :int
            (let ((a 3) (b 4))
              (let ((f (lambda ((x :int)) :int (+ (* a x) b))))
                (call f 10)))))
       34)

;; Pass closure as argument
(check "hof"
       '((defn apply-fn ((f :Fn) (x :int)) :int (call f x))
         (defn main () :int
            (let ((m 5))
              (let ((times-m (lambda ((x :int)) :int (* x m))))
                (apply-fn times-m 8)))))
       40)

;; Two closures over different captures, used independently
(check "two-closures"
       '((defn main () :int
            (let ((a (let ((n1 10))
                       (lambda ((x :int)) :int (+ x n1))))
                  (b (let ((n2 20))
                       (lambda ((x :int)) :int (+ x n2)))))
              (+ (call a 1) (call b 1)))))
       32)

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
