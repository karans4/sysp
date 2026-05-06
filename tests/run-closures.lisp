(load "tests/common.lisp")
(in-package :sysp-ir)

;; All exit-code tests — sysp main IS the C main; no driver needed.
(defparameter +driver+ "")

;; Non-capturing
(check-prog "lambda-no-capture"
            '((defn main () :int
                (let ((f (lambda ((x :int)) :int (+ x 1))))
                  (call f 9))))
            +driver+ 10 :mode :exit)

;; Single capture
(check-prog "lambda-1-capture"
            '((defn main () :int
                (let ((n 100))
                  (let ((adder (lambda ((x :int)) :int (+ x n))))
                    (call adder 7)))))
            +driver+ 107 :mode :exit)

;; Multiple captures
(check-prog "lambda-2-captures"
            '((defn main () :int
                (let ((a 3) (b 4))
                  (let ((f (lambda ((x :int)) :int (+ (* a x) b))))
                    (call f 10)))))
            +driver+ 34 :mode :exit)

;; Pass closure as argument
(check-prog "hof"
            '((defn apply-fn ((f :Fn) (x :int)) :int (call f x))
              (defn main () :int
                (let ((m 5))
                  (let ((times-m (lambda ((x :int)) :int (* x m))))
                    (apply-fn times-m 8)))))
            +driver+ 40 :mode :exit)

;; Two closures over different captures, used independently
(check-prog "two-closures"
            '((defn main () :int
                (let ((a (let ((n1 10))
                           (lambda ((x :int)) :int (+ x n1))))
                      (b (let ((n2 20))
                           (lambda ((x :int)) :int (+ x n2)))))
                  (+ (call a 1) (call b 1)))))
            +driver+ 32 :mode :exit)

;; rc'd capture: lambda captures a String. Without retain at capture +
;; release on Fn cleanup, the captured buf would be freed by the outer
;; fn's ARC pass before the lambda runs (UAF), or leak forever. Lambda
;; body returns string-len(captured) — UAF would crash or return junk;
;; correct behavior returns the actual length.
(check-prog "lambda-captures-string"
            '((defn make-len-of ((prefix :string)) (:fn () :int)
                (lambda () :int (string-len prefix)))
              (defn main () :int
                (let ((s (string-concat "hello" "_world")))
                  (let ((f (make-len-of s)))
                    (call f)))))
            +driver+ 11 :mode :exit)

(report-and-exit)
