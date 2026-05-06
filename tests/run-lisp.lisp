(load "tests/common.lisp")
(in-package :sysp-ir)

;; All these embed (defn main ...) inside the program — no driver, no
;; preamble injection (compile-program already pulls in value.h).
;;
;; runtime :value links runtime/value.c for cons/symbol primitives.

;; Simplest cons + print
(check-prog "cons-print"
            '((defn main () :int
                (val-print (cons 1 (cons 2 (cons 3 (val-nil)))))
                0))
            "" "(1 2 3)" :valgrind t :preamble "")

;; Cons w/ nested list
(check-prog "nested-cons"
            '((defn main () :int
                (val-print (cons (cons 1 (cons 2 (val-nil))) (cons 3 (val-nil))))
                0))
            "" "((1 2) 3)" :valgrind t :preamble "")

;; (list ...) sugar
(check-prog "list-sugar"
            '((defn main () :int
                (val-print (list 1 2 3 4 5))
                0))
            "" "(1 2 3 4 5)" :valgrind t :preamble "")

;; car/cdr
(check-prog "car-cdr"
            '((defn main () :int
                (let ((xs (list 10 20 30)))
                  (val-print (car xs))
                  (val-print (car (cdr xs)))
                  (val-print (car (cdr (cdr xs)))))
                0))
            "" (format nil "10~%20~%30") :valgrind t :preamble "")

;; nil?
(check-prog "nil-test"
            '((defn main () :int
                (let ((xs (list 1 2)))
                  (if (nil? xs)
                      (val-print (sym "empty"))
                      (val-print (sym "non-empty"))))
                0))
            "" "non-empty" :valgrind t :preamble "")

;; symbols
(check-prog "symbols"
            '((defn main () :int
                (let ((s (sym "hello")))
                  (val-print s)
                  (if (sym-eq? s (sym "hello"))
                      (val-print (sym "match"))
                      (val-print (sym "no-match"))))
                0))
            "" (format nil "hello~%match") :valgrind t :preamble "")

;; build a typed-form-tree-as-data (this is what macros will manipulate)
(check-prog "ast-shape"
            '((defn main () :int
                (let ((form (list (sym "if")
                                  (list (sym ">") (sym "x") 0)
                                  (list (sym "println") (sym "x"))
                                  (sym "nil"))))
                  (val-print form))
                0))
            "" "(if (> x 0) (println x) nil)" :valgrind t :preamble "")

(report-and-exit)
