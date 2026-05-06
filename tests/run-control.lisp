(load "tests/common.lisp")
(in-package :sysp-ir)

;; early-return short-circuits
(check-prog "early-return"
            '((defn pos-or-neg ((x :int)) :int
                (when (< x 0) (return -1))
                (when (> x 0) (return 1))
                0))
            "int main(){ printf(\"%d %d %d\\n\", pos_or_neg(-5), pos_or_neg(0), pos_or_neg(7)); return 0; }"
            "-1 0 1")

;; do-block sequentially
(check-prog "do-sequence"
            '((defn add3 ((x :int) (y :int) (z :int)) :int
                (do (+ x y) (+ x z) (+ x (+ y z)))))
            "int main(){ printf(\"%d\\n\", add3(1, 2, 3)); return 0; }"
            "6")

;; when as side-effect-only branch in a counting loop
(check-prog "when-side-effect"
            '((extern putchar ((c :int)) :int)
              (defn print-evens ((n :int)) :unit
                (let ((i 0))
                  (while (< i n)
                    (when (= (band i 1) 0)
                      (putchar (+ #x30 i)))
                    (set! i (+ i 1))))))
            "int main(){ print_evens(8); putchar(10); return 0; }"
            "0246")

(report-and-exit)
