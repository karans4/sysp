(load "tests/common.lisp")
(in-package :sysp-ir)

(check-prog "count-down"
            '((defn count-down ((n :int)) :int
                (while (> n 0) (set! n (- n 1)))
                n))
            "int main(){ printf(\"%d\\n\", count_down(7)); return 0; }"
            "0")

(check-prog "factorial"
            '((defn fact ((n :int)) :int
                (let ((acc 1))
                  (while (> n 0)
                    (set! acc (* acc n))
                    (set! n (- n 1)))
                  acc)))
            "int main(){ printf(\"%d\\n\", fact(5)); return 0; }"
            "120")

(check-prog "sum-to-n"
            '((defn sum ((n :int)) :int
                (let ((acc 0)
                      (i 1))
                  (while (< i (+ n 1))
                    (set! acc (+ acc i))
                    (set! i (+ i 1)))
                  acc)))
            "int main(){ printf(\"%d\\n\", sum(10)); return 0; }"
            "55")

(check-prog "nested-loops"
            '((defn rect-sum ((rows :int) (cols :int)) :int
                (let ((sum 0)
                      (r 0))
                  (while (< r rows)
                    (let ((c 0))
                      (while (< c cols)
                        (set! sum (+ sum 1))
                        (set! c (+ c 1))))
                    (set! r (+ r 1)))
                  sum)))
            "int main(){ printf(\"%d\\n\", rect_sum(4, 5)); return 0; }"
            "20")

(check-prog "loop-with-if"
            '((defn count-evens-to ((n :int)) :int
                (let ((count 0)
                      (i 0))
                  (while (< i n)
                    (set! count (+ count (if (= (- i (* (/ i 2) 2)) 0) 1 0)))
                    (set! i (+ i 1)))
                  count)))
            "int main(){ printf(\"%d\\n\", count_evens_to(10)); return 0; }"
            "5")

(report-and-exit)
