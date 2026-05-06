(load "tests/common.lisp")
(in-package :sysp-ir)

(check-prog "add"
            '((defn add ((x :int) (y :int)) :int (+ x y)))
            "int main(){ printf(\"%d\\n\", add(2,3)); return 0; }"
            "5")

(check-prog "let-add"
            '((defn f ((x :int)) :int
                (let ((a (+ x 1)) (b (+ x 2))) (* a b))))
            "int main(){ printf(\"%d\\n\", f(3)); return 0; }"
            "20")

(check-prog "abs-neg"
            '((defn myabs ((x :int)) :int (if (< x 0) (- 0 x) x)))
            "int main(){ printf(\"%d\\n\", myabs(-7)); return 0; }"
            "7")

(check-prog "abs-pos"
            '((defn myabs ((x :int)) :int (if (< x 0) (- 0 x) x)))
            "int main(){ printf(\"%d\\n\", myabs(7)); return 0; }"
            "7")

(check-prog "sgn-neg"
            '((defn sgn ((x :int)) :int
                (if (< x 0) (- 0 1) (if (= x 0) 0 1))))
            "int main(){ printf(\"%d\\n\", sgn(-5)); return 0; }"
            "-1")

(check-prog "sgn-zero"
            '((defn sgn ((x :int)) :int
                (if (< x 0) (- 0 1) (if (= x 0) 0 1))))
            "int main(){ printf(\"%d\\n\", sgn(0)); return 0; }"
            "0")

(check-prog "sgn-pos"
            '((defn sgn ((x :int)) :int
                (if (< x 0) (- 0 1) (if (= x 0) 0 1))))
            "int main(){ printf(\"%d\\n\", sgn(42)); return 0; }"
            "1")

(report-and-exit)
