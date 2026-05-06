(load "tests/common.lisp")
(in-package :sysp-ir)

;; bitwise via named forms
(check-prog "band-bor"
            '((defn f ((x :int) (y :int)) :int (bor (band x y) (bxor x y))))
            "int main(){ printf(\"%d\\n\", f(0xc, 0xa)); return 0; }"
            "14")

(check-prog "shifts"
            '((defn shl ((x :int) (n :int)) :int (bshl x n))
              (defn shr ((x :int) (n :int)) :int (bshr x n)))
            "int main(){ printf(\"%d %d\\n\", shl(1, 8), shr(256, 4)); return 0; }"
            "256 16")

(check-prog "bnot"
            '((defn f ((x :int)) :int (band (bnot x) #xff)))
            "int main(){ printf(\"%d\\n\", f(0x0f)); return 0; }"
            "240")

;; u8 storage roundtrip
(check-prog "u8-arg"
            '((defn add1u8 ((x :u8)) :u8 (band (+ x 1) #xff)))
            "int main(){ printf(\"%d\\n\", add1u8(254)); return 0; }"
            "255")

;; comparison via named forms
(check-prog "compares"
            '((defn lt ((x :int) (y :int)) :int (if (< x y) 1 0))
              (defn ne ((x :int) (y :int)) :int (if (!= x y) 1 0)))
            "int main(){ printf(\"%d %d\\n\", lt(3, 5), ne(7, 7)); return 0; }"
            "1 0")

(report-and-exit)
