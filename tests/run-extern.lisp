(load "tests/common.lisp")
(in-package :sysp-ir)

;; include + use libc fn via extern. The defn calls puts and printf.
(check-prog "puts-via-extern"
            '((include "<stdio.h>")
              (extern puts ((s :cstr)) :int)
              (defn say-hi () :int (puts (cstr "hello from sysp"))))
            "int main(){ return say_hi() < 0 ? 1 : 0; }"
            "hello from sysp")

(check-prog "absint-libc"
            '((include "<stdlib.h>")
              (extern abs ((x :int)) :int)
              (defn neg-test () :int (abs -42)))
            "int main(){ printf(\"%d\\n\", neg_test()); return 0; }"
            "42")

;; Two externs called from two defns
(check-prog "compose-libc"
            '((include "<stdlib.h>")
              (include "<string.h>")
              (extern abs ((x :int)) :int)
              (extern strlen ((s :cstr)) :size)
              (defn longest ((a :cstr) (b :cstr)) :int
                (if (> (strlen a) (strlen b)) (strlen a) (strlen b))))
            "int main(){ printf(\"%d\\n\", (int)longest(\"foo\", \"hello\")); return 0; }"
            "5")

;; Verify both extern param shapes (flat / pairs) compile + register.
(handler-case
    (progn
      (compile-program '((extern flat-add (x :int y :int) :int))
                       (make-broadcast-stream))
      (incf *ok*) (format t "flat-params: ok~%"))
  (error (e) (incf *fail*) (format t "flat-params: FAIL ~a~%" e)))

(handler-case
    (progn
      (compile-program '((extern pair-add ((x :int) (y :int)) :int))
                       (make-broadcast-stream))
      (incf *ok*) (format t "pair-params: ok~%"))
  (error (e) (incf *fail*) (format t "pair-params: FAIL ~a~%" e)))

(report-and-exit)
