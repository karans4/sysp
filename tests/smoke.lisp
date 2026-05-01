(load "src/compiler.lisp")
(in-package :sysp-ir)

(defun test (label form)
  (format t "~%;; --- ~a ---~%" label)
  (format t ";; surface: ~s~%" form)
  (let ((fn (compile-defn form)))
    (format t ";; IR:~%")
    (pp-ir fn)
    (format t ";; C:~%")
    (emit-c-fn fn)))

(test "add"
      '(defn add ((x :int) (y :int)) :int (+ x y)))

(test "let-add"
      '(defn f ((x :int)) :int
         (let ((a (+ x 1))
               (b (+ x 2)))
           (* a b))))

(test "if"
      '(defn abs ((x :int)) :int
         (if (< x 0) (- 0 x) x)))

(test "nested-if"
      '(defn sgn ((x :int)) :int
         (if (< x 0) (- 0 1)
             (if (= x 0) 0 1))))
