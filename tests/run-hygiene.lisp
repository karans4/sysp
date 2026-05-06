;;;; State hygiene regression: compile-program is a pure function of its
;;;; input. Running it twice on the same form list must produce the same
;;;; C output, even though mono rewrites ctor heads in place internally.

(load "tests/common.lisp")
(in-package :sysp-ir)

(defun compile-twice-output (defns)
  "Returns (values first-output second-output)."
  (let* ((first-c  (with-output-to-string (s) (compile-program defns s)))
         (second-c (with-output-to-string (s) (compile-program defns s))))
    (values first-c second-c)))

(defun check-pure (label defns)
  (format t "~a:" label)
  (multiple-value-bind (a b) (compile-twice-output defns)
    (cond
      ((string= a b)
       (incf *ok*) (format t " ok (~a chars)~%" (length a)))
      (t
       (incf *fail*)
       (format t " FAIL — outputs differ across two compiles~%")))))

;; A program that exercises every state global a fresh compile would touch:
(check-pure "generic struct + lambda + multiple instantiations"
            '((defstruct (Box :T) ((value :T)))
              (defn make-box ((s :string)) (Box :string) (Box s))
              (defn use () :int (get-field (Box 5) value))
              (defn run () :string
                (let ((f (lambda ((x :int)) :int (* x 2))))
                  (let ((b (make-box (string-concat "ab" "cd"))))
                    (call f (get-field (Box 7) value))
                    (get-field b value))))))

;; Multiple poly fns + monomorphization at multiple types
(check-pure "polymorphism: id at int and string"
            '((defn id (x) x)
              (defn use-int () :int (id 42))
              (defn use-str () :string (id "hi"))))

;; Concrete struct + poly fn together
(check-pure "concrete struct + poly fn"
            '((defstruct POINT ((x :int) (y :int)))
              (defn id (x) x)
              (defn use () :int
                (let ((p (POINT 3 4)))
                  (id (get-field p x))))))

(report-and-exit)
