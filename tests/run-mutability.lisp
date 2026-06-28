;;;; Mutability axis (SPEC §9.2): `mut` field parsing + deep-immutability.
(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0)
(defvar *fail* 0)

(defun check (label got want)
  (cond ((equal got want) (incf *ok*) (format t "~a: ok~%" label))
        (t (incf *fail*) (format t "~a: FAIL (got ~s want ~s)~%" label got want))))

(defun register (name raw)
  "Register a struct under NAME (symbol) with raw field specs."
  (setf (gethash name *struct-fields*) (normalize-struct-fields raw)))

;;; --- `mut` parsing ---

(let ((fs (normalize-struct-fields '((a :int) (mut b :int)))))
  (check "parse-immutable-field" (field-mut-p (first fs)) nil)
  (check "parse-mut-field"       (field-mut-p (second fs)) t)
  (check "parse-keeps-name"      (first (second fs)) 'b)
  (check "parse-keeps-type"      (second (second fs)) :int))

;;; --- deep-immutability over a fresh registry ---

(clrhash *struct-fields*)
(register 'POINT   '((x :int) (y :int)))
(register 'COUNTER '((mut n :int)))
(register 'LINE    '((a :POINT) (b :POINT)))          ; immutable struct of immutables
(register 'WRAP    '((c :COUNTER)))                   ; transitively holds a mut field
(register 'HOLDER  '((s :string)))                    ; String is immutable
(register 'NODE    '((val :Value)))                   ; Value (Cons) is immutable

(check "prim-int-immutable"      (deeply-immutable-p :int)     t)
(check "ptr-immutable"           (deeply-immutable-p :ptr-void) t)
(check "string-immutable"        (deeply-immutable-p :string)  t)
(check "value-immutable"         (deeply-immutable-p :Value)   t)
(check "plain-struct-immutable"  (deeply-immutable-p :POINT)   t)
(check "mut-field-struct-mutable"     (deeply-immutable-p :COUNTER) nil)
(check "nested-immutable"        (deeply-immutable-p :LINE)    t)
(check "transitive-mutable"      (deeply-immutable-p :WRAP)    nil)
(check "string-field-immutable"  (deeply-immutable-p :HOLDER)  t)
(check "value-field-immutable"   (deeply-immutable-p :NODE)    t)

(check "mutable-type-p complement" (mutable-type-p :COUNTER) t)
(check "mutable-type-p immutable"  (mutable-type-p :POINT)   nil)

;;; --- enforcement: mutating a non-mut field is rejected ---

(defun rejects-p (forms)
  (handler-case (progn (compile-program forms (make-broadcast-stream)) nil)
    (error () t)))

(check "reject-immutable-field-set"
       (rejects-p '((defstruct PT ((x :int)))
                    (defn f ((p :PT)) :unit (set-field! p x 9))))
       t)
(check "allow-mut-field-set"
       (rejects-p '((defstruct PT ((mut x :int)))
                    (defn f ((p :PT)) :unit (set-field! p x 9))))
       nil)

(format t "~%~d passed, ~d failed~%" *ok* *fail*)
(sb-ext:exit :code (if (zerop *fail*) 0 1))
