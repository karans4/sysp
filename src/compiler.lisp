;;;; sysp-ir: surface s-exprs → ANF/basic-block IR → C
;;;; Stage 1: literals, vars, prim ops, let, if, defn. No ownership yet.

(defpackage :sysp-ir
  (:use :cl)
  (:export :compile-form :emit-c-fn :compile-and-emit))
(in-package :sysp-ir)

;;; ---------- IR datatypes ----------

(defstruct ir-fn   name params ret-type blocks)
(defstruct ir-block name params instrs term)  ; term = (:ret v) | (:ret-unit) | (:br c then-blk else-blk then-args else-args) | (:jump blk args)
(defstruct ir-instr dst type op args)         ; op ∈ :const :prim :copy :call

;;; ---------- builder state ----------

(defvar *tmp-counter*)
(defvar *blocks*)              ; list of ir-block, reverse order
(defvar *cur-instrs*)          ; list, reverse order
(defvar *cur-block-name*)
(defvar *cur-block-params*)

(defun fresh-tmp ()
  (intern (format nil "T~D" (incf *tmp-counter*))))

(defun fresh-blk (base)
  (intern (format nil "~A~D" base (incf *tmp-counter*))))

(defun emit (instr) (push instr *cur-instrs*))

(defun finish-block (term)
  (push (make-ir-block :name *cur-block-name*
                       :params *cur-block-params*
                       :instrs (nreverse *cur-instrs*)
                       :term term)
        *blocks*)
  (setf *cur-instrs* nil
        *cur-block-name* nil
        *cur-block-params* nil))

(defun start-block (name params)
  (setf *cur-block-name* name
        *cur-block-params* params
        *cur-instrs* nil))

;;; ---------- lowering ----------
;;; lower : surface-expr × env → (values value-name type)
;;; env is alist of (sym . type)

(defun lower (e env)
  (cond
    ((integerp e)
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :int :op :const :args (list e)))
       (values d :int)))
    ((eq e t)   (let ((d (fresh-tmp)))
                  (emit (make-ir-instr :dst d :type :bool :op :const :args (list 1)))
                  (values d :bool)))
    ((null e)   (let ((d (fresh-tmp)))
                  (emit (make-ir-instr :dst d :type :bool :op :const :args (list 0)))
                  (values d :bool)))
    ((symbolp e)
     (let ((b (assoc e env)))
       (unless b (error "unbound symbol: ~A" e))
       (values e (cdr b))))
    ((consp e)
     (lower-form (car e) (cdr e) env))
    (t (error "cannot lower: ~A" e))))

(defgeneric lower-form (head args env))

(defmethod lower-form ((head (eql '+)) args env) (lower-binop '+ :int args env))
(defmethod lower-form ((head (eql '-)) args env) (lower-binop '- :int args env))
(defmethod lower-form ((head (eql '*)) args env) (lower-binop '* :int args env))
(defmethod lower-form ((head (eql '/)) args env) (lower-binop '/ :int args env))
(defmethod lower-form ((head (eql '<)) args env) (lower-binop '< :bool args env))
(defmethod lower-form ((head (eql '>)) args env) (lower-binop '> :bool args env))
(defmethod lower-form ((head (eql '=)) args env) (lower-binop '== :bool args env))

(defun lower-binop (op rty args env)
  (multiple-value-bind (a _at) (lower (first args) env) (declare (ignore _at))
    (multiple-value-bind (b _bt) (lower (second args) env) (declare (ignore _bt))
      (let ((d (fresh-tmp)))
        (emit (make-ir-instr :dst d :type rty :op :prim :args (list op a b)))
        (values d rty)))))

(defmethod lower-form ((head (eql 'let)) args env)
  ;; (let ((x v) ...) body...)
  (let ((bindings (first args))
        (body (rest args))
        (env2 env))
    (dolist (b bindings)
      (multiple-value-bind (n ty) (lower (second b) env2)
        (emit (make-ir-instr :dst (first b) :type ty :op :copy :args (list n)))
        (push (cons (first b) ty) env2)))
    (let (last-n last-ty)
      (dolist (s body)
        (multiple-value-bind (n ty) (lower s env2)
          (setf last-n n last-ty ty)))
      (values last-n last-ty))))

(defmethod lower-form ((head (eql 'if)) args env)
  ;; (if c then else)
  (destructuring-bind (c-expr t-expr e-expr) args
    (multiple-value-bind (cn _ct) (lower c-expr env) (declare (ignore _ct))
      (let* ((then-blk (fresh-blk "THEN"))
             (else-blk (fresh-blk "ELSE"))
             (join-blk (fresh-blk "JOIN"))
             (result   (fresh-tmp)))
        ;; finish current with branch
        (finish-block (list :br cn then-blk else-blk nil nil))
        ;; then
        (start-block then-blk nil)
        (multiple-value-bind (tn tty) (lower t-expr env)
          (finish-block (list :jump join-blk (list tn)))
          ;; else
          (start-block else-blk nil)
          (multiple-value-bind (en _ety) (lower e-expr env) (declare (ignore _ety))
            (finish-block (list :jump join-blk (list en)))
            ;; join
            (start-block join-blk (list (list result tty)))
            (values result tty)))))))

(defmethod lower-form (head args env)
  ;; default: function call to user-defined fn
  (let ((arg-names nil) (arg-types nil))
    (dolist (a args)
      (multiple-value-bind (n ty) (lower a env)
        (push n arg-names) (push ty arg-types)))
    (let ((d (fresh-tmp))
          (rty (or (get head 'ret-type) :int))) ; default :int for now
      (emit (make-ir-instr :dst d :type rty :op :call
                           :args (cons head (nreverse arg-names))))
      (values d rty))))

;;; ---------- top-level: defn ----------

(defun compile-defn (form)
  "(defn name (params...) ret-type body...) → ir-fn"
  (destructuring-bind (_defn name params ret-type &rest body) form
    (declare (ignore _defn))
    (let ((*tmp-counter* 0)
          (*blocks* nil)
          (*cur-instrs* nil)
          (*cur-block-name* 'entry)
          (*cur-block-params* nil)
          (env (mapcar (lambda (p) (cons (first p) (second p))) params)))
      (setf (get name 'ret-type) ret-type)
      (let (last-n)
        (dolist (s body)
          (multiple-value-bind (n ty) (lower s env)
            (declare (ignore ty))
            (setf last-n n)))
        (finish-block (list :ret last-n)))
      (make-ir-fn :name name :params params :ret-type ret-type
                  :blocks (nreverse *blocks*)))))

;;; ---------- IR pretty printer ----------

(defun pp-ir (fn &optional (s t))
  (format s "(fn ~(~a~) ~a ~(~a~)~%"
          (ir-fn-name fn) (ir-fn-params fn) (ir-fn-ret-type fn))
  (dolist (b (ir-fn-blocks fn))
    (format s "  (~(~a~) ~a~%" (ir-block-name b) (ir-block-params b))
    (dolist (i (ir-block-instrs b))
      (format s "    (= ~(~a~) ~(~a~) (~(~a~)~{ ~(~a~)~}))~%"
              (ir-instr-dst i) (ir-instr-type i)
              (ir-instr-op i) (ir-instr-args i)))
    (format s "    ~(~a~))~%" (ir-block-term b)))
  (format s ")~%"))

;;; ---------- C emit ----------

(defun c-type (ty)
  (case ty (:int "int") (:bool "int") (:unit "void") (t "int")))

(defun c-name (s) (string-downcase (symbol-name s)))

(defvar *block-by-name*)

(defun emit-c-fn (fn &optional (out t))
  (let ((*block-by-name* (make-hash-table)))
    (dolist (b (ir-fn-blocks fn))
      (setf (gethash (ir-block-name b) *block-by-name*) b))
    (format out "~a ~a(" (c-type (ir-fn-ret-type fn)) (c-name (ir-fn-name fn)))
    (loop for p in (ir-fn-params fn) for first = t then nil
          do (unless first (format out ", "))
             (format out "~a ~a" (c-type (second p)) (c-name (first p))))
    (format out ") {~%")
    (dolist (b (ir-fn-blocks fn))
      (dolist (p (ir-block-params b))
        (format out "  ~a ~a;~%" (c-type (second p)) (c-name (first p)))))
    (dolist (b (ir-fn-blocks fn))
      (format out "~a:; ~%" (c-name (ir-block-name b)))
      (dolist (i (ir-block-instrs b))
        (emit-c-instr i out))
      (emit-c-term (ir-block-term b) out))
    (format out "}~%")))

(defun emit-c-instr (i out)
  (let ((dst (c-name (ir-instr-dst i)))
        (ty (c-type (ir-instr-type i))))
    (case (ir-instr-op i)
      (:const (format out "  ~a ~a = ~a;~%" ty dst (first (ir-instr-args i))))
      (:copy  (format out "  ~a ~a = ~a;~%" ty dst (c-name (first (ir-instr-args i)))))
      (:prim  (let ((a (ir-instr-args i)))
                (format out "  ~a ~a = ~a ~a ~a;~%"
                        ty dst (c-name (second a)) (first a) (c-name (third a)))))
      (:call  (format out "  ~a ~a = ~a(~{~a~^, ~});~%"
                      ty dst (c-name (first (ir-instr-args i)))
                      (mapcar #'c-name (rest (ir-instr-args i))))))))

(defun emit-c-term (term out)
  (case (first term)
    (:ret      (format out "  return ~a;~%" (c-name (second term))))
    (:ret-unit (format out "  return;~%"))
    (:br       (destructuring-bind (_ c tblk eblk _ta _ea) term
                 (declare (ignore _ _ta _ea))
                 (format out "  if (~a) goto ~a; else goto ~a;~%"
                         (c-name c) (c-name tblk) (c-name eblk))))
    (:jump     (destructuring-bind (_ blk args) term
                 (declare (ignore _))
                 (let ((dest (gethash blk *block-by-name*)))
                   (when dest
                     (loop for p in (ir-block-params dest)
                           for a in args
                           do (format out "  ~a = ~a;~%"
                                      (c-name (first p)) (c-name a)))))
                 (format out "  goto ~a;~%" (c-name blk))))))

(defun compile-and-emit (form &optional (out t))
  (emit-c-fn (compile-defn form) out))
