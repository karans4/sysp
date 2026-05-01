;;;; Surface s-exprs → raw IR (no passes yet).
;;;; lower / lower-form methods + builder state.

(in-package :sysp-ir)

;;; Builder state — shared across one defn lowering.

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
    ((stringp e)
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :string :op :str-lit :args (list e)))
       (values d :string)))
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
(defmethod lower-form ((head (eql '%)) args env) (lower-binop '% :int args env))

;; Bitwise — emit C operators directly. Same shape as arithmetic.
;; Both symbol and named forms supported (band == &, etc.).
(defmethod lower-form ((head (eql '&))    args env) (lower-binop "&"  :int args env))
(defmethod lower-form ((head (eql '\|))   args env) (lower-binop "|"  :int args env))
(defmethod lower-form ((head (eql '^))    args env) (lower-binop "^"  :int args env))
(defmethod lower-form ((head (eql '<<))   args env) (lower-binop "<<" :int args env))
(defmethod lower-form ((head (eql '>>))   args env) (lower-binop ">>" :int args env))
(defmethod lower-form ((head (eql 'band)) args env) (lower-binop "&"  :int args env))
(defmethod lower-form ((head (eql 'bor))  args env) (lower-binop "|"  :int args env))
(defmethod lower-form ((head (eql 'bxor)) args env) (lower-binop "^"  :int args env))
(defmethod lower-form ((head (eql 'bshl)) args env) (lower-binop "<<" :int args env))
(defmethod lower-form ((head (eql 'bshr)) args env) (lower-binop ">>" :int args env))
(defmethod lower-form ((head (eql 'bnot)) args env)
  (multiple-value-bind (a _) (lower (first args) env) (declare (ignore _))
    (let ((d (fresh-tmp)))
      (emit (make-ir-instr :dst d :type :int :op :unary
                           :args (list "~" a)))
      (values d :int))))

(defmethod lower-form ((head (eql '<))  args env) (lower-binop '< :bool args env))
(defmethod lower-form ((head (eql '>))  args env) (lower-binop '> :bool args env))
(defmethod lower-form ((head (eql '<=)) args env) (lower-binop "<=" :bool args env))
(defmethod lower-form ((head (eql '>=)) args env) (lower-binop ">=" :bool args env))
(defmethod lower-form ((head (eql '=))  args env) (lower-binop '== :bool args env))
(defmethod lower-form ((head (eql '!=)) args env) (lower-binop "!=" :bool args env))

(defmethod lower-form ((head (eql 'string-concat)) args env)
  (lower-rt-call 'sysp_str_concat :string args env))
(defmethod lower-form ((head (eql 'string-len)) args env)
  (lower-rt-call 'sysp_str_len :int args env))
(defmethod lower-form ((head (eql 'string-print)) args env)
  (lower-rt-call 'sysp_str_print :unit args env))

(defmethod lower-form ((head (eql 'set!)) args env)
  ;; (set! target expr) — re-assign. Currently int-only.
  (let ((target (first args)))
    (multiple-value-bind (vn vty) (lower (second args) env)
      (emit (make-ir-instr :dst nil :type vty :op :set
                           :args (list target vn)))
      (values target vty))))

(defmethod lower-form ((head (eql 'while)) args env)
  ;; (while cond body...) — body is a sequence; while returns unit.
  (let* ((cond-expr (first args))
         (body-forms (rest args))
         (header-blk (fresh-blk "WHILE"))
         (body-blk   (fresh-blk "BODY"))
         (exit-blk   (fresh-blk "EXIT")))
    (finish-block (list :jump header-blk nil))
    (start-block header-blk nil)
    (multiple-value-bind (cn _) (lower cond-expr env)
      (declare (ignore _))
      (finish-block (list :loop cn body-blk exit-blk)))
    (start-block body-blk nil)
    (dolist (s body-forms) (lower s env))
    (finish-block (list :jump header-blk nil))
    (start-block exit-blk nil)
    (values nil :unit)))

(defun lower-rt-call (cfn rty args env)
  (let ((arg-names nil))
    (dolist (a args)
      (multiple-value-bind (n _) (lower a env) (declare (ignore _))
        (push n arg-names)))
    (let ((d (fresh-tmp)))
      (emit (make-ir-instr :dst d :type rty :op :call
                           :args (cons cfn (nreverse arg-names))))
      (values d rty))))

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
  ;; :br shape: (:br cond then-blk else-blk join-blk then-deaths else-deaths)
  (destructuring-bind (c-expr t-expr e-expr) args
    (multiple-value-bind (cn _ct) (lower c-expr env) (declare (ignore _ct))
      (let* ((then-blk (fresh-blk "THEN"))
             (else-blk (fresh-blk "ELSE"))
             (join-blk (fresh-blk "JOIN"))
             (result   (fresh-tmp)))
        (finish-block (list :br cn then-blk else-blk join-blk nil nil))
        (start-block then-blk nil)
        (multiple-value-bind (tn tty) (lower t-expr env)
          (finish-block (list :jump join-blk (list tn)))
          (start-block else-blk nil)
          (multiple-value-bind (en _ety) (lower e-expr env) (declare (ignore _ety))
            (finish-block (list :jump join-blk (list en)))
            (start-block join-blk (list (list result tty)))
            (values result tty)))))))

(defmethod lower-form (head args env)
  ;; default: call to user-defined fn (or unknown — uses (get head 'ret-type)).
  (let ((arg-names nil))
    (dolist (a args)
      (multiple-value-bind (n _ty) (lower a env)
        (declare (ignore _ty))
        (push n arg-names)))
    (let ((d (fresh-tmp))
          (rty (or (get head 'ret-type) :int)))
      (emit (make-ir-instr :dst d :type rty :op :call
                           :args (cons head (nreverse arg-names))))
      (values d rty))))

(defun lower-defn (form)
  "Build the raw IR for one (defn ...) form. No optimization passes — those
   are run by compile-defn in the top-level driver."
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
