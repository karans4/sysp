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
    ((floatp e)
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :float :op :const :args (list e)))
       (values d :float)))
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
       (cond
         (b (values e (cdr b)))
         ((gethash e *globals*)
          (values e (first (gethash e *globals*))))
         (t (error "unbound symbol: ~A" e)))))
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

;;; --- Lisp data: cons / Value / symbols ---

(defun box-as-value (name ty)
  "Emit IR that converts (name, ty) to a :Value tmp. Returns the new dst.
   Pass-through if already :Value. nil/false → val_nil()."
  (cond
    ((eq ty :Value) name)
    ((eq ty :symbol)
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :Value :op :call
                            :args (list 'val_sym name)))
       d))
    ((eq ty :int)
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :Value :op :call
                            :args (list 'val_int name)))
       d))
    ((eq ty :float)
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :Value :op :call
                            :args (list 'val_float name)))
       d))
    ((eq ty :bool)
     ;; bool nil (false) → val_nil(); true → val_int(1).
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :Value :op :call
                            :args (list 'val_int name)))
       d))
    (t (error "cannot box type ~A as Value" ty))))

(defun lower-and-box (expr env)
  "Lower expr, then box the result to :Value. Returns the boxed name."
  (multiple-value-bind (n ty) (lower expr env)
    (box-as-value n ty)))

(defun lower-value-arg (expr env)
  "Lower an arg that must end up as :Value. Special-cases:
   - literal nil → val_nil()  (CL's nil is also our empty list)
   - everything else: lower then auto-box."
  (cond
    ((null expr)
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :Value :op :call
                            :args (list 'val_nil)))
       d))
    (t (lower-and-box expr env))))

(defmethod lower-form ((head (eql 'cons)) args env)
  (let ((a (lower-value-arg (first args) env))
        (b (lower-value-arg (second args) env))
        (d (fresh-tmp)))
    (emit (make-ir-instr :dst d :type :Value :op :call
                         :args (list 'val_cons a b)))
    (values d :Value)))

(defmethod lower-form ((head (eql 'car)) args env)
  (multiple-value-bind (n _) (lower (first args) env) (declare (ignore _))
    (let ((d (fresh-tmp)))
      (emit (make-ir-instr :dst d :type :Value :op :call
                           :args (list 'val_car n)))
      (values d :Value))))

(defmethod lower-form ((head (eql 'cdr)) args env)
  (multiple-value-bind (n _) (lower (first args) env) (declare (ignore _))
    (let ((d (fresh-tmp)))
      (emit (make-ir-instr :dst d :type :Value :op :call
                           :args (list 'val_cdr n)))
      (values d :Value))))

(defmethod lower-form ((head (eql 'nil?)) args env)
  (multiple-value-bind (n _) (lower (first args) env) (declare (ignore _))
    (let ((d (fresh-tmp)))
      (emit (make-ir-instr :dst d :type :bool :op :call
                           :args (list 'is_nil n)))
      (values d :bool))))

(defmethod lower-form ((head (eql 'list)) args env)
  ;; (list a b c) → (cons a (cons b (cons c nil)))
  (lower (build-list-form args) env))

(defun build-list-form (args)
  (if (null args)
      'nil
      (list 'cons (first args) (build-list-form (rest args)))))

(defmethod lower-form ((head (eql 'sym)) args env)
  (declare (ignore env))
  ;; (sym name-string) → val_sym(intern_sym("name"))
  (let ((s (first args)))
    (unless (stringp s) (error "sym expects a string literal, got ~A" s))
    (let ((cs (fresh-tmp)) (id (fresh-tmp)) (d (fresh-tmp)))
      (emit (make-ir-instr :dst cs :type :cstr :op :cstr-lit :args (list s)))
      (emit (make-ir-instr :dst id :type :symbol :op :call
                           :args (list 'intern_sym cs)))
      (emit (make-ir-instr :dst d :type :Value :op :call
                           :args (list 'val_sym id)))
      (values d :Value))))

(defmethod lower-form ((head (eql 'sym-eq?)) args env)
  (let ((a (lower-and-box (first args) env))
        (b (lower-and-box (second args) env))
        (d (fresh-tmp)))
    (emit (make-ir-instr :dst d :type :bool :op :call
                         :args (list 'sym_eq a b)))
    (values d :bool)))

(defmethod lower-form ((head (eql 'val-nil)) args env)
  (declare (ignore args env))
  (let ((d (fresh-tmp)))
    (emit (make-ir-instr :dst d :type :Value :op :call
                         :args (list 'val_nil)))
    (values d :Value)))

(defmethod lower-form ((head (eql 'val-print)) args env)
  ;; Print a Value as s-expr followed by newline.
  (let ((n (lower-value-arg (first args) env)))
    (emit (make-ir-instr :dst nil :type :unit :op :call
                         :args (list 'val_println n)))
    (values nil :unit)))

(defmethod lower-form ((head (eql 'cstr)) args env)
  ;; (cstr "literal") → const char*. No allocation, no rc.
  (declare (ignore env))
  (let ((s (first args)))
    (unless (stringp s) (error "cstr expects a string literal, got ~A" s))
    (let ((d (fresh-tmp)))
      (emit (make-ir-instr :dst d :type :cstr :op :cstr-lit :args (list s)))
      (values d :cstr))))

(defun ptr-of (inner-type)
  (intern (format nil "PTR-~A" (symbol-name inner-type)) :keyword))

(defun ptr-inner (ty)
  "Strip the :ptr- prefix or unwrap (:ptr T)."
  (cond
    ((and (consp ty) (eq (first ty) :ptr)) (second ty))
    ((eq ty :ptr-void) :u8)   ; treat void* as opaque byte ptr for deref purposes
    ((and (keywordp ty)
          (let ((s (symbol-name ty)))
            (and (> (length s) 4) (string-equal s "PTR-" :end1 4))))
     (intern (subseq (symbol-name ty) 4) :keyword))
    (t (error "not a pointer type: ~A" ty))))

(defmethod lower-form ((head (eql 'addr-of)) args env)
  (let* ((sym (first args))
         (b (assoc sym env)))
    (unless b (error "addr-of: unbound ~A" sym))
    (let ((d (fresh-tmp))
          (pty (ptr-of (cdr b))))
      (emit (make-ir-instr :dst d :type pty :op :addr-of :args (list sym)))
      (values d pty))))

(defmethod lower-form ((head (eql 'cast)) args env)
  (let* ((target-ty (first args))
         (val-expr (second args)))
    (multiple-value-bind (vn _vty) (lower val-expr env)
      (declare (ignore _vty))
      (let ((d (fresh-tmp)))
        (emit (make-ir-instr :dst d :type target-ty :op :cast
                             :args (list target-ty vn)))
        (values d target-ty)))))

(defmethod lower-form ((head (eql 'deref)) args env)
  (multiple-value-bind (pn pty) (lower (first args) env)
    (let ((inner (ptr-inner pty))
          (d (fresh-tmp)))
      (emit (make-ir-instr :dst d :type inner :op :deref :args (list pn)))
      (values d inner))))

(defmethod lower-form ((head (eql 'ptr-ref)) args env)
  ;; (ptr-ref p i) → p[i]
  (multiple-value-bind (pn pty) (lower (first args) env)
    (multiple-value-bind (in _) (lower (second args) env) (declare (ignore _))
      (let ((inner (ptr-inner pty))
            (d (fresh-tmp)))
        (emit (make-ir-instr :dst d :type inner :op :ptr-ref :args (list pn in)))
        (values d inner)))))

(defmethod lower-form ((head (eql 'ptr-set!)) args env)
  ;; (ptr-set! p val) → *p = val;
  (multiple-value-bind (pn _pty) (lower (first args) env) (declare (ignore _pty))
    (multiple-value-bind (vn _vty) (lower (second args) env) (declare (ignore _vty))
      (emit (make-ir-instr :dst nil :type :unit :op :ptr-set :args (list pn vn)))
      (values nil :unit))))

(defmethod lower-form ((head (eql 'ptr-set-at!)) args env)
  ;; (ptr-set-at! p i val) → p[i] = val;
  (multiple-value-bind (pn _pty) (lower (first args) env) (declare (ignore _pty))
    (multiple-value-bind (in _ity) (lower (second args) env) (declare (ignore _ity))
      (multiple-value-bind (vn _vty) (lower (third args) env) (declare (ignore _vty))
        (emit (make-ir-instr :dst nil :type :unit :op :ptr-set-at
                             :args (list pn in vn)))
        (values nil :unit)))))

(defmethod lower-form ((head (eql 'set!)) args env)
  ;; (set! target expr) — re-assign. Currently int-only.
  (let ((target (first args)))
    (multiple-value-bind (vn vty) (lower (second args) env)
      (emit (make-ir-instr :dst nil :type vty :op :set
                           :args (list target vn)))
      (values target vty))))

(defmethod lower-form ((head (eql 'do)) args env)
  ;; (do e1 e2 ... eN) — sequential, value is eN.
  (let (last-n last-ty)
    (dolist (e args)
      (multiple-value-bind (n ty) (lower e env)
        (setf last-n n last-ty ty)))
    (values last-n last-ty)))

(defmethod lower-form ((head (eql 'when)) args env)
  ;; (when cond body...) — branch with no value; result is :unit.
  (let* ((cond-expr (first args))
         (body-forms (rest args))
         (then-blk (fresh-blk "WTHEN"))
         (else-blk (fresh-blk "WELSE"))
         (cont-blk (fresh-blk "WCONT")))
    (multiple-value-bind (cn _) (lower cond-expr env) (declare (ignore _))
      (finish-block (list :br cn then-blk else-blk cont-blk nil nil)))
    (start-block then-blk nil)
    (dolist (e body-forms) (lower e env))
    (finish-block (list :jump cont-blk nil))
    (start-block else-blk nil)
    (finish-block (list :jump cont-blk nil))
    (start-block cont-blk nil)
    (values nil :unit)))

(defmethod lower-form ((head (eql 'return)) args env)
  ;; Early return. Finishes current block with :ret; subsequent code in
  ;; the same lexical position continues in a fresh (likely-dead) block.
  (multiple-value-bind (vn _) (lower (first args) env) (declare (ignore _))
    (finish-block (list :ret vn))
    (start-block (fresh-blk "AFTER-RET") nil)
    (values vn :unit)))

;;; --- syntactic sugar lowered as macros (re-call lower) ---

(defmethod lower-form ((head (eql 'for)) args env)
  ;; (for (var lo hi) body...) — bracket form (var lo hi) after parser collapse.
  (let* ((spec (first args))
         (var (first spec))
         (lo  (second spec))
         (hi  (third spec))
         (body (rest args)))
    (lower `(let ((,var ,lo))
              (while (< ,var ,hi)
                ,@body
                (set! ,var (+ ,var 1))))
           env)))

(defmethod lower-form ((head (eql 'cond)) args env)
  ;; (cond [c1 b1] [c2 b2] [else b]) — each arm parses as (c b).
  ;; Expand to nested if.
  (let ((arms args))
    (lower (cond-expand arms) env)))

(defun cond-expand (arms)
  (cond
    ((null arms) 0)
    ((let ((c (first (first arms))))
       (or (eq c (intern "ELSE" :sysp-ir))
           (eq c 'else)))
     (second (first arms)))
    (t `(if ,(first (first arms))
            ,(second (first arms))
            ,(cond-expand (rest arms))))))

(defmethod lower-form ((head (eql 'and)) args env)
  (cond
    ((null args)         (lower 1 env))
    ((null (rest args))  (lower (first args) env))
    (t (lower `(if ,(first args)
                   (and ,@(rest args))
                   0)
              env))))

(defmethod lower-form ((head (eql 'or)) args env)
  (cond
    ((null args)         (lower 0 env))
    ((null (rest args))  (lower (first args) env))
    (t (let ((tmp (gensym "ORTMP")))
         (lower `(let ((,tmp ,(first args)))
                   (if ,tmp ,tmp (or ,@(rest args))))
                env)))))

(defmethod lower-form ((head (eql 'not)) args env)
  (lower `(if ,(first args) 0 1) env))

;;; --- array sugar: alias to ptr ops ---

(defmethod lower-form ((head (eql 'nth)) args env)
  (lower `(ptr-ref ,(first args) ,(second args)) env))

(defmethod lower-form ((head (eql 'array-set!)) args env)
  (lower `(ptr-set-at! ,(first args) ,(second args) ,(third args)) env))

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

(defun struct-or-ptr-target (ty)
  "If ty is a struct or pointer-to-struct, return (values struct-ty is-ptr-p).
   Else error."
  (cond
    ((struct-type-p ty) (values ty nil))
    ((and (keywordp ty)
          (let ((s (symbol-name ty)))
            (and (> (length s) 4) (string-equal s "PTR-" :end1 4))))
     (let ((inner (intern (subseq (symbol-name ty) 4) :keyword)))
       (if (struct-type-p inner)
           (values inner t)
           (error "field access on non-struct pointer ~A" ty))))
    (t (error "field access on non-struct type ~A" ty))))

(defmethod lower-form ((head (eql 'get-field)) args env)
  (multiple-value-bind (obj-name obj-ty) (lower (first args) env)
    (multiple-value-bind (struct-ty is-ptr) (struct-or-ptr-target obj-ty)
      (let* ((field-sym (second args))
             (field-ty (struct-field-type struct-ty field-sym))
             (d (fresh-tmp)))
        (emit (make-ir-instr :dst d :type field-ty
                             :op (if is-ptr :field-get-ptr :field-get)
                             :args (list obj-name field-sym)))
        (values d field-ty)))))

(defmethod lower-form ((head (eql 'set-field!)) args env)
  (multiple-value-bind (obj-name obj-ty) (lower (first args) env)
    (multiple-value-bind (_struct-ty is-ptr) (struct-or-ptr-target obj-ty)
      (declare (ignore _struct-ty))
      (multiple-value-bind (val-name _vt) (lower (third args) env) (declare (ignore _vt))
        (let ((field-sym (second args)))
          (emit (make-ir-instr :dst nil :type :unit
                               :op (if is-ptr :field-set-ptr :field-set)
                               :args (list obj-name field-sym val-name)))
          (values nil :unit))))))

(defmethod lower-form (head args env)
  ;; default: struct constructor OR call to user/extern fn.
  (cond
    ((struct-name-p head)
     ;; Struct constructor: (Name v1 v2 ...) → struct literal.
     (let ((arg-names nil))
       (dolist (a args)
         (multiple-value-bind (n _ty) (lower a env)
           (declare (ignore _ty))
           (push n arg-names)))
       (let ((d (fresh-tmp))
             (sty (struct-type-keyword head)))
         (emit (make-ir-instr :dst d :type sty :op :struct-init
                              :args (cons head (nreverse arg-names))))
         (values d sty))))
    (t
     (let ((arg-names nil))
       (dolist (a args)
         (multiple-value-bind (n _ty) (lower a env)
           (declare (ignore _ty))
           (push n arg-names)))
       (let ((d (fresh-tmp))
             (rty (or (get head 'ret-type) :int)))
         (emit (make-ir-instr :dst d :type rty :op :call
                              :args (cons head (nreverse arg-names))))
         (values d rty))))))

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
        (if (eq ret-type :unit)
            (finish-block (list :ret-unit))
            (finish-block (list :ret last-n))))
      (make-ir-fn :name name :params params :ret-type ret-type
                  :blocks (nreverse *blocks*)))))
