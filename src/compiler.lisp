;;;; sysp-ir: surface s-exprs → ANF/basic-block IR → C
;;;; Stage 1: literals, vars, prim ops, let, if, defn. No ownership yet.

(defpackage :sysp-ir
  (:use :cl)
  (:export :compile-form :emit-c-fn :compile-and-emit))
(in-package :sysp-ir)

;;; ---------- IR datatypes ----------

(defstruct ir-fn   name params ret-type blocks)
(defstruct ir-block name params instrs term)  ; term = (:ret v) | (:ret-unit) | (:br c then-blk else-blk then-args else-args) | (:jump blk args)
(defstruct ir-instr dst type op args)         ; op ∈ :const :prim :copy :call :str-lit :release :retain

;; Reference-counted types. Extend as we add more.
(defun ref-type-p (ty) (eq ty :string))

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
(defmethod lower-form ((head (eql '<)) args env) (lower-binop '< :bool args env))
(defmethod lower-form ((head (eql '>)) args env) (lower-binop '> :bool args env))
(defmethod lower-form ((head (eql '=)) args env) (lower-binop '== :bool args env))

(defmethod lower-form ((head (eql 'string-concat)) args env)
  (lower-rt-call 'sysp_str_concat :string args env))
(defmethod lower-form ((head (eql 'string-len)) args env)
  (lower-rt-call 'sysp_str_len :int args env))
(defmethod lower-form ((head (eql 'string-print)) args env)
  (lower-rt-call 'sysp_str_print :unit args env))

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
      (insert-releases
       (make-ir-fn :name name :params params :ret-type ret-type
                   :blocks (nreverse *blocks*))))))

;;; ---------- ownership / release-insertion pass ----------
;;; v0: per-block, no cross-block flow. Straight-line code only.
;;; Each ref-typed binding (param or local) gets released after its last use.
;;; Exception: if the value flows into a :ret terminator, ownership transfers.

(defun instr-uses (i)
  "Return list of var-symbols this instruction uses (reads)."
  (case (ir-instr-op i)
    (:const   nil)
    (:str-lit nil)
    (:copy    (list (first (ir-instr-args i))))
    (:prim    (rest (ir-instr-args i)))      ; (op a b) → uses a,b
    (:call    (rest (ir-instr-args i)))      ; (cfn a b ...) → uses args
    (:release (ir-instr-args i))
    (:retain  (ir-instr-args i))))

(defun term-uses (term)
  (case (first term)
    (:ret  (list (second term)))
    (:br   (list (second term)))
    (:jump (third term))
    (t     nil)))

(defun term-transfers (term)
  "Variables whose ownership transfers out of the function (no release needed)."
  (case (first term)
    (:ret  (list (second term)))
    (t     nil)))

(defun insert-releases-block (blk fn-params)
  "Walk block forward; track ref-typed live bindings + their types; at last
   use, append a :release. Bindings that flow into term-transfers are skipped."
  (let* ((instrs (ir-block-instrs blk))
         (term   (ir-block-term blk))
         ;; Collect all ref-typed bindings: params (for entry block) + locals.
         (ref-vars (make-hash-table))         ; sym → type
         ;; Add fn params if this is the entry block
         (is-entry (eq (ir-block-name blk) 'entry)))
    (when is-entry
      (dolist (p fn-params)
        (when (ref-type-p (second p))
          (setf (gethash (first p) ref-vars) (second p)))))
    ;; Add ref-typed defs from instrs.
    (dolist (i instrs)
      (when (ref-type-p (ir-instr-type i))
        (setf (gethash (ir-instr-dst i) ref-vars) (ir-instr-type i))))
    ;; Find last-use of each ref var by walking forward and remembering.
    (let ((last-use (make-hash-table)))      ; sym → instr-index (-1 = term)
      (loop for idx from 0
            for i in instrs
            do (dolist (u (instr-uses i))
                 (when (gethash u ref-vars)
                   (setf (gethash u last-use) idx))))
      (dolist (u (term-uses term))
        (when (gethash u ref-vars)
          (setf (gethash u last-use) :term)))
      ;; Bindings transferred by term: drop from release set.
      (dolist (u (term-transfers term))
        (remhash u last-use))
      ;; Now build new instr list: walk forward, after each instr at index k,
      ;; emit release for every var whose last-use is k AND not transferred.
      (let ((new-instrs nil))
        (loop for idx from 0
              for i in instrs
              do (push i new-instrs)
                 (maphash (lambda (v k)
                            (when (and (numberp k) (= k idx))
                              (push (make-ir-instr :dst nil :type (gethash v ref-vars)
                                                   :op :release :args (list v))
                                    new-instrs)))
                          last-use))
        ;; Also: ref-typed bindings that have NO uses at all (dead on arrival),
        ;; including unused fn params — release immediately at top of block.
        ;; For simplicity: if not in last-use AND not transferred, release at end of block (before term).
        (maphash (lambda (v ty)
                   (declare (ignore ty))
                   (unless (or (gethash v last-use)
                               (member v (term-transfers term)))
                     (push (make-ir-instr :dst nil :type (gethash v ref-vars)
                                          :op :release :args (list v))
                           new-instrs)))
                 ref-vars)
        ;; Special case: if last-use is :term but NOT transferred (e.g. used in
        ;; a branch condition), release before the term.
        (maphash (lambda (v k)
                   (when (and (eq k :term)
                              (not (member v (term-transfers term))))
                     (push (make-ir-instr :dst nil :type (gethash v ref-vars)
                                          :op :release :args (list v))
                           new-instrs)))
                 last-use)
        (setf (ir-block-instrs blk) (nreverse new-instrs))))))

(defun insert-releases (fn)
  (dolist (b (ir-fn-blocks fn))
    (insert-releases-block b (ir-fn-params fn)))
  fn)

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
  (case ty (:int "int") (:bool "int") (:unit "void") (:string "String") (t "int")))

(defun c-escape-string (s)
  (with-output-to-string (out)
    (loop for ch across s do
      (case ch
        (#\\ (write-string "\\\\" out))
        (#\" (write-string "\\\"" out))
        (#\Newline (write-string "\\n" out))
        (#\Tab (write-string "\\t" out))
        (t (write-char ch out))))))

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
      (:call  (if (eq (ir-instr-type i) :unit)
                  (format out "  ~a(~{~a~^, ~});~%"
                          (c-name (first (ir-instr-args i)))
                          (mapcar #'c-name (rest (ir-instr-args i))))
                  (format out "  ~a ~a = ~a(~{~a~^, ~});~%"
                          ty dst (c-name (first (ir-instr-args i)))
                          (mapcar #'c-name (rest (ir-instr-args i))))))
      (:str-lit (let ((s (first (ir-instr-args i))))
                  (format out "  String ~a = sysp_str_lit(\"~a\", ~d);~%"
                          dst (c-escape-string s) (length s))))
      (:release (format out "  sysp_str_release(~a);~%"
                        (c-name (first (ir-instr-args i)))))
      (:retain  (format out "  sysp_str_retain(~a);~%"
                        (c-name (first (ir-instr-args i))))))))

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
