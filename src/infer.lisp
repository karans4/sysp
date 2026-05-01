;;;; Hindley-Milner type inference (monomorphic).
;;;;
;;;; Surface form (possibly with naked params / no ret-type) → fully-annotated
;;;; form ready for lower-defn. Nothing below this layer needs to change.
;;;;
;;;; Type language:
;;;;   :int :bool :unit :string                         -- concrete
;;;;   (:fn (T1 T2 ...) Tret)                           -- function type
;;;;   (:tvar N)                                        -- type variable

(in-package :sysp-ir)

(defvar *subst*)          ; hash table: tvar id → type
(defvar *tvar-counter*)
(defvar *fn-sigs*)        ; sym → (:fn arg-types ret-type)

(defun fresh-tvar ()
  (list :tvar (incf *tvar-counter*)))

(defun tvar-p (ty) (and (consp ty) (eq (first ty) :tvar)))

(defun resolve-type (ty)
  "Follow tvar chain to a (possibly partially) concrete type."
  (cond
    ((tvar-p ty)
     (let ((sub (gethash (second ty) *subst*)))
       (if sub (resolve-type sub) ty)))
    ((and (consp ty) (eq (first ty) :fn))
     (list :fn (mapcar #'resolve-type (second ty)) (resolve-type (third ty))))
    (t ty)))

(defun unify (t1 t2)
  (let ((r1 (resolve-type t1)) (r2 (resolve-type t2)))
    (cond
      ((equal r1 r2) t)
      ((tvar-p r1) (setf (gethash (second r1) *subst*) r2))
      ((tvar-p r2) (setf (gethash (second r2) *subst*) r1))
      ;; numeric ↔ numeric: silently accept; C handles all width/float
      ;; promotions and narrowing implicitly.
      ((and (numeric-type-p r1) (numeric-type-p r2)) t)
      ;; :unit unifies with anything — value is discarded at C level.
      ((or (eq r1 :unit) (eq r2 :unit)) t)
      ((and (consp r1) (consp r2)
            (eq (first r1) :fn) (eq (first r2) :fn))
       (unless (= (length (second r1)) (length (second r2)))
         (error "infer: arity mismatch ~A vs ~A" r1 r2))
       (mapc #'unify (second r1) (second r2))
       (unify (third r1) (third r2)))
      (t (error "infer: type mismatch ~A vs ~A" r1 r2)))))

;;; --- inference walk ---

(defun infer (e env)
  (cond
    ((integerp e) :int)
    ((floatp e)   :float)
    ((stringp e)  :string)
    ((eq e t)     :bool)
    ((null e)     :bool)
    ((symbolp e)
     (let ((b (assoc e env)))
       (cond
         (b (cdr b))
         ((gethash e *globals*) (first (gethash e *globals*)))
         (t (error "infer: unbound symbol ~A" e)))))
    ((consp e) (infer-form (car e) (cdr e) env))
    (t (error "infer: cannot type ~A" e))))

(defgeneric infer-form (head args env))

(defparameter *int-types* '(:int :bool :u8 :u16 :u32 :u64 :i8 :i16 :i32 :i64 :size))
(defun int-type-p (ty) (member (if (consp ty) ty ty) *int-types*))
(defun float-type-p (ty) (member ty '(:float :double)))
(defun numeric-type-p (ty) (or (int-type-p ty) (float-type-p ty)))

(defmethod infer-form ((head (eql '+)) args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql '-)) args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql '*)) args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql '/)) args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql '%)) args env) (infer-int-arith args env))

(defmethod infer-form ((head (eql '&))    args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql '\|))   args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql '^))    args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql '<<))   args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql '>>))   args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql 'band)) args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql 'bor))  args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql 'bxor)) args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql 'bshl)) args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql 'bshr)) args env) (infer-int-arith args env))
(defmethod infer-form ((head (eql 'bnot)) args env)
  (let ((ty (resolve-type (infer (first args) env))))
    (cond ((int-type-p ty) ty)
          ((tvar-p ty) (unify ty :int) :int)
          (t (error "bnot expects int, got ~A" ty)))))

(defmethod infer-form ((head (eql '<))  args env) (infer-int-cmp args env))
(defmethod infer-form ((head (eql '>))  args env) (infer-int-cmp args env))
(defmethod infer-form ((head (eql '<=)) args env) (infer-int-cmp args env))
(defmethod infer-form ((head (eql '>=)) args env) (infer-int-cmp args env))

(defmethod infer-form ((head (eql '=))  args env)
  (unify (infer (first args) env) (infer (second args) env))
  :bool)
(defmethod infer-form ((head (eql '!=)) args env)
  (unify (infer (first args) env) (infer (second args) env))
  :bool)

(defun ensure-numeric-typed (a env)
  (let ((ty (resolve-type (infer a env))))
    (cond
      ((numeric-type-p ty) ty)
      ((tvar-p ty) (unify ty :int) :int)
      (t (error "expected number, got ~A" ty)))))

(defun ensure-int-typed (a env)
  (let ((ty (resolve-type (infer a env))))
    (cond
      ((int-type-p ty) ty)
      ((tvar-p ty) (unify ty :int) :int)
      (t (error "expected int type, got ~A" ty)))))

(defun infer-int-arith (args env)
  "Args may be any number; result is :float if any arg is float, else :int."
  (let ((any-float nil))
    (dolist (a args)
      (let ((ty (ensure-numeric-typed a env)))
        (when (float-type-p ty) (setf any-float t))))
    (if any-float :float :int)))

(defun infer-int-cmp (args env)
  (dolist (a args) (ensure-numeric-typed a env))
  :bool)

(defmethod infer-form ((head (eql 'string-concat)) args env)
  (dolist (a args) (unify :string (infer a env)))
  :string)
(defmethod infer-form ((head (eql 'string-len)) args env)
  (unify :string (infer (first args) env))
  :int)
(defmethod infer-form ((head (eql 'string-print)) args env)
  (unify :string (infer (first args) env))
  :unit)

(defmethod infer-form ((head (eql 'cstr)) args env)
  (declare (ignore env))
  (unless (stringp (first args)) (error "cstr expects a string literal"))
  :cstr)

;; Lisp data: cons / car / cdr / nil? / list / sym / sym-eq? / val-nil / val-print
(defmethod infer-form ((head (eql 'cons)) args env)
  (infer (first args) env)
  (infer (second args) env)
  :Value)
(defmethod infer-form ((head (eql 'car)) args env)
  (infer (first args) env) :Value)
(defmethod infer-form ((head (eql 'cdr)) args env)
  (infer (first args) env) :Value)
(defmethod infer-form ((head (eql 'nil?)) args env)
  (infer (first args) env) :bool)
(defmethod infer-form ((head (eql 'list)) args env)
  (dolist (a args) (infer a env)) :Value)
(defmethod infer-form ((head (eql 'sym)) args env)
  (declare (ignore env))
  (unless (stringp (first args)) (error "sym expects a string literal")) :Value)
(defmethod infer-form ((head (eql 'sym-eq?)) args env)
  (infer (first args) env)
  (infer (second args) env) :bool)
(defmethod infer-form ((head (eql 'val-nil)) args env)
  (declare (ignore args env)) :Value)
(defmethod infer-form ((head (eql 'val-print)) args env)
  (infer (first args) env) :unit)

(defmethod infer-form ((head (eql 'addr-of)) args env)
  (let* ((sym (first args))
         (b (assoc sym env)))
    (unless b (error "addr-of: unbound ~A" sym))
    (let ((inner (resolve-type (cdr b))))
      (intern (format nil "PTR-~A" (symbol-name inner)) :keyword))))

(defmethod infer-form ((head (eql 'cast)) args env)
  (infer (second args) env)   ; type-check the expr but discard its type
  (first args))               ; result type is the cast target

(defmethod infer-form ((head (eql 'deref)) args env)
  (let ((pty (resolve-type (infer (first args) env))))
    (cond
      ((and (keywordp pty)
            (let ((s (symbol-name pty)))
              (and (> (length s) 4) (string-equal s "PTR-" :end1 4))))
       (intern (subseq (symbol-name pty) 4) :keyword))
      ((eq pty :ptr-void) :u8)
      (t (error "deref: expected pointer, got ~A" pty)))))

(defmethod infer-form ((head (eql 'ptr-ref)) args env)
  (let ((pty (resolve-type (infer (first args) env))))
    (ensure-int-typed (second args) env)
    (cond
      ((and (keywordp pty)
            (let ((s (symbol-name pty)))
              (and (> (length s) 4) (string-equal s "PTR-" :end1 4))))
       (intern (subseq (symbol-name pty) 4) :keyword))
      (t :int))))

(defmethod infer-form ((head (eql 'ptr-set!)) args env)
  (infer (first args) env)
  (infer (second args) env)
  :unit)

(defmethod infer-form ((head (eql 'ptr-set-at!)) args env)
  (infer (first args) env)
  (ensure-int-typed (second args) env)
  (infer (third args) env)
  :unit)

(defmethod infer-form ((head (eql 'let)) args env)
  (let* ((bindings (first args))
         (body (rest args))
         (env2 env))
    (dolist (b bindings)
      (let ((ty (infer (second b) env2)))
        (push (cons (first b) ty) env2)))
    (let (last-ty)
      (dolist (s body) (setf last-ty (infer s env2)))
      last-ty)))

(defmethod infer-form ((head (eql 'if)) args env)
  (unify (infer (first args) env) :bool)
  (let ((t-ty (infer (second args) env))
        (e-ty (infer (third args) env)))
    (unify t-ty e-ty)
    t-ty))

(defmethod infer-form ((head (eql 'set!)) args env)
  (let* ((target (first args))
         (tgt-ty (cdr (assoc target env))))
    (unless tgt-ty (error "infer: set! on unbound ~A" target))
    (unify tgt-ty (infer (second args) env))
    :unit))

(defmethod infer-form ((head (eql 'do)) args env)
  (let (last-ty)
    (dolist (e args) (setf last-ty (infer e env)))
    last-ty))

(defmethod infer-form ((head (eql 'when)) args env)
  (unify (infer (first args) env) :bool)
  (dolist (b (rest args)) (infer b env))
  :unit)

(defmethod infer-form ((head (eql 'return)) args env)
  ;; Treat return as :unit-typed; the inferred type of the body up to the
  ;; return is what the fn signature must match. We don't have full sig
  ;; visibility here, so just type-check the value and report :unit.
  (infer (first args) env)
  :unit)

;;; --- sugar passes (mirror lower's macros so types resolve) ---

(defmethod infer-form ((head (eql 'for)) args env)
  (let* ((spec (first args))
         (var (first spec)) (lo (second spec)) (hi (third spec))
         (body (rest args)))
    (infer `(let ((,var ,lo))
              (while (< ,var ,hi)
                ,@body
                (set! ,var (+ ,var 1))))
           env)))

(defmethod infer-form ((head (eql 'cond)) args env)
  (infer (cond-expand args) env))

(defmethod infer-form ((head (eql 'and)) args env)
  (cond
    ((null args)        :int)
    ((null (rest args)) (infer (first args) env))
    (t (infer `(if ,(first args) (and ,@(rest args)) 0) env))))

(defmethod infer-form ((head (eql 'or)) args env)
  (cond
    ((null args)        :int)
    ((null (rest args)) (infer (first args) env))
    (t (let ((tmp (gensym "ORTMP")))
         (infer `(let ((,tmp ,(first args)))
                   (if ,tmp ,tmp (or ,@(rest args))))
                env)))))

(defmethod infer-form ((head (eql 'not)) args env)
  (infer `(if ,(first args) 0 1) env))

(defmethod infer-form ((head (eql 'nth)) args env)
  (infer `(ptr-ref ,(first args) ,(second args)) env))

(defmethod infer-form ((head (eql 'array-set!)) args env)
  (infer `(ptr-set-at! ,(first args) ,(second args) ,(third args)) env))

(defmethod infer-form ((head (eql 'while)) args env)
  (unify (infer (first args) env) :bool)
  (dolist (b (rest args)) (infer b env))
  :unit)

(defun resolve-struct-or-ptr (obj-ty)
  "Strip one level of pointer if present and the inner is a struct.
   Returns the struct type."
  (cond
    ((struct-type-p obj-ty) obj-ty)
    ((and (keywordp obj-ty)
          (let ((s (symbol-name obj-ty)))
            (and (> (length s) 4) (string-equal s "PTR-" :end1 4))))
     (let ((inner (intern (subseq (symbol-name obj-ty) 4) :keyword)))
       (when (struct-type-p inner) inner)))))

(defmethod infer-form ((head (eql 'get-field)) args env)
  (let* ((obj-ty (resolve-type (infer (first args) env)))
         (field-sym (second args))
         (struct-ty (resolve-struct-or-ptr obj-ty)))
    (unless struct-ty
      (error "get-field: ~A is not a struct or struct pointer, got ~A"
             (first args) obj-ty))
    (struct-field-type struct-ty field-sym)))

(defmethod infer-form ((head (eql 'set-field!)) args env)
  (let* ((obj-ty (resolve-type (infer (first args) env)))
         (field-sym (second args))
         (val-ty (infer (third args) env))
         (struct-ty (resolve-struct-or-ptr obj-ty)))
    (unless struct-ty
      (error "set-field!: ~A is not a struct or struct pointer, got ~A"
             (first args) obj-ty))
    (let ((field-ty (struct-field-type struct-ty field-sym)))
      (unify field-ty val-ty)
      :unit)))

(defmethod infer-form (head args env)
  ;; Default: struct constructor OR function call.
  (cond
    ((struct-name-p head)
     ;; Struct constructor: types must match field types.
     (let ((fields (gethash head *struct-fields*)))
       (unless (= (length fields) (length args))
         (error "struct ~A: expected ~D fields, got ~D"
                head (length fields) (length args)))
       (loop for a in args for f in fields
             do (unify (second f) (infer a env)))
       (struct-type-keyword head)))
    (t
     (let ((sig (and *fn-sigs* (gethash head *fn-sigs*))))
       (unless sig
         (error "infer: unknown function ~A" head))
       (let ((arg-tys (second sig))
             (ret-ty  (third sig)))
         (unless (= (length arg-tys) (length args))
           (error "infer: ~A expects ~D args, got ~D"
                  head (length arg-tys) (length args)))
         (loop for a in args for at in arg-tys
               do (unify at (infer a env)))
         ret-ty)))))

;;; --- defn / program drivers ---

(defun type-annotation-p (x)
  "Heuristic: distinguish a type form from a body form. Types are keywords
   like :int, :string, :u8, :ptr-void, :CPU (struct), or compound (:fn ...)
   / (:ptr T) forms."
  (cond
    ((keywordp x)
     (or (member x '(:int :bool :unit :string :cstr :size
                     :u8 :u16 :u32 :u64 :i8 :i16 :i32 :i64
                     :float :double
                     :ptr-void
                     :Value :symbol))
         (let ((s (symbol-name x)))
           (and (> (length s) 4) (string= s "PTR-" :end1 4)))
         (struct-type-p x)))
    ((consp x) (member (first x) '(:fn :ptr)))))

(defun split-defn-shape (rest-of-form)
  "Given the part after 'name' in (defn name PARAMS [ret] BODY...), return
   (values params ret-type body) where ret-type may be nil (infer)."
  (let ((params (first rest-of-form))
        (after (rest rest-of-form)))
    (cond
      ((and after (type-annotation-p (first after)))
       (values params (first after) (rest after)))
      (t
       (values params nil after)))))

(defun param-name-and-tvar (p)
  "p is either a naked symbol (or single-element list) or (name :type)."
  (cond
    ((symbolp p)               (list p (fresh-tvar)))
    ((and (consp p) (= (length p) 1)) (list (first p) (fresh-tvar)))
    ((and (consp p) (= (length p) 2)) (list (first p) (second p)))
    (t (error "infer: bad param spec ~A" p))))

(defun defaulting (ty)
  "If a tvar remains after solving, default to :int with a warning. Avoids
   emitting (:tvar N) into the C output."
  (let ((r (resolve-type ty)))
    (cond
      ((tvar-p r) (warn "unconstrained type variable, defaulting to :int") :int)
      ((and (consp r) (eq (first r) :fn))
       (list :fn (mapcar #'defaulting (second r)) (defaulting (third r))))
      (t r))))

(defun infer-defn (form)
  "Annotate one defn. Used when there's no surrounding program context."
  (let ((*subst* (make-hash-table))
        (*tvar-counter* 0)
        (*fn-sigs* (make-hash-table)))
    ;; Allow self-recursion: register own sig before walking body.
    (destructuring-bind (defn-sym name &rest body-rest) form
      (declare (ignore defn-sym))
      (multiple-value-bind (params ret-annot body) (split-defn-shape body-rest)
        (let* ((typed-params (mapcar #'param-name-and-tvar params))
               (param-types (mapcar #'second typed-params))
               (ret-type (or ret-annot (fresh-tvar))))
          (setf (gethash name *fn-sigs*) (list :fn param-types ret-type))
          (let ((env (mapcar (lambda (p) (cons (first p) (second p))) typed-params)))
            (let (last-ty)
              (dolist (b body) (setf last-ty (infer b env)))
              (when last-ty (unify ret-type last-ty))))
          (let ((resolved-params (mapcar (lambda (p)
                                           (list (first p) (defaulting (second p))))
                                         typed-params))
                (resolved-ret (defaulting ret-type)))
            (list* 'defn name resolved-params resolved-ret body)))))))

(defun normalize-extern-params (params)
  "Accept either flat (name1 :ty1 name2 :ty2 ...) or pairs ((n1 :ty1)
   (n2 :ty2) ...). Returns list of (name type) pairs."
  (cond
    ((null params) nil)
    ((consp (first params))
     (mapcar (lambda (p) (list (first p) (second p))) params))
    (t (loop for (name ty) on params by #'cddr collect (list name ty)))))

(defun infer-program (forms &key externs)
  "Annotate all defns in a program. Handles mutual recursion. Externs are
   pre-registered so defns can call them."
  (let ((*subst* (make-hash-table))
        (*tvar-counter* 0)
        (*fn-sigs* (make-hash-table))
        (info nil))
    ;; Pre-register externs.
    (dolist (e externs)
      (let* ((name (second e))
             (params (normalize-extern-params (third e)))
             (param-types (mapcar #'second params))
             (ret-type (fourth e)))
        (setf (gethash name *fn-sigs*) (list :fn param-types ret-type))))
    ;; Pass 1: register each fn's signature with tvars where unannotated.
    (dolist (f forms)
      (destructuring-bind (defn-sym name &rest rest) f
        (declare (ignore defn-sym))
        (multiple-value-bind (params ret-annot body) (split-defn-shape rest)
          (let* ((typed-params (mapcar #'param-name-and-tvar params))
                 (param-types (mapcar #'second typed-params))
                 (ret-type (or ret-annot (fresh-tvar))))
            (setf (gethash name *fn-sigs*) (list :fn param-types ret-type))
            (push (list name typed-params ret-type body) info)))))
    (setf info (nreverse info))
    ;; Pass 2: infer each body.
    (dolist (e info)
      (destructuring-bind (name typed-params ret-type body) e
        (declare (ignore name))
        (let ((env (mapcar (lambda (p) (cons (first p) (second p))) typed-params)))
          (let (last-ty)
            (dolist (b body) (setf last-ty (infer b env)))
            (when last-ty (unify ret-type last-ty))))))
    ;; Pass 3: produce annotated forms.
    (mapcar (lambda (e)
              (destructuring-bind (name typed-params ret-type body) e
                (let ((rp (mapcar (lambda (p)
                                    (list (first p) (defaulting (second p))))
                                  typed-params))
                      (rt (defaulting ret-type)))
                  (list* 'defn name rp rt body))))
            info)))
