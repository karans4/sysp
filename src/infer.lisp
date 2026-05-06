;;;; Hindley-Milner type inference with let-polymorphism.
;;;;
;;;; Surface form (possibly with naked params / no ret-type) → fully-annotated
;;;; form ready for lower-defn. Nothing below this layer needs to change.
;;;;
;;;; Type language:
;;;;   :int :bool :unit :string                         -- concrete
;;;;   (:fn (T1 T2 ...) Tret)                           -- function type
;;;;   (:tvar N)                                        -- type variable
;;;;   (:forall (id ...) ty)                            -- type scheme

(in-package :sysp-ir)

(defvar *subst*)          ; hash table: tvar id → type
(defvar *tvar-counter*)
(defvar *fn-sigs*)        ; sym → (:fn arg-types ret-type) | (:forall ids (:fn ...))

;;; The cons cell currently being type-checked. Read by infer-error to look
;;; up the source location attached by the parser. Reset by every recursive
;;; descent into a child form.
(defvar *current-form* nil)

(defun infer-error (fmt &rest args)
  "Signal an inference error pointing at *current-form* if a location is
   known. Falls back to a plain error when called from a form built at
   compile time (no parser-attached location)."
  (cond
    ((and *current-form* (loc-of *current-form*))
     (apply #'error-at *current-form* fmt args))
    (t (apply #'error fmt args))))

(defun fresh-tvar ()
  (list :tvar (incf *tvar-counter*)))

(defun tvar-p (ty) (and (consp ty) (eq (first ty) :tvar)))
(defun forall-p (ty) (and (consp ty) (eq (first ty) :forall)))
(defun fn-type-p (ty) (and (consp ty) (eq (first ty) :fn)))
(defun generic-type-p (ty) (and (consp ty) (eq (first ty) :generic)))

(defun canonicalize-type (ty)
  "Recognize (Name args) where Name is a registered generic struct as the
   applied form (:generic Name args). Idempotent and recursive — :ptr,
   :fn, and nested (:generic ...) all get walked."
  (cond
    ((and (consp ty) (symbolp (first ty)) (generic-struct-name-p (first ty)))
     (list* :generic (first ty) (mapcar #'canonicalize-type (rest ty))))
    ((generic-type-p ty)
     (list* :generic (second ty) (mapcar #'canonicalize-type (cddr ty))))
    ((and (consp ty) (eq (first ty) :ptr))
     (list :ptr (canonicalize-type (second ty))))
    ((fn-type-p ty)
     (list :fn (mapcar #'canonicalize-type (second ty))
           (canonicalize-type (third ty))))
    (t ty)))

(defun subst-type-params (ty subs)
  "Substitute type-param keywords (e.g. :T) with concrete types per alist subs.
   Distinct from substitute-tvars: this targets keyword params, not tvar IDs.
   Canonicalizes first so (Name args) sugar inside templates is handled."
  (let ((ty (canonicalize-type ty)))
    (cond
      ((and (keywordp ty) (assoc ty subs)) (cdr (assoc ty subs)))
      ((and (consp ty) (eq (first ty) :ptr))
       (list :ptr (subst-type-params (second ty) subs)))
      ((fn-type-p ty)
       (list :fn (mapcar (lambda (a) (subst-type-params a subs)) (second ty))
             (subst-type-params (third ty) subs)))
      ((generic-type-p ty)
       (list* :generic (second ty)
              (mapcar (lambda (a) (subst-type-params a subs)) (cddr ty))))
      (t ty))))

(defun free-tvars (ty)
  "Tvar IDs free in ty, after resolution. Walks fn types and forall bodies."
  (let ((seen (make-hash-table)) (acc nil))
    (labels ((rec (ty1 bound)
               (let ((r (resolve-type ty1)))
                 (cond
                   ((tvar-p r)
                    (let ((id (second r)))
                      (unless (or (member id bound) (gethash id seen))
                        (setf (gethash id seen) t)
                        (push id acc))))
                   ((forall-p r)
                    (rec (third r) (append (second r) bound)))
                   ((fn-type-p r)
                    (mapc (lambda (a) (rec a bound)) (second r))
                    (rec (third r) bound))
                   ((generic-type-p r)
                    (mapc (lambda (a) (rec a bound)) (cddr r)))))))
      (rec ty nil)
      (nreverse acc))))

(defun env-free-tvars (env)
  (let ((acc nil))
    (dolist (b env) (setf acc (union acc (free-tvars (cdr b)))))
    acc))

(defun substitute-tvars (ty subs)
  "Substitute tvar IDs to types per alist subs. Resolves before substituting."
  (let ((r (resolve-type ty)))
    (cond
      ((tvar-p r)
       (let ((s (assoc (second r) subs)))
         (if s (cdr s) r)))
      ((fn-type-p r)
       (list :fn (mapcar (lambda (a) (substitute-tvars a subs)) (second r))
             (substitute-tvars (third r) subs)))
      ((generic-type-p r)
       (list* :generic (second r)
              (mapcar (lambda (a) (substitute-tvars a subs)) (cddr r))))
      ;; forall: don't substitute under bound names
      ((forall-p r)
       (let ((bound (second r)))
         (list :forall bound
               (substitute-tvars (third r)
                                 (remove-if (lambda (s) (member (car s) bound))
                                            subs)))))
      (t r))))

(defun generalize (ty env)
  "Wrap free tvars of ty (not free in env) in a forall."
  (let* ((ty-r (resolve-type ty))
         (env-tvars (env-free-tvars env))
         (free (set-difference (free-tvars ty-r) env-tvars)))
    (if free (list :forall free ty-r) ty-r)))

(defun instantiate (scheme)
  "Replace forall-bound tvars with fresh ones. Pass-through for non-schemes."
  (cond
    ((forall-p scheme)
     (let ((subs (mapcar (lambda (id) (cons id (fresh-tvar))) (second scheme))))
       (substitute-tvars (third scheme) subs)))
    (t scheme)))

(defun resolve-type (ty)
  "Follow tvar chain to a (possibly partially) concrete type."
  (cond
    ((tvar-p ty)
     (let ((sub (gethash (second ty) *subst*)))
       (if sub (resolve-type sub) ty)))
    ((fn-type-p ty)
     (list :fn (mapcar #'resolve-type (second ty)) (resolve-type (third ty))))
    ((generic-type-p ty)
     (list* :generic (second ty) (mapcar #'resolve-type (cddr ty))))
    (t ty)))

(defun unify (t1 t2)
  (let ((r1 (resolve-type t1)) (r2 (resolve-type t2)))
    (cond
      ((equal r1 r2) t)
      ((tvar-p r1) (setf (gethash (second r1) *subst*) r2))
      ((tvar-p r2) (setf (gethash (second r2) *subst*) r1))
      ;; Case-insensitive keyword equality — bridges parser-preserved case
      ;; (:Fn, :Value) with CL-reader-upcased (:FN, :VALUE).
      ((and (keywordp r1) (keywordp r2)
            (string-equal (symbol-name r1) (symbol-name r2)))
       t)
      ;; numeric ↔ numeric: silently accept; C handles all width/float
      ;; promotions and narrowing implicitly.
      ((and (numeric-type-p r1) (numeric-type-p r2)) t)
      ;; Opaque :Fn unifies with any structural (:fn ...). Keeps legacy
      ;; :Fn-annotated params interchangeable with structurally-typed
      ;; lambda values. Information is lost — callers using :Fn-annotated
      ;; vars stay on the legacy ret-ty=:int path inside the callee body.
      ((or (and (keywordp r1) (string-equal (symbol-name r1) "FN") (fn-type-p r2))
           (and (keywordp r2) (string-equal (symbol-name r2) "FN") (fn-type-p r1)))
       t)
      ;; :unit unifies with anything — value is discarded at C level.
      ((or (eq r1 :unit) (eq r2 :unit)) t)
      ((and (consp r1) (consp r2)
            (eq (first r1) :fn) (eq (first r2) :fn))
       (unless (= (length (second r1)) (length (second r2)))
         (infer-error "infer: arity mismatch ~A vs ~A" r1 r2))
       (mapc #'unify (second r1) (second r2))
       (unify (third r1) (third r2)))
      ;; Two generic struct apps unify when the names match and each
      ;; argument unifies positionally — same shape as :fn.
      ((and (generic-type-p r1) (generic-type-p r2)
            (eq (second r1) (second r2))
            (= (length (cddr r1)) (length (cddr r2))))
       (mapc #'unify (cddr r1) (cddr r2))
       t)
      ;; Pointer types unify element-wise.
      ((and (consp r1) (consp r2)
            (eq (first r1) :ptr) (eq (first r2) :ptr))
       (unify (second r1) (second r2))
       t)
      (t (infer-error "infer: type mismatch ~A vs ~A" r1 r2)))))

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
         (t (infer-error "infer: unbound symbol ~A" e)))))
    ((consp e)
     ;; Track the current form so deeper errors carry the right location.
     (let ((*current-form* e))
       (infer-form (car e) (cdr e) env)))
    (t (infer-error "infer: cannot type ~A" e))))

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

;; Closures: structural (:fn (param-tys) ret-ty) types.
(defmethod infer-form ((head (eql 'lambda)) args env)
  (multiple-value-bind (raw-params ret-annot body) (lambda-split-args args)
    (let* ((typed-params
            (mapcar (lambda (p)
                      (let ((np (parse-lambda-param p)))
                        (list (first np) (or (second np) (fresh-tvar)))))
                    raw-params))
           (param-types (mapcar #'second typed-params))
           (ret-type (or ret-annot (fresh-tvar)))
           (env2 env))
      (dolist (p typed-params) (push (cons (first p) (second p)) env2))
      (let (last-ty)
        (dolist (b body) (setf last-ty (infer b env2)))
        (when last-ty (unify ret-type last-ty)))
      (list :fn param-types ret-type))))

(defmethod infer-form ((head (eql 'call)) args env)
  ;; (call f arg...). f's type drives result:
  ;;   - :Fn (legacy opaque): walks args, returns fresh tvar (defaults to :int)
  ;;   - :tvar: unify with structural fn type, drive ret from there
  ;;   - (:fn (a-tys) r-ty): unify args, return r-ty
  (let ((fty (resolve-type (infer (first args) env))))
    (cond
      ((and (keywordp fty) (string-equal (symbol-name fty) "FN"))
       (dolist (a (rest args)) (infer a env))
       (fresh-tvar))
      ((tvar-p fty)
       (let* ((arg-tvars (mapcar (lambda (_) (declare (ignore _)) (fresh-tvar))
                                 (rest args)))
              (ret-tvar (fresh-tvar)))
         (unify fty (list :fn arg-tvars ret-tvar))
         (loop for a in (rest args) for at in arg-tvars
               do (unify at (infer a env)))
         ret-tvar))
      ((fn-type-p fty)
       (let ((arg-tys (second fty))
             (ret-ty  (third fty)))
         (unless (= (length arg-tys) (length (rest args)))
           (infer-error "call: expected ~D args, got ~D"
                        (length arg-tys) (length (rest args))))
         (loop for a in (rest args) for at in arg-tys
               do (unify at (infer a env)))
         ret-ty))
      (t (infer-error "call: expected fn, got ~A" fty)))))

(defmethod infer-form ((head (eql 'addr-of)) args env)
  (let* ((sym (first args))
         (b (assoc sym env)))
    (unless b (infer-error "addr-of: unbound ~A" sym))
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
      (t (infer-error "deref: expected pointer, got ~A" pty)))))

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
    (unless tgt-ty (infer-error "infer: set! on unbound ~A" target))
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

(defmethod infer-form ((head (eql 'recur)) args env)
  ;; recur returns :unit (control flow); each arg is type-checked but
  ;; we don't have current-fn signature here, so just walk args.
  (dolist (a args) (infer a env))
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

(defun generic-field-type (obj-ty field-sym)
  "obj-ty is (:generic Name args...). Look up the template, build subs from
   params→concrete-args, return the field's type with subs applied."
  (let* ((name (second obj-ty))
         (concrete (cddr obj-ty))
         (entry (gethash name *generic-structs*))
         (params (first entry))
         (fields (second entry))
         (subs (mapcar #'cons params concrete))
         (field-spec (assoc field-sym fields)))
    (unless field-spec
      (infer-error "get-field: generic struct ~A has no field ~A" name field-sym))
    (subst-type-params (second field-spec) subs)))

(defmethod infer-form ((head (eql 'get-field)) args env)
  (let* ((obj-ty (resolve-type (infer (first args) env)))
         (field-sym (second args))
         (struct-ty (resolve-struct-or-ptr obj-ty)))
    (cond
      ((generic-type-p obj-ty) (generic-field-type obj-ty field-sym))
      (struct-ty (struct-field-type struct-ty field-sym))
      (t (infer-error "get-field: ~A is not a struct or struct pointer, got ~A"
                      (first args) obj-ty)))))

(defmethod infer-form ((head (eql 'set-field!)) args env)
  (let* ((obj-ty (resolve-type (infer (first args) env)))
         (field-sym (second args))
         (val-ty (infer (third args) env))
         (struct-ty (resolve-struct-or-ptr obj-ty)))
    (cond
      ((generic-type-p obj-ty)
       (unify (generic-field-type obj-ty field-sym) val-ty)
       :unit)
      (struct-ty
       (unify (struct-field-type struct-ty field-sym) val-ty)
       :unit)
      (t (infer-error "set-field!: ~A is not a struct or struct pointer, got ~A"
                      (first args) obj-ty)))))

(defmethod infer-form (head args env)
  ;; Default: struct constructor (concrete or generic) OR function call.
  (cond
    ((struct-name-p head)
     ;; Concrete struct constructor: types must match field types.
     (let ((fields (gethash head *struct-fields*)))
       (unless (= (length fields) (length args))
         (infer-error "struct ~A: expected ~D fields, got ~D"
                      head (length fields) (length args)))
       (loop for a in args for f in fields
             do (unify (second f) (infer a env)))
       (struct-type-keyword head)))
    ((generic-struct-name-p head)
     ;; Generic ctor: build subs from params→fresh tvars, unify each field's
     ;; substituted type against the arg's inferred type, return the applied
     ;; (:generic Name concrete-args) — concrete-args are the resolved tvars.
     (let* ((entry (gethash head *generic-structs*))
            (params (first entry))
            (fields (second entry))
            (subs (mapcar (lambda (p) (cons p (fresh-tvar))) params)))
       (unless (= (length fields) (length args))
         (infer-error "generic struct ~A: expected ~D fields, got ~D"
                      head (length fields) (length args)))
       (loop for a in args for f in fields
             do (unify (subst-type-params (second f) subs) (infer a env)))
       (list* :generic head (mapcar #'cdr subs))))
    (t
     (let ((sig (and *fn-sigs* (gethash head *fn-sigs*))))
       (unless sig
         (infer-error "infer: unknown function ~A" head))
       ;; Forall-bound schemes get fresh tvars per call site (let-poly).
       ;; Raw fn types (intra-SCC recursive references) pass through.
       (let* ((insted (instantiate sig))
              (arg-tys (second insted))
              (ret-ty  (third insted)))
         (unless (= (length arg-tys) (length args))
           (infer-error "infer: ~A expects ~D args, got ~D"
                        head (length arg-tys) (length args)))
         (loop for a in args for at in arg-tys
               do (unify at (infer a env)))
         ret-ty)))))

;;; --- defn / program drivers ---

(defun type-annotation-p (x)
  "Heuristic: distinguish a type form from a body form. Types are keywords
   like :int, :string, :u8, :ptr-void, :CPU (struct), or compound (:fn ...)
   / (:ptr T) / (:generic Name args) / (Name args) forms."
  (cond
    ((keywordp x)
     (or (member x '(:int :bool :unit :string :cstr :size
                     :u8 :u16 :u32 :u64 :i8 :i16 :i32 :i64
                     :float :double
                     :ptr-void
                     :Value :symbol :Fn))
         (let ((s (symbol-name x)))
           (and (> (length s) 4) (string= s "PTR-" :end1 4)))
         (struct-type-p x)))
    ((consp x)
     (or (member (first x) '(:fn :ptr :generic))
         (and (symbolp (first x)) (generic-struct-name-p (first x)))))))

(defun split-defn-shape (rest-of-form)
  "Given the part after 'name' in (defn name PARAMS [ret] BODY...), return
   (values params ret-type body) where ret-type may be nil (infer).
   Generic struct sugar in ret-type is canonicalized."
  (let ((params (first rest-of-form))
        (after (rest rest-of-form)))
    (cond
      ((and after (type-annotation-p (first after)))
       (values params (canonicalize-type (first after)) (rest after)))
      (t
       (values params nil after)))))

(defun param-name-and-tvar (p)
  "p is either a naked symbol (or single-element list) or (name :type).
   Type annotations are canonicalized so generic struct sugar (Name args)
   becomes (:generic Name args)."
  (cond
    ((symbolp p)               (list p (fresh-tvar)))
    ((and (consp p) (= (length p) 1)) (list (first p) (fresh-tvar)))
    ((and (consp p) (= (length p) 2))
     (list (first p) (canonicalize-type (second p))))
    (t (error "infer: bad param spec ~A" p))))

(defun defaulting (ty)
  "If a tvar remains after solving, default to :int with a warning. Avoids
   emitting (:tvar N) into the C output. (:generic Name args) types are
   materialized into a mangled struct keyword so the rest of the pipeline
   sees a normal struct type."
  (let ((r (resolve-type ty)))
    (cond
      ((tvar-p r) (warn "unconstrained type variable, defaulting to :int") :int)
      ((fn-type-p r)
       (list :fn (mapcar #'defaulting (second r)) (defaulting (third r))))
      ((generic-type-p r)
       (let* ((name (second r))
              (args (cddr r))
              (mangled (materialize-generic-instance name args)))
         (struct-type-keyword mangled)))
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

;;; --- call graph + SCC for let-polymorphism ---

(defun collect-call-targets (form known)
  "Head-position symbols in form that appear in known."
  (let ((acc nil))
    (labels ((rec (e)
               (when (consp e)
                 (let ((h (first e)))
                   (when (and (symbolp h) (member h known))
                     (pushnew h acc)))
                 (mapc #'rec (rest e)))))
      (rec form))
    acc))

(defun build-call-graph (defn-info)
  (let ((g (make-hash-table))
        (names (mapcar #'first defn-info)))
    (dolist (e defn-info)
      (destructuring-bind (name typed-params ret-type body) e
        (declare (ignore typed-params ret-type))
        (let ((calls nil))
          (dolist (b body)
            (setf calls (union calls (collect-call-targets b names))))
          (setf (gethash name g) calls))))
    g))

(defun tarjan-sccs (graph node-list)
  "Tarjan's SCC. Returns SCCs in topological order — callees first."
  (let ((index 0) (stack nil)
        (idx (make-hash-table)) (low (make-hash-table))
        (on-stack (make-hash-table))
        (sccs nil))
    (labels ((strongconnect (v)
               (setf (gethash v idx) index (gethash v low) index)
               (incf index)
               (push v stack)
               (setf (gethash v on-stack) t)
               (dolist (w (gethash v graph))
                 (cond
                   ((not (gethash w idx))
                    (strongconnect w)
                    (setf (gethash v low)
                          (min (gethash v low) (gethash w low))))
                   ((gethash w on-stack)
                    (setf (gethash v low)
                          (min (gethash v low) (gethash w idx))))))
               (when (= (gethash v low) (gethash v idx))
                 (let ((scc nil))
                   (loop
                     (let ((w (pop stack)))
                       (setf (gethash w on-stack) nil)
                       (push w scc)
                       (when (eq w v) (return))))
                   (push scc sccs)))))
      (dolist (v node-list)
        (unless (gethash v idx) (strongconnect v))))
    (nreverse sccs)))

;;; --- monomorphization ---

(defvar *mono-cache*)         ; (poly-name concrete-args) → mono-name
(defvar *mono-defns*)         ; list of (name typed-params ret-type body)
(defvar *info-table-mono*)    ; name → defn-info entry

(defun mono-type-suffix (ty)
  (cond
    ((keywordp ty) (string-downcase (symbol-name ty)))
    ((fn-type-p ty)
     (with-output-to-string (s)
       (write-string "fn" s)
       (dolist (a (second ty)) (write-char #\_ s) (write-string (mono-type-suffix a) s))
       (write-char #\_ s) (write-string (mono-type-suffix (third ty)) s)))
    (t (format nil "~a" ty))))

(defun mono-mangle (name concrete-args)
  "Symbol for a monomorphized fn or generic-struct instance, e.g.
   id + (:int) → id_int, Box + (:string) → Box_string. Used by both poly-fn
   mono and generic-struct mono. The symbol is interned mixed-case so
   c-name's preserve-on-mixed heuristic emits it verbatim in C."
  (intern (with-output-to-string (s)
            (write-string (symbol-name name) s)
            (dolist (ty concrete-args)
              (write-char #\_ s)
              (write-string (mono-type-suffix ty) s)))
          :sysp-ir))

(defun materialize-generic-instance (name concrete-args)
  "Register a concrete instantiation of generic struct `name`. Resolves
   each concrete-arg (so :int is actually :int, not a tvar bound to it),
   then writes the substituted fields into *struct-fields* under the
   mangled name. Cached via *generic-struct-instances*."
  (let* ((concrete-args (mapcar (lambda (a) (defaulting a)) concrete-args))
         (key (cons name concrete-args)))
    (or (gethash key *generic-struct-instances*)
        (let* ((mangled (mono-mangle name concrete-args))
               (entry (gethash name *generic-structs*))
               (params (first entry))
               (fields (second entry))
               (subs (mapcar #'cons params concrete-args))
               (concrete-fields
                (mapcar (lambda (f)
                          (list (first f)
                                (defaulting (subst-type-params (second f) subs))))
                        fields)))
          (setf (gethash key *generic-struct-instances*) mangled)
          (setf (gethash mangled *struct-fields*) concrete-fields)
          mangled))))

(defun monomorphize-program (defn-info)
  "Specialize poly defns at each call site. Drops uninstantiated polys
   in favor of a single :int-defaulted copy (legacy behavior)."
  (let ((*mono-cache* (make-hash-table :test 'equal))
        (*mono-defns* nil)
        (*info-table-mono* (make-hash-table))
        (concrete nil))
    ;; Make a working copy of each defn's body. mono-walk uses rplaca to
    ;; rewrite generic ctors / poly-fn-call heads to mangled names — it
    ;; would mutate the parser-tracked source forms otherwise, breaking
    ;; both source locations and any second compile-program on the same input.
    (dolist (e defn-info)
      (setf (fourth e) (copy-tree (fourth e)))
      (setf (gethash (first e) *info-table-mono*) e))
    ;; Walk concrete defns, specialize their poly call sites in place.
    (dolist (e defn-info)
      (let ((scheme (gethash (first e) *fn-sigs*)))
        (unless (forall-p scheme)
          (let ((env (mapcar (lambda (p) (cons (first p) (resolve-type (second p))))
                             (second e))))
            (dolist (b (fourth e)) (mono-walk b env)))
          (push e concrete))))
    ;; For poly defns never instantiated, default-emit (back-compat).
    (dolist (e defn-info)
      (let* ((name (first e))
             (scheme (gethash name *fn-sigs*))
             (instantiated (loop for k being the hash-keys of *mono-cache*
                                 thereis (eq (first k) name))))
        (when (and (forall-p scheme) (not instantiated))
          (push e concrete))))
    ;; Annotate forms in declaration order: materialized monos first
    ;; (they're called by concretes), then concretes.
    (let ((all (append (nreverse *mono-defns*) (nreverse concrete))))
      (mapcar (lambda (e)
                (destructuring-bind (name typed-params ret-type body) e
                  (let ((rp (mapcar (lambda (p)
                                      (list (first p) (defaulting (second p))))
                                    typed-params)))
                    (list* 'defn name rp (defaulting ret-type) body))))
              all))))

(defun mono-walk (form env)
  "Walk form, rewriting poly call heads in place to specialized names."
  (cond
    ((atom form) nil)
    ((eq (first form) 'quote) nil)
    ((eq (first form) 'cstr)  nil)
    ((eq (first form) 'sym)   nil)
    ((eq (first form) 'let)
     (let ((bindings (second form)) (body (cddr form)) (env2 env))
       (dolist (b bindings)
         (mono-walk (second b) env2)
         (push (cons (first b) (resolve-type (infer (second b) env2))) env2))
       (dolist (b body) (mono-walk b env2))))
    ((eq (first form) 'lambda)
     (multiple-value-bind (raw-params _ret body) (lambda-split-args (rest form))
       (declare (ignore _ret))
       (let ((env2 env))
         (dolist (p raw-params)
           (let ((np (parse-lambda-param p)))
             (push (cons (first np) (or (second np) :int)) env2)))
         (dolist (b body) (mono-walk b env2)))))
    ((eq (first form) 'set!)
     (mono-walk (third form) env))
    ((eq (first form) 'for)
     (let* ((spec (second form))
            (var (first spec)) (lo (second spec)) (hi (third spec))
            (body (cddr form)))
       (mono-walk lo env) (mono-walk hi env)
       (dolist (b body)
         (mono-walk b (cons (cons var :int) env)))))
    ((eq (first form) 'while)
     (mono-walk (second form) env)
     (dolist (b (cddr form)) (mono-walk b env)))
    ((eq (first form) 'if)
     (mono-walk (second form) env)
     (mono-walk (third form) env)
     (when (fourth form) (mono-walk (fourth form) env)))
    ((eq (first form) 'do)
     (dolist (b (rest form)) (mono-walk b env)))
    ((eq (first form) 'when)
     (mono-walk (second form) env)
     (dolist (b (cddr form)) (mono-walk b env)))
    ((and (symbolp (first form))
          (let ((sig (gethash (first form) *fn-sigs*)))
            (forall-p sig)))
     (dolist (a (rest form)) (mono-walk a env))
     (mono-walk-poly-call form env))
    ;; Generic struct ctor (Box 5): re-infer args, materialize the
    ;; instance, and rewrite the call head to the mangled struct name so
    ;; lower sees a regular concrete struct ctor.
    ((and (symbolp (first form)) (generic-struct-name-p (first form)))
     (dolist (a (rest form)) (mono-walk a env))
     (let* ((name (first form))
            (entry (gethash name *generic-structs*))
            (params (first entry))
            (fields (second entry))
            (subs (mapcar (lambda (p) (cons p (fresh-tvar))) params)))
       (loop for a in (rest form) for f in fields
             do (unify (subst-type-params (second f) subs) (infer a env)))
       (let* ((concrete-args (mapcar (lambda (s) (resolve-type (cdr s))) subs))
              (mangled (materialize-generic-instance name concrete-args)))
         (rplaca form mangled))))
    (t
     (dolist (a (rest form)) (mono-walk a env)))))

(defun mono-walk-poly-call (call-form env)
  (let* ((poly-name (first call-form))
         (scheme (gethash poly-name *fn-sigs*))
         (bound-ids (second scheme))
         (sig (third scheme))
         (param-types (second sig))
         (ret-type (third sig))
         ;; Fresh substitution for this call site, tracked explicitly so we
         ;; can read concrete types back per bound id.
         (subs (mapcar (lambda (id) (cons id (fresh-tvar))) bound-ids))
         (fresh-params (mapcar (lambda (pt) (substitute-tvars pt subs)) param-types)))
    (declare (ignore ret-type))
    ;; Drive unification by re-inferring args.
    (loop for arg in (rest call-form) for fpt in fresh-params
          do (unify fpt (infer arg env)))
    ;; Resolve each bound id to its concrete type.
    (let* ((concrete-subs (mapcar (lambda (s)
                                    (cons (car s) (resolve-type (cdr s))))
                                  subs))
           (concrete-args (mapcar (lambda (pt) (substitute-tvars pt concrete-subs))
                                  param-types))
           (key (list poly-name concrete-args))
           (mono-name (or (gethash key *mono-cache*)
                          (materialize-mono poly-name concrete-subs))))
      (rplaca call-form mono-name))))

(defun materialize-mono (poly-name concrete-subs)
  (let* ((info (gethash poly-name *info-table-mono*))
         (orig-typed-params (second info))
         (orig-ret-type (third info))
         (orig-body (fourth info))
         (mono-params (mapcar (lambda (p)
                                (list (first p)
                                      (substitute-tvars (second p) concrete-subs)))
                              orig-typed-params))
         (mono-ret (substitute-tvars orig-ret-type concrete-subs))
         (mono-name (mono-mangle poly-name (mapcar #'second mono-params)))
         (key (list poly-name (mapcar #'second mono-params))))
    ;; Cache before recursing — supports recursive poly fns.
    (setf (gethash key *mono-cache*) mono-name)
    (setf (gethash mono-name *fn-sigs*)
          (list :fn (mapcar #'second mono-params) mono-ret))
    (let* ((cloned-body (copy-tree orig-body))
           (env (mapcar (lambda (p) (cons (first p) (second p))) mono-params)))
      (dolist (b cloned-body) (mono-walk b env))
      (push (list mono-name mono-params mono-ret cloned-body) *mono-defns*))
    mono-name))

(defun infer-program (forms &key externs)
  "Annotate all defns. Handles mutual recursion via SCC and let-polymorphism
   via forall schemes + a per-call-site monomorphization pass."
  (let ((*subst* (make-hash-table))
        (*tvar-counter* 0)
        (*fn-sigs* (make-hash-table))
        (defn-info nil))
    ;; Pre-register externs as monomorphic.
    (dolist (e externs)
      (let* ((name (second e))
             (params (normalize-extern-params (third e)))
             (param-types (mapcar #'second params))
             (ret-type (fourth e)))
        (setf (gethash name *fn-sigs*) (list :fn param-types ret-type))))
    ;; Pass 1: register each defn with fresh-tvars sig.
    (dolist (f forms)
      (destructuring-bind (defn-sym name &rest rest) f
        (declare (ignore defn-sym))
        (multiple-value-bind (params ret-annot body) (split-defn-shape rest)
          (let* ((typed-params (mapcar #'param-name-and-tvar params))
                 (param-types (mapcar #'second typed-params))
                 (ret-type (or ret-annot (fresh-tvar))))
            (setf (gethash name *fn-sigs*) (list :fn param-types ret-type))
            (push (list name typed-params ret-type body) defn-info)))))
    (setf defn-info (nreverse defn-info))
    ;; Pass 2: SCC-aware inference. Within an SCC, sigs are raw (shared
    ;; tvars; mutual recursion works). After each SCC's bodies are inferred,
    ;; generalize all its sigs into forall schemes.
    (let* ((info-table (make-hash-table))
           (graph (build-call-graph defn-info))
           (sccs (tarjan-sccs graph (mapcar #'first defn-info))))
      (dolist (e defn-info) (setf (gethash (first e) info-table) e))
      (dolist (scc sccs)
        (dolist (name scc)
          (let* ((info (gethash name info-table))
                 (typed-params (second info))
                 (ret-type (third info))
                 (body (fourth info))
                 (env (mapcar (lambda (p) (cons (first p) (second p))) typed-params)))
            (let (last-ty)
              (dolist (b body) (setf last-ty (infer b env)))
              (when last-ty (unify ret-type last-ty)))))
        (dolist (name scc)
          (setf (gethash name *fn-sigs*)
                (generalize (gethash name *fn-sigs*) nil)))))
    ;; Pass 3: monomorphize. Returns final list of concrete annotated forms.
    (monomorphize-program defn-info)))
