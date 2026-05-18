;;;; Traits: deftrait / impl + static (monomorphized) dispatch.
;;;;
;;;; A trait method call `(m self ...)` is resolved to a concrete impl
;;;; function by self's inferred type, then handled by the ordinary
;;;; infer -> lower -> emit pipeline. Each `(impl Trait (Type) (defn m
;;;; ...))` materializes a normal defn named `m_<type>` (mangled via
;;;; mono-mangle, so call sites and impls always agree on the name).
;;;; No runtime dispatch: every trait call lowers to a direct C call.

(in-package :sysp-ir)

(defvar *traits*       (make-hash-table :test 'equal)) ; "Trait" -> (tparams sigs)
(defvar *trait-impls*  (make-hash-table :test 'equal)) ; "Trait:Type" -> (mname . mangled)*
(defvar *method->trait* (make-hash-table :test 'equal)) ; "m" -> "Trait"

(defun reset-trait-state ()
  (clrhash *traits*)
  (clrhash *trait-impls*)
  (clrhash *method->trait*))

(defun trait-method-name-p (sym)
  "True if SYM is a method of some registered trait."
  (and (symbolp sym)
       (nth-value 1 (gethash (symbol-name sym) *method->trait*))))

(defun register-deftrait (form)
  "(deftrait Name [tparams] (m (params) :ret) ...) — record signatures."
  (let ((name (symbol-name (second form)))
        (tparams (third form))
        (sigs nil))
    (dolist (m (cdddr form))
      (when (consp m)
        (let ((mn (symbol-name (first m))))
          (push (list mn (second m) (and (cddr m) (third m))) sigs)
          (setf (gethash mn *method->trait*) name))))
    (setf (gethash name *traits*) (list tparams (nreverse sigs)))))

(defun impl-type-keyword (type-form)
  "The keyword the inferer yields for an impl's declared self type.
   (Point) / Point -> :Point (struct kw);  int -> :int;  :int -> :int.
   Routed through mono-type-suffix later, so case never matters."
  (let ((h (if (consp type-form) (first type-form) type-form)))
    (cond ((keywordp h) h)
          ((struct-name-p h) (struct-type-keyword h))
          (t (intern (string-downcase (symbol-name h)) :keyword)))))

(defun trait-impl-mangled (method self-ty)
  "Mangled impl-fn symbol for METHOD on a concrete SELF-TY. Both impl
   registration and call sites go through here, so they always agree."
  (mono-mangle method (list (resolve-type self-ty))))

(defun register-impl (form)
  "(impl Trait (Type ...) (defn m (params) :ret body) ...).
   Returns the materialized concrete defns (renamed to mangled names)
   to splice into the program's defn list."
  (let* ((trait (symbol-name (second form)))
         (tform (third form))
         (tkw   (impl-type-keyword tform))
         (key   (format nil "~a:~a" trait (mono-type-suffix tkw)))
         (out   nil))
    (dolist (d (cdddr form))
      (when (and (consp d) (eq (first d) 'defn))
        (let* ((mname   (symbol-name (second d)))
               (mangled (mono-mangle (second d) (list tkw))))
          (push (cons mname mangled) (gethash key *trait-impls*))
          (push (list* 'defn mangled (cddr d)) out))))
    (nreverse out)))

(defun resolve-trait-call (method first-arg env)
  "Resolve a trait method call to its concrete impl-fn symbol, using the
   inferred type of FIRST-ARG. Shared by inference (type-check) and
   mono-walk (head rewrite) so both pick the same impl. Errors if no
   impl exists for the concrete self type."
  (let* ((self-ty (resolve-type (infer first-arg env)))
         (mangled (trait-impl-mangled method self-ty)))
    (unless (and *fn-sigs* (gethash mangled *fn-sigs*))
      (infer-error "no impl of ~A for ~A (looked for ~A)"
                   (gethash (symbol-name method) *method->trait*)
                   self-ty mangled))
    mangled))

(defun infer-trait-method (head args env)
  "Type a trait method call by delegating to the resolved impl's
   signature — identical to the ordinary fn-call path, just with the
   head resolved to the concrete impl via self's type."
  (let* ((m (resolve-trait-call head (first args) env))
         (sig (gethash m *fn-sigs*))
         (insted (instantiate sig))
         (arg-tys (second insted))
         (ret-ty (third insted)))
    (unless (= (length arg-tys) (length args))
      (infer-error "infer: ~A expects ~D args, got ~D"
                   m (length arg-tys) (length args)))
    (loop for a in args for at in arg-tys
          do (unify at (infer a env)))
    ret-ty))
