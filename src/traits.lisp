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

(defun tname (x)
  "Canonical (case-insensitive) name for a trait/method symbol. The test
   harness reads forms with the CL reader (upcased) while the sysp parser
   preserves case — upcasing the name makes lookups agree across both."
  (string-upcase (symbol-name x)))

(defun trait-method-name-p (sym)
  "True if SYM is a method of some registered trait."
  (and (symbolp sym)
       (nth-value 1 (gethash (tname sym) *method->trait*))))

(defun register-deftrait (form)
  "(deftrait Name [tparams] (m (params) :ret) ...) — record signatures."
  (let ((name (tname (second form)))
        (tparams (third form))
        (sigs nil))
    (dolist (m (cdddr form))
      (when (consp m)
        (let ((mn (tname (first m))))
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

(defun canon-sym (x)
  "Case-canonical symbol for trait mangling. A method written `show`
   reaches us upcased from the CL-reader test path but case-preserved
   from the sysp parser (libs). Mangle on the canonical name so a
   `(use \"lib...\")` impl and an in-program call always agree."
  (intern (tname x) :sysp-ir))

(defun trait-self-key (ty)
  "Dispatch key for a self type. A generic instantiation keys by its
   struct name only — `(:generic Vec :int)` and `(:generic Vec :bool)`
   share the one `(impl Trait (Vec :T) ...)`; the impl method is then
   monomorphized per element type by the ordinary poly pipeline."
  (let ((r (resolve-type ty)))
    (if (and (consp r) (eq (first r) :generic))
        (intern (string-upcase (string (second r))) :keyword)
        r)))

(defun trait-impl-mangled (method self-ty)
  "Mangled impl-fn symbol for METHOD on a concrete SELF-TY. Both impl
   registration and call sites go through here, so they always agree."
  (mono-mangle (canon-sym method) (list (trait-self-key self-ty))))

(defun register-impl (form)
  "(impl Trait (Type ...) (defn m (params) :ret body) ...).
   Returns the materialized concrete defns (renamed to mangled names)
   to splice into the program's defn list."
  (let* ((trait (tname (second form)))
         (tform (third form))
         (tkw   (impl-type-keyword tform))
         (key   (format nil "~a:~a" trait (mono-type-suffix tkw)))
         (out   nil))
    (dolist (d (cdddr form))
      (when (and (consp d) (eq (first d) 'defn))
        (let* ((mname   (tname (second d)))
               (mangled (mono-mangle (canon-sym (second d)) (list tkw))))
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
                   (gethash (tname method) *method->trait*)
                   self-ty mangled))
    mangled))

(defun trait-impl-fn (trait method self-ty)
  "Mangled impl-fn symbol for TRAIT's METHOD on the concrete SELF-TY, or
   nil if no such impl is registered. Used by the compiler-magic
   Gettable/Settable: an impl overrides, absence falls back to the
   built-in struct field access."
  (let* ((key  (format nil "~a:~a" (string-upcase trait)
                        (mono-type-suffix (trait-self-key self-ty))))
         (cell (assoc (string-upcase method) (gethash key *trait-impls*)
                      :test #'equal)))
    (and cell (cdr cell))))

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
