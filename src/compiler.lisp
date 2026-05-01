;;;; Top-level: compose lower → arc → peephole into compile-defn /
;;;; compile-program.

(in-package :sysp-ir)

(defun compile-defn (form)
  "(defn name (params...) [ret-type] body...) → fully-optimized ir-fn.
   Type annotations are optional; missing types get inferred."
  (let* ((annotated (infer-defn form))
         (fn (lower-defn annotated)))
    (insert-releases fn)
    (rewrite-jump-to-ret fn)
    (prune-unreachable fn)
    fn))

(defun compile-and-emit (form &optional (out t))
  (emit-c-fn (compile-defn form) out))

(defun expand-uses (forms)
  "Recursively splice in forms from (use \"file.sysp\")."
  (loop for f in forms
        if (and (consp f) (eq (first f) 'use))
          append (expand-uses (parse-file (second f)))
        else collect f))

(defun compile-program (forms &optional (out t))
  "Compile a top-level program: (use ...), (include ...), (defstruct ...),
   (extern-struct ...), (extern ...), (define ...), (enum ...), (defn ...)."
  (setf forms (expand-uses forms))
  (let (includes structs extern-structs defines externs defns)
    (dolist (f forms)
      (case (first f)
        (include       (push f includes))
        (defstruct     (push f structs))
        (extern-struct (push f extern-structs))
        (extern        (push f externs))
        (define        (push f defines))
        (enum          (dolist (variant (cddr f))
                         (push (list 'define (first variant) (second variant))
                               defines)))
        (defn          (push f defns))
        (t (error "compile-program: unknown top-level form ~A" (first f)))))
    (setf includes        (nreverse includes)
          structs         (nreverse structs)
          extern-structs  (nreverse extern-structs)
          defines         (nreverse defines)
          externs         (nreverse externs)
          defns           (nreverse defns))
    ;; extern-structs register fields but emit no typedef (the C header has it).
    (dolist (s extern-structs)
      (setf (gethash (second s) *struct-fields*)
            (normalize-struct-fields (cddr s))))
    ;; Register defines as globals.
    (dolist (d defines)
      (let* ((name (second d)) (val (third d))
             (ty (cond ((integerp val) :int)
                       ((stringp val)  :cstr)
                       (t :int))))
        (setf (gethash name *globals*) (list ty val))))
    ;; Register all structs first so types resolve.
    (dolist (s structs)
      (setf (gethash (second s) *struct-fields*)
            (normalize-struct-fields (cddr s))))
    (dolist (i includes) (emit-include i out))
    (when (and includes (or structs defines externs defns)) (terpri out))
    (dolist (s structs) (emit-struct-decl s out) (terpri out))
    (dolist (d defines)
      (let ((name (second d)) (val (third d)))
        (format out "static const ~a ~a = ~a;~%"
                (c-type (first (gethash name *globals*)))
                (c-name name)
                (if (stringp val) (format nil "\"~a\"" val) val))))
    (when (and defines (or externs defns)) (terpri out))
    ;; Externs: signatures are registered for type-checking; the C
    ;; prototype comes from the user's (include ...) header. We don't
    ;; emit our own extern proto because it would conflict on subtle
    ;; types (e.g., raylib uses `bool` not `int` for predicates).
    ;; Pre-register extern ret-types for the user-fn dispatch in lower-form.
    (dolist (e externs)
      (setf (get (second e) 'ret-type) (fourth e)))
    (let ((annotated (infer-program defns :externs externs)))
      (dolist (f annotated)
        (destructuring-bind (_d name _params ret-type &rest _body) f
          (declare (ignore _d _params _body))
          (setf (get name 'ret-type) ret-type)))
      (let ((fns (mapcar (lambda (f)
                           (let ((fn (lower-defn f)))
                             (insert-releases fn)
                             (rewrite-jump-to-ret fn)
                             (prune-unreachable fn)
                             fn))
                         annotated)))
        (dolist (fn fns) (emit-c-proto fn out))
        (when fns (terpri out))
        (dolist (fn fns) (emit-c-fn fn out) (terpri out))))))
