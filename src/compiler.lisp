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

(defun compile-program (forms &optional (out t))
  "Compile a top-level program: (include ...), (defstruct ...), (extern ...),
   (defn ...). Output: includes → struct typedefs → extern protos → defn
   protos → defn bodies."
  (let (includes structs externs defns)
    (dolist (f forms)
      (case (first f)
        (include   (push f includes))
        (defstruct (push f structs))
        (extern    (push f externs))
        (defn      (push f defns))
        (t (error "compile-program: unknown top-level form ~A" (first f)))))
    (setf includes (nreverse includes)
          structs  (nreverse structs)
          externs  (nreverse externs)
          defns    (nreverse defns))
    ;; Register all structs first so types resolve.
    (dolist (s structs)
      (setf (gethash (second s) *struct-fields*)
            (normalize-struct-fields (cddr s))))
    (dolist (i includes) (emit-include i out))
    (when (and includes (or structs externs defns)) (terpri out))
    (dolist (s structs) (emit-struct-decl s out) (terpri out))
    (dolist (e externs) (emit-extern-proto e out))
    (when (and externs defns) (terpri out))
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
