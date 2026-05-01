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
  "Compile a list of (defn ...) forms together. Runs HM inference across
   the whole program (handles mutual recursion), then lowers each defn,
   emits prototypes + bodies."
  (let ((annotated (infer-program forms)))
    ;; Pre-register ret-types so the lower-form default-call can resolve.
    (dolist (f annotated)
      (destructuring-bind (_d name _params ret-type &rest _body) f
        (declare (ignore _d _params _body))
        (setf (get name 'ret-type) ret-type)))
    (let ((fns (mapcar (lambda (f)
                         ;; lower then run passes (compile-defn would re-infer).
                         (let ((fn (lower-defn f)))
                           (insert-releases fn)
                           (rewrite-jump-to-ret fn)
                           (prune-unreachable fn)
                           fn))
                       annotated)))
      (dolist (fn fns) (emit-c-proto fn out))
      (terpri out)
      (dolist (fn fns) (emit-c-fn fn out) (terpri out)))))
