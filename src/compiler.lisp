;;;; Top-level: compose lower → arc → peephole into compile-defn /
;;;; compile-program.

(in-package :sysp-ir)

(defun compile-defn (form)
  "(defn name (params...) ret-type body...) → fully-optimized ir-fn"
  (let ((fn (lower-defn form)))
    (insert-releases fn)
    (rewrite-jump-to-ret fn)
    (prune-unreachable fn)
    fn))

(defun compile-and-emit (form &optional (out t))
  (emit-c-fn (compile-defn form) out))

(defun compile-program (forms &optional (out t))
  "Compile a list of (defn ...) forms together. Pre-registers each fn's
   return type so cross-references resolve, then emits prototypes + bodies."
  (dolist (f forms)
    (destructuring-bind (_d name _params ret-type &rest _body) f
      (declare (ignore _d _params _body))
      (setf (get name 'ret-type) ret-type)))
  (let ((fns (mapcar #'compile-defn forms)))
    (dolist (fn fns) (emit-c-proto fn out))
    (terpri out)
    (dolist (fn fns) (emit-c-fn fn out) (terpri out))))
