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
    (dolist (s extern-structs)
      (setf (gethash (second s) *struct-fields*)
            (normalize-struct-fields (cddr s))))
    (dolist (d defines)
      (let* ((name (second d)) (val (third d))
             (ty (cond ((integerp val) :int)
                       ((stringp val)  :cstr)
                       (t :int))))
        (setf (gethash name *globals*) (list ty val))))
    (dolist (s structs)
      (setf (gethash (second s) *struct-fields*)
            (normalize-struct-fields (cddr s))))
    (dolist (e externs)
      (setf (get (second e) 'ret-type) (fourth e)))
    ;; Lower defns first so we can detect Value usage before emitting headers.
    (let* ((annotated (infer-program defns :externs externs)))
      (dolist (f annotated)
        (destructuring-bind (_d name _params ret-type &rest _body) f
          (declare (ignore _d _params _body))
          (setf (get name 'ret-type) ret-type)))
      (let* ((*uses-value* nil)
             (fns (mapcar (lambda (f)
                            (let ((fn (lower-defn f)))
                              (insert-releases fn)
                              (rewrite-jump-to-ret fn)
                              (prune-unreachable fn)
                              fn))
                          annotated))
             (body-buf (make-string-output-stream))
             (proto-buf (make-string-output-stream)))
        ;; Render bodies + protos to buffers (this also updates *uses-value*).
        (dolist (fn fns) (emit-c-proto fn proto-buf))
        (dolist (fn fns) (emit-c-fn fn body-buf) (terpri body-buf))
        ;; Now emit the final output: includes (incl. value.h if needed),
        ;; structs, defines, then the buffered protos + bodies.
        (dolist (i includes) (emit-include i out))
        (when (or *uses-value*) (format out "#include \"value.h\"~%"))
        (when (or includes *uses-value*) (terpri out))
        (dolist (s structs) (emit-struct-decl s out) (terpri out))
        (dolist (d defines)
          (let ((name (second d)) (val (third d)))
            (format out "static const ~a ~a = ~a;~%"
                    (c-type (first (gethash name *globals*)))
                    (c-name name)
                    (if (stringp val) (format nil "\"~a\"" val) val))))
        (when defines (terpri out))
        (write-string (get-output-stream-string proto-buf) out)
        (when fns (terpri out))
        (write-string (get-output-stream-string body-buf) out)))))
