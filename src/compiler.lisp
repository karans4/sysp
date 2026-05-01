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

(defparameter *interp-binary* "runtime/interp")

(defun expand-macros (forms)
  "If any form is a (defmacro ...), spawn the interpreter, register all
   defmacros, and request macroexpand for every other form. Returns the
   transformed form list. If no defmacros are present, returns forms
   unchanged (no subprocess overhead)."
  (let ((macros nil) (others nil))
    (dolist (f forms)
      (if (and (consp f) (eq (first f) 'defmacro))
          (push f macros)
          (push f others)))
    (setf macros (nreverse macros) others (nreverse others))
    (cond
      ((null macros) forms)
      (t (run-interp-expand macros others)))))

(defun run-interp-expand (defmacros others)
  (unless (probe-file *interp-binary*)
    (error "expand-macros: ~a not found. Build via runtime/build-interp.sh"
           *interp-binary*))
  (let* ((proc (sb-ext:run-program *interp-binary* nil
                                   :wait nil
                                   :input :stream
                                   :output :stream
                                   :error :output))
         (in  (sb-ext:process-input proc))
         (out (sb-ext:process-output proc)))
    (unwind-protect
         (progn
           ;; Register all macros first.
           (dolist (m defmacros) (format in "~s~%" m))
           (force-output in)
           ;; Drain any output (defmacro emits nothing, but be safe).
           (loop while (listen out) do (read-char out))
           ;; For each non-macro form, ask for the macroexpand.
           (let ((result nil))
             (dolist (o others)
               (format in "(macroexpand '~s)~%" o)
               (force-output in)
               (push (read out nil :eof) result))
             (nreverse result)))
      (close in)
      (sb-ext:process-wait proc)
      (sb-ext:process-close proc))))

(defun compile-program (forms &optional (out t))
  "Compile a top-level program: (use ...), (include ...), (defstruct ...),
   (extern-struct ...), (extern ...), (define ...), (enum ...), (defn ...)."
  (setf forms (expand-uses forms))
  (setf forms (expand-macros forms))
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
             (*lambda-fns* nil)
             (*lambda-structs* nil)
             (user-fns (mapcar (lambda (f)
                                 (let ((fn (lower-defn f)))
                                   (insert-releases fn)
                                   (rewrite-jump-to-ret fn)
                                   (prune-unreachable fn)
                                   fn))
                               annotated))
             ;; Now finalize lambda-synthesized fns. They were lowered at
             ;; lambda-site time; run the same passes on each.
             (lambda-fns (mapcar (lambda (fn)
                                   (insert-releases fn)
                                   (rewrite-jump-to-ret fn)
                                   (prune-unreachable fn)
                                   fn)
                                 (nreverse *lambda-fns*)))
             (fns (append lambda-fns user-fns))
             (extra-structs (nreverse *lambda-structs*))
             (body-buf (make-string-output-stream))
             (proto-buf (make-string-output-stream)))
        (dolist (fn fns) (emit-c-proto fn proto-buf))
        (dolist (fn fns) (emit-c-fn fn body-buf) (terpri body-buf))
        (dolist (i includes) (emit-include i out))
        (when *uses-value* (format out "#include \"value.h\"~%"))
        (when (or includes *uses-value*) (terpri out))
        (dolist (s structs)        (emit-struct-decl s out) (terpri out))
        (dolist (s extra-structs)  (emit-struct-decl s out) (terpri out))
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
