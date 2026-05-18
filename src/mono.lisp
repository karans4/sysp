;;;; Monomorphization: SCC over the call graph + per-call-site specialization
;;;; of poly fns and generic structs.
;;;;
;;;; infer-program (in infer.lisp) drives this — once the SCC pass has
;;;; produced a forall scheme for each user fn, monomorphize-program walks
;;;; concrete defns, materializes a specialized clone for each unique
;;;; (poly-name, concrete-args) pair, and rewrites call/ctor heads to the
;;;; mangled name. The rest of the pipeline (lower → emit) sees only
;;;; concrete types from then on.

(in-package :sysp-ir)

;;; --- call-graph + SCC -------------------------------------------------

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

;;; --- monomorphization state + name mangling --------------------------

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

;;; --- the mono walk ---------------------------------------------------

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
    ((eq (first form) 'get)
     ;; Gettable override → rewrite to a plain call to the impl fn;
     ;; otherwise leave it for lower's struct-field default.
     (dolist (a (rest form)) (mono-walk a env))
     (let ((m (trait-impl-fn "Gettable" "get"
                             (resolve-type (infer (second form) env)))))
       (when m (rplaca form m))))
    ((eq (first form) 'set!)
     (let ((target (second form)))
       (cond
         ((and (consp target) (eq (first target) 'get))
          (let ((obj (second target)) (key (third target)) (val (third form)))
            (mono-walk obj env) (mono-walk key env) (mono-walk val env)
            (let ((m (trait-impl-fn "Settable" "set"
                                    (resolve-type (infer obj env)))))
              (when m
                ;; (set! (get o k) v) → (set_<ty> o k v)
                (setf (car form) m
                      (cdr form) (list obj key val))))))
         (t (mono-walk (third form) env)))))
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
    ;; Trait method call: rewrite head to the concrete impl resolved by
    ;; self's type. After this the head is an ordinary concrete fn.
    ((trait-method-name-p (first form))
     (dolist (a (rest form)) (mono-walk a env))
     (let ((m (resolve-trait-call (first form) (second form) env)))
       (rplaca form m)
       ;; A generic impl method is an ordinary poly fn — let the
       ;; existing per-call-site monomorphization specialize it.
       (when (forall-p (gethash m *fn-sigs*))
         (mono-walk-poly-call form env))))
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
