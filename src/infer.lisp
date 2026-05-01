;;;; Hindley-Milner type inference (monomorphic).
;;;;
;;;; Surface form (possibly with naked params / no ret-type) → fully-annotated
;;;; form ready for lower-defn. Nothing below this layer needs to change.
;;;;
;;;; Type language:
;;;;   :int :bool :unit :string                         -- concrete
;;;;   (:fn (T1 T2 ...) Tret)                           -- function type
;;;;   (:tvar N)                                        -- type variable

(in-package :sysp-ir)

(defvar *subst*)          ; hash table: tvar id → type
(defvar *tvar-counter*)
(defvar *fn-sigs*)        ; sym → (:fn arg-types ret-type)

(defun fresh-tvar ()
  (list :tvar (incf *tvar-counter*)))

(defun tvar-p (ty) (and (consp ty) (eq (first ty) :tvar)))

(defun resolve-type (ty)
  "Follow tvar chain to a (possibly partially) concrete type."
  (cond
    ((tvar-p ty)
     (let ((sub (gethash (second ty) *subst*)))
       (if sub (resolve-type sub) ty)))
    ((and (consp ty) (eq (first ty) :fn))
     (list :fn (mapcar #'resolve-type (second ty)) (resolve-type (third ty))))
    (t ty)))

(defun unify (t1 t2)
  (let ((r1 (resolve-type t1)) (r2 (resolve-type t2)))
    (cond
      ((equal r1 r2) t)
      ((tvar-p r1) (setf (gethash (second r1) *subst*) r2))
      ((tvar-p r2) (setf (gethash (second r2) *subst*) r1))
      ((and (consp r1) (consp r2)
            (eq (first r1) :fn) (eq (first r2) :fn))
       (unless (= (length (second r1)) (length (second r2)))
         (error "infer: arity mismatch ~A vs ~A" r1 r2))
       (mapc #'unify (second r1) (second r2))
       (unify (third r1) (third r2)))
      (t (error "infer: type mismatch ~A vs ~A" r1 r2)))))

;;; --- inference walk ---

(defun infer (e env)
  (cond
    ((integerp e) :int)
    ((stringp e)  :string)
    ((eq e t)     :bool)
    ((null e)     :bool)
    ((symbolp e)
     (let ((b (assoc e env)))
       (unless b (error "infer: unbound symbol ~A" e))
       (cdr b)))
    ((consp e) (infer-form (car e) (cdr e) env))
    (t (error "infer: cannot type ~A" e))))

(defgeneric infer-form (head args env))

(defmethod infer-form ((head (eql '+)) args env) (infer-binop :int :int args env))
(defmethod infer-form ((head (eql '-)) args env) (infer-binop :int :int args env))
(defmethod infer-form ((head (eql '*)) args env) (infer-binop :int :int args env))
(defmethod infer-form ((head (eql '/)) args env) (infer-binop :int :int args env))
(defmethod infer-form ((head (eql '<)) args env) (infer-binop :int :bool args env))
(defmethod infer-form ((head (eql '>)) args env) (infer-binop :int :bool args env))

(defmethod infer-form ((head (eql '=)) args env)
  ;; = polymorphic-ish: same type both sides, returns :bool.
  (unify (infer (first args) env) (infer (second args) env))
  :bool)

(defun infer-binop (arg-ty ret-ty args env)
  (dolist (a args) (unify arg-ty (infer a env)))
  ret-ty)

(defmethod infer-form ((head (eql 'string-concat)) args env)
  (dolist (a args) (unify :string (infer a env)))
  :string)
(defmethod infer-form ((head (eql 'string-len)) args env)
  (unify :string (infer (first args) env))
  :int)
(defmethod infer-form ((head (eql 'string-print)) args env)
  (unify :string (infer (first args) env))
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
    (unless tgt-ty (error "infer: set! on unbound ~A" target))
    (unify tgt-ty (infer (second args) env))
    :unit))

(defmethod infer-form ((head (eql 'while)) args env)
  (unify (infer (first args) env) :bool)
  (dolist (b (rest args)) (infer b env))
  :unit)

(defmethod infer-form (head args env)
  ;; Default: function call to a registered fn (or runtime fn known by name).
  (let ((sig (and *fn-sigs* (gethash head *fn-sigs*))))
    (unless sig
      (error "infer: unknown function ~A. Either declare it via defn or add to runtime."
             head))
    (let ((arg-tys (second sig))
          (ret-ty  (third sig)))
      (unless (= (length arg-tys) (length args))
        (error "infer: ~A expects ~D args, got ~D" head (length arg-tys) (length args)))
      (loop for a in args for at in arg-tys
            do (unify at (infer a env)))
      ret-ty)))

;;; --- defn / program drivers ---

(defun type-annotation-p (x)
  "Heuristic: distinguish a type form from a body form. Types are keywords
   like :int, :string, or a (:fn ...) form."
  (or (and (keywordp x) (member x '(:int :bool :unit :string)))
      (and (consp x) (eq (first x) :fn))))

(defun split-defn-shape (rest-of-form)
  "Given the part after 'name' in (defn name PARAMS [ret] BODY...), return
   (values params ret-type body) where ret-type may be nil (infer)."
  (let ((params (first rest-of-form))
        (after (rest rest-of-form)))
    (cond
      ((and after (type-annotation-p (first after)))
       (values params (first after) (rest after)))
      (t
       (values params nil after)))))

(defun param-name-and-tvar (p)
  "p is either a naked symbol (or single-element list) or (name :type)."
  (cond
    ((symbolp p)               (list p (fresh-tvar)))
    ((and (consp p) (= (length p) 1)) (list (first p) (fresh-tvar)))
    ((and (consp p) (= (length p) 2)) (list (first p) (second p)))
    (t (error "infer: bad param spec ~A" p))))

(defun defaulting (ty)
  "If a tvar remains after solving, default to :int with a warning. Avoids
   emitting (:tvar N) into the C output."
  (let ((r (resolve-type ty)))
    (cond
      ((tvar-p r) (warn "unconstrained type variable, defaulting to :int") :int)
      ((and (consp r) (eq (first r) :fn))
       (list :fn (mapcar #'defaulting (second r)) (defaulting (third r))))
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

(defun infer-program (forms)
  "Annotate all defns in a program. Handles mutual recursion."
  (let ((*subst* (make-hash-table))
        (*tvar-counter* 0)
        (*fn-sigs* (make-hash-table))
        (info nil))
    ;; Pass 1: register each fn's signature with tvars where unannotated.
    (dolist (f forms)
      (destructuring-bind (defn-sym name &rest rest) f
        (declare (ignore defn-sym))
        (multiple-value-bind (params ret-annot body) (split-defn-shape rest)
          (let* ((typed-params (mapcar #'param-name-and-tvar params))
                 (param-types (mapcar #'second typed-params))
                 (ret-type (or ret-annot (fresh-tvar))))
            (setf (gethash name *fn-sigs*) (list :fn param-types ret-type))
            (push (list name typed-params ret-type body) info)))))
    (setf info (nreverse info))
    ;; Pass 2: infer each body.
    (dolist (e info)
      (destructuring-bind (name typed-params ret-type body) e
        (declare (ignore name))
        (let ((env (mapcar (lambda (p) (cons (first p) (second p))) typed-params)))
          (let (last-ty)
            (dolist (b body) (setf last-ty (infer b env)))
            (when last-ty (unify ret-type last-ty))))))
    ;; Pass 3: produce annotated forms.
    (mapcar (lambda (e)
              (destructuring-bind (name typed-params ret-type body) e
                (let ((rp (mapcar (lambda (p)
                                    (list (first p) (defaulting (second p))))
                                  typed-params))
                      (rt (defaulting ret-type)))
                  (list* 'defn name rp rt body))))
            info)))
