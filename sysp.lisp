;;;; sysp.lisp — Bootstrap compiler for Systems Lisp
;;;; Compiles .sysp files to C

(defpackage :sysp
  (:use :cl))
(in-package :sysp)

;;; === Types ===
;;; Types are s-expressions:
;;;   Primitives: :int, :float, :bool, :void, :str, :char, :value, :nil, ...
;;;   Compound:   (:ptr :int), (:fn (:int :int) :int), (:array :int 10)
;;;              (:struct "Point"), (:enum "Color"), (:list :int)
;;;              (:cons :int :str), (:vector :float), (:tuple :int :str)
;;;              (:variadic :int)
;;;   Type vars:  (:? 1), (:? 2), ...

;; Compound type constructors
(defun make-ptr-type (pointee) `(:ptr ,pointee))
(defun make-list-type (elem-type) `(:list ,elem-type))
(defun make-variadic-type (elem-type) `(:variadic ,elem-type))
(defun make-cons-type (car-type cdr-type) `(:cons ,car-type ,cdr-type))
(defun make-struct-type (name) `(:struct ,name))
(defun make-enum-type (name) `(:enum ,name))
(defun make-fn-type (arg-types ret-type) `(:fn ,arg-types ,ret-type))
(defun make-vector-type (elem-type) `(:vector ,elem-type))
(defun make-tuple-type (elem-types) `(:tuple ,@elem-types))
(defun make-array-type (elem-type size) `(:array ,elem-type ,size))
(defun make-rc-type (inner) `(:rc ,inner))
(defun rc-type-p (tp) (and (consp tp) (eq (car tp) :rc)))
(defun rc-inner-type (tp) (second tp))

;; Future types: (:future T spawn-id) — typed future from spawn
(defun make-future-type (inner spawn-id) `(:future ,inner ,spawn-id))
(defun future-type-p (tp) (and (consp tp) (eq (car tp) :future)))
(defun future-inner-type (tp) (second tp))
(defun future-spawn-id (tp) (third tp))

;; Union types: (:union :int :str) — sorted, deduped, flattened
(defun make-union-type (variants)
  "Create a normalized union type from a list of variant types.
   Sorts alphabetically by mangle name, deduplicates, flattens nested unions.
   Single-variant unions collapse to the variant itself."
  (let ((flat nil))
    ;; Flatten nested unions
    (dolist (v variants)
      (if (and (consp v) (eq (car v) :union))
          (dolist (inner (cdr v)) (push inner flat))
          (push v flat)))
    ;; Deduplicate
    (setf flat (remove-duplicates flat :test #'equal))
    ;; Single variant → collapse
    (when (= (length flat) 1)
      (return-from make-union-type (first flat)))
    ;; Sort by mangled name for canonical ordering
    (setf flat (sort flat #'string<
                     :key (lambda (tp) (mangle-type-name tp))))
    `(:union ,@flat)))

(defun union-type-p (tp) (and (consp tp) (eq (car tp) :union)))
(defun union-variants (tp) (cdr tp))

;; Accessors for compound types
(defun fn-type-args (ft) (second ft))
(defun fn-type-ret (ft) (third ft))

(defun type-kind (tp)
  "Extract the kind/tag of a type: :int -> :int, (:ptr :int) -> :ptr"
  (if (consp tp) (car tp) tp))

(defun type-equal-p (a b)
  "Check if two types are equal"
  (equal a b))

;;; === Type Inference (Hindley-Milner) ===

;; Type variable counter
(defvar *tvar-counter* 0)

;; Temp variable counter for statement lifting
(defvar *tmp-counter* 0)

;; Pending statements to emit before current expression
(defvar *pending-stmts* nil)

;; Type variable bindings: hash table from tvar-id -> type
(defvar *tvar-bindings* (make-hash-table))

;; Create a fresh type variable: (:? 1), (:? 2), ...
(defun make-tvar ()
  (let ((id (incf *tvar-counter*)))
    `(:? ,id)))

(defun tvar-p (tp)
  (and (consp tp) (eq (car tp) :?)))

(defun tvar-id (tv) (second tv))

(defun tvar-bound (tv)
  (gethash (tvar-id tv) *tvar-bindings*))

(defun tvar-bind! (tv type)
  (setf (gethash (tvar-id tv) *tvar-bindings*) type))

;; Follow type variable chains to find the concrete type (or unbound tvar)
(defun resolve-type (tp)
  (if (and (tvar-p tp) (tvar-bound tp))
      (let ((resolved (resolve-type (tvar-bound tp))))
        ;; Path compression
        (tvar-bind! tp resolved)
        resolved)
      tp))

;; Occurs check: does tvar `tv` appear anywhere in `tp`?
(defun occurs-in-p (tv tp)
  (let ((tp (resolve-type tp)))
    (cond
      ((tvar-p tp) (= (tvar-id tv) (tvar-id tp)))
      ((consp tp)
       (some (lambda (p) (occurs-in-p tv p)) (cdr tp)))
      (t nil))))

;; Numeric type checking and ranking for C-like promotion
(defun numeric-type-p (tp)
  "Check if a type is numeric (can participate in promotion)."
  (member (resolve-type tp) '(:int :i8 :i16 :i32 :i64
                               :uint :u8 :u16 :u32 :u64
                               :long :long-long :ulong :ulong-long
                               :char :uchar :short :ushort
                               :float :double :f32 :f64
                               :size :ptrdiff :intptr :uintptr)))


;; Unify two types. Returns t on success, nil on failure.
(defun unify (t1 t2)
  (let ((t1 (resolve-type t1))
        (t2 (resolve-type t2)))
    (cond
      ;; Same type (equal handles both atoms and lists)
      ((equal t1 t2) t)

      ;; Type variable on left: bind it
      ((tvar-p t1)
       (if (occurs-in-p t1 t2)
           nil ; infinite type
           (progn (tvar-bind! t1 t2) t)))

      ;; Type variable on right: bind it
      ((tvar-p t2)
       (if (occurs-in-p t2 t1)
           nil
           (progn (tvar-bind! t2 t1) t)))

      ;; :value unifies with anything (it's the Any type)
      ((eq t1 :value) t)
      ((eq t2 :value) t)

      ;; Same compound kind: unify params pairwise
      ((and (consp t1) (consp t2)
            (eq (car t1) (car t2))
            (= (length t1) (length t2)))
       (every #'unify (cdr t1) (cdr t2)))

      ;; List/nil compatibility
      ((and (consp t1) (eq (car t1) :list) (eq t2 :nil)) t)
      ((and (consp t2) (eq (car t2) :list) (eq t1 :nil)) t)

      ;; (:list T) unifies with (:cons T (:list T))
      ((and (consp t1) (eq (car t1) :list)
            (consp t2) (eq (car t2) :cons))
       (and (unify (second t1) (second t2))       ; elem = car
            (unify t1 (third t2))))                ; list = cdr
      ((and (consp t2) (eq (car t2) :list)
            (consp t1) (eq (car t1) :cons))
       (and (unify (second t2) (second t1))
            (unify t2 (third t1))))

      ;; Variadic is incompatible with list
      ((or (and (consp t1) (eq (car t1) :variadic))
           (and (consp t2) (eq (car t2) :variadic)))
       nil)

      ;; Numeric promotion
      ((and (numeric-type-p t1) (numeric-type-p t2)) t)

      ;; Incompatible
      (t nil))))

;; Generalize: replace free tvars with quantified vars
;; Returns a type scheme: (:scheme (tvar-ids...) type)
(defun free-tvars (tp &optional (seen nil))
  "Collect all unbound type variable IDs in a type."
  (let ((tp (resolve-type tp)))
    (cond
      ((tvar-p tp)
       (if (member (tvar-id tp) seen) nil (list (tvar-id tp))))
      ((consp tp)
       (reduce #'append
               (mapcar (lambda (p) (free-tvars p seen))
                       (cdr tp))
               :initial-value nil))
      (t nil))))

(defun generalize (tp env-tvars)
  "Generalize a type by quantifying tvars not in env-tvars."
  (let ((free (remove-duplicates
               (set-difference (free-tvars tp) env-tvars))))
    (if free
        (list :scheme free tp)
        tp)))

(defun instantiate (scheme)
  "Instantiate a type scheme with fresh tvars."
  (if (and (consp scheme) (eq (car scheme) :scheme))
      (let* ((quantified (second scheme))
             (body (third scheme))
             (subst (mapcar (lambda (id) (cons id (make-tvar))) quantified)))
        (apply-subst body subst))
      scheme))

(defun apply-subst (tp subst)
  "Apply substitution to type."
  (let ((tp (resolve-type tp)))
    (cond
      ((tvar-p tp)
       (let ((entry (assoc (tvar-id tp) subst)))
         (if entry (cdr entry) tp)))
      ((consp tp)
       (cons (car tp)
             (mapcar (lambda (p) (apply-subst p subst)) (cdr tp))))
      (t tp))))

;; Reset inference state (call before each compilation unit)
(defun reset-inference ()
  (setf *tvar-counter* 0)
  (clrhash *tvar-bindings*))

;;; === Constraint Generation (Phase 2: AST → Type Constraints) ===

;; Type environment for inference: alist of (name . type-or-scheme)
(defvar *infer-env* nil)

(defun infer-env-lookup (name)
  (let ((entry (assoc name *infer-env* :test #'equal)))
    (when entry
      (let ((tp (cdr entry)))
        (if (and (consp tp) (eq (car tp) :scheme))
            (instantiate tp)
            tp)))))

(defun infer-env-bind (name type)
  (push (cons name type) *infer-env*))

;; Resolve a type variable to its final concrete type, defaulting unbound tvars to :int
(defun resolve-or-default (tp)
  (let ((resolved (resolve-type tp)))
    (cond
      ((tvar-p resolved) :int)  ; unbound tvar defaults to int
      ((consp resolved)
       (cons (car resolved)
             (mapcar #'resolve-or-default (cdr resolved))))
      (t resolved))))

;; Infer the type of an expression, generating constraints via unification.
;; Returns the inferred type (may contain tvars until resolution).
(defun infer-expr (form)
  "Walk an expression form and return its inferred type."
  (cond
    ((null form) :nil)  ; nil is the empty list type
    ((characterp form) :char)
    ((integerp form)
     ;; Infer integer type based on value range (C99 rules)
     (cond
       ((<= -2147483648 form 2147483647) :int)
       ((<= form 9223372036854775807) :long-long)
       (t :ulong-long)))
    ((floatp form) :float)
    ((stringp form) :str)
    ((symbolp form)
     (let ((name (string form)))
       (cond
         ((string-equal name "true") :bool)
         ((string-equal name "false") :bool)
         ((string-equal name "null") (make-ptr-type :void))
         (t (or (infer-env-lookup name) (make-tvar))))))
    ((listp form) (infer-list form))
    (t :int)))

(defun infer-list (form)
  "Infer the type of a list expression."
  (let ((head (first form)))
    ;; Handle non-symbol heads (e.g., numbers in quoted lists)
    (unless (symbolp head)
      (return-from infer-list (make-tvar)))
    (cond
      ;; Arithmetic: operands must unify, result = operand type
      ((member (string head) '("+" "-" "*" "/" "%" "mod") :test #'string-equal)
       (if (and (= (length form) 2) (string-equal (string head) "-"))
           ;; Unary minus
           (infer-expr (second form))
           ;; Binary op: infer both sides, try to unify, return result
           (let ((lt (infer-expr (second form)))
                 (rt (infer-expr (third form))))
             (unify lt rt)
             lt)))

      ;; Comparison: operands unify, result is bool
      ((member (string head) '("<" ">" "<=" ">=" "==" "!=") :test #'string-equal)
       (let ((lt (infer-expr (second form)))
             (rt (infer-expr (third form))))
         (unify lt rt)
         :bool))

      ;; Logical: result is bool
      ((member (string head) '("and" "or" "not") :test #'string-equal) :bool)

      ;; Bitwise: operands are int, result is int
      ((member (string head) '("bit-and" "bit-or" "bit-xor" "bit-not" "shl" "shr")
               :test #'string-equal) :int)

      ;; if expression: unify both branches
      ((sym= head "if")
       (infer-expr (second form))  ; condition
       (let ((then-type (infer-expr (third form))))
         (when (>= (length form) 5)  ; has else branch
           (let ((else-type (infer-expr (fifth form))))
             (unify then-type else-type)))
         then-type))

      ;; do block: type of last expression
      ((sym= head "do")
       (let ((result :int))
         (dolist (subform (cdr form))
           (setf result (infer-expr subform)))
         result))

      ;; vector: all elements unify, result is vector of element type
      ((sym= head "vector")
       (let ((elem-type (make-tvar)))
         (dolist (e (cdr form))
           (unify elem-type (infer-expr e)))
         (make-vector-type elem-type)))

      ;; vector-ref: result is element type
      ((sym= head "vector-ref")
       (let* ((vec-type (infer-expr (second form)))
              (elem-tvar (make-tvar))
              (expected-vec (make-vector-type elem-tvar)))
         (unify vec-type expected-vec)
         elem-tvar))

      ;; tuple: result is tuple of element types
      ((sym= head "tuple")
       (make-tuple-type (mapcar #'infer-expr (cdr form))))

      ;; tuple-ref: we can't statically know which element without evaluating index
      ((sym= head "tuple-ref")
       (make-tvar))

      ;; lambda: parse param types, infer body
      ((sym= head "lambda")
       (let* ((params-raw (second form))
              (rest (cddr form))
              (ret-ann (when (keywordp (first rest))
                         (prog1 (parse-type-annotation (first rest))
                           (setf rest (cdr rest)))))
              (body rest)
              (param-types nil)
              (old-env *infer-env*))
         ;; Parse params with tvars for unannotated
         (let ((lst (if (listp params-raw) (copy-list params-raw) nil)))
           (loop while lst do
             (let* ((name (string (pop lst)))
                    (type (if (and lst (keywordp (first lst)))
                              (let ((result (parse-type-from-list lst)))
                                (setf lst (cdr result))
                                (car result))
                              (make-tvar))))
               (push type param-types)
               (infer-env-bind name type))))
         (setf param-types (nreverse param-types))
         ;; Infer body type
         (let ((body-type :int))
           (dolist (f body)
             (setf body-type (infer-expr f)))
           (let ((ret-type (or ret-ann body-type)))
             ;; Restore env
             (setf *infer-env* old-env)
             (make-fn-type param-types ret-type)))))

      ;; nil? : returns bool
      ((sym= head "nil?") :bool)

      ;; cons: creates a cons cell
      ;; If cdr is a (:list T), result is (:list T) (homogeneous)
      ;; Otherwise result is (:cons car-type cdr-type)
      ((sym= head "cons")
       (let ((car-type (infer-expr (second form)))
             (cdr-type (infer-expr (third form))))
         (cond
           ;; If cdr is nil, create a new list
           ((eq (type-kind cdr-type) :nil)
            (make-list-type car-type))
           ;; If cdr is already a list of same type, extend it
           ((and (eq (type-kind cdr-type) :list)
                 (unify car-type (second cdr-type)))
            cdr-type)
           ;; Otherwise create an improper cons
           (t (make-cons-type car-type cdr-type)))))

      ;; car: extracts car from cons or list
      ((sym= head "car")
       (let ((cons-type (infer-expr (second form)))
             (elem-tvar (make-tvar)))
         (cond
           ;; If it's a list, return the element type
           ((eq (type-kind cons-type) :list)
            (second cons-type))
           ;; If it's a cons, return the car type
           ((eq (type-kind cons-type) :cons)
            (second cons-type))
           ;; Otherwise unify with expected and return element
           (t (unify cons-type (make-cons-type elem-tvar (make-tvar)))
              elem-tvar))))

      ;; cdr: extracts cdr from cons or list
      ((sym= head "cdr")
       (let ((cons-type (infer-expr (second form)))
             (cdr-tvar (make-tvar)))
         (cond
           ;; If it's a list, return (:list elem) or nil
           ((eq (type-kind cons-type) :list)
            cons-type)  ; (:list T) cdr is (:list T) or nil
           ;; If it's a cons, return the cdr type
           ((eq (type-kind cons-type) :cons)
            (third cons-type))
           ;; Otherwise unify with expected
           (t (unify cons-type (make-cons-type (make-tvar) cdr-tvar))
              cdr-tvar))))

      ;; list: creates a homogeneous list
      ((sym= head "list")
       (let ((elem-type (make-tvar)))
         (dolist (e (cdr form))
           (unify elem-type (infer-expr e)))
         (make-list-type elem-type)))

      ;; quote/quasiquote: for now return Value (could be smarter)
      ((member (string head) '("quote" "quasiquote") :test #'string-equal)
       :value)

      ;; Simple type returns
      ((sym= head "nil?") :bool)
      ((sym= head "null?") :bool)
      ((sym= head "sym") :value)
      ((sym= head "sym-eq?") :bool)
      ((sym= head "gensym") :value)

      ;; get: struct field access — need struct info
      ((sym= head "get")
       (make-tvar))  ; can't resolve without struct definition context

      ;; set!: returns the assigned type
      ((sym= head "set!")
       (infer-expr (third form)))

      ;; addr-of, deref, cast, sizeof
      ((sym= head "addr-of")
       (make-ptr-type (infer-expr (second form))))
      ((sym= head "deref")
       (let ((ptr-type (infer-expr (second form)))
             (elem-tvar (make-tvar)))
         (unify ptr-type (make-ptr-type elem-tvar))
         elem-tvar))
      ((sym= head "cast")
       (parse-type-annotation (second form)))
      ((sym= head "sizeof")
       :int)

      ;; Simple type returns for vector/array ops
      ((sym= head "vector-len") :int)
      ((sym= head "vector-set!") :void)
      ((sym= head "vector-push!") :void)
      ((sym= head "array-ref") (make-tvar))
      ((sym= head "array-set!") :void)
      ((sym= head "make-array") (make-tvar))

      ;; match: infer scrutinee, collect body types from all clauses, unify
      ((sym= head "match")
       (infer-expr (second form))  ; scrutinee
       (let ((body-type (make-tvar)))
         (dolist (clause (cddr form))
           (when (listp clause)
             (let ((clause-body (second clause)))
               (when clause-body
                 (unify body-type (infer-expr clause-body))))))
         body-type))

      ;; new: RC-managed heap allocation → (:rc (:struct T))
      ((sym= head "new")
       (let ((struct-name (string (second form))))
         (dolist (a (cddr form)) (infer-expr a))
         (make-rc-type (make-struct-type struct-name))))

      ;; ptr-alloc: raw pointer allocation → (:ptr T)
      ((sym= head "ptr-alloc")
       (make-ptr-type (parse-type-annotation (second form))))

      ;; ptr-deref: dereference → element type
      ((sym= head "ptr-deref") (make-tvar))

      ;; Function call: look up function type, unify args, return ret type
      (t (let* ((fn-name (string head))
                (fn-type (infer-env-lookup fn-name)))
           (if (and fn-type (eq (type-kind fn-type) :fn))
               ;; Known function: unify arguments
               (let ((arg-types (fn-type-args fn-type))
                     (ret-type (fn-type-ret fn-type)))
                 (loop for arg in (cdr form)
                       for expected in arg-types
                       do (let ((actual (infer-expr arg)))
                            (unify expected actual)))
                 ret-type)
               ;; Unknown function or constructor: infer args, return tvar
               (progn
                 (dolist (arg (cdr form))
                   (infer-expr arg))
                 (make-tvar))))))))

;; Infer types for a function body's statements (let bindings add to env)
(defun infer-stmt (form)
  "Walk a statement form, updating *infer-env* with let bindings."
  (when (listp form)
    (let ((head (first form)))
      (cond
        ;; let / let-mut: bind variable with inferred or annotated type
        ((or (sym= head "let") (sym= head "let-mut"))
         (let* ((name (string (second form)))
                (rest (cddr form))
                (type-ann (when (keywordp (first rest))
                            (prog1 (parse-type-annotation (first rest))
                              (setf rest (cdr rest)))))
                (init-form (first rest))
                (init-type (when init-form (infer-expr init-form)))
                (final-type (or type-ann init-type (make-tvar))))
           (when (and type-ann init-type)
             (unify type-ann init-type))
           (infer-env-bind name final-type)))

        ;; if/when/unless/while/for: recurse into sub-statements
        ((sym= head "if")
         (infer-expr (second form))
         (dolist (f (cddr form))
           (if (and (symbolp f) (string-equal (string f) "else"))
               nil
               (infer-stmt f))))
        ((or (sym= head "when") (sym= head "unless"))
         (infer-expr (second form))
         (dolist (f (cddr form))
           (infer-stmt f)))
        ((sym= head "while")
         (infer-expr (second form))
         (dolist (f (cddr form))
           (infer-stmt f)))
        ((sym= head "for")
         (dolist (f (cdddr form))
           (infer-stmt f)))
        ((sym= head "cond")
         (dolist (clause (cdr form))
           (when (listp clause)
             (infer-expr (first clause))
             (dolist (f (cdr clause))
               (infer-stmt f)))))

        ;; match: walk scrutinee and clause bodies
        ((sym= head "match")
         (infer-expr (second form))
         (dolist (clause (cddr form))
           (when (listp clause)
             (dolist (f (cdr clause))
               (infer-stmt f)))))

        ;; set!: unify target with value
        ((sym= head "set!")
         (let* ((target (second form))
                (target-type (if (symbolp target)
                                 (infer-env-lookup (string target))
                                 (infer-expr target)))
                (val-type (infer-expr (third form))))
           (when target-type
             (unify target-type val-type))))

        ;; return: infer the returned expression
        ((sym= head "return")
         (when (second form)
           (infer-expr (second form))))

        ;; print/println: just infer the expression
        ((or (sym= head "print") (sym= head "println"))
         (infer-expr (second form)))

        ;; printf: infer all arg expressions
        ((sym= head "printf")
         (dolist (arg (cddr form))
           (infer-expr arg)))

        ;; recur: infer arguments
        ((sym= head "recur")
         (dolist (arg (cdr form))
           (infer-expr arg)))

        ;; do block as statement
        ((sym= head "do")
         (dolist (f (cdr form))
           (infer-stmt f)))

        ;; Otherwise: treat as expression statement
        (t (infer-expr form))))))

;; Top-level inference for a function definition
(defun infer-defn (form)
  "Run type inference on a defn form. Updates *infer-env* with the function's type.
   Returns the inferred function type (with resolved tvars)."
  ;; Skip inference for polymorphic functions — they'll be inferred per instantiation
  (when (defn-is-poly-p form)
    (let ((name (string (second form))))
      (infer-env-bind name :poly)
      (return-from infer-defn :poly)))
  (let* ((name (string (second form)))
         (params-raw (third form))
         (rest-forms (cdddr form))
         (ret-annotation (when (keywordp (first rest-forms))
                           (prog1 (parse-type-annotation (first rest-forms))
                             (setf rest-forms (cdr rest-forms)))))
         (body-forms rest-forms)
         (old-env *infer-env*)
         (param-types nil))
    ;; Parse params: annotated get concrete types, unannotated get tvars
    ;; Handles: [x :int] or [items (:list :int)] or [x :int & rest :int]
    (let ((lst (if (listp params-raw) (copy-list params-raw) nil))
          (in-rest nil))
      (loop while lst do
        (let ((item (pop lst)))
          (cond
            ;; & indicates variadic rest args
            ((and (symbolp item) (string= (string item) "&"))
             (setf in-rest t))
            ;; Regular or rest parameter
            (t
             (let* ((pname (string item))
                    (type (if (and lst (or (keywordp (first lst)) (listp (first lst))))
                              (let ((result (parse-type-from-list lst)))
                                (setf lst (cdr result))
                                ;; Rest params in variadic position get :variadic wrapper
                                (if in-rest
                                    (make-variadic-type (car result))
                                    (car result)))
                              (make-tvar))))
               (push type param-types)
               (infer-env-bind pname type)))))))
    (setf param-types (nreverse param-types))
    ;; Infer body
    (let ((body-type :int))
      (dolist (f (butlast body-forms))
        (infer-stmt f))
      (when (car (last body-forms))
        (setf body-type (infer-expr (car (last body-forms)))))
      (let* ((ret-type (or ret-annotation body-type))
             (resolved-params (mapcar #'resolve-or-default param-types))
             (resolved-ret (resolve-or-default ret-type))
             (fn-type (make-fn-type resolved-params resolved-ret)))
        ;; Restore env but keep function binding
        (setf *infer-env* old-env)
        (infer-env-bind name fn-type)
        fn-type))))

;; Run inference on all top-level forms (pre-pass before compilation)
(defun infer-toplevel (forms)
  "Run type inference on all top-level forms. Populates *infer-env*."
  (setf *infer-env* nil)
  (reset-inference)
  (dolist (form forms)
    (when (listp form)
      (cond
        ((sym= (first form) "defn")
         (infer-defn form))
        ((sym= (first form) "struct")
         ;; Register struct constructor as a function type
         (let* ((name (string (second form)))
                (fields-raw (third form))
                (field-types nil))
           (let ((lst (if (listp fields-raw) (copy-list fields-raw) nil)))
             (loop while lst do
               (pop lst)  ; field name
               (when (and lst (keywordp (first lst)))
                 (let ((result (parse-type-from-list lst)))
                   (push (car result) field-types)
                   (setf lst (cdr result))))))
           (setf field-types (nreverse field-types))
           (infer-env-bind name (make-fn-type field-types (make-struct-type name)))))
        ((sym= (first form) "extern")
         ;; Register extern function type
         (let* ((name (string (second form)))
                (params-raw (third form))
                (rest (cdddr form))
                (ret-type (if (keywordp (first rest))
                              (parse-type-annotation (first rest))
                              :void))
                (param-types nil))
           (let ((lst (if (listp params-raw) (copy-list params-raw) nil)))
             (loop while lst do
               (pop lst)  ; param name
               (when (and lst (keywordp (first lst)))
                 (let ((result (parse-type-from-list lst)))
                   (push (car result) param-types)
                   (setf lst (cdr result))))))
           (setf param-types (nreverse param-types))
           (infer-env-bind name (make-fn-type param-types ret-type))))))))

;;; === Environment ===

(defstruct env
  (bindings nil)  ; alist of (name . type)
  (parent nil)
  (releases nil)  ; list of C variable names needing val_release at scope exit
  (mutables nil)  ; list of mutable variable names (from let-mut)
  (rc-releases nil)) ; list of (c-name . inner-type) for RC release at scope exit

(defun env-lookup (env name)
  (if (null env) nil
      (let ((found (assoc name (env-bindings env) :test #'equal)))
        (if found (cdr found)
            (env-lookup (env-parent env) name)))))

(defun env-bind (env name type)
  (push (cons name type) (env-bindings env))
  env)

(defun value-type-p (tp)
  "Does this type need refcount management?"
  (member (type-kind tp) '(:value :cons)))

(defun env-add-release (env c-name)
  "Record a variable name for release at scope exit"
  (push c-name (env-releases env)))

(defun env-mark-mutable (env name)
  "Mark a variable as mutable (from let-mut)"
  (push name (env-mutables env)))

(defun env-mutable-p (env name)
  "Check if a variable is mutable (walks parent chain)"
  (if (null env) nil
      (or (member name (env-mutables env) :test #'equal)
          (env-mutable-p (env-parent env) name))))

(defun emit-releases (env)
  "Generate release statements for all Value locals in this scope"
  (mapcar (lambda (name) (format nil "  val_release(~a);" name))
          (env-releases env)))

(defun env-add-rc-release (env c-name inner-type)
  "Record an RC variable for release at scope exit"
  (push (cons c-name inner-type) (env-rc-releases env)))

(defun emit-rc-releases (env)
  "Generate RC release statements for all RC locals in this scope"
  (mapcar (lambda (entry)
            (let ((c-name (car entry))
                  (inner-type (cdr entry)))
              (format nil "  _rc_~a_release(&~a);" (mangle-type-name inner-type) c-name)))
          (env-rc-releases env)))

;;; === Global State ===

(defvar *structs* (make-hash-table :test 'equal))
(defvar *enums* (make-hash-table :test 'equal))  ; name -> list of (variant-name . value)
(defvar *functions* nil)
(defvar *struct-defs* nil)
(defvar *lambda-counter* 0)
(defvar *temp-counter* 0)
(defvar *generated-types* (make-hash-table :test 'equal))
(defvar *type-decls* nil)
(defvar *forward-decls* nil)
(defvar *top-level-vars* nil)  ; top-level let/const
(defvar *lambda-forward-decls* nil)  ; forward declarations for lambdas
(defvar *global-env* (make-env))
(defvar *string-literals* nil)  ; collected string constants
(defvar *includes* nil)         ; extra #includes
(defvar *macros* (make-hash-table :test 'equal))  ; name -> expander function
(defvar *current-fn-name* nil)  ; for recur: name of function being compiled
(defvar *current-fn-params* nil) ; for recur: param names of current function
(defvar *symbol-table* (make-hash-table :test 'equal))  ; name -> integer ID
(defvar *symbol-counter* 0)
(defvar *sysp-gensym-counter* #x80000000)  ; gensyms start high to avoid collision
(defvar *type-aliases* (make-hash-table :test 'equal))  ; name -> type s-expr (deftype)
(defvar *name-overrides* (make-hash-table :test 'equal))  ; sysp name -> C name override
(defvar *included-files* (make-hash-table :test 'equal))  ; absolute path -> t (dedup for use)
(defvar *uses-value-type* nil)  ; emit Value/Cons preamble if true
;; Monomorphization state
(defvar *poly-fns* (make-hash-table :test #'equal))       ; name -> (params-raw ret-ann body-forms)
(defvar *mono-instances* (make-hash-table :test #'equal))  ; mangled-name -> t (already generated)
(defvar *macro-fns* (make-hash-table :test 'equal))  ; name -> (params body) for compile-time eval
(defvar *direct-fns* (make-hash-table :test 'equal))  ; names of defn/extern functions (direct call, not Fn)
(defvar *env-counter* 0)  ; counter for closure env structs
(defvar *interp-gensym-counter* 0)
(defvar *spawn-counter* 0)    ; counter for spawn sites
(defvar *uses-threads* nil)   ; emit #include <pthread.h> if true
(defvar *restart-counter* 0)  ; counter for restart-case sites
(defvar *handler-counter* 0)  ; counter for handler-bind sites
(defvar *handler-wrap-counter* 0) ; counter for handler wrapper functions
(defvar *uses-conditions* nil) ; emit condition system preamble if true

(defun intern-symbol (name)
  "Get or assign an integer ID for a named symbol"
  (or (gethash name *symbol-table*)
      (setf (gethash name *symbol-table*) (incf *symbol-counter*))))

(defun mangle-symbol-name (name)
  "Convert a symbol name to a valid C identifier for #defines"
  (with-output-to-string (s)
    (loop for ch across (string-upcase name) do
      (cond
        ((alphanumericp ch) (write-char ch s))
        ((char= ch #\-) (write-char #\_ s))
        ((char= ch #\+) (write-string "PLUS" s))
        ((char= ch #\-) (write-string "MINUS" s))
        ((char= ch #\*) (write-string "STAR" s))
        ((char= ch #\/) (write-string "SLASH" s))
        ((char= ch #\=) (write-string "EQ" s))
        ((char= ch #\<) (write-string "LT" s))
        ((char= ch #\>) (write-string "GT" s))
        ((char= ch #\!) (write-string "BANG" s))
        ((char= ch #\?) (write-string "P" s))
        (t (format s "_~2,'0X" (char-code ch)))))))

(defun lookup-enum-variant (name)
  "If name is an enum variant, return (enum-name . value). Else nil."
  (maphash (lambda (enum-name variants)
             (dolist (v variants)
               (when (string= (car v) name)
                 (return-from lookup-enum-variant (cons enum-name (cdr v))))))
           *enums*)
  nil)

;;; === Parsing ===

;;; === Custom Parser (tokenizer + recursive descent) ===
;;; Replaces CL's read for sysp source. Handles string escapes properly,
;;; preserves comments, tracks source locations.

;; Comments associated with top-level forms (form-index -> list of comment strings)
(defvar *form-comments* (make-hash-table))

;; Source locations: eq hash from form cons cells → (file line col)
(defvar *source-locations* (make-hash-table :test 'eq))

;; Comments to emit with functions/structs/vars
(defvar *function-comments* nil)  ; alist (name . (comment-strings...))
(defvar *struct-comments* nil)
(defvar *var-comments* nil)

;; Parser state
(defstruct pstate
  (source "" :type string)
  (pos 0 :type fixnum)
  (line 1 :type fixnum)
  (col 1 :type fixnum)
  (file "" :type string)
  (comments nil))  ; list of (line . text) for pending comments

(defun ps-eof-p (ps)
  (>= (pstate-pos ps) (length (pstate-source ps))))

(defun ps-peek (ps)
  (if (ps-eof-p ps) nil
      (char (pstate-source ps) (pstate-pos ps))))

(defun ps-advance (ps)
  "Advance one character, updating line/col."
  (let ((c (char (pstate-source ps) (pstate-pos ps))))
    (incf (pstate-pos ps))
    (if (char= c #\Newline)
        (progn (incf (pstate-line ps)) (setf (pstate-col ps) 1))
        (incf (pstate-col ps)))
    c))

(defun ps-skip-whitespace (ps)
  "Skip whitespace and commas (commas are whitespace in sysp). Collect comments."
  (loop while (not (ps-eof-p ps)) do
    (let ((c (ps-peek ps)))
      (cond
        ((member c '(#\Space #\Tab #\Newline #\Return #\,))
         (ps-advance ps))
        ((char= c #\;)
         ;; Comment: collect text until end of line
         (let ((line (pstate-line ps))
               (text (make-array 0 :element-type 'character :adjustable t :fill-pointer 0)))
           (loop while (and (not (ps-eof-p ps)) (not (char= (ps-peek ps) #\Newline)))
                 do (vector-push-extend (ps-advance ps) text))
           (push (cons line (coerce text 'string)) (pstate-comments ps))))
        (t (return))))))

(defun ps-read-string (ps)
  "Read a double-quoted string with proper escape handling."
  (ps-advance ps)  ; consume opening "
  (let ((buf (make-array 0 :element-type 'character :adjustable t :fill-pointer 0)))
    (loop
      (when (ps-eof-p ps) (error "sysp parser: unterminated string at line ~d" (pstate-line ps)))
      (let ((c (ps-advance ps)))
        (cond
          ((char= c #\") (return (coerce buf 'string)))
          ((char= c #\\)
           (when (ps-eof-p ps) (error "sysp parser: unterminated escape in string"))
           (let ((esc (ps-advance ps)))
             (vector-push-extend
              (case esc
                (#\n #\Newline)
                (#\t #\Tab)
                (#\\ #\\)
                (#\" #\")
                (#\0 (code-char 0))
                (#\r #\Return)
                (otherwise esc))
              buf)))
          (t (vector-push-extend c buf)))))))

(defun ps-symbol-char-p (c)
  "Is c a valid sysp symbol character?"
  (and c (not (member c '(#\( #\) #\[ #\] #\" #\; #\Space #\Tab #\Newline #\Return #\,)))))

(defun ps-read-atom (ps)
  "Read a symbol, keyword, or number."
  (let ((buf (make-array 0 :element-type 'character :adjustable t :fill-pointer 0)))
    (loop while (and (not (ps-eof-p ps)) (ps-symbol-char-p (ps-peek ps)))
          do (vector-push-extend (ps-advance ps) buf))
    (let ((s (coerce buf 'string)))
      (cond
        ;; Keyword: starts with :
        ((and (> (length s) 1) (char= (char s 0) #\:))
         (intern (subseq s 1) :keyword))
        ;; Number: try integer then float
        ((and (> (length s) 0)
              (or (digit-char-p (char s 0))
                  (and (> (length s) 1) (char= (char s 0) #\-) (digit-char-p (char s 1)))))
         (cond
           ;; Hex: 0x...
           ((and (> (length s) 2) (string-equal s "0x" :end1 2))
            (parse-integer s :start 2 :radix 16))
           ;; Float
           ((find #\. s)
            (read-from-string s))
           ;; Integer
           (t (parse-integer s :junk-allowed nil))))
        ;; Symbol
        (t (intern s :sysp))))))

(defun ps-read-char-literal (ps)
  "Read a #\\c character literal."
  (ps-advance ps)  ; consume #
  (ps-advance ps)  ; consume backslash
  (when (ps-eof-p ps) (error "sysp parser: unterminated character literal"))
  ;; Check for named chars like #\newline, #\space, #\tab
  (let ((first-char (ps-advance ps)))
    (if (and (not (ps-eof-p ps)) (alpha-char-p first-char) (alpha-char-p (ps-peek ps)))
        ;; Multi-char name
        (let ((buf (make-array 1 :element-type 'character :adjustable t :fill-pointer 1
                               :initial-element first-char)))
          (loop while (and (not (ps-eof-p ps)) (alpha-char-p (ps-peek ps)))
                do (vector-push-extend (ps-advance ps) buf))
          (let ((name (coerce buf 'string)))
            (cond
              ((string-equal name "newline") #\Newline)
              ((string-equal name "space") #\Space)
              ((string-equal name "tab") #\Tab)
              ((string-equal name "return") #\Return)
              (t (error "sysp parser: unknown character name #\\~a" name)))))
        first-char)))

(defun ps-read-form (ps)
  "Read one form from parser state. Returns (values form has-form-p)."
  (ps-skip-whitespace ps)
  (when (ps-eof-p ps) (return-from ps-read-form (values nil nil)))
  (let ((line (pstate-line ps))
        (col (pstate-col ps))
        (c (ps-peek ps)))
    (let ((form
            (cond
              ;; List: ( or [
              ((or (char= c #\() (char= c #\[))
               (ps-read-list ps))
              ;; String
              ((char= c #\")
               (ps-read-string ps))
              ;; Quote
              ((char= c #\')
               (ps-advance ps)
               (multiple-value-bind (inner has) (ps-read-form ps)
                 (declare (ignore has))
                 (list (intern "quote" :sysp) inner)))
              ;; Quasiquote
              ((char= c #\`)
               (ps-advance ps)
               (multiple-value-bind (inner has) (ps-read-form ps)
                 (declare (ignore has))
                 (list (intern "quasiquote" :sysp) inner)))
              ;; Unquote
              ((char= c #\~)
               (ps-advance ps)
               (if (and (not (ps-eof-p ps)) (char= (ps-peek ps) #\@))
                   (progn (ps-advance ps)
                          (multiple-value-bind (inner has) (ps-read-form ps)
                            (declare (ignore has))
                            (list (intern "splice" :sysp) inner)))
                   (multiple-value-bind (inner has) (ps-read-form ps)
                     (declare (ignore has))
                     (list (intern "unquote" :sysp) inner))))
              ;; Character literal
              ((and (char= c #\#) (not (ps-eof-p ps))
                    (< (1+ (pstate-pos ps)) (length (pstate-source ps)))
                    (char= (char (pstate-source ps) (1+ (pstate-pos ps))) #\\))
               (ps-read-char-literal ps))
              ;; Atom (symbol, keyword, number)
              (t (ps-read-atom ps)))))
      ;; Store source location for lists
      (when (consp form)
        (setf (gethash form *source-locations*) (list (pstate-file ps) line col)))
      (values form t))))

(defun ps-read-list (ps)
  "Read a list delimited by ( ) or [ ]."
  (let ((open-char (ps-advance ps))
        (close-char (if (char= (char (pstate-source ps) (1- (pstate-pos ps))) #\() #\) #\]))
        (elements nil))
    (declare (ignore open-char))
    (loop
      (ps-skip-whitespace ps)
      (when (ps-eof-p ps)
        (error "sysp parser: unterminated list at line ~d" (pstate-line ps)))
      (when (char= (ps-peek ps) close-char)
        (ps-advance ps)  ; consume closing delimiter
        (return (nreverse elements)))
      ;; Check for wrong delimiter
      (when (member (ps-peek ps) '(#\) #\]))
        (error "sysp parser: mismatched delimiter '~c' at line ~d col ~d"
               (ps-peek ps) (pstate-line ps) (pstate-col ps)))
      (multiple-value-bind (form has) (ps-read-form ps)
        (when has (push form elements))))))

(defun parse-sysp-source (source &optional (file "<string>"))
  "Parse sysp source string into list of forms with comment tracking."
  (let ((ps (make-pstate :source source :file file)))
    (let ((forms nil)
          (form-idx 0))
      (loop
        (ps-skip-whitespace ps)
        ;; Attach pending comments to next form
        (let ((pending-comments (nreverse (pstate-comments ps))))
          (setf (pstate-comments ps) nil)
          (multiple-value-bind (form has) (ps-read-form ps)
            (unless has (return))
            (when pending-comments
              (setf (gethash form-idx *form-comments*)
                    (mapcar #'cdr pending-comments)))
            (push form forms)
            (incf form-idx))))
      ;; Handle trailing comments
      (nreverse forms))))

(defun read-sysp-file (path)
  "Read sysp file using custom parser. Preserves comments, handles string escapes."
  (clrhash *form-comments*)
  (let ((source (with-open-file (in path :direction :input)
                  (let ((s (make-string (file-length in))))
                    (read-sequence s in)
                    s))))
    (parse-sysp-source source (namestring path))))

(defun read-sysp-forms (path)
  "Read a .sysp file and return its top-level forms (no comment tracking)."
  (let ((source (with-open-file (in path :direction :input)
                  (let ((s (make-string (file-length in))))
                    (read-sequence s in)
                    s))))
    (parse-sysp-source source (namestring path))))

(defun expand-uses (forms base-dir)
  "Walk FORMS, replacing (use ...) with the included file's forms. Deduplicates by absolute path."
  (loop for form in forms
        if (and (listp form)
                (symbolp (first form))
                (string-equal (symbol-name (first form)) "use"))
          nconc (let* ((arg (second form))
                       (resolved (cond
                                   ((stringp arg) (merge-pathnames arg base-dir))
                                   ((symbolp arg)
                                    ;; Bare symbol: try lib/X.sysp first, fall back to lib/X.sysph
                                    ;; (.sysph used when only header bindings exist, e.g. imported C libs)
                                    (let ((sname (string-downcase (symbol-name arg))))
                                      (let ((sysp (merge-pathnames (format nil "lib/~a.sysp" sname))))
                                        (if (probe-file sysp)
                                            sysp
                                            (merge-pathnames (format nil "lib/~a.sysph" sname))))))
                                   (t (error "use: argument must be a string or symbol, got ~s" arg))))
                       (abs-path (namestring (truename resolved))))
                  (if (gethash abs-path *included-files*)
                      nil  ; already included — skip
                      (progn
                        (setf (gethash abs-path *included-files*) t)
                        (let* ((child-forms (read-sysp-forms abs-path))
                               (child-dir (make-pathname :directory (pathname-directory abs-path))))
                          (expand-uses child-forms child-dir)))))
        else collect form))

;;; === Header Emission (.sysph) ===

(defun serialize-atom (x)
  "Serialize a single atom to sysp source string."
  (cond
    ((null x) "nil")
    ((keywordp x) (format nil ":~a" (string-downcase (symbol-name x))))
    ((symbolp x) (let ((n (symbol-name x)))
                   ;; Preserve case from parser (sysp package is case-sensitive)
                   n))
    ((stringp x) (format nil "~s" x))  ; CL ~s gives quoted string with escapes
    ((characterp x)
     (cond
       ((char= x #\Newline) "#\\newline")
       ((char= x #\Space) "#\\space")
       ((char= x #\Tab) "#\\tab")
       (t (format nil "#\\~c" x))))
    ((integerp x) (format nil "~d" x))
    ((floatp x) (format nil "~f" x))
    (t (format nil "~a" x))))

(defun serialize-list (items &optional (brackets nil))
  "Serialize a list of forms. If BRACKETS, use [...], else (...)."
  (let ((open (if brackets "[" "("))
        (close (if brackets "]" ")")))
    (format nil "~a~{~a~^ ~}~a" open (mapcar #'serialize-atom-or-form items) close)))

(defun serialize-atom-or-form (x)
  "Serialize any value — atom or list."
  (if (listp x)
      (serialize-list x)
      (serialize-atom x)))

(defun serialize-params (params-raw)
  "Serialize a parameter vector [name :type, name :type, ...]."
  (let ((parts nil))
    (let ((items (if (listp params-raw) params-raw nil)))
      (loop for rest on items
            for x = (car rest)
            do (push (serialize-atom x) parts)
            ;; Add comma before next param name if next item is a symbol (not keyword)
            ;; Pattern: name :type, name :type — comma separates pairs
            when (and (cdr rest) (cddr rest)
                      (keywordp x)
                      (not (keywordp (cadr rest))))
              do (push "," parts)))
    (format nil "[~{~a~^ ~}]" (nreverse parts))))

(defun serialize-form (form)
  "Serialize a top-level sysp form back to source."
  (when (not (listp form)) (return-from serialize-form (serialize-atom form)))
  (let ((head (first form)))
    (cond
      ;; (defn name [params] :ret body...)
      ;; (extern name [params] :ret)
      ((or (sym= head "defn") (sym= head "extern"))
       (let* ((name (second form))
              (params (third form))
              (rest (cdddr form)))
         (format nil "(~a ~a ~a~{ ~a~})"
                 (serialize-atom head)
                 (serialize-atom name)
                 (serialize-params params)
                 (mapcar #'serialize-atom-or-form rest))))
      ;; (defn-ct name [params] body...)
      ((sym= head "defn-ct")
       (let* ((name (second form))
              (params (third form))
              (body (cdddr form)))
         (format nil "(~a ~a ~a~{ ~a~})"
                 (serialize-atom head)
                 (serialize-atom name)
                 (serialize-params params)
                 (mapcar #'serialize-atom-or-form body))))
      ;; (defmacro name [params] body...)
      ((sym= head "defmacro")
       (let* ((name (second form))
              (params (third form))
              (body (cdddr form)))
         (format nil "(~a ~a ~a~{ ~a~})"
                 (serialize-atom head)
                 (serialize-atom name)
                 (serialize-params params)
                 (mapcar #'serialize-atom-or-form body))))
      ;; (struct Name [fields...])
      ((sym= head "struct")
       (format nil "(~a ~a ~a)"
               (serialize-atom head)
               (serialize-atom (second form))
               (serialize-params (third form))))
      ;; (enum Name [Variant val] ...)
      ((sym= head "enum")
       (format nil "(~a ~a~{ ~a~})"
               (serialize-atom head)
               (serialize-atom (second form))
               (mapcar (lambda (v)
                         (if (listp v)
                             (serialize-list v t)
                             (serialize-atom v)))
                       (cddr form))))
      ;; (deftype Name type-expr)
      ((sym= head "deftype")
       (format nil "(~a ~a ~a)"
               (serialize-atom head)
               (serialize-atom (second form))
               (serialize-atom-or-form (third form))))
      ;; (include "header.h")
      ((sym= head "include")
       (format nil "(include ~s)" (second form)))
      ;; (const name :type expr) / (let name :type expr)
      ((or (sym= head "const") (sym= head "let"))
       (format nil "(~a~{ ~a~})"
               (serialize-atom head)
               (mapcar #'serialize-atom-or-form (cdr form))))
      ;; Fallback: generic list
      (t (serialize-list form)))))

(defun emit-header (in-path out-path)
  "Read a .sysp file and emit a .sysph header with public API only."
  (let* ((forms (read-sysp-forms in-path))
         (abs-in (namestring (truename in-path)))
         (base-dir (make-pathname :directory (pathname-directory (truename in-path)))))
    ;; Reset included-files for use expansion
    (setf *included-files* (make-hash-table :test 'equal))
    (setf (gethash abs-in *included-files*) t)
    (setf forms (expand-uses forms base-dir))
    (with-open-file (out out-path :direction :output :if-exists :supersede)
      (format out ";; ~a — auto-generated header~%" (file-namestring out-path))
      (format out ";; Source: ~a~%~%" (file-namestring in-path))
      (dolist (form forms)
        (when (listp form)
          (let ((head (first form)))
            (cond
              ;; struct/deftype/enum — verbatim
              ((or (sym= head "struct") (sym= head "deftype") (sym= head "enum"))
               (format out "~a~%" (serialize-form form)))
              ;; include — verbatim
              ((sym= head "include")
               (format out "~a~%" (serialize-form form)))
              ;; const / let at top level — verbatim
              ((or (sym= head "const") (sym= head "let"))
               (format out "~a~%" (serialize-form form)))
              ;; defmacro / defn-ct — verbatim (compile-time)
              ((or (sym= head "defmacro") (sym= head "defn-ct"))
               (format out "~a~%" (serialize-form form)))
              ;; extern — verbatim
              ((sym= head "extern")
               (format out "~a~%" (serialize-form form)))
              ;; defn — check if private (starts with _), poly, or normal
              ((sym= head "defn")
               (let ((name (string (second form))))
                 (unless (and (> (length name) 0) (char= (char name 0) #\_))
                   ;; Private functions skipped
                   (if (defn-is-poly-p form)
                       ;; Poly: emit verbatim (needs body for monomorphization)
                       (format out "~a~%" (serialize-form form))
                       ;; Mono: strip body → extern
                       (let* ((params (third form))
                              (rest (cdddr form))
                              (ret-kw (when (keywordp (first rest)) (first rest))))
                         (format out "(extern ~a ~a~a)~%"
                                 (serialize-atom (second form))
                                 (serialize-params params)
                                 (if ret-kw
                                     (format nil " ~a" (serialize-atom ret-kw))
                                     "")))))))
              ;; c-decl — skip (raw C, not part of sysp API)
              ((sym= head "c-decl") nil)
              ;; use — skip (already expanded)
              ((sym= head "use") nil))))))))

;;; === Macro System ===

(defun macroexpand-1-sysp (form)
  "Expand one macro call. Returns (values expanded-form expanded-p)"
  (if (and (listp form) (symbolp (first form)))
      (let ((expander (gethash (string (first form)) *macros*)))
        (if expander
            (values (funcall expander form) t)
            (values form nil)))
      (values form nil)))

(defun macroexpand-all (form)
  "Recursively expand all macros in form"
  (if (not (listp form))
      form
      ;; First try to expand the form itself
      (multiple-value-bind (expanded was-expanded) (macroexpand-1-sysp form)
        (if was-expanded
            (macroexpand-all expanded)  ; re-expand in case macro produces another macro call
            ;; Not a macro — recurse into subforms
            (mapcar #'macroexpand-all form)))))

(defun install-builtin-macros ()
  "Install the standard macros: ->, ->>, when-let, dotimes, etc."
  ;; Threading macro: (-> x (f a) (g b)) => (g (f x a) b)
  (setf (gethash "->" *macros*)
        (lambda (form)
          (let ((val (second form))
                (forms (cddr form)))
            (reduce (lambda (acc f)
                      (if (listp f)
                          (list* (first f) acc (rest f))
                          (list f acc)))
                    forms :initial-value val))))
  ;; Thread-last: (->> x (f a) (g b)) => (g a (f b x))  wait no:
  ;; (->> x (f a) (g b)) => (g b (f a x))
  (setf (gethash "->>" *macros*)
        (lambda (form)
          (let ((val (second form))
                (forms (cddr form)))
            (reduce (lambda (acc f)
                      (if (listp f)
                          (append f (list acc))
                          (list f acc)))
                    forms :initial-value val))))
  ;; when-let: (when-let name expr body...) => (let name expr) (when name body...)
  ;; Actually emits a do block
  (setf (gethash "when-let" *macros*)
        (lambda (form)
          (let ((name (second form))
                (init (third form))
                (body (cdddr form)))
            (list* 'do
                   (list 'let name init)
                   (list* 'when name body)
                   nil))))
  ;; dotimes: (dotimes [i n] body...) => (for [i 0 n] body...)
  (setf (gethash "dotimes" *macros*)
        (lambda (form)
          (let ((spec (second form))
                (body (cddr form)))
            (list* 'for (list (first spec) 0 (second spec)) body))))
  ;; inc!: (inc! x) => (set! x (+ x 1))
  (setf (gethash "inc!" *macros*)
        (lambda (form)
          (list 'set! (second form) (list '+ (second form) 1))))
  ;; dec!: (dec! x) => (set! x (- x 1))
  (setf (gethash "dec!" *macros*)
        (lambda (form)
          (list 'set! (second form) (list '- (second form) 1)))))

(install-builtin-macros)

;;; === Type Annotation Parsing ===

(defun parse-type-expr (form)
  "Parse a type expression: keyword → parse-type-annotation, list → compound type.
   Handles (:cons :int :int), (:ptr :int), (:fn (:int) :int), (:union :int :str), etc.
   Note: readtable-case :preserve means keywords from source are lowercase (:|ptr|).
   We normalize via string-downcase comparison."
  (cond
    ((keywordp form)
     (parse-type-annotation form))
    ((symbolp form)
     ;; Could be a named type alias (no colon prefix)
     (let ((sname (symbol-name form)))
       (or (gethash sname *type-aliases*)
           `(:unknown ,sname))))
    ((and (listp form) (keywordp (first form)))
     (let ((head (string-downcase (symbol-name (first form)))))
       (cond
         ((string= head "ptr") (make-ptr-type (parse-type-expr (second form))))
         ((string= head "fn") (make-fn-type (mapcar #'parse-type-expr (second form))
                                             (parse-type-expr (third form))))
         ((string= head "cons") (make-cons-type (parse-type-expr (second form))
                                                 (parse-type-expr (third form))))
         ((string= head "array") (make-array-type (parse-type-expr (second form)) (third form)))
         ((string= head "vector") (make-vector-type (parse-type-expr (second form))))
         ((string= head "list") (make-list-type (parse-type-expr (second form))))
         ((string= head "tuple") (make-tuple-type (mapcar #'parse-type-expr (rest form))))
         ((string= head "union") `(:union ,@(mapcar #'parse-type-expr (rest form))))
         (t form))))
    (t form)))

(defparameter *primitive-type-map*
  (let ((ht (make-hash-table :test #'equal)))
    (dolist (pair '(("char" . :char) ("short" . :short) ("int" . :int) ("long" . :long)
                    ("long-long" . :long-long) ("uchar" . :uchar) ("ushort" . :ushort)
                    ("uint" . :uint) ("ulong" . :ulong) ("ulong-long" . :ulong-long)
                    ("i8" . :i8) ("i16" . :i16) ("i32" . :i32) ("i64" . :i64)
                    ("u8" . :u8) ("u16" . :u16) ("u32" . :u32) ("u64" . :u64)
                    ("float" . :float) ("double" . :double) ("f32" . :f32) ("f64" . :f64)
                    ("size" . :size) ("ptrdiff" . :ptrdiff) ("intptr" . :intptr) ("uintptr" . :uintptr)
                    ("void" . :void) ("bool" . :bool) ("str" . :str)
                    ("symbol" . :symbol) ("value" . :value) ("cons" . :cons) ("nil" . :nil))
              ht)
      (setf (gethash (car pair) ht) (cdr pair)))))

(defun parse-type-annotation (sym)
  (let* ((name (string-downcase (symbol-name sym)))
         (prim (gethash name *primitive-type-map*)))
    (cond
      (prim prim)
      ;; Polymorphic type variable: :? means "infer at call site"
      ((string= name "?") :poly)
      ;; Pointer shorthand: :ptr-int, :ptr-float, etc.
      ((and (> (length name) 4) (string= (subseq name 0 4) "ptr-"))
       ;; Use original symbol-name suffix to preserve case for struct names
       (make-ptr-type (parse-type-annotation
                       (intern (subseq (symbol-name sym) 4) :keyword))))
      (t (let ((sname (symbol-name sym)))
           (cond
             ((gethash sname *structs*) (make-struct-type sname))
             ((gethash sname *enums*) (make-enum-type sname))
             ((gethash sname *type-aliases*) (gethash sname *type-aliases*))
             (t `(:unknown ,sname))))))))


;;; === C Type Emission ===

(defun type-to-c (tp)
  (case (type-kind tp)
    ;; Signed integers
    (:char "char")
    (:short "short")
    (:int "int")
    (:long "long")
    (:long-long "long long")
    ;; Unsigned integers
    (:uchar "unsigned char")
    (:ushort "unsigned short")
    (:uint "unsigned int")
    (:ulong "unsigned long")
    (:ulong-long "unsigned long long")
    ;; Fixed-width signed (C99 stdint.h)
    (:i8 "int8_t")
    (:i16 "int16_t")
    (:i32 "int32_t")
    (:i64 "int64_t")
    ;; Fixed-width unsigned (C99 stdint.h)
    (:u8 "uint8_t")
    (:u16 "uint16_t")
    (:u32 "uint32_t")
    (:u64 "uint64_t")
    ;; Floating point
    (:float "float")
    (:double "double")
    (:f32 "float")
    (:f64 "double")
    ;; Size/pointer types (C99 stddef.h/stdint.h)
    (:size "size_t")
    (:ptrdiff "ptrdiff_t")
    (:intptr "intptr_t")
    (:uintptr "uintptr_t")
    ;; Other
    (:bool "int")
    (:void "void")
    (:str "const char*")
    ;; Compound types
    (:ptr (format nil "~a*" (type-to-c (second tp))))
    (:struct (second tp))
    (:enum (second tp))
    (:array (type-to-c (second tp)))  ; array decl handled specially
    (:vector (vector-type-c-name tp))
    (:tuple (tuple-type-c-name tp))
    (:fn (fn-type-c-name tp))
    (:symbol "Symbol")
    (:value "Value")
    (:cons "Value")  ; cons cells are Values (tagged)
    (:nil "Value")   ; nil is a Value
    (:list "Value")  ; lists are also Values (tagged cons chain)
    (:variadic "Value")  ; variadic rest compiles to Value at runtime
    (:union (union-type-c-name tp))
    (:rc (format nil "_RC_~a*" (type-to-c (rc-inner-type tp))))
    (:future (format nil "_spawn_~a*" (third tp)))  ; (:future T spawn-id) → _spawn_N*
    (otherwise "int")))

(defun mangle-type-name (tp)
  (case (type-kind tp)
    ;; Integer types
    (:int "int")
    (:char "char")
    (:short "short")
    (:long "long")
    (:long-long "longlong")
    (:uchar "uchar")
    (:ushort "ushort")
    (:uint "uint")
    (:ulong "ulong")
    (:ulong-long "ulonglong")
    ;; Fixed-width integers
    (:i8 "i8") (:i16 "i16") (:i32 "i32") (:i64 "i64")
    (:u8 "u8") (:u16 "u16") (:u32 "u32") (:u64 "u64")
    ;; Size types
    (:size "size") (:ptrdiff "ptrdiff") (:intptr "intptr") (:uintptr "uintptr")
    ;; Float types
    (:float "float") (:double "double") (:f32 "f32") (:f64 "f64")
    ;; Other primitives
    (:bool "bool")
    (:str "str")
    (:void "void")
    (:symbol "sym")
    (:value "val")
    (:cons "cons")
    (:nil "nil")
    ;; Compound types
    (:ptr (format nil "ptr_~a" (mangle-type-name (second tp))))
    (:struct (second tp))
    (:enum (second tp))
    (:array (format nil "arr_~a_~a" (mangle-type-name (second tp))
                    (third tp)))
    (:vector (vector-type-c-name tp))
    (:tuple (tuple-type-c-name tp))
    (:fn (fn-type-c-name tp))
    (:list (format nil "list_~a" (mangle-type-name (second tp))))
    (:variadic (format nil "var_~a" (mangle-type-name (second tp))))
    ;; Union types
    (:union (format nil "Union_~{~a~^_~}" (mapcar #'mangle-type-name (cdr tp))))
    ;; RC-managed types
    (:rc (format nil "rc_~a" (mangle-type-name (rc-inner-type tp))))
    ;; Future types
    (:future (format nil "future_~a" (mangle-type-name (second tp))))
    (otherwise (warn "mangle-type-name: unhandled type ~a" tp) "unknown")))

(defun vector-type-c-name (tp)
  (let* ((elem (second tp))
         (name (format nil "Vector_~a" (mangle-type-name elem))))
    (ensure-vector-type name elem)
    name))

(defun tuple-type-c-name (tp)
  (let* ((elems (cdr tp))
         (name (format nil "Tuple_~{~a~^_~}" (mapcar #'mangle-type-name elems))))
    (ensure-tuple-type name elems)
    name))

(defun fn-type-c-name (tp)
  (let* ((args (fn-type-args tp))
         (ret (fn-type-ret tp))
         (name (format nil "Fn_~{~a~^_~}_~a"
                       (or (mapcar #'mangle-type-name args) '("void"))
                       (mangle-type-name ret))))
    (ensure-fn-type name args ret)
    name))

;;; === Generated Type Structs ===

(defun ensure-vector-type (name elem-type)
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    (push (format nil "typedef struct { ~a* data; int len; int cap; } ~a;~%"
                  (type-to-c elem-type) name)
          *type-decls*)))

(defun ensure-tuple-type (name elem-types)
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    (let ((fields (loop for tp in elem-types
                        for i from 0
                        collect (format nil "  ~a _~d;" (type-to-c tp) i))))
      (push (format nil "typedef struct {~%~{~a~%~}} ~a;~%" fields name)
            *type-decls*))))

(defun ensure-fn-type (name arg-types ret-type)
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    ;; Fn struct: { ret_type (*fn)(void* _ctx, arg_types...); void* env; }
    (let ((arg-str (format nil "void*~{, ~a~}" (mapcar #'type-to-c arg-types))))
      (push (format nil "typedef struct { ~a (*fn)(~a); void* env; } ~a;~%"
                    (type-to-c ret-type) arg-str name)
            *type-decls*))))

(defun ensure-union-type (tp)
  "Ensure the C tagged union for a union type is generated.
   Returns the C type name (e.g. Union_int_str)."
  (let* ((variants (union-variants tp))
         (name (format nil "Union_~{~a~^_~}" (mapcar #'mangle-type-name variants))))
    (unless (gethash name *generated-types*)
      (setf (gethash name *generated-types*) t)
      ;; Generate: typedef enum { Union_int_str_TAG_INT, ... } Union_int_str_tag;
      ;; typedef struct { Union_int_str_tag tag; union { int as_int; ... }; } Union_int_str;
      ;; static Union_int_str Union_int_str_from_int(int x) { ... }
      (let* ((tag-enum-name (format nil "~a_tag" name))
             (tag-values (mapcar (lambda (v)
                                   (format nil "~a_TAG_~a"
                                           name (string-upcase (mangle-type-name v))))
                                 variants))
             (enum-def (format nil "typedef enum { ~{~a~^, ~} } ~a;~%"
                               tag-values tag-enum-name))
             ;; Union fields
             (fields (mapcar (lambda (v)
                               (format nil "    ~a as_~a;"
                                       (type-to-c v) (mangle-type-name v)))
                             variants))
             (struct-def (format nil "typedef struct {~%  ~a tag;~%  union {~%~{~a~%~}  };~%} ~a;~%"
                                 tag-enum-name fields name))
             ;; Constructor functions
             (ctors (mapcar (lambda (v tag)
                              (let ((mname (mangle-type-name v)))
                                (format nil "static ~a ~a_from_~a(~a x) { ~a r; r.tag = ~a; r.as_~a = x; return r; }~%"
                                        name name mname (type-to-c v) name tag mname)))
                            variants tag-values)))
        ;; First pushed = last after nreverse. Want: enum, struct, ctors.
        (push enum-def *type-decls*)
        (push struct-def *type-decls*)
        (dolist (ctor (reverse ctors))
          (push ctor *type-decls*))))
    name))

(defun ensure-rc-type (inner-type)
  "Ensure the RC wrapper struct and helpers for a type are generated.
   Returns the C struct name (e.g. _RC_Point)."
  (let* ((c-inner (type-to-c inner-type))
         (name (format nil "_RC_~a" c-inner)))
    (unless (gethash name *generated-types*)
      (setf (gethash name *generated-types*) t)
      ;; typedef struct { int _rc; T data; } _RC_T;
      (push (format nil "typedef struct { int _rc; ~a data; } ~a;~%" c-inner name)
            *type-decls*)
      ;; _RC_T* _rc_T_new(T val) { _RC_T* p = malloc(sizeof(_RC_T)); p->_rc = 1; p->data = val; return p; }
      (push (format nil "static ~a* _rc_~a_new(~a val) { ~a* p = malloc(sizeof(~a)); p->_rc = 1; p->data = val; return p; }~%"
                    name (mangle-type-name inner-type) c-inner name name)
            *type-decls*)
      ;; void _rc_T_retain(_RC_T* p) { RC_INC(p->_rc); }
      (push (format nil "static void _rc_~a_retain(~a* p) { if (p) RC_INC(p->_rc); }~%"
                    (mangle-type-name inner-type) name)
            *type-decls*)
      ;; void _rc_T_release(_RC_T** p) { if (*p && RC_DEC((*p)->_rc) == 1) { free(*p); *p = NULL; } }
      (push (format nil "static void _rc_~a_release(~a** p) { if (*p && RC_DEC((*p)->_rc) == 1) { free(*p); *p = NULL; } }~%"
                    (mangle-type-name inner-type) name)
            *type-decls*))
    name))

(defun union-type-c-name (tp)
  "Get the C type name for a union type, ensuring it's generated."
  (ensure-union-type tp))

(defun ensure-vector-helper (name c-elem c-vec)
  "Emit a helper function for creating vectors of a specific type"
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    (pushnew "stdarg.h" *includes* :test #'string=)
    ;; Emit: Vector_T sysp_mkvec_T(int n, ...) { ... }
    (push (format nil "static ~a ~a(int n, ...) { va_list ap; va_start(ap, n); ~a* d = malloc(sizeof(~a) * n); for(int i = 0; i < n; i++) d[i] = va_arg(ap, ~a); va_end(ap); return (~a){d, n, n}; }~%"
                  c-vec name c-elem c-elem
                  ;; For small types, va_arg promotes to int
                  (if (member c-elem '("char" "unsigned char" "short" "float") :test #'string=)
                      (if (string= c-elem "float") "double" "int")
                      c-elem)
                  c-vec)
          *functions*)))

(defun wrap-as-union (code concrete-type union-type)
  "Generate C code to wrap a concrete value into a union type.
   e.g., (wrap-as-union \"42\" :int (:union :int :str)) → \"Union_int_str_from_int(42)\""
  (if (union-type-p union-type)
      (let ((union-name (ensure-union-type union-type))
            (mname (mangle-type-name concrete-type)))
        (format nil "~a_from_~a(~a)" union-name mname code))
      code))

(defun ensure-vector-push-helper (name c-vec c-elem)
  "Emit a helper function for pushing to vectors of a specific type"
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    (pushnew "string.h" *includes* :test #'string=)
    ;; Emit: void sysp_vecpush_T(Vector_T* v, T val) { ... }
    (push (format nil "static void ~a(~a* v, ~a val) { if(v->len >= v->cap) { v->cap = v->cap ? v->cap * 2 : 4; v->data = realloc(v->data, sizeof(~a) * v->cap); } v->data[v->len++] = val; }~%"
                  name c-vec c-elem c-elem)
          *functions*)))

;;; === Statement Lifting (expressions that are really statements) ===

;; Generate a fresh temp variable name
(defun fresh-tmp ()
  (format nil "_tmp~d" (incf *tmp-counter*)))

;; Detect if a form is a statement-like construct (do, if with side effects, cond)
(defun statement-like-p (form)
  (and (listp form)
       (not (null form))
       (symbolp (first form))
       (let ((head (string (first form))))
         (member head '("do" "if" "cond" "let" "let-mut" "match") :test #'string-equal))))

;; Compile form so its value ends up assigned to target-var.
;; Returns (values type statements-list).
;; Recursively handles nested statement-like forms.
(defun compile-expr-returning (form env target)
  (cond
    ;; recur → goto, no target assignment (recur never produces a value)
    ((and (listp form) (symbolp (first form)) (sym= (first form) "recur"))
     (values :void (compile-recur-stmt form env)))
    ;; return → explicit return, no target assignment
    ((and (listp form) (symbolp (first form)) (sym= (first form) "return"))
     (values :void (compile-return-stmt form env)))
    ;; Statement-like: compile-stmt-returning returns stmts directly
    ((statement-like-p form)
     (compile-stmt-returning form env target))
    ;; Simple expression: isolate pending stmts, compile, assign/return
    (t (let ((*pending-stmts* nil))
         (multiple-value-bind (code type) (compile-expr form env)
           (values type
                   (append *pending-stmts*
                           (list (if (string= target ":return")
                                     (format nil "  return ~a;" code)
                                     (format nil "  ~a = ~a;" target code))))))))))

;; Compile a statement-like form so its value is assigned to target.
;; Returns (values type statements-list).
(defun compile-stmt-returning (form env target)
  (let ((head (string (first form))))
    (cond
      ((string-equal head "if") (compile-if-stmt-returning form env target))
      ((string-equal head "do") (compile-do-stmt-returning form env target))
      ((string-equal head "cond") (compile-cond-stmt-returning form env target))
      ((string-equal head "match") (compile-match-stmt-returning form env target))
      ((or (string-equal head "let") (string-equal head "let-mut"))
       (compile-let-stmt-returning form env target)))))

;;; === Expression Compilation ===

(defun compile-expr (form env)
  "Compile an expression, return (values c-string type).
   Statement-like forms (if, do, cond) are lifted to temp variables
   with their statements pushed onto *pending-stmts*."
  (if (statement-like-p form)
      ;; Lift statement-like form: compile as statement assigning to temp
      (let ((tmp (fresh-tmp)))
        (multiple-value-bind (type stmts) (compile-stmt-returning form env tmp)
          (setf *pending-stmts* (append *pending-stmts*
                                        (list (format nil "  ~a ~a;" (type-to-c type) tmp))
                                        stmts))
          (values tmp type)))
      (compile-expr-inner form env)))

(defun compile-expr-inner (form env)
  "Compile a non-statement-like expression"
  (cond
    ((null form) (values "0" :int))
    ((characterp form)
     ;; Character literal: \a → 'a', \+ → '+', \space → ' ', \newline → '\n', \tab → '\t'
     (let ((c form))
       (cond
         ((char= c #\Newline) (values "'\\n'" :char))
         ((char= c #\Tab) (values "'\\t'" :char))
         ((char= c #\Space) (values "' '" :char))
         ((char= c #\\) (values "'\\\\'" :char))
         ((char= c #\') (values "'\\''" :char))
         (t (values (format nil "'~a'" c) :char)))))
    ((integerp form)
     ;; Add suffix for large integers (C99)
     (cond
       ((<= -2147483648 form 2147483647)
        (values (format nil "~d" form) :int))
       ((<= form 9223372036854775807)
        ;; Fits in signed long long
        (values (format nil "~dLL" form) :long-long))
       (t
        ;; Larger than signed max - use unsigned long long
        (values (format nil "~dULL" form) :ulong-long))))
    ((floatp form) (values (format nil "~f" form) :float))
    ((stringp form) (values (format nil "~s" form) :str))
    ((symbolp form)
     (let ((name (string form)))
       (cond
         ((string-equal name "true") (values "1" :bool))
         ((string-equal name "false") (values "0" :bool))
         ((string-equal name "null") (values "NULL" (make-ptr-type :void)))
         (t (let ((tp (env-lookup env name)))
              (if tp
                  (values (sanitize-name name) tp)
                  ;; Check if it's an enum variant
                  (let ((enum-info (lookup-enum-variant name)))
                    (if enum-info
                        (values (sanitize-name name)
                                (make-enum-type (car enum-info)))
                        (values (sanitize-name name)
                                :unknown)))))))))
    ((listp form)
     ;; Try macro expansion first
     (multiple-value-bind (expanded was-expanded) (macroexpand-1-sysp form)
       (if was-expanded
           (compile-expr (macroexpand-all expanded) env)
           (compile-list form env))))
    (t (values (format nil "~a" form) :unknown))))

(defun sanitize-name (name)
  (let* ((result (substitute #\_ #\- name))
         (result (with-output-to-string (s)
                   (loop for ch across result do
                     (case ch
                       (#\? (write-string "_p" s))
                       (#\! (write-string "_bang" s))
                       (otherwise (write-char ch s)))))))
    ;; Handle names that are C keywords
    (if (member result '("int" "float" "double" "char" "void" "struct"
                         "if" "else" "while" "for" "return" "break"
                         "continue" "switch" "case" "default" "do"
                         "typedef" "static" "const" "sizeof" "union"
                         "enum" "extern" "register" "volatile" "goto")
               :test #'string-equal)
        (concatenate 'string result "_")
        result)))

(defun sym= (sym name)
  (and (symbolp sym) (string-equal (symbol-name sym) name)))

(defmacro define-accessor (name pattern type-expr)
  "Define a simple accessor compiler function.
   Pattern is a format string with ~a for object and ~a for index.
   Type-expr computes the result type from the container type."
  `(defun ,(intern (format nil "COMPILE-~a" name)) (form env)
     (multiple-value-bind (obj tp) (compile-expr (second form) env)
       (multiple-value-bind (idx it) (compile-expr (third form) env)
         (declare (ignore it))
         (let ((elem-type ,type-expr))
           (values (format nil ,pattern obj idx) elem-type))))))

(defmacro define-len (name pattern)
  `(defun ,(intern (format nil "COMPILE-~a" name)) (form env)
     (multiple-value-bind (obj tp) (compile-expr (second form) env)
       (declare (ignore tp))
       (values (format nil ,pattern obj) :int))))

(defmacro define-value-accessor (name c-fun ret-type)
  `(defun ,(intern (format nil "COMPILE-~a" name)) (form env)
     (setf *uses-value-type* t)
     (multiple-value-bind (code tp) (compile-expr (second form) env)
       (declare (ignore tp))
       (values (format nil ,(format nil "~a(~~a)" c-fun) code) ,ret-type))))

;; Operator dispatch tables
(defparameter *binop-ops*
  '(("+" . "+") ("-" . "-") ("*" . "*") ("/" . "/") ("%" . "%") ("mod" . "%")
    ("<" . "<") (">" . ">") ("<=" . "<=") (">=" . ">=") ("==" . "==") ("!=" . "!=")
    ("bit-and" . "&") ("bit-or" . "|") ("bit-xor" . "^") ("shl" . "<<") ("shr" . ">>")))

(defparameter *logical-ops* '(("and" . "&&") ("or" . "||")))

(defparameter *expr-dispatch*
  '(("if" . compile-if-expr) ("do" . compile-do-expr) ("cond" . compile-cond-expr)
    ("get" . compile-get) ("vector" . compile-vector)
    ("vector-ref" . compile-vector-ref) ("vector-set!" . compile-vector-set)
    ("vector-push!" . compile-vector-push) ("vector-len" . compile-vector-len)
    ("tuple" . compile-tuple) ("tuple-ref" . compile-tuple-ref)
    ("lambda" . compile-lambda)
    ("array-ref" . compile-array-ref) ("array-set!" . compile-array-set)
    ("make-array" . compile-make-array)
    ("set!" . compile-set-expr)
    ("addr-of" . compile-addr-of) ("deref" . compile-deref)
    ("cast" . compile-cast) ("sizeof" . compile-sizeof)
    ("runtype" . compile-runtype) ("as" . compile-as)
    ("cons" . compile-cons) ("car" . compile-car) ("cdr" . compile-cdr)
    ("nil?" . compile-nilp) ("list" . compile-list-expr)
    ("quote" . compile-quote) ("quasiquote" . compile-quasiquote)
    ("sym" . compile-sym-literal) ("sym-eq?" . compile-sym-eq)
    ("gensym" . compile-gensym-expr)
    ("not" . compile-not) ("bit-not" . compile-bit-not)
    ("match" . compile-match-expr)
    ("new" . compile-new-expr)
    ("ptr-alloc" . compile-ptr-alloc)
    ("ptr-deref" . compile-ptr-deref)
    ("null?" . compile-null-check)
    ("spawn" . compile-spawn)
    ("await" . compile-await)
    ("restart-case" . compile-restart-case)
    ("handler-bind" . compile-handler-bind)
    ("signal" . compile-signal)
    ("invoke-restart" . compile-invoke-restart)
    ("c-expr" . compile-c-expr)
    ("ptr+" . compile-ptr-add)
    ("ptr-to" . compile-ptr-to)))

(defun compile-list (form env)
  (let* ((head (first form))
         (name (when (symbolp head) (symbol-name head))))
    (unless name (return-from compile-list (compile-call form env)))
    (let ((binop (cdr (assoc name *binop-ops* :test #'string-equal))))
      (when binop
        (return-from compile-list
          (if (and (string= binop "-") (= (length form) 2))
              (compile-unary-minus form env)
              (compile-binop binop form env)))))
    (let ((logical (cdr (assoc name *logical-ops* :test #'string-equal))))
      (when logical
        (return-from compile-list (compile-logical logical form env))))
    (let ((handler (cdr (assoc name *expr-dispatch* :test #'string-equal))))
      (when handler
        (return-from compile-list (funcall handler form env))))
    (cond
      ((sym= head "recur")
       (error "sysp: recur must be in tail position (last expression of a function, or branch of if/cond in tail position)"))
      ((sym= head "return")
       (error "sysp: return cannot be used as an expression"))
      (t (compile-call form env)))))

(defun sysp-arithmetic-type (t1 t2)
  "Compute result type for binary arithmetic.
   Unlike C, sysp preserves types: i8 + i8 = i8, not int.
   Only promotes when mixing different types."
  (let ((k1 (type-kind t1))
        (k2 (type-kind t2)))
    ;; Same type? Return it. No surprises.
    (when (eq k1 k2)
      (return-from sysp-arithmetic-type t1))
    ;; Normalize aliases
    (when (eq k1 :f32) (setf k1 :float))
    (when (eq k2 :f32) (setf k2 :float))
    (when (eq k1 :f64) (setf k1 :double))
    (when (eq k2 :f64) (setf k2 :double))
    ;; Different types - promote to the wider one
    (flet ((rank (k)
             (case k
               ((:double :f64) 200)
               ((:float :f32) 100)
               ((:i64 :u64 :long-long :ulong-long) 64)
               ((:long :ulong) 48)  ; platform-dependent
               ((:i32 :u32 :int :uint) 32)
               ((:i16 :u16 :short :ushort) 16)
               ((:i8 :u8 :char :uchar) 8)
               ((:size :ptrdiff :intptr :uintptr) 48)
               (otherwise 32)))
           (unsigned-p (k)
             (member k '(:u8 :u16 :u32 :u64 :uchar :ushort :uint :ulong :ulong-long :size :uintptr))))
      (let ((r1 (rank k1))
            (r2 (rank k2)))
        (cond
          ;; Float wins over everything
          ((or (>= r1 100) (>= r2 100))
           (if (>= (max r1 r2) 200) :double :float))
          ;; Both integers - use wider type
          ((> r1 r2) t1)
          ((> r2 r1) t2)
          ;; Same rank, different types - prefer unsigned if either is unsigned
          ((or (unsigned-p k1) (unsigned-p k2))
           (if (unsigned-p k1) t1 t2))
          ;; Default to first type
          (t t1))))))

(defun compile-binop (op form env)
  (multiple-value-bind (lhs lt) (compile-expr (second form) env)
    (multiple-value-bind (rhs rt) (compile-expr (third form) env)
      (let ((result-type
              (cond
                ;; Comparison and logical operators always return bool (int in C)
                ((member op '("<" ">" "<=" ">=" "==" "!=" "&&" "||") :test #'string=)
                 :bool)
                ;; Bitwise operators return int (operate on integer types)
                ((member op '("&" "|" "^" "<<" ">>") :test #'string=)
                 :int)
                ;; Arithmetic operators: use C99 promotion rules
                (t (sysp-arithmetic-type lt rt)))))
        (values (format nil "(~a ~a ~a)" lhs op rhs) result-type)))))

(defun compile-logical (op form env)
  "(and a b c ...) or (or a b c ...) — variadic logical"
  (let* ((args (rest form))
         (compiled (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args)))
    (if (= (length compiled) 1)
        (values (first compiled) :bool)
        (values (format nil "(~a)"
                        (reduce (lambda (acc x) (format nil "~a ~a ~a" acc op x))
                                compiled))
                :bool))))

(defun compile-unary-minus (form env)
  (multiple-value-bind (val tp) (compile-expr (second form) env)
    (values (format nil "(-~a)" val) tp)))

(defun compile-not (form env)
  (multiple-value-bind (val tp) (compile-expr (second form) env)
    (declare (ignore tp))
    (values (format nil "(!~a)" val) :bool)))

(defun compile-bit-not (form env)
  (multiple-value-bind (val tp) (compile-expr (second form) env)
    (declare (ignore tp))
    (values (format nil "(~~~a)" val) :int)))

(defun parse-if-branches (forms &key arc-style)
  "Parse forms after (if cond ...) into (values then-forms elif-list else-forms).
   elif-list is ((cond . body-forms) ...).
   Handles: keyword else/elif, positional else (2 forms), Arc-style pairs (arc-style t).
   Styles cannot be mixed: keywords or implicit pairs, not both."
  (let* ((has-elif (some (lambda (x) (and (symbolp x) (sym= x "elif"))) forms))
         (has-else (some (lambda (x) (and (symbolp x) (sym= x "else"))) forms))
         (has-keywords (or has-elif has-else)))
    ;; Positional else: exactly 2 forms, no keywords
    (when (and (not has-keywords) (= (length forms) 2))
      (return-from parse-if-branches
        (values (list (first forms)) nil (list (second forms)))))
    ;; Arc-style: no keywords, >2 forms -> alternating cond/expr pairs
    (when (and arc-style (not has-keywords) (> (length forms) 2))
      (let ((then-form (first forms))
            (remaining (rest forms))
            (pairs nil))
        (loop while (> (length remaining) 1)
              do (let ((c (pop remaining))
                       (e (pop remaining)))
                   (push (cons c (list e)) pairs)))
        (return-from parse-if-branches
          (values (list then-form) (nreverse pairs) remaining))))
    ;; Keyword-based parsing
    (let ((then-forms nil)
          (elifs nil)
          (else-forms nil)
          (state :then)
          (current nil)
          (elif-cond nil))
      (dolist (f forms)
        (cond
          ((and (symbolp f) (sym= f "elif"))
           (case state
             (:then (setf then-forms (nreverse current)))
             (:elif-body (push (cons elif-cond (nreverse current)) elifs))
             (:elif-cond (error "sysp: elif without body before next elif")))
           (setf state :elif-cond current nil))
          ((and (symbolp f) (sym= f "else"))
           (case state
             (:then (setf then-forms (nreverse current)))
             (:elif-body (push (cons elif-cond (nreverse current)) elifs))
             (:elif-cond (error "sysp: elif without body before else")))
           (setf state :else current nil))
          ((eq state :elif-cond)
           (setf elif-cond f state :elif-body current nil))
          (t (push f current))))
      (when (eq state :elif-cond)
        (error "sysp: elif at end of if without condition/body"))
      (case state
        (:then (setf then-forms (nreverse current)))
        (:elif-body (push (cons elif-cond (nreverse current)) elifs))
        (:else (setf else-forms (nreverse current))))
      (values then-forms (nreverse elifs) else-forms))))

(defun compile-if-expr (form env)
  "(if cond then [elif cond2 then2]... [else else-expr]) -> ternary"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (multiple-value-bind (then-code then-type) (compile-expr (third form) env)
      (let ((rest (cdddr form)))
        (if (null rest)
            (values (format nil "(~a ? ~a : 0)" cond-code then-code) then-type)
            ;; Get else expression: elif recurses, else/positional are direct
            (multiple-value-bind (else-code else-type)
                (cond
                  ((and (symbolp (first rest)) (sym= (first rest) "elif"))
                   (compile-if-expr (list* 'if (cdr rest)) env))
                  ((and (symbolp (first rest)) (sym= (first rest) "else"))
                   (compile-expr (second rest) env))
                  ;; Multiple forms, no keywords -> Arc-style pairs
                  ((> (length rest) 1)
                   (compile-if-expr (list* 'if rest) env))
                  ;; Single form -> positional else
                  (t (compile-expr (first rest) env)))
              (let ((result-type (if (type-equal-p then-type else-type)
                                     then-type
                                     (make-union-type (list then-type else-type)))))
                (if (union-type-p result-type)
                    (values (format nil "(~a ? ~a : ~a)" cond-code
                                    (wrap-as-union then-code then-type result-type)
                                    (wrap-as-union else-code else-type result-type))
                            result-type)
                    (values (format nil "(~a ? ~a : ~a)" cond-code then-code else-code)
                            result-type)))))))))

(defun compile-do-expr (form env)
  "(do expr...) -> GNU statement expression, value is last"
  (let* ((exprs (rest form))
         (new-env (make-env :parent env)))
    (if (= (length exprs) 1)
        (compile-expr (first exprs) new-env)
        (let* ((stmts (compile-body (butlast exprs) new-env))
               (last-expr (car (last exprs))))
          (multiple-value-bind (last-code last-type) (compile-expr last-expr new-env)
            (values (format nil "({ ~{~a ~}~a; })"
                            (mapcar (lambda (s) (format nil "~a " (string-trim '(#\Space) s))) stmts)
                            last-code)
                    last-type))))))

;;; === ARC Memory Model & Raw Pointers ===

(defun compile-new-expr (form env)
  "(new StructName args...) → RC-managed heap allocation.
   Returns (:rc (:struct Name))."
  (let* ((struct-name (string (second form)))
         (args (cddr form))
         (inner-type (make-struct-type struct-name))
         (rc-type (make-rc-type inner-type))
         (compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args))
         (rc-c-name (ensure-rc-type inner-type))
         (mname (mangle-type-name inner-type)))
    (values (format nil "_rc_~a_new((~a){~{~a~^, ~}})"
                    mname struct-name compiled-args)
            rc-type)))

(defun compile-ptr-alloc (form env)
  "(ptr-alloc :type n) → malloc(n * sizeof(T)), returns (:ptr :T)"
  (let* ((type-keyword (second form))
         (alloc-type (parse-type-annotation type-keyword))
         (n-form (third form)))
    (multiple-value-bind (n-code nt) (compile-expr n-form env)
      (declare (ignore nt))
      (values (format nil "malloc(~a * sizeof(~a))" n-code (type-to-c alloc-type))
              (make-ptr-type alloc-type)))))

(defun compile-ptr-free-stmt (form env)
  "(ptr-free p) → free(p);"
  (multiple-value-bind (p-code pt) (compile-expr (second form) env)
    (declare (ignore pt))
    (list (format nil "  free(~a);" p-code))))

(defun compile-ptr-deref (form env)
  "(ptr-deref p) → *p, or (ptr-deref p i) → p[i]"
  (multiple-value-bind (p-code pt) (compile-expr (second form) env)
    (let ((elem-type (if (and (consp pt) (eq (car pt) :ptr)) (second pt) :int)))
      (if (third form)
          (multiple-value-bind (i-code it) (compile-expr (third form) env)
            (declare (ignore it))
            (values (format nil "~a[~a]" p-code i-code) elem-type))
          (values (format nil "(*~a)" p-code) elem-type)))))

(defun compile-ptr-set-stmt (form env)
  "(ptr-set! p val) → *p = val; or (ptr-set! p i val) → p[i] = val;"
  (let ((args (rest form)))
    (if (= (length args) 3)
        ;; (ptr-set! p i val)
        (multiple-value-bind (p-code pt) (compile-expr (first args) env)
          (declare (ignore pt))
          (multiple-value-bind (i-code it) (compile-expr (second args) env)
            (declare (ignore it))
            (multiple-value-bind (v-code vt) (compile-expr (third args) env)
              (declare (ignore vt))
              (list (format nil "  ~a[~a] = ~a;" p-code i-code v-code)))))
        ;; (ptr-set! p val)
        (multiple-value-bind (p-code pt) (compile-expr (first args) env)
          (declare (ignore pt))
          (multiple-value-bind (v-code vt) (compile-expr (second args) env)
            (declare (ignore vt))
            (list (format nil "  *~a = ~a;" p-code v-code)))))))

(defun compile-ptr-add (form env)
  "(ptr+ ptr offset) — pointer arithmetic, returns same pointer type."
  (multiple-value-bind (p-code pt) (compile-expr (second form) env)
    (multiple-value-bind (n-code nt) (compile-expr (third form) env)
      (declare (ignore nt))
      (values (format nil "(~a + ~a)" p-code n-code) pt))))

(defun compile-ptr-to (form env)
  "(ptr-to :type expr) — cast expression to (:ptr type)."
  (let ((target-type (parse-type-annotation (second form))))
    (multiple-value-bind (code ct) (compile-expr (third form) env)
      (declare (ignore ct))
      (values (format nil "((~a*)~a)" (type-to-c target-type) code)
              (make-ptr-type target-type)))))

(defun compile-cond-expr (form env)
  "(cond [test1 expr1] [test2 expr2] ... [else exprN]) -> nested ternary"
  (let ((clauses (rest form)))
    (compile-cond-clauses clauses env)))

(defun compile-cond-clauses (clauses env)
  (if (null clauses)
      (values "0" :int)
      (let ((clause (first clauses)))
        (if (and (symbolp (first clause)) (sym= (first clause) "else"))
            (compile-expr (second clause) env)
            (multiple-value-bind (test-code tt) (compile-expr (first clause) env)
              (declare (ignore tt))
              (multiple-value-bind (then-code then-type) (compile-expr (second clause) env)
                (multiple-value-bind (rest-code rest-type) (compile-cond-clauses (rest clauses) env)
                  ;; Unify this clause type with rest type
                  (let ((result-type (if (type-equal-p then-type rest-type)
                                         then-type
                                         (make-union-type (list then-type rest-type)))))
                    (if (union-type-p result-type)
                        (values (format nil "(~a ? ~a : ~a)" test-code
                                        (wrap-as-union then-code then-type result-type)
                                        (wrap-as-union rest-code rest-type result-type))
                                result-type)
                        (values (format nil "(~a ? ~a : ~a)" test-code then-code rest-code)
                                result-type))))))))))

(defun compile-if-stmt-returning (form env target)
  "(if cond then [elif cond2 then2]... [else else]) -> if/else-if chain assigning to target"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (multiple-value-bind (then-forms elifs else-forms) (parse-if-branches (cddr form) :arc-style t)
      (let ((all-types nil)
            (result nil))
        ;; Then branch
        (let ((then-form (if (= (length then-forms) 1) (first then-forms) (cons 'do then-forms))))
          (multiple-value-bind (then-type then-stmts) (compile-expr-returning then-form env target)
            (push then-type all-types)
            (setf result (list (format nil "  if (~a) {" cond-code)))
            (dolist (s then-stmts) (setf result (append result (list (format nil "  ~a" s)))))))
        ;; Elif branches
        (dolist (elif-pair elifs)
          (let ((elif-cond (car elif-pair))
                (elif-body (cdr elif-pair)))
            (multiple-value-bind (econd-code ect) (compile-expr elif-cond env)
              (declare (ignore ect))
              (let ((elif-form (if (= (length elif-body) 1) (first elif-body) (cons 'do elif-body))))
                (multiple-value-bind (elif-type elif-stmts) (compile-expr-returning elif-form env target)
                  (push elif-type all-types)
                  (setf result (append result (list (format nil "  } else if (~a) {" econd-code))))
                  (dolist (s elif-stmts) (setf result (append result (list (format nil "  ~a" s))))))))))
        ;; Else branch
        (let ((else-form (cond
                           ((= (length else-forms) 1) (first else-forms))
                           (else-forms (cons 'do else-forms))
                           (t nil))))
          (multiple-value-bind (else-type else-stmts)
              (if else-form
                  (compile-expr-returning else-form env target)
                  (values (first all-types) (list (if (string= target ":return")
                                                      "  return 0;"
                                                      (format nil "  ~a = 0;" target)))))
            (push else-type all-types)
            (setf result (append result (list "  } else {")))
            (dolist (s else-stmts) (setf result (append result (list (format nil "  ~a" s)))))
            (setf result (append result (list "  }")))))
        ;; Compute result type from all branches
        (let ((result-type (reduce (lambda (a b)
                                     (cond ((eq a :void) b)
                                           ((eq b :void) a)
                                           ((type-equal-p a b) a)
                                           (t (make-union-type (list a b)))))
                                   (nreverse all-types))))
          (values result-type result))))))

(defun compile-do-stmt-returning (form env target)
  "(do stmt... expr) -> statements, last expr assigned to target"
  (let* ((exprs (rest form))
         (new-env (make-env :parent env)))
    (if (= (length exprs) 1)
        (compile-expr-returning (first exprs) new-env target)
        (let* ((body-stmts (compile-body (butlast exprs) new-env))
               (last-form (car (last exprs))))
          (multiple-value-bind (type last-stmts)
              (compile-expr-returning last-form new-env target)
            (values type (append body-stmts last-stmts)))))))

(defun compile-cond-stmt-returning (form env target)
  "(cond [t1 e1] [t2 e2] [else e3]) -> if-else chain assigning to target"
  (let ((clauses (rest form))
        (result nil)
        (first-clause t)
        (clause-types nil))
    (dolist (clause clauses)
      (let ((test (first clause))
            (body (second clause)))
        (cond
          ((and (symbolp test) (sym= test "else"))
           (setf result (append result (list "  } else {")))
           (multiple-value-bind (type stmts) (compile-expr-returning body env target)
             (unless (eq type :void) (push type clause-types))
             (dolist (s stmts) (setf result (append result (list (format nil "  ~a" s)))))))
          (first-clause
           (multiple-value-bind (test-code tt) (compile-expr test env)
             (declare (ignore tt))
             (setf result (append result (list (format nil "  if (~a) {" test-code))))
             (multiple-value-bind (type stmts) (compile-expr-returning body env target)
               (unless (eq type :void) (push type clause-types))
               (dolist (s stmts) (setf result (append result (list (format nil "  ~a" s))))))
             (setf first-clause nil)))
          (t
           (multiple-value-bind (test-code tt) (compile-expr test env)
             (declare (ignore tt))
             (setf result (append result (list (format nil "  } else if (~a) {" test-code))))
             (multiple-value-bind (type stmts) (compile-expr-returning body env target)
               (unless (eq type :void) (push type clause-types))
               (dolist (s stmts) (setf result (append result (list (format nil "  ~a" s)))))))))))
    (setf result (append result (list "  }")))
    ;; Compute result type from all clause types
    (let ((result-type (cond
                         ((null clause-types) :int)
                         ((every (lambda (t2) (type-equal-p (first clause-types) t2)) (rest clause-types))
                          (first clause-types))
                         (t (make-union-type clause-types)))))
      (values result-type result))))

(defun compile-let-stmt-returning (form env target)
  "(let name [type] init body...) -> let decl + body, last expr assigned to target"
  ;; Reuse compile-let-stmt for the binding, then compile-expr-returning for the body
  (let* ((let-stmts (compile-let-stmt form env))
         ;; Body forms: everything after (let name [type] init)
         (rest (cddr form))
         (rest (if (keywordp (first rest)) (cdr rest) rest))  ; skip type annotation
         (body-forms (cdr rest)))  ; skip init form
    (if (null body-forms)
        ;; No body: let itself is the value (just return the bound var)
        (let ((var-name (sanitize-name (string (second form)))))
          (values (env-lookup env (string (second form)))
                  (append let-stmts
                          (list (format nil "  ~a = ~a;" target var-name)))))
        ;; Has body: compile body, last form returns to target
        (let* ((init-stmts (butlast body-forms))
               (last-form (car (last body-forms)))
               (body-stmts (when init-stmts (compile-body init-stmts env))))
          (multiple-value-bind (type last-stmts)
              (compile-expr-returning last-form env target)
            (values type (append let-stmts (or body-stmts nil) last-stmts)))))))

(defun compile-get (form env)
  "(get struct field) — auto-derefs through RC wrapper"
  (multiple-value-bind (obj tp) (compile-expr (second form) env)
    (let* ((field-name (string (third form)))
           ;; For RC types, look up the inner struct
           (is-rc (rc-type-p tp))
           (struct-type (if is-rc (rc-inner-type tp) tp))
           (struct-name (when (eq (type-kind struct-type) :struct) (second struct-type)))
           (field-type (if (and struct-name (gethash struct-name *structs*))
                           (let ((fields (gethash struct-name *structs*)))
                             (cdr (assoc field-name fields :test #'equal)))
                           :int)))
      (if is-rc
          (values (format nil "~a->data.~a" obj (sanitize-name field-name))
                  (or field-type :int))
          (values (format nil "~a.~a" obj (sanitize-name field-name))
                  (or field-type :int))))))

(defun compile-vector (form env)
  "(vector elem ...) - C99 compound literal with malloc helper"
  (let* ((elems (rest form))
         (compiled (mapcar (lambda (e) (multiple-value-list (compile-expr e env))) elems))
         (elem-type (if compiled (second (first compiled)) :int))
         (vec-type (make-vector-type elem-type))
         (c-name (type-to-c vec-type))
         (c-elem (type-to-c elem-type))
         (n (length elems)))
    (if (= n 0)
        ;; Empty vector: just zero-initialize
        (values (format nil "(~a){NULL, 0, 0}" c-name) vec-type)
        ;; Non-empty: use helper function call that returns initialized Vector
        ;; Generate: sysp_mkvec_T(n, e0, e1, e2, ...)
        (let ((helper-name (format nil "sysp_mkvec_~a" (mangle-type-name elem-type))))
          (ensure-vector-helper helper-name c-elem c-name)
          (values (format nil "~a(~d~{, ~a~})" helper-name n (mapcar #'first compiled))
                  vec-type)))))

(define-accessor vector-ref "~a.data[~a]"
  (if (eq (type-kind tp) :vector)
      (second tp)
      :int))

(defun compile-vector-set (form env)
  "(vector-set! vec idx val)"
  (multiple-value-bind (vec vt) (compile-expr (second form) env)
    (multiple-value-bind (idx it) (compile-expr (third form) env)
      (declare (ignore it))
      (multiple-value-bind (val val-type) (compile-expr (fourth form) env)
        (declare (ignore val-type))
        (let ((elem-type (if (eq (type-kind vt) :vector)
                             (second vt)
                             :int)))
          (values (format nil "(~a.data[~a] = ~a)" vec idx val) elem-type))))))

(defun compile-vector-push (form env)
  "(vector-push! vec val) — push to dynamic vector (C99 compliant)"
  (multiple-value-bind (vec vt) (compile-expr (second form) env)
    (multiple-value-bind (val val-type) (compile-expr (third form) env)
      (declare (ignore val-type))
      (let* ((elem-type (if (eq (type-kind vt) :vector)
                            (second vt)
                            :int))
             (c-vec (type-to-c vt))
             (c-elem (type-to-c elem-type))
             (helper-name (format nil "sysp_vecpush_~a" (mangle-type-name elem-type))))
        (ensure-vector-push-helper helper-name c-vec c-elem)
        (values (format nil "~a(&~a, ~a)" helper-name vec val)
                :void)))))

(define-len vector-len "~a.len")

(defun compile-tuple (form env)
  "(tuple elem ...)"
  (let* ((elems (rest form))
         (compiled (mapcar (lambda (e) (multiple-value-list (compile-expr e env))) elems))
         (elem-types (mapcar #'second compiled))
         (tup-type (make-tuple-type elem-types))
         (c-name (type-to-c tup-type)))
    (values (format nil "(~a){~{~a~^, ~}}"
                    c-name (mapcar #'first compiled))
            tup-type)))

(defun compile-tuple-ref (form env)
  "(tuple-ref tup idx)"
  (multiple-value-bind (tup tt) (compile-expr (second form) env)
    (let* ((idx (third form))
           (elem-type (if (eq (type-kind tt) :tuple)
                          (nth (1+ idx) tt)
                          :int)))
      (values (format nil "~a._~d" tup idx) elem-type))))

(define-accessor array-ref "~a[~a]"
  (if (eq (type-kind tp) :array)
      (second tp)
      :int))

(defun compile-array-set (form env)
  "(array-set! arr idx val)"
  (multiple-value-bind (arr at) (compile-expr (second form) env)
    (multiple-value-bind (idx it) (compile-expr (third form) env)
      (declare (ignore it))
      (multiple-value-bind (val vt) (compile-expr (fourth form) env)
        (declare (ignore vt))
        (let ((elem-type (if (eq (type-kind at) :array)
                             (second at)
                             :int)))
          (values (format nil "(~a[~a] = ~a)" arr idx val) elem-type))))))

(defun compile-make-array (form env)
  "(make-array :type size) — stack-allocated zero-init array"
  (declare (ignore env))
  (let* ((elem-type (parse-type-annotation (second form)))
         (size (third form))
         (arr-type (make-array-type elem-type size)))
    (values (format nil "{0}" ) arr-type)))

;;; === Closures ===

(defun free-vars (body-forms params env)
  "Find free variables in a lambda body: names referenced but not in params or *global-env*.
   Returns list of (name . type) pairs."
  (let ((free nil)
        (param-names (mapcar (lambda (p) (if (consp p) (first p) (string p))) params)))
    (labels
        ((collect-if-free (name shadows)
           (let ((tp (env-lookup env name)))
             (when (and tp
                        (not (member name param-names :test #'equal))
                        (not (member name shadows :test #'equal))
                        (not (env-lookup *global-env* name))
                        (not (assoc name free :test #'equal)))
               (push (cons name tp) free))))
         (walk (f shadows)
           (cond
             ((null f) nil)
             ((symbolp f) (collect-if-free (string f) shadows))
             ((not (listp f)) nil)
             ((and (symbolp (first f)) (sym= (first f) "lambda"))
              ;; Nested lambda: add its params to shadows, walk body
              (let* ((inner-params (second f))
                     (new-shadows (append shadows
                                         (loop for x in (if (listp inner-params) inner-params nil)
                                               when (symbolp x) collect (string x))))
                     (rest (cddr f))
                     (bodies (if (keywordp (first rest)) (cdr rest) rest)))
                (dolist (b bodies) (walk b new-shadows))))
             (t (dolist (sub f) (walk sub shadows))))))
      (dolist (bf body-forms)
        (walk bf nil))
      (nreverse free))))

(defun compile-lambda (form env)
  "(lambda [params...] :ret-type body...) — compiles to Fn struct (fat pointer).
   All lambdas get void* _ctx as first C param. Capturing lambdas use env struct."
  (let* ((params-raw (second form))
         (rest-forms (cddr form))
         (params (parse-params params-raw))
         (ret-annotation (when (keywordp (first rest-forms))
                           (prog1 (parse-type-annotation (first rest-forms))
                             (setf rest-forms (cdr rest-forms)))))
         (body-forms rest-forms)
         (lambda-name (format nil "_lambda_~d" (incf *lambda-counter*)))
         ;; Free variable analysis
         (captures (free-vars body-forms params env))
         (capturing-p (not (null captures)))
         (env-struct-name (when capturing-p
                            (format nil "_env_~d" (incf *env-counter*))))
         (fn-env (make-env :parent env)))
    ;; Bind params in function env
    (dolist (p params)
      (env-bind fn-env (first p) (second p)))
    ;; For capturing lambdas, bind captures to _env->name in function env
    (when capturing-p
      (dolist (cap captures)
        (env-bind fn-env (car cap) (cdr cap))))
    ;; Compile body — use inner *pending-stmts* for lambda body, save results
    (let* ((all-but-last (butlast body-forms))
           (last-form (car (last body-forms)))
           (result-code nil)
           (result-type nil)
           (env-decl-stmt nil))
      (let ((*pending-stmts* nil))
        (multiple-value-bind (last-code last-type) (compile-expr last-form fn-env)
          (let* ((ret-type (or ret-annotation last-type))
                 (arg-types (mapcar #'second params))
                 (fn-type (make-fn-type arg-types ret-type))
                 (fn-c-type (fn-type-c-name fn-type))
                 ;; C params: void* _ctx, then user params
                 (user-param-str (format nil "~{~a~^, ~}"
                                        (mapcar (lambda (p)
                                                  (format nil "~a ~a"
                                                          (type-to-c (second p))
                                                          (sanitize-name (first p))))
                                                params)))
                 (c-param-str (if (string= user-param-str "")
                                  "void* _ctx"
                                  (format nil "void* _ctx, ~a" user-param-str)))
                 ;; Env cast + capture access at function start
                 (env-stmts (when capturing-p
                              (list (format nil "  ~a* _env = (~a*)_ctx;"
                                            env-struct-name env-struct-name))))
                 (body-stmts-raw (append (or (when all-but-last (compile-body all-but-last fn-env)) nil)
                                         *pending-stmts*))
                 ;; Fix captured var references in body stmts and last-code
                 (body-stmts (if capturing-p
                                 (mapcar (lambda (s) (fix-capture-refs s captures)) body-stmts-raw)
                                 body-stmts-raw))
                 (last-code-fixed (if capturing-p
                                      (fix-capture-refs last-code captures)
                                      last-code))
                 (all-body (append env-stmts body-stmts)))
            ;; Generate env struct typedef if capturing
            (when capturing-p
              (let ((fields (format nil "~{~a~^~%~}"
                                   (mapcar (lambda (cap)
                                             (format nil "  ~a ~a;"
                                                     (type-to-c (cdr cap))
                                                     (sanitize-name (car cap))))
                                           captures))))
                (push (format nil "typedef struct {~%~a~%} ~a;~%"
                              fields env-struct-name)
                      *struct-defs*)))
            ;; Forward decl
            (push (format nil "static ~a ~a(~a);"
                          (type-to-c ret-type) lambda-name c-param-str)
                  *lambda-forward-decls*)
            ;; Function body
            (push (format nil "static ~a ~a(~a) {~%~{~a~%~}  return ~a;~%}~%"
                          (type-to-c ret-type) lambda-name c-param-str
                          (or all-body nil)
                          last-code-fixed)
                  *functions*)
            ;; Prepare result
            (setf result-type fn-type)
            (if capturing-p
                (let ((env-var (format nil "_ctx_~d" *env-counter*)))
                  (setf env-decl-stmt
                        (format nil "  ~a ~a = {~{~a~^, ~}};"
                                env-struct-name env-var
                                (mapcar (lambda (cap) (sanitize-name (car cap))) captures)))
                  (setf result-code
                        (format nil "(~a){~a, &~a}" fn-c-type lambda-name env-var)))
                (setf result-code
                      (format nil "(~a){~a, NULL}" fn-c-type lambda-name))))))
      ;; Now back in outer scope — push env decl to OUTER *pending-stmts*
      (when env-decl-stmt
        (push env-decl-stmt *pending-stmts*))
      (values result-code result-type))))

(defun compile-spawn (form env)
  "(spawn expr) — run expr in a new thread, return Future<T>.
   Wraps expr as (lambda [] expr), compiles it, generates spawn struct + entry fn."
  (let* ((expr (second form))
         (spawn-id (incf *spawn-counter*))
         (spawn-struct (format nil "_spawn_~d" spawn-id))
         (spawn-run (format nil "_spawn_~d_run" spawn-id))
         ;; Wrap as zero-arg lambda to reuse capture machinery
         (lambda-form `(lambda nil ,expr)))
    ;; Compile the lambda — this generates _lambda_N, env struct, etc.
    (multiple-value-bind (lambda-code lambda-type) (compile-lambda lambda-form env)
      ;; lambda-type is (:fn () T), extract return type
      (let* ((ret-type (fn-type-ret lambda-type))
             (ret-c (type-to-c ret-type))
             (fut-type (make-future-type ret-type spawn-id))
             (fut-var (format nil "_fut_~d" spawn-id))
             ;; lambda-code is like (Fn_void_int){_lambda_N, &_ctx_M} or {_lambda_N, NULL}
             ;; Parse fn pointer and env pointer from the Fn struct literal
             (brace-start (position #\{ lambda-code))
             (brace-end (position #\} lambda-code :from-end t))
             (inner (subseq lambda-code (1+ brace-start) brace-end))
             (comma-pos (position #\, inner))
             (fn-ptr (string-trim " " (subseq inner 0 comma-pos)))
             (env-ptr (string-trim " " (subseq inner (1+ comma-pos)))))
        ;; Generate spawn struct typedef
        (push (format nil "typedef struct {~%  pthread_t _thread;~%  ~a _result;~%  ~a (*_fn)(void*);~%  void* _env;~%} ~a;~%"
                      ret-c ret-c spawn-struct)
              *struct-defs*)
        ;; Generate spawn entry function
        (push (format nil "static void* ~a(void* arg);~%" spawn-run)
              *lambda-forward-decls*)
        (push (format nil "static void* ~a(void* arg) {~%  ~a* s = (~a*)arg;~%  s->_result = s->_fn(s->_env);~%  if (s->_env) free(s->_env);~%  s->_env = NULL;~%  return NULL;~%}~%"
                      spawn-run spawn-struct spawn-struct)
              *functions*)
        ;; Build ordered list of statements, then push in reverse (LIFO stack)
        (let ((stmts nil)
              (heap-env-code nil))
          ;; Check if lambda was capturing — env-ptr will be &_ctx_N (not NULL)
          (when (and (not (string= env-ptr "NULL"))
                     (> (length env-ptr) 1)
                     (char= (char env-ptr 0) #\&))
            (let* ((env-var-name (subseq env-ptr 1))  ; strip &
                   (env-stmt (find-if (lambda (s) (search env-var-name s)) *pending-stmts*)))
              (when env-stmt
                (setf *pending-stmts* (remove env-stmt *pending-stmts* :count 1))
                (let* ((trimmed (string-trim '(#\Space #\Tab) env-stmt))
                       (space1 (position #\Space trimmed))
                       (env-struct-type (subseq trimmed 0 space1))
                       (eq-pos (position #\= trimmed))
                       (init-part (string-trim '(#\Space #\Tab #\;) (subseq trimmed (1+ eq-pos)))))
                  (push (format nil "  ~a* ~a = malloc(sizeof(~a));"
                                env-struct-type env-var-name env-struct-type)
                        stmts)
                  (push (format nil "  *~a = (~a)~a;"
                                env-var-name env-struct-type init-part)
                        stmts)
                  (setf heap-env-code env-var-name)))))
          ;; Spawn struct alloc + field init + pthread_create (in execution order)
          (push (format nil "  ~a* ~a = malloc(sizeof(~a));"
                        spawn-struct fut-var spawn-struct)
                stmts)
          (push (format nil "  ~a->_fn = ~a;" fut-var fn-ptr)
                stmts)
          (push (format nil "  ~a->_env = ~a;"
                        fut-var (or heap-env-code
                                    (if (string= env-ptr "NULL") "NULL" env-ptr)))
                stmts)
          (push (format nil "  pthread_create(&~a->_thread, NULL, ~a, ~a);"
                        fut-var spawn-run fut-var)
                stmts)
          ;; stmts is in reverse execution order; push in that order so *pending-stmts*
          ;; (also LIFO) emits them in correct execution order
          (dolist (s stmts)
            (push s *pending-stmts*)))
        (setf *uses-threads* t)
        (values fut-var fut-type)))))

(defun compile-await (form env)
  "(await future-expr) — block until thread completes, extract result."
  (multiple-value-bind (fut-code fut-type) (compile-expr (second form) env)
    (unless (future-type-p fut-type)
      (error "await: expected future type, got ~a" fut-type))
    (let* ((inner-type (future-inner-type fut-type))
           (result-var (format nil "_await_~d" (incf *temp-counter*)))
           (inner-c (type-to-c inner-type)))
      ;; Push in reverse execution order (LIFO stack)
      (push (format nil "  free(~a);" fut-code)
            *pending-stmts*)
      (push (format nil "  ~a ~a = ~a->_result;" inner-c result-var fut-code)
            *pending-stmts*)
      (push (format nil "  pthread_join(~a->_thread, NULL);" fut-code)
            *pending-stmts*)
      (values result-var inner-type))))

;;; === Condition System (CL-style) ===

(defun compile-signal (form env)
  "(signal :type) or (signal :type val) — signal a condition.
   Walks handler stack; does NOT unwind. If unhandled, aborts."
  (let* ((type-kw (second form))
         (type-name (string-downcase (symbol-name type-kw)))
         (has-val (>= (length form) 3))
         (stmts nil))
    (if has-val
        (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
          (let ((tmp (format nil "_sig_~d" (incf *temp-counter*))))
            (push (format nil "  ~a ~a = ~a;" (type-to-c val-type) tmp val-code) stmts)
            (push (format nil "  _sysp_signal(\"~a\", &~a);" type-name tmp) stmts)))
        (push (format nil "  _sysp_signal(\"~a\", NULL);" type-name) stmts))
    ;; Push in reverse order (LIFO)
    (dolist (s stmts) (push s *pending-stmts*))
    (setf *uses-conditions* t)
    (values "0" :int)))

(defun compile-invoke-restart (form env)
  "(invoke-restart :name) or (invoke-restart :name val) — longjmp to restart.
   Never returns."
  (let* ((name-kw (second form))
         (restart-name (string-downcase (symbol-name name-kw)))
         (has-val (>= (length form) 3))
         (stmts nil))
    (if has-val
        (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
          (let ((tmp (format nil "_irv_~d" (incf *temp-counter*))))
            (push (format nil "  ~a ~a = ~a;" (type-to-c val-type) tmp val-code) stmts)
            (push (format nil "  _sysp_invoke_restart(\"~a\", &~a, sizeof(~a));" restart-name tmp tmp) stmts)))
        (push (format nil "  _sysp_invoke_restart(\"~a\", NULL, 0);" restart-name) stmts))
    (dolist (s stmts) (push s *pending-stmts*))
    (setf *uses-conditions* t)
    (values "0" :int)))

(defun compile-restart-case (form env)
  "(restart-case body (:name [v :type] expr) ...) — establish named restart points.
   Each restart is a setjmp. Body runs normally; invoke-restart longjmps to matching restart."
  (let* ((body (second form))
         (clauses (cddr form))  ; list of (:name [params] body...)
         (rc-id (incf *restart-counter*))
         (result-var (format nil "_rc_res_~d" rc-id))
         (result-type nil)
         (restart-nodes nil)   ; list of (node-var name clause-params clause-body)
         (stmts nil))          ; accumulated C statements (execution order)
    ;; Parse restart clauses
    (let ((node-id 0))
      (dolist (clause clauses)
        (let* ((kw (first clause))
               (name (string-downcase (symbol-name kw)))
               (params-vec (second clause))
               (clause-body (cddr clause))
               (node-var (format nil "_r_~d_~d" rc-id (incf node-id))))
          (push (list node-var name params-vec clause-body) restart-nodes)))
      (setf restart-nodes (nreverse restart-nodes)))
    ;; Declare restart struct nodes and chain them
    (let ((prev-next "_restart_stack"))
      (dolist (rn restart-nodes)
        (let ((node-var (first rn))
              (name (second rn)))
          (push (format nil "  _sysp_restart ~a;" node-var) stmts)
          (push (format nil "  ~a.name = \"~a\";" node-var name) stmts)
          (push (format nil "  ~a.next = ~a;" node-var prev-next) stmts)
          (setf prev-next (format nil "&~a" node-var)))))
    ;; Push all onto restart stack
    (let ((last-node (first (last restart-nodes))))
      (push (format nil "  _restart_stack = &~a;" (first last-node)) stmts))
    ;; Generate the if/else if chain with setjmp
    ;; First: each restart clause as "if (setjmp(...) != 0)"
    ;; Last else: normal body
    (let ((first-clause t))
      (dolist (rn restart-nodes)
        (let* ((node-var (first rn))
               (name (second rn))
               (params-vec (third rn))
               (clause-body (fourth rn)))
          (declare (ignore name))
          ;; Parse params: [v :type] or []
          (let ((has-param (and params-vec (> (length params-vec) 0))))
            (if first-clause
                (push (format nil "  if (setjmp(~a.buf) != 0) {" node-var) stmts)
                (push (format nil "  } else if (setjmp(~a.buf) != 0) {" node-var) stmts))
            (setf first-clause nil)
            ;; Extract param and compile clause body
            (let ((clause-env (make-env :parent env)))
              (if has-param
                  ;; Bind the param from restart value
                  (let* ((parsed-params (parse-params params-vec))
                         (param-name (first (first parsed-params)))
                         (param-type (second (first parsed-params)))
                         (param-c (sanitize-name param-name)))
                    (env-bind clause-env param-name param-type)
                    (push (format nil "    ~a ~a = *(~a*)~a.value;"
                                  (type-to-c param-type) param-c (type-to-c param-type) node-var)
                          stmts)
                    ;; Compile clause body (may be multiple forms)
                    (let ((*pending-stmts* nil))
                      (if (= (length clause-body) 1)
                          (multiple-value-bind (code tp) (compile-expr (first clause-body) clause-env)
                            (dolist (ps *pending-stmts*) (push ps stmts))
                            (push (format nil "    ~a = ~a;" result-var code) stmts)
                            (when (null result-type) (setf result-type tp)))
                          ;; Multiple body forms
                          (let* ((all-but-last (butlast clause-body))
                                 (last-form (car (last clause-body))))
                            (dolist (bf all-but-last)
                              (dolist (s (compile-stmt bf clause-env))
                                (push s stmts)))
                            (multiple-value-bind (code tp) (compile-expr last-form clause-env)
                              (dolist (ps *pending-stmts*) (push ps stmts))
                              (push (format nil "    ~a = ~a;" result-var code) stmts)
                              (when (null result-type) (setf result-type tp)))))))
                  ;; No params
                  (let ((*pending-stmts* nil))
                    (if (= (length clause-body) 1)
                        (multiple-value-bind (code tp) (compile-expr (first clause-body) clause-env)
                          (dolist (ps *pending-stmts*) (push ps stmts))
                          (push (format nil "    ~a = ~a;" result-var code) stmts)
                          (when (null result-type) (setf result-type tp)))
                        (let* ((all-but-last (butlast clause-body))
                               (last-form (car (last clause-body))))
                          (dolist (bf all-but-last)
                            (dolist (s (compile-stmt bf clause-env))
                              (push s stmts)))
                          (multiple-value-bind (code tp) (compile-expr last-form clause-env)
                            (dolist (ps *pending-stmts*) (push ps stmts))
                            (push (format nil "    ~a = ~a;" result-var code) stmts)
                            (when (null result-type) (setf result-type tp)))))))))))
    ;; else: normal body
    (push "  } else {" stmts)
    (let ((*pending-stmts* nil))
      (multiple-value-bind (code tp) (compile-expr body env)
        (dolist (ps *pending-stmts*) (push ps stmts))
        (push (format nil "    ~a = ~a;" result-var code) stmts)
        (when (null result-type) (setf result-type tp))))
    (push "  }" stmts)
    ;; Pop restart stack — restore from outermost restart's .next
    (let ((outermost (first restart-nodes)))
      (push (format nil "  _restart_stack = ~a.next;" (first outermost)) stmts))
    ;; Reverse stmts (we pushed in reverse) and prepend result var decl
    (setf stmts (nreverse stmts))
    (push (format nil "  volatile ~a ~a;" (type-to-c result-type) result-var) stmts)
    ;; Push all to *pending-stmts*
    (dolist (s (nreverse stmts)) (push s *pending-stmts*))
    (setf *uses-conditions* t)
    (values result-var result-type))))

(defun compile-handler-bind (form env)
  "(handler-bind ((:type [params] body...) ...) body...) — bind condition handlers.
   Handlers run in signaler's frame without unwinding.
   Each binding is (:condition-type [param :type] handler-body-forms...)."
  (let* ((bindings (second form))
         (body-forms (cddr form))
         (hb-id (incf *handler-counter*))
         (handler-nodes nil)  ; list of (node-var type-name)
         (stmts nil))
    ;; Process each binding: (:type [param :type] body...)
    (let ((binding-id 0))
      (dolist (binding bindings)
        (let* ((type-kw (first binding))
               (type-name (string-downcase (symbol-name type-kw)))
               (params-vec (second binding))
               (handler-body (cddr binding))
               (node-var (format nil "_h_~d_~d" hb-id (incf binding-id)))
               (wrap-id (incf *handler-wrap-counter*))
               (wrap-name (format nil "_handler_wrap_~d" wrap-id))
               (params (parse-params params-vec))
               (cond-param-name (first (first params)))
               (cond-param-type (second (first params)))
               (lambda-name (format nil "_lambda_~d" (incf *lambda-counter*)))
               (fn-env (make-env :parent env)))
          ;; Bind param in function env
          (env-bind fn-env cond-param-name cond-param-type)
          ;; Compile handler body
          (let ((*pending-stmts* nil))
            (let* ((all-but-last (butlast handler-body))
                   (last-form (car (last handler-body)))
                   (body-stmts (when all-but-last (compile-body all-but-last fn-env))))
              (multiple-value-bind (last-code last-type) (compile-expr last-form fn-env)
                (declare (ignore last-type))
                (let ((all-body (append body-stmts *pending-stmts*)))
                  ;; Generate the handler function (void return)
                  (push (format nil "static void ~a(void* _ctx, ~a ~a);"
                                lambda-name (type-to-c cond-param-type) (sanitize-name cond-param-name))
                        *lambda-forward-decls*)
                  (push (format nil "static void ~a(void* _ctx, ~a ~a) {~%~{~a~%~}  ~a;~%}~%"
                                lambda-name (type-to-c cond-param-type) (sanitize-name cond-param-name)
                                (or all-body nil) last-code)
                        *functions*)
                  ;; Generate void(*)(void*,void*) wrapper that casts void* → typed param
                  (push (format nil "static void ~a(void* _ctx, void* _cval);"
                                wrap-name)
                        *lambda-forward-decls*)
                  (push (format nil "static void ~a(void* _ctx, void* _cval) {~%  ~a(_ctx, *(~a*)_cval);~%}~%"
                                wrap-name lambda-name (type-to-c cond-param-type))
                        *functions*)))))
          ;; Generate handler struct node setup
          (push (format nil "  _sysp_handler ~a;" node-var) stmts)
          (push (format nil "  ~a.type = \"~a\";" node-var type-name) stmts)
          (push (format nil "  ~a.fn = ~a;" node-var wrap-name) stmts)
          (push (format nil "  ~a.env = NULL;" node-var) stmts)
          (push (format nil "  ~a.next = _handler_stack;" node-var) stmts)
          (push (format nil "  _handler_stack = &~a;" node-var) stmts)
          (push (list node-var type-name) handler-nodes))))
    ;; Compile body
    (let ((result-var (format nil "_hb_res_~d" hb-id))
          (result-type nil))
      ;; Compile body forms
      (let ((*pending-stmts* nil))
        (if (= (length body-forms) 1)
            (multiple-value-bind (code tp) (compile-expr (first body-forms) env)
              (dolist (ps *pending-stmts*) (push ps stmts))
              (push (format nil "  ~a = ~a;" result-var code) stmts)
              (setf result-type tp))
            (let* ((all-but-last (butlast body-forms))
                   (last-form (car (last body-forms))))
              (dolist (bf all-but-last)
                (dolist (s (compile-stmt bf env))
                  (push s stmts)))
              (multiple-value-bind (code tp) (compile-expr last-form env)
                (dolist (ps *pending-stmts*) (push ps stmts))
                (push (format nil "  ~a = ~a;" result-var code) stmts)
                (setf result-type tp)))))
      ;; Pop handler stack — restore from first node's .next
      (let ((first-node (first handler-nodes)))
        (push (format nil "  _handler_stack = ~a.next;" (first first-node)) stmts))
      ;; Reverse and prepend result decl
      (setf stmts (nreverse stmts))
      (push (format nil "  ~a ~a;" (type-to-c result-type) result-var) stmts)
      ;; Push all to *pending-stmts*
      (dolist (s (nreverse stmts)) (push s *pending-stmts*))
      (setf *uses-conditions* t)
      (values result-var result-type))))

(defun fix-capture-refs (code captures)
  "Replace captured variable names with _env->name in generated C code.
   Simple string replacement — works because sanitize-name produces unique C identifiers."
  (let ((result code))
    (dolist (cap captures)
      (let* ((c-name (sanitize-name (car cap)))
             (replacement (format nil "_env->~a" c-name)))
        ;; Replace standalone occurrences (word boundary)
        ;; Use a simple approach: replace with regex-like word boundaries
        (setf result (replace-c-identifier result c-name replacement))))
    result))

(defun replace-c-identifier (str old new)
  "Replace occurrences of C identifier `old` with `new` in `str`,
   only at word boundaries (not inside longer identifiers)."
  (let ((old-len (length old))
        (result (make-array 0 :element-type 'character :adjustable t :fill-pointer 0))
        (i 0)
        (len (length str)))
    (loop while (< i len) do
      (if (and (<= (+ i old-len) len)
               (string= str old :start1 i :end1 (+ i old-len))
               ;; Check left boundary: start of string or non-identifier char
               (or (= i 0)
                   (not (c-ident-char-p (char str (1- i)))))
               ;; Check right boundary: end of string or non-identifier char
               (or (= (+ i old-len) len)
                   (not (c-ident-char-p (char str (+ i old-len))))))
          (progn
            (loop for c across new do (vector-push-extend c result))
            (incf i old-len))
          (progn
            (vector-push-extend (char str i) result)
            (incf i))))
    (coerce result 'string)))

(defun c-ident-char-p (c)
  "Is c a valid C identifier character?"
  (or (alphanumericp c) (char= c #\_)))


(defun compile-set-expr (form env)
  "(set! name expr) as expression"
  (let ((target (second form)))
    (cond
      ;; (set! (get struct field) val) -> struct.field = val (or ->data.field for RC)
      ((and (listp target) (sym= (first target) "get"))
       (multiple-value-bind (obj tp) (compile-expr (second target) env)
         (let* ((field (string (third target)))
                (is-rc (rc-type-p tp))
                (accessor (if is-rc
                              (format nil "~a->data.~a" obj (sanitize-name field))
                              (format nil "~a.~a" obj (sanitize-name field)))))
           (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
             (values (format nil "(~a = ~a)" accessor val-code)
                     val-type)))))
      ;; (set! (deref ptr) val) -> *ptr = val
      ((and (listp target) (sym= (first target) "deref"))
       (multiple-value-bind (ptr-code pt) (compile-expr (second target) env)
         (declare (ignore pt))
         (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
           (values (format nil "(*~a = ~a)" ptr-code val-code) val-type))))
      ;; (set! (vector-ref vec idx) val) -> vec.data[idx] = val
      ((and (listp target) (sym= (first target) "vector-ref"))
       (multiple-value-bind (vec-code vt) (compile-expr (second target) env)
         (declare (ignore vt))
         (multiple-value-bind (idx-code it) (compile-expr (third target) env)
           (declare (ignore it))
           (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
             (values (format nil "(~a.data[~a] = ~a)" vec-code idx-code val-code)
                     val-type)))))
      ;; simple variable
      (t (let ((name (string target)))
           (when (and (env-lookup env name) (not (env-mutable-p env name)))
             (error "Cannot set! immutable variable '~a' (use let-mut for mutable bindings)" name))
           (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
             (values (format nil "(~a = ~a)" (sanitize-name name) val-code)
                     val-type)))))))

(defun compile-addr-of (form env)
  "(addr-of expr)"
  (multiple-value-bind (code tp) (compile-expr (second form) env)
    (values (format nil "(&~a)" code) (make-ptr-type tp))))

(defun compile-deref (form env)
  "(deref ptr)"
  (multiple-value-bind (code tp) (compile-expr (second form) env)
    (let ((pointee (if (eq (type-kind tp) :ptr)
                       (second tp)
                       :int)))
      (values (format nil "(*~a)" code) pointee))))

(defun compile-null-check (form env)
  "(null? expr) → (expr == NULL), returns :bool"
  (multiple-value-bind (code tp) (compile-expr (second form) env)
    (declare (ignore tp))
    (values (format nil "(~a == NULL)" code) :bool)))

(defun compile-cast (form env)
  "(cast :type expr)"
  (let ((target-type (parse-type-annotation (second form))))
    (multiple-value-bind (code tp) (compile-expr (third form) env)
      (declare (ignore tp))
      (values (format nil "((~a)~a)" (type-to-c target-type) code) target-type))))

(defun compile-sizeof (form env)
  "(sizeof :type) or (sizeof expr)"
  (declare (ignore env))
  (let ((arg (second form)))
    (if (keywordp arg)
        (values (format nil "sizeof(~a)" (type-to-c (parse-type-annotation arg)))
                :int)
        (values (format nil "sizeof(~a)" (sanitize-name (string arg)))
                :int))))

;;; === Union Type Ops ===

(defun compile-runtype (form env)
  "(runtype expr) → expr.tag (integer). For union types, returns the tag enum value."
  (multiple-value-bind (code tp) (compile-expr (second form) env)
    (declare (ignore tp))
    (values (format nil "~a.tag" code) :int)))

(defun compile-as (form env)
  "(as :type expr) → expr.as_type. Extract a specific variant from a union."
  (let* ((target-type (parse-type-annotation (second form)))
         (mname (mangle-type-name target-type)))
    (multiple-value-bind (code tp) (compile-expr (third form) env)
      (declare (ignore tp))
      (values (format nil "~a.as_~a" code mname) target-type))))

;;; === Value Type (cons cells, symbols, quote) ===

(defun wrap-as-value (code tp)
  "Wrap a compiled C expression as a Value based on its type"
  (setf *uses-value-type* t)
  (case (type-kind tp)
    (:int (format nil "val_int(~a)" code))
    (:float (format nil "val_float(~a)" code))
    (:f32 (format nil "val_float((double)~a)" code))
    (:str (format nil "val_str(~a)" code))
    (:symbol (format nil "val_sym(~a)" code))
    (:value code)  ; already a Value
    (:cons code)   ; cons is already a Value
    (:bool (format nil "val_int(~a)" code))
    (otherwise (format nil "val_int(~a)" code))))

(defun fresh-value-allocation-p (form)
  "Is this form a fresh Value allocation (cons/list/quote)? These have rc=1, don't need retain."
  (and (listp form)
       (symbolp (first form))
       (member (string (first form)) '("cons" "list" "quote" "quasiquote") :test #'string-equal)))

(defun needs-retain-for-storage-p (arg-form env)
  "Does this expression need val_retain when stored?
   YES for: variables (sharing), car/cdr (borrowed ref)
   NO for: fresh allocations (cons/list/quote already have rc=1), primitives"
  (cond
    ;; Fresh allocations don't need retain
    ((fresh-value-allocation-p arg-form) nil)
    ;; Variables need retain (shared ownership)
    ((and (symbolp arg-form)
          (not (sym= arg-form "nil"))
          (let ((tp (env-lookup env (string arg-form))))
            (and tp (value-type-p tp))))
     t)
    ;; car/cdr calls need retain (borrowed refs being stored)
    ((and (listp arg-form)
          (symbolp (first arg-form))
          (member (string (first arg-form)) '("car" "cdr") :test #'string-equal))
     t)
    ;; Everything else (primitives, nil, etc.) - no retain needed
    (t nil)))

(defun compile-cons (form env)
  "(cons x y)"
  (setf *uses-value-type* t)
  (multiple-value-bind (car-code car-type) (compile-expr (second form) env)
    (multiple-value-bind (cdr-code cdr-type) (compile-expr (third form) env)
      (let ((car-val (wrap-as-value car-code car-type))
            (cdr-val (wrap-as-value cdr-code cdr-type)))
        ;; Retain if storing borrowed ref or shared variable
        (when (needs-retain-for-storage-p (second form) env)
          (setf car-val (format nil "val_retain(~a)" car-val)))
        (when (needs-retain-for-storage-p (third form) env)
          (setf cdr-val (format nil "val_retain(~a)" cdr-val)))
        (values (format nil "val_cons(make_cons(~a, ~a))" car-val cdr-val)
                :value)))))

;; car/cdr with constant folding for quoted literals
(defun compile-car (form env)
  "(car x) - with constant folding for (car 'literal)"
  (setf *uses-value-type* t)
  (let ((arg (second form)))
    ;; Constant fold: (car '(a b c)) -> compile 'a directly
    (if (and (listp arg) (symbolp (first arg))
             (string-equal (string (first arg)) "quote")
             (listp (second arg)))
        (values (compile-quoted-datum (first (second arg))) :value)
        (multiple-value-bind (code tp) (compile-expr arg env)
          (declare (ignore tp))
          (values (format nil "sysp_car(~a)" code) :value)))))

(defun compile-cdr (form env)
  "(cdr x) - with constant folding for (cdr 'literal)"
  (setf *uses-value-type* t)
  (let ((arg (second form)))
    ;; Constant fold: (cdr '(a b c)) -> compile '(b c) directly
    (if (and (listp arg) (symbolp (first arg))
             (string-equal (string (first arg)) "quote")
             (listp (second arg)))
        (values (compile-quoted-datum (rest (second arg))) :value)
        (multiple-value-bind (code tp) (compile-expr arg env)
          (declare (ignore tp))
          (values (format nil "sysp_cdr(~a)" code) :value)))))
(define-value-accessor nilp "sysp_nilp" :bool)

(defun compile-list-expr (form env)
  "(list x y z ...) -> nested cons"
  (setf *uses-value-type* t)
  (if (null (rest form))
      (values "val_nil()" :value)
      (let ((elems (rest form)))
        (labels ((build (items)
                   (if (null items)
                       "val_nil()"
                       (multiple-value-bind (code tp) (compile-expr (first items) env)
                         (let ((val (wrap-as-value code tp)))
                           ;; Retain if storing borrowed ref or shared variable
                           (when (needs-retain-for-storage-p (first items) env)
                             (setf val (format nil "val_retain(~a)" val)))
                           (format nil "val_cons(make_cons(~a, ~a))"
                                   val (build (rest items))))))))
          (values (build elems) :value)))))

(defun compile-quote (form env)
  "(quote datum) — compile quoted literal to runtime Value"
  (declare (ignore env))
  (setf *uses-value-type* t)
  (values (compile-quoted-datum (second form)) :value))

(defun compile-quoted-datum (datum)
  "Recursively compile a quoted datum to C code building Value cells"
  (cond
    ((null datum) "val_nil()")
    ((integerp datum) (format nil "val_int(~d)" datum))
    ((floatp datum) (format nil "val_float(~f)" datum))
    ((stringp datum) (format nil "val_str(~s)" datum))
    ((symbolp datum)
     (let ((name (string datum)))
       (cond
         ((string-equal name "nil") "val_nil()")
         (t (let ((id (intern-symbol name)))
              (format nil "val_sym(~d)" id))))))
    ((listp datum)
     (format nil "val_cons(make_cons(~a, ~a))"
             (compile-quoted-datum (first datum))
             (compile-quoted-datum (rest datum))))
    (t (format nil "val_int(0)"))))

(defun compile-quasiquote (form env)
  "(quasiquote datum) — like quote but with ~unquote and ~@splice"
  (setf *uses-value-type* t)
  (values (compile-qq (second form) env) :value))

(defun compile-qq (datum env)
  "Recursively compile a quasiquoted datum"
  (cond
    ;; (unquote x) → evaluate x, wrap as Value
    ((and (listp datum) (symbolp (first datum))
          (string-equal (symbol-name (first datum)) "unquote"))
     (multiple-value-bind (code tp) (compile-expr (second datum) env)
       (wrap-as-value code tp)))
    ;; A list — build cons cells, handling splice
    ((listp datum)
     (compile-qq-list datum env))
    ;; Atom — same as quote
    (t (compile-quoted-datum datum))))

(defun compile-qq-list (items env)
  "Compile a quasiquoted list, handling splice"
  (if (null items)
      "val_nil()"
      (let ((first-item (first items))
            (rest-code (compile-qq-list (rest items) env)))
        (cond
          ;; (splice x) → append x to rest
          ((and (listp first-item) (symbolp (first first-item))
                (string-equal (symbol-name (first first-item)) "splice"))
           (multiple-value-bind (code tp) (compile-expr (second first-item) env)
             (let ((val (if (member (type-kind tp) '(:value :cons))
                            code
                            (wrap-as-value code tp))))
               (format nil "sysp_append(~a, ~a)" val rest-code))))
          ;; (unquote x) → evaluate and cons
          ((and (listp first-item) (symbolp (first first-item))
                (string-equal (symbol-name (first first-item)) "unquote"))
           (multiple-value-bind (code tp) (compile-expr (second first-item) env)
             (let ((val (wrap-as-value code tp)))
               ;; Retain if storing borrowed ref or shared variable
               (when (needs-retain-for-storage-p (second first-item) env)
                 (setf val (format nil "val_retain(~a)" val)))
               (format nil "val_cons(make_cons(~a, ~a))" val rest-code))))
          ;; Regular element — quote it and cons
          (t (format nil "val_cons(make_cons(~a, ~a))"
                     (compile-qq first-item env) rest-code))))))

(defun compile-sym-literal (form env)
  "(sym name) — get symbol ID for a name"
  (declare (ignore env))
  (setf *uses-value-type* t)
  (let* ((name (string (second form)))
         (id (intern-symbol name)))
    (values (format nil "~d" id) :symbol)))

(defun compile-sym-eq (form env)
  "(sym-eq? a b) — compare two Values as symbols"
  (setf *uses-value-type* t)
  (multiple-value-bind (a-code at) (compile-expr (second form) env)
    (declare (ignore at))
    (multiple-value-bind (b-code bt) (compile-expr (third form) env)
      (declare (ignore bt))
      (values (format nil "sysp_sym_eq(~a, ~a)" a-code b-code) :bool))))

(defun compile-gensym-expr (form env)
  "(gensym) — generate a unique symbol at runtime"
  (declare (ignore form env))
  (setf *uses-value-type* t)
  (values "val_sym(_sysp_gensym++)" :value))

(defun c-fn-name (fn-name)
  "Get the C name for a function, checking overrides first."
  (or (gethash fn-name *name-overrides*)
      (sanitize-name fn-name)))

(defun compile-call (form env)
  "Compile a function call, handling variadic and polymorphic functions."
  (let* ((fn-name (string (first form)))
         (args (rest form)))
    ;; Check for polymorphic function — instantiate with concrete types
    (when (gethash fn-name *poly-fns*)
      (let* ((compiled-args-data (mapcar (lambda (a) (multiple-value-list (compile-expr a env))) args))
             (arg-codes (mapcar #'first compiled-args-data))
             (arg-types (mapcar #'second compiled-args-data))
             (mangled (instantiate-poly-fn fn-name arg-types))
             ;; Look up the instantiated function's return type
             (inst-fn-type (env-lookup *global-env* mangled))
             (ret-type (if (and inst-fn-type (eq (type-kind inst-fn-type) :fn))
                           (fn-type-ret inst-fn-type)
                           (first arg-types))))  ; fallback for identity-like
        (return-from compile-call
          (values (format nil "~a(~{~a~^, ~})" mangled arg-codes) ret-type))))
    (if (gethash fn-name *structs*)
        (compile-struct-construct fn-name args env)
        (let* ((fn-type (env-lookup env fn-name))
               (fn-arg-types (when (and fn-type (eq (type-kind fn-type) :fn))
                               (fn-type-args fn-type)))
               (ret-type (if fn-type (fn-type-ret fn-type) :int))
               (variadic-p (and fn-arg-types (> (length fn-arg-types) 0)
                                (eq (type-kind (car (last fn-arg-types))) :value)))
               (fixed-count (if variadic-p (1- (length fn-arg-types)) (length fn-arg-types)))
               (compiled-args nil)
               (rest-list nil))
          ;; Build call
          (if variadic-p
              ;; Variadic: compile fixed args + pack rest into list
              (progn
                ;; Compile fixed args
                (dotimes (i fixed-count)
                  (push (multiple-value-list (compile-expr (nth i args) env)) compiled-args))
                (setf compiled-args (nreverse compiled-args))
                ;; Pack remaining args into a list
                (when (> (length args) fixed-count)
                  (setf *uses-value-type* t)
                  (let ((rest-args (subseq args fixed-count)))
                    (setf rest-list
                          (format nil "~{~a~^, ~}"
                                  (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env))))
                                          rest-args)))))
                (let ((all-args (mapcar #'first compiled-args))
                      (rest-code (if rest-list
                                     (format nil "sysp_list(~d, ~a)" (- (length args) fixed-count) rest-list)
                                     "val_nil()")))
                  (setf all-args (append all-args (list rest-code)))
                  (values (format nil "~a(~{~a~^, ~})" (c-fn-name fn-name) all-args)
                          ret-type)))
              ;; Non-variadic: compile all args directly
              (let ((compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args))
                    (is-fn-var (and (not (gethash fn-name *direct-fns*))
                                    fn-type
                                    (eq (type-kind fn-type) :fn))))
                (if is-fn-var
                    ;; Call through Fn struct: f.fn(f.env, args...)
                    (let ((c-name (sanitize-name fn-name)))
                      (values (format nil "~a.fn(~a.env~{, ~a~})"
                                      c-name c-name compiled-args)
                              ret-type))
                    ;; Direct function call
                    (values (format nil "~a(~{~a~^, ~})" (c-fn-name fn-name) compiled-args)
                            ret-type))))))))

(defun compile-struct-construct (name args env)
  "Compile struct construction — positional or named (designated initializer).
   Positional: (Point 10 20) → (Point){10, 20}
   Named: (Point :x 10 :y 20) → (Point){.x = 10, .y = 20}"
  (if (and args (keywordp (first args)))
      ;; Named initialization: (:field val :field val ...)
      (let ((inits nil)
            (remaining args))
        (loop while remaining do
          (let* ((field-kw (pop remaining))
                 (field-name (string-downcase (symbol-name field-kw)))
                 (val-form (pop remaining)))
            (multiple-value-bind (code tp) (compile-expr val-form env)
              (declare (ignore tp))
              (push (format nil ".~a = ~a" (sanitize-name field-name) code) inits))))
        (values (format nil "(~a){~{~a~^, ~}}" name (nreverse inits))
                (make-struct-type name)))
      ;; Positional initialization
      (let ((compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args)))
        (values (format nil "(~a){~{~a~^, ~}}" name compiled-args)
                (make-struct-type name)))))

;;; === Statement Compilation ===

(defun compile-body (forms env)
  "Compile a sequence of body forms, return list of C statement strings"
  (let ((stmts nil))
    (dolist (form forms)
      (let ((new-stmts (compile-stmt form env)))
        (setf stmts (append stmts new-stmts))))
    stmts))

(defun compile-stmt (form env)
  "Compile a single form as a statement, return list of C statement strings"
  ;; Try macro expansion first
  (when (and (listp form) (symbolp (first form)))
    (multiple-value-bind (expanded was-expanded) (macroexpand-1-sysp form)
      (when was-expanded
        (return-from compile-stmt (compile-stmt (macroexpand-all expanded) env)))))
  (cond
    ((and (listp form) (sym= (first form) "let"))
     (compile-let-stmt form env))
    ((and (listp form) (sym= (first form) "let-mut"))
     (compile-let-stmt form env))  ; same as let for now, mut is future annotation
    ((and (listp form) (sym= (first form) "print"))
     (compile-print-stmt form env))
    ((and (listp form) (sym= (first form) "println"))
     (compile-println-stmt form env))
    ((and (listp form) (sym= (first form) "printf"))
     (compile-printf-stmt form env))
    ((and (listp form) (sym= (first form) "if"))
     (compile-if-stmt form env))
    ((and (listp form) (sym= (first form) "when"))
     (compile-when-stmt form env))
    ((and (listp form) (sym= (first form) "unless"))
     (compile-unless-stmt form env))
    ((and (listp form) (sym= (first form) "while"))
     (compile-while-stmt form env))
    ((and (listp form) (sym= (first form) "for"))
     (compile-for-stmt form env))
    ((and (listp form) (sym= (first form) "set!"))
     (compile-set-stmt form env))
    ((and (listp form) (sym= (first form) "return"))
     (compile-return-stmt form env))
    ((and (listp form) (sym= (first form) "break"))
     (list "  break;"))
    ((and (listp form) (sym= (first form) "continue"))
     (list "  continue;"))
    ((and (listp form) (sym= (first form) "recur"))
     (compile-recur-stmt form env))
    ((and (listp form) (sym= (first form) "cond"))
     (compile-cond-stmt form env))
    ((and (listp form) (sym= (first form) "match"))
     (compile-match-stmt form env))
    ((and (listp form) (sym= (first form) "block"))
     (compile-block-stmt form env))
    ((and (listp form) (sym= (first form) "do"))
     ;; do as block: compile all sub-forms as statements
     ;; Use (for [var start end] body...) for loops
     (compile-body (rest form) env))
    ((and (listp form) (sym= (first form) "ptr-free"))
     (compile-ptr-free-stmt form env))
    ((and (listp form) (sym= (first form) "ptr-set!"))
     (compile-ptr-set-stmt form env))
    ((and (listp form) (sym= (first form) "c-stmt"))
     (compile-c-stmt form env))
    ((and (listp form) (sym= (first form) "do-while"))
     (compile-do-while-stmt form env))
    ((and (listp form) (sym= (first form) "switch"))
     (compile-switch-stmt form env))
    ((and (listp form) (sym= (first form) "pragma"))
     (list (format nil "#pragma ~a" (second form))))
    ((and (listp form) (sym= (first form) "kernel-launch"))
     (compile-kernel-launch-stmt form env))
    (t (let ((*pending-stmts* nil))
         (multiple-value-bind (code tp) (compile-expr form env)
           (declare (ignore tp))
           (append *pending-stmts*
                   (list (format nil "  ~a;" code))))))))

(defun compile-let-stmt (form env)
  "(let name expr) or (let name :type expr) or (let name (make-array :type size))
   (let-mut name expr) for mutable bindings"
  (let* ((is-mut (sym= (first form) "let-mut"))
         (name (string (second form)))
         (rest (cddr form))
         (type-ann (when (keywordp (first rest))
                     (prog1 (parse-type-annotation (first rest))
                       (setf rest (cdr rest)))))
         (init-form (first rest)))
    (let ((*pending-stmts* nil))
      (multiple-value-bind (init-code init-type) (compile-expr init-form env)
        (let* ((lifted-stmts *pending-stmts*)
               (final-type (or type-ann init-type))
               (c-name (sanitize-name name))
               ;; Retain if storing borrowed ref or shared variable (not fresh allocs)
               (needs-retain (and *uses-value-type*
                                 (value-type-p final-type)
                                 (needs-retain-for-storage-p init-form env))))
          (env-bind env name final-type)
          (when is-mut (env-mark-mutable env name))
          ;; Track Value-typed locals for release at scope exit
          (when (and *uses-value-type* (value-type-p final-type))
            (env-add-release env c-name))
          ;; Track RC-typed locals for release at scope exit
          (when (rc-type-p final-type)
            (env-add-rc-release env c-name (rc-inner-type final-type)))
          ;; Determine if this is an RC copy (variable → variable, needs retain)
          (let* ((rc-copy-p (and (rc-type-p final-type)
                                 (symbolp init-form)
                                 (not (null init-form))))
                 (decl (cond
                         ((eq (type-kind final-type) :array)
                          (list (format nil "  ~a ~a[~a] = ~a;"
                                        (type-to-c (second final-type))
                                        c-name
                                        (third final-type)
                                        init-code)))
                         (rc-copy-p
                          ;; RC copy: retain the source
                          (list (format nil "  ~a ~a = ~a; _rc_~a_retain(~a);"
                                        (type-to-c final-type) c-name init-code
                                        (mangle-type-name (rc-inner-type final-type)) c-name)))
                         (needs-retain
                          (list (format nil "  ~a ~a = val_retain(~a);"
                                        (type-to-c final-type) c-name init-code)))
                         (t
                          (list (format nil "  ~a ~a = ~a;"
                                        (type-to-c final-type) c-name init-code))))))
            (append lifted-stmts decl)))))))

(defun format-print-arg (val-code val-type)
  "Return format string and arg for a typed value (C99 format specifiers)
   Uses inttypes.h macros for portable fixed-width printing."
  (case (type-kind val-type)
    ;; Signed integers
    (:char (values "%c" val-code))
    (:short (values "%hd" val-code))
    (:int (values "%d" val-code))
    (:long (values "%ld" val-code))
    (:long-long (values "%lld" val-code))
    ;; Unsigned integers
    (:uchar (values "%u" val-code))
    (:ushort (values "%hu" val-code))
    (:uint (values "%u" val-code))
    (:ulong (values "%lu" val-code))
    (:ulong-long (values "%llu" val-code))
    ;; Fixed-width signed (portable via inttypes.h macros)
    (:i8 (values :pri "PRId8" val-code))
    (:i16 (values :pri "PRId16" val-code))
    (:i32 (values :pri "PRId32" val-code))
    (:i64 (values :pri "PRId64" val-code))
    ;; Fixed-width unsigned (portable via inttypes.h macros)
    (:u8 (values :pri "PRIu8" val-code))
    (:u16 (values :pri "PRIu16" val-code))
    (:u32 (values :pri "PRIu32" val-code))
    (:u64 (values :pri "PRIu64" val-code))
    ;; Floating point
    (:float (values "%f" val-code))
    (:f32 (values "%f" val-code))
    (:double (values "%f" val-code))
    (:f64 (values "%f" val-code))
    ;; Size/pointer types (C99)
    (:size (values "%zu" val-code))
    (:ptrdiff (values "%td" val-code))
    (:intptr (values :pri "PRIdPTR" val-code))
    (:uintptr (values :pri "PRIuPTR" val-code))
    ;; Strings and chars
    (:str (values "%s" val-code))
    ;; Bool
    (:bool (values "%s" (format nil "(~a ? \"true\" : \"false\")" val-code)))
    ;; Value types
    ((:value :cons) (values :value-print val-code))
    ;; Default to %d for unknown int-like types
    (otherwise (values "%d" val-code))))

(defun compile-print-stmt (form env)
  "(print expr) — print without newline"
  (multiple-value-bind (val-code val-type) (compile-expr (second form) env)
    (multiple-value-bind (fmt arg) (format-print-arg val-code val-type)
      (cond
        ((eq fmt :value-print)
         (list (format nil "  sysp_print_value(~a);" arg)))
        ((eq fmt :pri)
         ;; Use inttypes.h macros for portable fixed-width printing
         ;; arg is the macro name (e.g., "PRId64"), val-code is the value
         (list (format nil "  printf(\"%\" ~a, ~a);" arg val-code)))
        (t
         (list (format nil "  printf(\"~a\", ~a);" fmt arg)))))))

(defun compile-println-stmt (form env)
  "(println expr) or (println) — print with newline"
  (if (null (rest form))
      (list "  printf(\"\\n\");")
      (multiple-value-bind (val-code val-type) (compile-expr (second form) env)
        (multiple-value-bind (fmt arg) (format-print-arg val-code val-type)
          (cond
            ((eq fmt :value-print)
             (list (format nil "  sysp_print_value(~a); printf(\"\\n\");" arg)))
            ((eq fmt :pri)
             ;; Use inttypes.h macros for portable fixed-width printing
             (list (format nil "  printf(\"%\" ~a \"\\n\", ~a);" arg val-code)))
            (t
             (list (format nil "  printf(\"~a\\n\", ~a);" fmt arg))))))))

(defun c-escape-string (s)
  "Escape a CL string for C string literal content.
   Handles embedded quotes and actual newlines; backslash sequences from
   user source (e.g., \\\\n in sysp → \\n in CL string) pass through as-is."
  (with-output-to-string (out)
    (loop for c across s do
      (case c
        (#\" (write-string "\\\"" out))
        (#\Newline (write-string "\\n" out))
        (#\Tab (write-string "\\t" out))
        (#\Return (write-string "\\r" out))
        (otherwise (write-char c out))))))

(defun compile-printf-stmt (form env)
  "(printf fmt-string args...) → printf(fmt, arg1, arg2, ...)"
  (let* ((fmt-str (second form))
         (args (cddr form))
         (compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args)))
    (if compiled-args
        (list (format nil "  printf(\"~a\"~{, ~a~});" (c-escape-string fmt-str) compiled-args))
        (list (format nil "  printf(\"~a\");" (c-escape-string fmt-str))))))

(defun compile-if-stmt (form env)
  "(if cond then-body... [elif cond2 body2...]... [else else-body...])
   Also: (if cond then else) positional (no keywords, exactly 2 forms)"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (multiple-value-bind (then-forms elifs else-forms) (parse-if-branches (cddr form))
      (let ((result (list (format nil "  if (~a) {" cond-code))))
        ;; Then body
        (let ((then-env (make-env :parent env)))
          (dolist (s (compile-body then-forms then-env))
            (push (format nil "  ~a" s) result))
          (push "  }" result))
        ;; Elif chains
        (dolist (elif-pair elifs)
          (let ((elif-cond (car elif-pair))
                (elif-body (cdr elif-pair))
                (elif-env (make-env :parent env)))
            (multiple-value-bind (econd-code ect) (compile-expr elif-cond env)
              (declare (ignore ect))
              (setf (car result) (format nil "  } else if (~a) {" econd-code))
              (dolist (s (compile-body elif-body elif-env))
                (push (format nil "  ~a" s) result))
              (push "  }" result))))
        ;; Else body
        (when else-forms
          (let ((else-env (make-env :parent env)))
            (setf (car result) "  } else {")
            (dolist (s (compile-body else-forms else-env))
              (push (format nil "  ~a" s) result))
            (push "  }" result)))
        (nreverse result)))))

(defun compile-when-stmt (form env)
  "(when cond body...)"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let ((body-env (make-env :parent env))
          (result (list (format nil "  if (~a) {" cond-code))))
      (dolist (s (compile-body (cddr form) body-env))
        (push (format nil "  ~a" s) result))
      (push "  }" result)
      (nreverse result))))

(defun compile-unless-stmt (form env)
  "(unless cond body...)"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let ((body-env (make-env :parent env))
          (result (list (format nil "  if (!(~a)) {" cond-code))))
      (dolist (s (compile-body (cddr form) body-env))
        (push (format nil "  ~a" s) result))
      (push "  }" result)
      (nreverse result))))

(defun compile-while-stmt (form env)
  "(while cond body...)"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let ((body-env (make-env :parent env))
          (result (list (format nil "  while (~a) {" cond-code))))
      (dolist (s (compile-body (cddr form) body-env))
        (push (format nil "  ~a" s) result))
      ;; Release Value locals at end of each iteration
      (when *uses-value-type*
        (dolist (r (emit-releases body-env))
          (push (format nil "  ~a" r) result)))
      (push "  }" result)
      (nreverse result))))

(defun compile-for-stmt (form env)
  "(for [var start end] body...) or (for [var start end step] body...)"
  (let* ((spec (second form))
         (var-name (string (first spec)))
         (body-forms (cddr form))
         (body-env (make-env :parent env)))
    (env-bind body-env var-name :int)
    (multiple-value-bind (start-code st) (compile-expr (second spec) body-env)
      (declare (ignore st))
      (multiple-value-bind (end-code et) (compile-expr (third spec) body-env)
        (declare (ignore et))
        (let* ((step (fourth spec))
               (step-code (if step
                              (first (multiple-value-list (compile-expr step body-env)))
                              "1"))
               (c-var (sanitize-name var-name))
               (result (list (format nil "  for (int ~a = ~a; ~a < ~a; ~a += ~a) {"
                                     c-var start-code c-var end-code c-var step-code))))
          (dolist (s (compile-body body-forms body-env))
            (push (format nil "  ~a" s) result))
          ;; Release Value locals at end of each iteration
          (when *uses-value-type*
            (dolist (r (emit-releases body-env))
              (push (format nil "  ~a" r) result)))
          (push "  }" result)
          (nreverse result))))))

(defun compile-do-while-stmt (form env)
  "(do-while body... condition) — body always executes at least once."
  (let* ((all-forms (rest form))
         (body-forms (butlast all-forms))
         (cond-form (car (last all-forms)))
         (body-env (make-env :parent env))
         (result (list "  do {")))
    (dolist (s (compile-body body-forms body-env))
      (push (format nil "  ~a" s) result))
    (multiple-value-bind (cond-code ct) (compile-expr cond-form body-env)
      (declare (ignore ct))
      (push (format nil "  } while (~a);" cond-code) result))
    (nreverse result)))

(defun compile-switch-stmt (form env)
  "(switch expr (val body...) ... (default body...)) — C switch statement."
  (multiple-value-bind (expr-code et) (compile-expr (second form) env)
    (declare (ignore et))
    (let ((clauses (cddr form))
          (result (list (format nil "  switch (~a) {" expr-code))))
      (dolist (clause clauses)
        (let* ((head (first clause))
               (body-forms (rest clause))
               (is-default (and (symbolp head) (sym= head "default"))))
          (if is-default
              (push "    default: {" result)
              (let ((case-code (first (multiple-value-list (compile-expr head env)))))
                (push (format nil "    case ~a: {" case-code) result)))
          (dolist (s (compile-body body-forms env))
            (push (format nil "    ~a" s) result))
          (push "      break;" result)
          (push "    }" result)))
      (push "  }" result)
      (nreverse result))))

(defun compile-kernel-launch-stmt (form env)
  "(kernel-launch name (grid block) args...) — emits name<<<grid,block>>>(args)"
  (let* ((name (sanitize-name (string (second form))))
         (config (third form))
         (args (cdddr form)))
    (multiple-value-bind (grid-code gt) (compile-expr (first config) env)
      (declare (ignore gt))
      (multiple-value-bind (block-code bt) (compile-expr (second config) env)
        (declare (ignore bt))
        (let ((arg-codes nil))
          (dolist (a args)
            (multiple-value-bind (ac at) (compile-expr a env)
              (declare (ignore at))
              (push ac arg-codes)))
          (setf arg-codes (nreverse arg-codes))
          (list (format nil "  ~a<<<~a, ~a>>>(~{~a~^, ~});"
                        name grid-code block-code arg-codes)))))))

(defun compile-set-stmt (form env)
  "(set! target val)"
  (let ((*pending-stmts* nil))
    (multiple-value-bind (code tp) (compile-set-expr form env)
      (declare (ignore tp))
      (append *pending-stmts*
              (list (format nil "  ~a;" code))))))

(defun compile-return-stmt (form env)
  "(return expr) or (return)"
  (if (rest form)
      (multiple-value-bind (code tp) (compile-expr (second form) env)
        (declare (ignore tp))
        (list (format nil "  return ~a;" code)))
      (list "  return;")))

;;; === Pattern Matching ===

(defun match-pattern-check (pattern scrutinee scrutinee-type env)
  "Parse a match pattern and return (condition-code bindings-stmts bound-env).
   Pattern types:
     (:type var) — union variant match with binding
     (:type literal) — union variant match with literal check inside
     (:type _) — union variant match, no binding
     42 / \"hello\" — literal equality check
     _ — wildcard (always matches)"
  (cond
    ;; Union variant pattern: (:type var) or (:type literal) or (:type _)
    ((and (listp pattern) (keywordp (first pattern)))
     (let* ((variant-keyword (first pattern))
            (variant-type (parse-type-annotation variant-keyword))
            (mname (mangle-type-name variant-type))
            (union-c-name (if (union-type-p scrutinee-type)
                              (ensure-union-type scrutinee-type)
                              (type-to-c scrutinee-type)))
            (tag-check (format nil "~a.tag == ~a_TAG_~a"
                               scrutinee union-c-name (string-upcase mname)))
            (inner (second pattern))
            (new-env (make-env :parent env)))
       (cond
         ;; (:type _) — match variant, no binding
         ((and (symbolp inner) (string-equal (string inner) "_"))
          (values tag-check nil new-env))
         ;; (:type var) where var is a symbol — bind extracted value
         ((and (symbolp inner) (not (integerp inner)))
          (let* ((var-name (string inner))
                 (c-var (sanitize-name var-name))
                 (extract (format nil "~a.as_~a" scrutinee mname))
                 (binding (format nil "  ~a ~a = ~a;" (type-to-c variant-type) c-var extract)))
            (env-bind new-env var-name variant-type)
            (values tag-check (list binding) new-env)))
         ;; (:type literal) — match variant + literal equality
         ((integerp inner)
          (let ((lit-check (format nil "(~a && ~a.as_~a == ~d)"
                                   tag-check scrutinee mname inner)))
            (values lit-check nil new-env)))
         ;; (:type string-literal)
         ((stringp inner)
          (pushnew "string.h" *includes* :test #'string=)
          (let ((lit-check (format nil "(~a && strcmp(~a.as_~a, ~s) == 0)"
                                   tag-check scrutinee mname inner)))
            (values lit-check nil new-env)))
         ;; Default: just tag check
         (t (values tag-check nil new-env)))))
    ;; Wildcard: always matches
    ((and (symbolp pattern) (string-equal (string pattern) "_"))
     (values nil nil (make-env :parent env)))
    ;; Integer literal match
    ((integerp pattern)
     (let ((check (format nil "~a == ~d" scrutinee pattern)))
       (values check nil (make-env :parent env))))
    ;; String literal match
    ((stringp pattern)
     (pushnew "string.h" *includes* :test #'string=)
     (let ((check (format nil "strcmp(~a, ~s) == 0" scrutinee pattern)))
       (values check nil (make-env :parent env))))
    ;; Bare symbol — bind scrutinee to name
    ((symbolp pattern)
     (let* ((var-name (string pattern))
            (c-var (sanitize-name var-name))
            (new-env (make-env :parent env))
            (binding (format nil "  ~a ~a = ~a;" (type-to-c scrutinee-type) c-var scrutinee)))
       (env-bind new-env var-name scrutinee-type)
       (values nil (list binding) new-env)))
    ;; Fallback
    (t (values nil nil (make-env :parent env)))))

(defun compile-match-stmt (form env)
  "(match scrutinee (pattern1 body1...) (pattern2 body2...) ...)"
  (let* ((*pending-stmts* nil)
         (scrutinee-form (second form))
         (clauses (cddr form)))
    (multiple-value-bind (scrut-code scrut-type) (compile-expr scrutinee-form env)
      (let* ((lifted *pending-stmts*)
             ;; Store scrutinee in a temp to avoid re-evaluation
             (tmp (fresh-tmp))
             (tmp-decl (format nil "  ~a ~a = ~a;" (type-to-c scrut-type) tmp scrut-code))
             (result (append lifted (list tmp-decl)))
             (first-clause t))
        (dolist (clause clauses)
          (let* ((pattern (first clause))
                 (body-forms (rest clause)))
            (multiple-value-bind (cond-code bindings clause-env)
                (match-pattern-check pattern tmp scrut-type env)
              (let ((branch-stmts (compile-body body-forms clause-env)))
                (cond
                  ;; Wildcard (no condition) — emit else
                  ((null cond-code)
                   (if first-clause
                       ;; Only clause, no condition needed
                       (progn
                         (when bindings (setf result (append result bindings)))
                         (setf result (append result (list "  {")))
                         (dolist (s branch-stmts)
                           (setf result (append result (list (format nil "  ~a" s)))))
                         (setf result (append result (list "  }"))))
                       (progn
                         (setf result (append result (list "  } else {")))
                         (when bindings
                           (dolist (b bindings)
                             (setf result (append result (list (format nil "  ~a" b))))))
                         (dolist (s branch-stmts)
                           (setf result (append result (list (format nil "  ~a" s))))))))
                  ;; First clause with condition
                  (first-clause
                   (setf result (append result (list (format nil "  if (~a) {" cond-code))))
                   (when bindings
                     (dolist (b bindings)
                       (setf result (append result (list (format nil "  ~a" b))))))
                   (dolist (s branch-stmts)
                     (setf result (append result (list (format nil "  ~a" s)))))
                   (setf first-clause nil))
                  ;; Subsequent clause
                  (t
                   (setf result (append result (list (format nil "  } else if (~a) {" cond-code))))
                   (when bindings
                     (dolist (b bindings)
                       (setf result (append result (list (format nil "  ~a" b))))))
                   (dolist (s branch-stmts)
                     (setf result (append result (list (format nil "  ~a" s)))))))))))
        (unless first-clause
          (setf result (append result (list "  }"))))
        result))))

(defun compile-match-stmt-returning (form env target)
  "(match scrutinee (pattern1 body1) ...) -> if-else chain assigning to target"
  (let* ((*pending-stmts* nil)
         (scrutinee-form (second form))
         (clauses (cddr form)))
    (multiple-value-bind (scrut-code scrut-type) (compile-expr scrutinee-form env)
      (let* ((lifted *pending-stmts*)
             (tmp (fresh-tmp))
             (tmp-decl (format nil "  ~a ~a = ~a;" (type-to-c scrut-type) tmp scrut-code))
             (result (append lifted (list tmp-decl)))
             (first-clause t)
             (clause-types nil))
        (dolist (clause clauses)
          (let* ((pattern (first clause))
                 (body-form (if (= (length (rest clause)) 1)
                                (second clause)
                                (cons 'do (rest clause)))))
            (multiple-value-bind (cond-code bindings clause-env)
                (match-pattern-check pattern tmp scrut-type env)
              (multiple-value-bind (body-type body-stmts)
                  (compile-expr-returning body-form clause-env target)
                (unless (eq body-type :void) (push body-type clause-types))
                (cond
                  ;; Wildcard
                  ((null cond-code)
                   (if first-clause
                       (progn
                         (when bindings (setf result (append result bindings)))
                         (setf result (append result (list "  {")))
                         (dolist (s body-stmts)
                           (setf result (append result (list (format nil "  ~a" s)))))
                         (setf result (append result (list "  }"))))
                       (progn
                         (setf result (append result (list "  } else {")))
                         (when bindings
                           (dolist (b bindings)
                             (setf result (append result (list (format nil "  ~a" b))))))
                         (dolist (s body-stmts)
                           (setf result (append result (list (format nil "  ~a" s))))))))
                  (first-clause
                   (setf result (append result (list (format nil "  if (~a) {" cond-code))))
                   (when bindings
                     (dolist (b bindings)
                       (setf result (append result (list (format nil "  ~a" b))))))
                   (dolist (s body-stmts)
                     (setf result (append result (list (format nil "  ~a" s)))))
                   (setf first-clause nil))
                  (t
                   (setf result (append result (list (format nil "  } else if (~a) {" cond-code))))
                   (when bindings
                     (dolist (b bindings)
                       (setf result (append result (list (format nil "  ~a" b))))))
                   (dolist (s body-stmts)
                     (setf result (append result (list (format nil "  ~a" s)))))))))))
        (unless first-clause
          (setf result (append result (list "  }"))))
        (let ((result-type (if clause-types
                               (reduce (lambda (a b)
                                         (cond ((eq a :void) b)
                                               ((eq b :void) a)
                                               ((type-equal-p a b) a)
                                               (t (make-union-type (list a b)))))
                                       clause-types)
                               :void)))
          (values result-type result))))))

(defun compile-match-expr (form env)
  "Expression form of match — lift to temp variable"
  (let ((tmp (fresh-tmp)))
    (multiple-value-bind (type stmts) (compile-match-stmt-returning form env tmp)
      (setf *pending-stmts* (append *pending-stmts*
                                    (list (format nil "  ~a ~a;" (type-to-c type) tmp))
                                    stmts))
      (values tmp type))))

(defun compile-cond-stmt (form env)
  "(cond [test1 body1...] [test2 body2...] [else bodyN...])"
  (let ((clauses (rest form))
        (result nil)
        (first-clause t))
    (dolist (clause clauses)
      (let ((test (first clause))
            (body (rest clause)))
        (cond
          ((and (symbolp test) (sym= test "else"))
           (push "  } else {" result)
           (dolist (s (compile-body body (make-env :parent env)))
             (push (format nil "  ~a" s) result)))
          (first-clause
           (multiple-value-bind (test-code tt) (compile-expr test env)
             (declare (ignore tt))
             (push (format nil "  if (~a) {" test-code) result)
             (dolist (s (compile-body body (make-env :parent env)))
               (push (format nil "  ~a" s) result))
             (setf first-clause nil)))
          (t
           (multiple-value-bind (test-code tt) (compile-expr test env)
             (declare (ignore tt))
             (push (format nil "  } else if (~a) {" test-code) result)
             (dolist (s (compile-body body (make-env :parent env)))
               (push (format nil "  ~a" s) result)))))))
    (push "  }" result)
    (nreverse result)))

(defun compile-block-stmt (form env)
  "(block body...) — new scope"
  (let ((body-env (make-env :parent env))
        (result (list "  {")))
    (dolist (s (compile-body (rest form) body-env))
      (push (format nil "  ~a" s) result))
    ;; Release Value locals at scope exit
    (when *uses-value-type*
      (dolist (r (emit-releases body-env))
        (push (format nil "  ~a" r) result)))
    (push "  }" result)
    (nreverse result)))

;;; === Top-Level Form Compilation ===

(defun parse-type-from-list (lst)
  "Parse a type annotation from LST, consuming tokens. Returns (type . remaining-lst).
   Handles multi-token types like :fn (:int :int) :int, (:list :int), (:variadic :int), (:cons T1 T2)."
  (let ((sym (pop lst)))
    (cond
      ;; Function type: :fn (arg-types...) :ret-type
      ((and (keywordp sym)
            (string-equal (symbol-name sym) "fn")
            lst
            (listp (first lst)))
       (let* ((arg-syms (pop lst))
              (ret-sym (pop lst))
              (arg-types (mapcar #'parse-type-annotation arg-syms))
              (ret-type (parse-type-annotation ret-sym)))
         (cons (make-fn-type arg-types ret-type) lst)))
      ;; List type: (:list elem-type)
      ((and (keywordp sym)
            (string-equal (symbol-name sym) "list")
            lst)
       (let ((elem-sym (pop lst)))
         (cons (make-list-type (parse-type-annotation elem-sym)) lst)))
      ;; Variadic type: (:variadic elem-type)
      ((and (keywordp sym)
            (string-equal (symbol-name sym) "variadic")
            lst)
       (let ((elem-sym (pop lst)))
         (cons (make-variadic-type (parse-type-annotation elem-sym)) lst)))
      ;; Cons type: (:cons car-type cdr-type)
      ((and (keywordp sym)
            (string-equal (symbol-name sym) "cons")
            lst)
       (let* ((car-sym (pop lst))
              (cdr-sym (pop lst))
              (car-type (parse-type-annotation car-sym))
              (cdr-type (parse-type-annotation cdr-sym)))
         (cons (make-cons-type car-type cdr-type) lst)))
      ;; Simple type
      (t (cons (parse-type-annotation sym) lst)))))

(defun parse-params (param-list &optional inferred-arg-types)
  "Parse parameters, handling [a :int & rest] for variadic functions.
   Uses inferred types for unannotated params when available.
   Returns (values fixed-params rest-param) where rest-param is nil or (name type)."
  (let ((fixed nil)
        (rest nil)
        (lst (if (listp param-list) (copy-list param-list) nil))
        (inf-idx 0)
        (in-rest nil))
    (loop while lst do
      (let ((item (pop lst)))
        (cond
          ((and (symbolp item) (string= (string item) "&"))
           (setf in-rest t))
          (t
           (let* ((name (string item))
                  (type (if (and lst (keywordp (first lst)))
                            (let ((result (parse-type-from-list lst)))
                              (setf lst (cdr result))
                              (car result))
                            (if (and inferred-arg-types
                                     (< inf-idx (length inferred-arg-types)))
                                (nth inf-idx inferred-arg-types)
                                :int))))
             (if in-rest
                 (setf rest (list name :value))
                 (push (list name type) fixed)))
           (incf inf-idx)))))
    (values (nreverse fixed) rest)))

(defun params-all (fixed rest)
  "Combine fixed and rest params for type registration."
  (if rest (append fixed (list rest)) fixed))

(defun compile-struct (form)
  "(struct Name [field :type, ...])"
  (let* ((name (string (second form)))
         ;; Register struct name early so fields can reference it (self-referential types)
         (already-registered (gethash name *structs*)))
    (unless already-registered
      (setf (gethash name *structs*) :forward-declared)  ; placeholder
      ;; Emit forward declaration
      (push (format nil "typedef struct ~a ~a;~%" name name) *struct-defs*))
    (let* ((fields-raw (third form))
           (fields (multiple-value-bind (fixed rest) (parse-params fields-raw)
                     (declare (ignore rest))
                     fixed)))
      (setf (gethash name *structs*)
            (mapcar (lambda (f) (cons (first f) (second f))) fields))
      (push (format nil "struct ~a {~%~{  ~a ~a;~%~}};~%"
                    name
                    (loop for f in fields
                          append (list (type-to-c (second f)) (sanitize-name (first f))))
                    )
            *struct-defs*))))

(defun compile-deftype (form)
  "(deftype Name TypeExpr) — register a named type alias and emit C typedef"
  (let* ((name (string (second form)))
         (type-expr (parse-type-expr (third form))))
    ;; Register in *type-aliases* for lookup by parse-type-annotation
    (setf (gethash name *type-aliases*) type-expr)
    ;; Emit C typedef
    (let ((c-type (type-to-c type-expr)))
      (push (format nil "typedef ~a ~a;~%" c-type name)
            *type-decls*))
    ;; For union types: register constructor functions in global env
    ;; e.g. (deftype IntOrFloat (:union :int :float)) registers:
    ;;   IntOrFloat-from-int : (:fn (:int) union-type)
    ;;   IntOrFloat-from-float : (:fn (:float) union-type)
    (when (union-type-p type-expr)
      (dolist (variant (union-variants type-expr))
        (let* ((mname (mangle-type-name variant))
               (fn-name (format nil "~a-from-~a" name mname))
               (c-name (format nil "~a_from_~a" (ensure-union-type type-expr) mname))
               (fn-type (make-fn-type (list variant) type-expr)))
          (env-bind *global-env* fn-name fn-type)
          (setf (gethash fn-name *direct-fns*) t)
          ;; Register name mapping so compile-call emits the right C name
          (setf (gethash fn-name *name-overrides*) c-name))))))

(defun form-uses-recur-p (forms)
  "Check if any form in the tree contains a (recur ...) call"
  (cond
    ((null forms) nil)
    ((symbolp forms) (sym= forms "recur"))
    ((listp forms)
     (or (and (symbolp (first forms)) (sym= (first forms) "recur"))
         (some #'form-uses-recur-p forms)))
    (t nil)))

(defun compile-recur-stmt (form env)
  "(recur args...) — assign params and goto top"
  (let* ((args (rest form))
         (compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args))
         (param-names (mapcar #'first *current-fn-params*))
         (stmts nil))
    ;; Use temp vars to avoid order-dependent assignment
    (loop for i from 0
          for arg-code in compiled-args
          for pname in param-names
          do (push (format nil "  __recur_~d = ~a;" i arg-code) stmts))
    ;; Declare temps and assign back
    (let ((temps nil) (assigns nil))
      (loop for i from 0
            for pname in param-names
            for ptype in (mapcar #'second *current-fn-params*)
            do (push (format nil "  ~a __recur_~d = ~a;"
                            (type-to-c ptype) i
                            (nth i compiled-args)) temps)
               (push (format nil "  ~a = __recur_~d;"
                            (sanitize-name pname) i) assigns))
      (append (nreverse temps)
              (nreverse assigns)
              (list "  goto _recur_top;")))))

(defun compile-foreign-struct (form)
  "(foreign-struct Name [field :type, ...]) — register struct from C header, no typedef emitted"
  (let* ((name (string (second form)))
         (fields-raw (third form))
         (fields (multiple-value-bind (fixed rest) (parse-params fields-raw)
                   (declare (ignore rest))
                   fixed)))
    (setf (gethash name *structs*)
          (mapcar (lambda (f) (cons (first f) (second f))) fields))))

(defun defn-is-poly-p (form)
  "Check if a defn form has any :? type annotations (polymorphic)."
  (let ((params-raw (third form))
        (rest-forms (cdddr form)))
    (or ;; Check params for :?
        (and (listp params-raw)
             (some (lambda (x) (and (keywordp x) (string-equal (symbol-name x) "?")))
                   params-raw))
        ;; Check return type annotation for :?
        (and (keywordp (first rest-forms))
             (string-equal (symbol-name (first rest-forms)) "?")))))

(defun mangle-poly-name (base-name concrete-types)
  "Generate a mangled name for a monomorphized instance."
  (format nil "~a_~{~a~^_~}" (sanitize-name base-name)
          (mapcar #'mangle-type-name concrete-types)))

(defun instantiate-poly-fn (name concrete-arg-types)
  "Instantiate a polymorphic function with concrete types.
   Returns the mangled C name."
  (let* ((poly-entry (gethash name *poly-fns*))
         (params-raw (first poly-entry))
         (ret-ann (second poly-entry))
         (body-forms (third poly-entry))
         (mangled (mangle-poly-name name concrete-arg-types)))
    (unless (gethash mangled *mono-instances*)
      (setf (gethash mangled *mono-instances*) t)
      ;; Build a concrete defn form with substituted types
      ;; Parse the original params to find which positions are :?
      (let ((new-params nil)
            (lst (if (listp params-raw) (copy-list params-raw) nil))
            (type-idx 0))
        (loop while lst do
          (let ((item (pop lst)))
            (push item new-params)
            (cond
              ;; :? annotation — substitute with concrete type
              ((and (keywordp item) (string-equal (symbol-name item) "?"))
               (pop new-params)  ; remove the :?
               ;; Push the concrete type keyword
               (let ((concrete (nth type-idx concrete-arg-types)))
                 (push (intern (string-upcase (mangle-type-name concrete)) :keyword) new-params))
               (incf type-idx))
              ;; Other type annotation — skip it for counting
              ((keywordp item)
               (incf type-idx))
              ;; Symbol (param name) — just keep
              (t nil))))
        (setf new-params (nreverse new-params))
        ;; Determine concrete return type
        (let* ((concrete-ret (if (eq ret-ann :poly)
                                 ;; For :? return, use the first concrete arg type as heuristic
                                 ;; (works for identity-like functions)
                                 (or (first concrete-arg-types) :int)
                                 ret-ann))
               (ret-keyword (if concrete-ret
                                (intern (string-upcase (mangle-type-name concrete-ret)) :keyword)
                                nil))
               ;; Build the synthetic defn form
               (synthetic-form `(,(intern "defn" :sysp)
                                 ,(intern mangled :sysp)
                                 ,new-params
                                 ,@(when ret-keyword (list ret-keyword))
                                 ,@body-forms)))
          ;; Compile it
          (compile-defn synthetic-form))))
    mangled))

(defun compile-defn (form)
  "(defn name [params] :ret-type body...) or
   (defn \"qualifier\" name [params] :ret-type body...) — with C function qualifier.
   Supports variadic [& rest]."
  ;; Extract optional C qualifier (e.g. \"__global__\", \"static inline\")
  (let* ((has-attr (stringp (second form)))
         (c-attr (when has-attr (second form)))
         ;; Shift form if attribute present so rest of function sees normal structure
         (form (if has-attr (cons (first form) (cddr form)) form)))
  ;; Check for polymorphic function — store template, don't compile
  (when (defn-is-poly-p form)
    (let* ((name (string (second form)))
           (params-raw (third form))
           (rest-forms (cdddr form))
           (ret-ann (when (keywordp (first rest-forms))
                      (prog1 (parse-type-annotation (first rest-forms))
                        (setf rest-forms (cdr rest-forms)))))
           (body-forms rest-forms))
      (setf (gethash name *poly-fns*) (list params-raw ret-ann body-forms))
      ;; Register a poly marker in global env so compile-call knows
      (env-bind *global-env* name :poly)
      (setf (gethash name *direct-fns*) t)
      (return-from compile-defn nil)))
  (let* ((name (string (second form)))
         (params-raw (third form))
         (rest-forms (cdddr form))
         ;; Look up inferred function type (from pre-pass)
         (inferred-fn-type (infer-env-lookup name))
         (inferred-arg-types (when (and inferred-fn-type
                                        (eq (type-kind inferred-fn-type) :fn))
                               (fn-type-args inferred-fn-type)))
         (inferred-ret-type (when (and inferred-fn-type
                                       (eq (type-kind inferred-fn-type) :fn))
                              (fn-type-ret inferred-fn-type)))
         ;; Parse params, handling & for variadic
         (params-fixed nil)
         (params-rest nil)
         (_ (multiple-value-setq (params-fixed params-rest)
              (parse-params params-raw inferred-arg-types)))
         (params (if params-rest (append params-fixed (list params-rest)) params-fixed))
         (variadic-p (not (null params-rest)))
         (ret-annotation (when (keywordp (first rest-forms))
                           (prog1 (parse-type-annotation (first rest-forms))
                             (setf rest-forms (cdr rest-forms)))))
         (body-forms rest-forms)
         ;; Also register for compile-time use by macros
         (raw-body (let ((rb (cdddr form)))
                     (if (keywordp (first rb)) (cdr rb) rb)))
         (env (make-env :parent *global-env*)))
    ;; Register function in global env (use inferred ret type if no annotation)
    (let* ((arg-types (mapcar #'second params))
           (ret-type (or ret-annotation inferred-ret-type :int))
           (fn-type (make-fn-type arg-types ret-type)))
      (env-bind *global-env* name fn-type)
      (setf (gethash name *direct-fns*) t))
    ;; Register for compile-time macro use (skip main)
    (unless (string-equal name "main")
      (setf (gethash name *macro-fns*) (list params-raw raw-body)))
    ;; Bind params
    (dolist (p params)
      (env-bind env (first p) (second p)))
    ;; Set recur context
    (let ((*current-fn-name* name)
          (*current-fn-params* params))
    ;; Compile body: all but last are statements, last is return value
    (let* ((all-but-last (butlast body-forms))
           (last-form (car (last body-forms)))
           (stmts (when all-but-last (compile-body all-but-last env)))
           (uses-recur (form-uses-recur-p body-forms))
           (ret-type (or ret-annotation inferred-ret-type :int))
           ;; For variadic: fixed params are C params, rest is Value list
           (c-params (if variadic-p params-fixed params))
           (param-str (format nil "~{~a~^, ~}"
                             (mapcar (lambda (p)
                                       (format nil "~a ~a"
                                               (type-to-c (second p))
                                               (sanitize-name (first p))))
                                     c-params)))
           ;; Add rest param as Value if variadic
           (_ (when variadic-p (setf *uses-value-type* t)))
           (param-str (if variadic-p
                          (format nil "~a~aValue ~a"
                                  param-str
                                  (if (string= param-str "") "" ", ")
                                  (sanitize-name (first params-rest)))
                          param-str))
           (c-name (if (or (string-equal name "main")
                            (string-equal name "sysp_main")
                            (string-equal name "sysp-main"))
                       "main"
                       (sanitize-name name))))
      ;; Handle void return or expression return
      (let (return-stmt)
        (if (eq (type-kind ret-type) :void)
            ;; Void: last form is just another statement, no return
            (progn
              (setf stmts (append stmts (compile-stmt last-form env)))
              (let ((releases (append (when *uses-value-type* (emit-releases env))
                                      (emit-rc-releases env))))
                (when releases
                  (setf return-stmt (format nil "~{~a~%~}" releases)))))
            ;; Non-void: last form is return value
            ;; If the last form is statement-like (if/cond/do/let) and uses recur,
            ;; use compile-expr-returning to handle branches that recur (goto)
            ;; vs branches that produce values (assign to temp).
            (cond
              ;; Return unlifting: statement-like, no Value/RC cleanup needed
              ;; Branches emit "return expr;" directly, no temp variable
              ((and (statement-like-p last-form) (not *uses-value-type*) (null (env-rc-releases env)))
               (multiple-value-bind (type ret-stmts)
                   (compile-expr-returning last-form env ":return")
                 (declare (ignore type))
                 (setf stmts (append stmts ret-stmts))))
              ;; Statement-like with Value/RC cleanup: need temp for releases before return
              ((statement-like-p last-form)
               (let* ((tmp (fresh-tmp))
                      (tmp-decl (format nil "  ~a ~a;" (type-to-c ret-type) tmp)))
                 (multiple-value-bind (type ret-stmts)
                     (compile-expr-returning last-form env tmp)
                   (declare (ignore type))
                   (setf stmts (append stmts (list tmp-decl) ret-stmts))
                   (let ((releases (append (when *uses-value-type* (emit-releases env))
                                           (emit-rc-releases env))))
                     (setf return-stmt
                           (if releases
                               (format nil "~{~a~%~}  return ~a;~%" releases tmp)
                               (format nil "  return ~a;~%" tmp)))))))
              ;; Normal: compile last form as expression
              (t
               (let ((*pending-stmts* nil))
                 (multiple-value-bind (last-code lt) (compile-expr last-form env)
                   (declare (ignore lt))
                   (when *pending-stmts*
                     (setf stmts (append stmts *pending-stmts*)))
                   (let* ((releases (append (when *uses-value-type* (emit-releases env))
                                            (emit-rc-releases env)))
                          (ret-var (and (symbolp last-form)
                                        (member (sanitize-name (string last-form))
                                                (env-releases env) :test #'equal))))
                     (setf return-stmt
                           (if (and ret-var *uses-value-type* releases)
                               (format nil "  val_retain(~a);~%~{~a~%~}  return ~a;~%"
                                       (sanitize-name (string last-form))
                                       releases
                                       last-code)
                               (if releases
                                   (format nil "~{~a~%~}  return ~a;~%" releases last-code)
                                   (format nil "  return ~a;~%" last-code))))))))))
          (let ((body-stmts (if uses-recur
                                  (cons "  _recur_top: ;" (or stmts nil))
                                  (or stmts nil)))
                ;; Look up any comments for this function
                (fn-comments (cdr (assoc name *function-comments* :test #'string-equal))))
            (push (format nil "~@[~{~a~%~}~]~@[~a ~]~a ~a(~a) {~%~{~a~%~}~@[~a~]}~%"
                          fn-comments
                          c-attr
                          (type-to-c ret-type)
                          c-name
                          (if (string= param-str "") "void" param-str)
                          body-stmts
                          return-stmt)
                  *functions*))
          ;; Forward declaration (skip for main, or for attributed functions — CUDA kernels etc.)
          (unless (or (string= c-name "main") c-attr)
            (push (format nil "~a ~a(~a);"
                          (type-to-c ret-type) c-name
                          (if (string= param-str "") "void" param-str))
                  *forward-decls*))))))))


(defun compile-extern (form)
  "(extern name [params] :ret-type) — declare external C function"
  (let* ((name (string (second form)))
         (params-raw (third form))
         (rest-forms (cdddr form))
         (params (parse-params params-raw))
         (ret-annotation (when (keywordp (first rest-forms))
                           (parse-type-annotation (first rest-forms))))
         (ret-type (or ret-annotation :int))
         (arg-types (mapcar #'second params))
         (fn-type (make-fn-type arg-types ret-type)))
    (env-bind *global-env* name fn-type)
    (setf (gethash name *direct-fns*) t)))

(defun compile-include (form)
  "(include \"header.h\")"
  (let ((header (second form)))
    (pushnew (if (stringp header) header (string header))
             *includes* :test #'string=)))

(defun compile-c-decl (form)
  "(c-decl \"raw C code\") — emit raw C at top level (after structs, before functions).
   Use for __global__ kernels, typedefs, inline functions, etc."
  (let ((code (second form)))
    (push (format nil "~a~%" code) *functions*)))

(defun compile-c-stmt (form env)
  "(c-stmt \"raw C;\") — emit raw C statement in function body."
  (declare (ignore env))
  (let ((code (second form)))
    (list (format nil "  ~a" code))))

(defun compile-c-expr (form env)
  "(c-expr \"raw C\" :type) — raw C expression with type annotation."
  (declare (ignore env))
  (let ((code (second form))
        (tp (parse-type-annotation (third form))))
    (values code tp)))

(defun compile-enum (form)
  "(enum Name [Variant1] [Variant2] ...) or (enum Name [Variant1 0] [Variant2 1] ...)"
  (let* ((name (string (second form)))
         (variants-raw (cddr form))
         (variants nil)
         (counter 0))
    (dolist (v variants-raw)
      (let* ((vspec (if (listp v) v (list v)))
             (vname (string (first vspec)))
             (vval (if (second vspec) (second vspec) counter)))
        (push (cons vname vval) variants)
        (setf counter (1+ (if (integerp vval) vval counter)))))
    (setf variants (nreverse variants))
    (setf (gethash name *enums*) variants)
    ;; Register each variant in global env as the enum type
    (dolist (v variants)
      (env-bind *global-env* (car v) (make-enum-type name)))
    ;; Emit C enum
    (push (format nil "typedef enum {~%~{  ~a = ~a~^,~%~}~%} ~a;~%"
                  (loop for v in variants
                        append (list (sanitize-name (car v)) (cdr v)))
                  name)
          *struct-defs*)))

(defun compile-toplevel-let (form mutable)
  "(let name :type expr) or (let-mut name :type expr) at top level"
  (let* ((name (string (second form)))
         (rest (cddr form))
         (type-ann (when (keywordp (first rest))
                     (prog1 (parse-type-annotation (first rest))
                       (setf rest (cdr rest)))))
         (init-form (first rest)))
    (multiple-value-bind (init-code init-type) (compile-expr init-form (make-env))
      (let ((final-type (or type-ann init-type)))
        (env-bind *global-env* name final-type)
        (when mutable (env-mark-mutable *global-env* name))
        (push (format nil "static ~a~a ~a = ~a;~%"
                      (if mutable "" "const ")
                      (type-to-c final-type) (sanitize-name name) init-code)
              *top-level-vars*)))))  ; emitted after functions for lambda ordering

;;; === Compile-Time Interpreter ===
;;; Evaluates sysp code at compile time for macro expansion.
;;; Works on CL values: cons=cons, symbols=symbols, nil=nil.

(defvar *macro-env* nil)  ; alist of (name . value) for compile-time eval

(defun interp-env-lookup (env name)
  (let ((found (assoc name env :test #'equal)))
    (if found (cdr found) nil)))

(defun interp-env-bind (env name val)
  (acons name val env))

(defun eval-sysp (form env)
  "Evaluate a sysp form at compile time. Returns a CL value."
  (cond
    ((null form) nil)
    ((integerp form) form)
    ((floatp form) form)
    ((stringp form) form)
    ((symbolp form)
     (let ((name (string form)))
       (cond
         ((string-equal name "true") t)
         ((string-equal name "false") nil)
         ((string-equal name "nil") nil)
         (t (let ((found (assoc name env :test #'equal)))
              (if found
                  (cdr found)
                  ;; Maybe it's a known macro-time function
                  (intern name :sysp)))))))
    ((listp form)
     (eval-sysp-list form env))
    (t form)))

(defun eval-sysp-list (form env)
  (let ((head (first form)))
    (cond
      ;; Special forms
      ((sym= head "quote") (second form))
      ((sym= head "quasiquote") (eval-quasiquote (second form) env))
      ((sym= head "if") (eval-if form env))
      ((sym= head "when") (eval-when-form form env))
      ((sym= head "unless") (eval-unless-form form env))
      ((sym= head "cond") (eval-cond form env))
      ((sym= head "do") (eval-do form env))
      ((sym= head "let") (eval-let form env))
      ((sym= head "let-mut") (eval-let form env))
      ((sym= head "set!") (eval-set form env))
      ((sym= head "lambda") (eval-lambda form env))
      ;; Arithmetic
      ((sym= head "+") (apply #'+ (mapcar (lambda (x) (eval-sysp x env)) (rest form))))
      ((sym= head "-") (if (= (length form) 2)
                           (- (eval-sysp (second form) env))
                           (apply #'- (mapcar (lambda (x) (eval-sysp x env)) (rest form)))))
      ((sym= head "*") (apply #'* (mapcar (lambda (x) (eval-sysp x env)) (rest form))))
      ((sym= head "/") (apply #'truncate (mapcar (lambda (x) (eval-sysp x env)) (rest form))))
      ((sym= head "%") (mod (eval-sysp (second form) env) (eval-sysp (third form) env)))
      ;; Comparison
      ((sym= head "==") (if (equal (eval-sysp (second form) env) (eval-sysp (third form) env)) t nil))
      ((sym= head "!=") (if (not (equal (eval-sysp (second form) env) (eval-sysp (third form) env))) t nil))
      ((sym= head "<") (if (< (eval-sysp (second form) env) (eval-sysp (third form) env)) t nil))
      ((sym= head ">") (if (> (eval-sysp (second form) env) (eval-sysp (third form) env)) t nil))
      ((sym= head "<=") (if (<= (eval-sysp (second form) env) (eval-sysp (third form) env)) t nil))
      ((sym= head ">=") (if (>= (eval-sysp (second form) env) (eval-sysp (third form) env)) t nil))
      ;; Logical
      ((sym= head "and") (every (lambda (x) (eval-sysp x env)) (rest form)))
      ((sym= head "or") (some (lambda (x) (eval-sysp x env)) (rest form)))
      ((sym= head "not") (not (eval-sysp (second form) env)))
      ;; List ops
      ((sym= head "cons") (cons (eval-sysp (second form) env) (eval-sysp (third form) env)))
      ((sym= head "car") (car (eval-sysp (second form) env)))
      ((sym= head "cdr") (cdr (eval-sysp (second form) env)))
      ((sym= head "nil?") (null (eval-sysp (second form) env)))
      ((sym= head "list") (mapcar (lambda (x) (eval-sysp x env)) (rest form)))
      ((sym= head "sym-eq?")
       (let ((a (eval-sysp (second form) env))
             (b (eval-sysp (third form) env)))
         (and (symbolp a) (symbolp b) (string= (string a) (string b)))))
      ((sym= head "gensym")
       (intern (format nil "_g~d" (incf *interp-gensym-counter*)) :sysp))
      ;; Print (for debugging macros at compile time)
      ((sym= head "println")
       (when (rest form)
         (format t "~a~%" (eval-sysp (second form) env)))
       nil)
      ;; Function call
      (t (eval-call form env)))))

(defun eval-if (form env)
  (let* ((rest (cddr form))
         (else-pos (position-if (lambda (x) (and (symbolp x) (sym= x "else"))) rest)))
    (if else-pos
        ;; Statement-style: (if cond then-body... else else-body...)
        (if (eval-sysp (second form) env)
            (eval-body (subseq rest 0 else-pos) env)
            (eval-body (subseq rest (1+ else-pos)) env))
        ;; Expression-style: (if cond then) or (if cond then else)
        (if (eval-sysp (second form) env)
            (eval-sysp (third form) env)
            (when (fourth form)
              (eval-sysp (fourth form) env))))))

(defun eval-when-form (form env)
  (when (eval-sysp (second form) env)
    (eval-body (cddr form) env)))

(defun eval-unless-form (form env)
  (unless (eval-sysp (second form) env)
    (eval-body (cddr form) env)))

(defun eval-cond (form env)
  (dolist (clause (rest form))
    (let ((test (first clause))
          (body (rest clause)))
      (when (or (and (symbolp test) (sym= test "else"))
                (eval-sysp test env))
        (return (eval-body body env))))))

(defun eval-do (form env)
  (eval-body (rest form) env))

(defun eval-body (forms env)
  "Evaluate forms in sequence, return last value"
  (let ((result nil)
        (current-env env))
    (dolist (f forms result)
      (if (and (listp f) (or (sym= (first f) "let") (sym= (first f) "let-mut")))
          ;; let extends env for subsequent forms
          (let ((name (string (second f)))
                (val (eval-sysp (third f) current-env)))
            (setf current-env (acons name val current-env))
            (setf result val))
          (setf result (eval-sysp f current-env))))))

(defun eval-let (form env)
  (let* ((name (string (second form)))
         (val (eval-sysp (third form) env)))
    (acons name val env)  ; return is only used for side effect in eval-body
    val))

(defun eval-set (form env)
  (let* ((name (string (second form)))
         (val (eval-sysp (third form) env))
         (cell (assoc name env :test #'equal)))
    (when cell (setf (cdr cell) val))
    val))

(defun eval-lambda (form env)
  "Create a closure: (params body... captured-env)"
  (let ((params (second form))
        (body (cddr form)))
    (list :closure params body env)))

(defun extract-param-names (params-raw)
  "Extract just the parameter names from a raw param list, skipping type annotations"
  (let ((names nil)
        (lst (if (listp params-raw) params-raw nil)))
    (loop while lst do
      (let ((item (pop lst)))
        (if (keywordp item)
            (pop lst)  ; skip :type annotations (though they don't have a following value here)
            (unless (keywordp item)
              (push (string item) names)
              ;; Skip following keyword if it's a type annotation
              (when (and lst (keywordp (first lst)))
                (pop lst))))))
    (nreverse names)))

(defun eval-call (form env)
  (let* ((fn-name (string (first form)))
         (args (mapcar (lambda (x) (eval-sysp x env)) (rest form)))
         ;; Check compile-time function table
         (fn-def (gethash fn-name *macro-fns*)))
    (cond
      (fn-def
       ;; Call a compile-time defined function
       (let* ((params-raw (first fn-def))
              (body (second fn-def))
              (param-names (extract-param-names params-raw))
              (call-env (loop for name in param-names
                              for a in args
                              collect (cons name a))))
         (eval-body body call-env)))
      ;; Check if it's a closure in the env
      (t (let ((fn-val (cdr (assoc fn-name env :test #'equal))))
           (if (and (listp fn-val) (eq (first fn-val) :closure))
               (let* ((params (second fn-val))
                      (body (third fn-val))
                      (closure-env (fourth fn-val))
                      (call-env (append
                                 (loop for p in (if (listp params) params (list params))
                                       for a in args
                                       collect (cons (string p) a))
                                 closure-env)))
                 (eval-body body call-env))
               (error "Unknown function in macro expansion: ~a" fn-name)))))))

(defun eval-quasiquote (datum env)
  "Process quasiquote at compile time — returns CL list structure"
  (cond
    ((null datum) nil)
    ((not (listp datum)) datum)
    ;; (unquote x) at top level
    ((and (symbolp (first datum))
          (string-equal (symbol-name (first datum)) "unquote"))
     (eval-sysp (second datum) env))
    ;; List — process elements
    (t (eval-qq-list datum env))))

(defun eval-qq-list (items env)
  (if (null items)
      nil
      (let ((first-item (first items)))
        (cond
          ;; (splice x) — append evaluated list
          ((and (listp first-item) (symbolp (first first-item))
                (string-equal (symbol-name (first first-item)) "splice"))
           (append (eval-sysp (second first-item) env)
                   (eval-qq-list (rest items) env)))
          ;; (unquote x) — evaluate and cons
          ((and (listp first-item) (symbolp (first first-item))
                (string-equal (symbol-name (first first-item)) "unquote"))
           (cons (eval-sysp (second first-item) env)
                 (eval-qq-list (rest items) env)))
          ;; Nested list — recurse
          ((listp first-item)
           (cons (eval-quasiquote first-item env)
                 (eval-qq-list (rest items) env)))
          ;; Atom — keep as-is
          (t (cons first-item (eval-qq-list (rest items) env)))))))

;;; === Main Compiler Driver ===

(defun compile-defmacro (form)
  "(defmacro name [params] body...) — register macro with compile-time evaluator"
  (let* ((name (string (second form)))
         (params (third form))
         (body (cdddr form)))
    ;; Register as a macro that evaluates its body at compile time
    (setf (gethash name *macros*)
          (lambda (call-form)
            (let* ((args (rest call-form))
                   ;; Bind params to unevaluated source forms
                   (env (loop for p in (if (listp params) params nil)
                              for a in args
                              collect (cons (string p) a))))
              (eval-body body env))))))

(defun compile-defn-ct (form)
  "(defn-ct name [params] body...) — compile-time only function (for macro helpers)"
  (let* ((name (string (second form)))
         (params-raw (third form))
         (rest-forms (cdddr form))
         (raw-body (if (keywordp (first rest-forms)) (cdr rest-forms) rest-forms)))
    (setf (gethash name *macro-fns*) (list params-raw raw-body))))

(defun sysp-comment-to-c (comment)
  "Convert a sysp comment (;; ...) to C comment (// ...)"
  (let ((text (string-left-trim '(#\;) comment)))
    (format nil "//~a" text)))

(defun compile-toplevel (forms)
  (let ((form-idx 0))
    (dolist (form forms)
      (when (listp form)
        ;; Get comments associated with this form
        (let ((comments (gethash form-idx *form-comments*)))
          ;; Handle defmacro and defn-ct first (no C emission)
          (cond
            ((sym= (first form) "defmacro") (compile-defmacro form))
            ((sym= (first form) "defn-ct") (compile-defn-ct form))
            (t
             ;; Expand macros, then compile
             (let ((expanded (macroexpand-all form)))
               (when (listp expanded)
                 ;; Queue comments to emit with definition
                 (when comments
                   (let ((c-comments (mapcar #'sysp-comment-to-c comments)))
                     (cond
                       ((sym= (first expanded) "defn")
                        (push (cons (string (second expanded)) c-comments) *function-comments*))
                       ((sym= (first expanded) "struct")
                        (push (cons (string (second expanded)) c-comments) *struct-comments*))
                       ((or (sym= (first expanded) "let")
                            (sym= (first expanded) "let-mut")
                            (sym= (first expanded) "const"))
                        (push (cons (string (second expanded)) c-comments) *var-comments*)))))
                 (cond
                   ((sym= (first expanded) "struct") (compile-struct expanded))
                   ((sym= (first expanded) "foreign-struct") (compile-foreign-struct expanded))
                   ((sym= (first expanded) "deftype") (compile-deftype expanded))
                   ((sym= (first expanded) "enum") (compile-enum expanded))
                   ((sym= (first expanded) "defn") (compile-defn expanded))
                   ((sym= (first expanded) "extern") (compile-extern expanded))
                   ((sym= (first expanded) "include") (compile-include expanded))
                   ((sym= (first expanded) "c-decl") (compile-c-decl expanded))
                   ((sym= (first expanded) "let") (compile-toplevel-let expanded nil))
                   ((sym= (first expanded) "let-mut") (compile-toplevel-let expanded t))
                   ((sym= (first expanded) "const") (compile-toplevel-let expanded nil)) ; legacy alias
                   (t (warn "Unknown top-level form: ~a" (first expanded))))))))))
      (incf form-idx))))

(defun emit-condition-preamble (out)
  "Emit the condition system runtime (restart/handler stacks, signal, invoke-restart)."
  (format out "/* Condition system runtime */~%")
  (format out "#include <setjmp.h>~%")
  (format out "#include <string.h>~%~%")
  (format out "typedef struct _sysp_restart {~%")
  (format out "    const char* name;~%")
  (format out "    jmp_buf buf;~%")
  (format out "    void* value;~%")
  (format out "    char _vbuf[16];~%")
  (format out "    struct _sysp_restart* next;~%")
  (format out "} _sysp_restart;~%~%")
  (format out "typedef struct _sysp_handler {~%")
  (format out "    const char* type;~%")
  (format out "    void (*fn)(void*, void*);~%")
  (format out "    void* env;~%")
  (format out "    struct _sysp_handler* next;~%")
  (format out "} _sysp_handler;~%~%")
  (format out "static SYSP_TLS _sysp_restart* _restart_stack = NULL;~%")
  (format out "static SYSP_TLS _sysp_handler* _handler_stack = NULL;~%~%")
  (format out "static void _sysp_signal(const char* type, void* val) {~%")
  (format out "    _sysp_handler* h = _handler_stack;~%")
  (format out "    while (h) {~%")
  (format out "        if (strcmp(h->type, type) == 0) {~%")
  (format out "            h->fn(h->env, val);~%")
  (format out "        }~%")
  (format out "        h = h->next;~%")
  (format out "    }~%")
  (format out "    fprintf(stderr, \"Unhandled condition: %s\\n\", type);~%")
  (format out "    abort();~%")
  (format out "}~%~%")
  (format out "static void _sysp_invoke_restart(const char* name, void* val, size_t vsize) {~%")
  (format out "    _sysp_restart* r = _restart_stack;~%")
  (format out "    while (r) {~%")
  (format out "        if (strcmp(r->name, name) == 0) {~%")
  (format out "            if (val && vsize <= sizeof(r->_vbuf)) {~%")
  (format out "                memcpy(r->_vbuf, val, vsize);~%")
  (format out "                r->value = r->_vbuf;~%")
  (format out "            } else {~%")
  (format out "                r->value = val;~%")
  (format out "            }~%")
  (format out "            longjmp(r->buf, 1);~%")
  (format out "        }~%")
  (format out "        r = r->next;~%")
  (format out "    }~%")
  (format out "    fprintf(stderr, \"No restart: %s\\n\", name);~%")
  (format out "    abort();~%")
  (format out "}~%~%"))

(defun emit-value-preamble (out)
  "Emit the Value/Cons/Symbol type system preamble with readable formatting"
  ;; Type definitions
  (format out "/*~%")
  (format out " * Value Type System~%")
  (format out " * Tagged union for dynamic values: nil, int, float, string, symbol, cons~%")
  (format out " */~%~%")

  (format out "typedef uint32_t Symbol;~%")
  (format out "typedef struct Cons Cons;~%~%")

  (format out "typedef enum {~%")
  (format out "    VAL_NIL,~%")
  (format out "    VAL_INT,~%")
  (format out "    VAL_FLOAT,~%")
  (format out "    VAL_STR,~%")
  (format out "    VAL_SYM,~%")
  (format out "    VAL_CONS~%")
  (format out "} ValueTag;~%~%")

  (format out "typedef struct {~%")
  (format out "    ValueTag tag;~%")
  (format out "    union {~%")
  (format out "        int as_int;~%")
  (format out "        double as_float;~%")
  (format out "        const char* as_str;~%")
  (format out "        Symbol as_sym;~%")
  (format out "        Cons* as_cons;~%")
  (format out "    };~%")
  (format out "} Value;~%~%")

  (format out "struct Cons {~%")
  (format out "    Value car;~%")
  (format out "    Value cdr;~%")
  (format out "    int refcount;~%")
  (format out "};~%~%")

  ;; Value constructors
  (format out "/* Value constructors */~%")
  (format out "static Value val_nil(void) {~%")
  (format out "    return (Value){.tag = VAL_NIL};~%")
  (format out "}~%~%")

  (format out "static Value val_int(int x) {~%")
  (format out "    Value v = {.tag = VAL_INT};~%")
  (format out "    v.as_int = x;~%")
  (format out "    return v;~%")
  (format out "}~%~%")

  (format out "static Value val_float(double x) {~%")
  (format out "    Value v = {.tag = VAL_FLOAT};~%")
  (format out "    v.as_float = x;~%")
  (format out "    return v;~%")
  (format out "}~%~%")

  (format out "static Value val_str(const char* x) {~%")
  (format out "    Value v = {.tag = VAL_STR};~%")
  (format out "    v.as_str = x;~%")
  (format out "    return v;~%")
  (format out "}~%~%")

  (format out "static Value val_sym(Symbol x) {~%")
  (format out "    Value v = {.tag = VAL_SYM};~%")
  (format out "    v.as_sym = x;~%")
  (format out "    return v;~%")
  (format out "}~%~%")

  (format out "static Value val_cons(Cons* x) {~%")
  (format out "    Value v = {.tag = VAL_CONS};~%")
  (format out "    v.as_cons = x;~%")
  (format out "    return v;~%")
  (format out "}~%~%")

  (format out "static Cons* make_cons(Value car, Value cdr) {~%")
  (format out "    Cons* c = malloc(sizeof(Cons));~%")
  (format out "    c->car = car;~%")
  (format out "    c->cdr = cdr;~%")
  (format out "    c->refcount = 1;~%")
  (format out "    return c;~%")
  (format out "}~%~%")

  ;; Reference counting
  (format out "/* Reference counting */~%")
  (format out "static Value val_retain(Value v) {~%")
  (format out "    if (v.tag == VAL_CONS && v.as_cons)~%")
  (format out "        RC_INC(v.as_cons->refcount);~%")
  (format out "    return v;~%")
  (format out "}~%~%")

  (format out "static void val_release(Value v) {~%")
  (format out "    if (v.tag == VAL_CONS && v.as_cons && RC_DEC(v.as_cons->refcount) == 1) {~%")
  (format out "        val_release(v.as_cons->car);~%")
  (format out "        val_release(v.as_cons->cdr);~%")
  (format out "        free(v.as_cons);~%")
  (format out "    }~%")
  (format out "}~%~%")

  ;; Accessors (borrow semantics)
  (format out "/* Accessors (borrow semantics - caller retains if storing) */~%")
  (format out "static Value sysp_car(Value v) { return v.as_cons->car; }~%")
  (format out "static Value sysp_cdr(Value v) { return v.as_cons->cdr; }~%")
  (format out "static int sysp_nilp(Value v) { return v.tag == VAL_NIL; }~%~%")

  (format out "static int sysp_sym_eq(Value a, Value b) {~%")
  (format out "    return a.tag == VAL_SYM && b.tag == VAL_SYM && a.as_sym == b.as_sym;~%")
  (format out "}~%~%")

  ;; List operations
  (format out "/* List operations */~%")
  (format out "static Value sysp_append(Value lst, Value tail) {~%")
  (format out "    if (lst.tag == VAL_NIL)~%")
  (format out "        return val_retain(tail);~%")
  (format out "    return val_cons(make_cons(val_retain(lst.as_cons->car),~%")
  (format out "                              sysp_append(lst.as_cons->cdr, tail)));~%")
  (format out "}~%~%")

  (format out "static Value sysp_list(int n, ...) {~%")
  (format out "    va_list args;~%")
  (format out "    va_start(args, n);~%")
  (format out "    Value result = val_nil();~%")
  (format out "    Value* values = malloc(n * sizeof(Value));~%")
  (format out "    for (int i = 0; i < n; i++)~%")
  (format out "        values[i] = va_arg(args, Value);~%")
  (format out "    va_end(args);~%")
  (format out "    for (int i = n - 1; i >= 0; i--)~%")
  (format out "        result = val_cons(make_cons(val_retain(values[i]), result));~%")
  (format out "    free(values);~%")
  (format out "    return result;~%")
  (format out "}~%~%")

  (format out "static SYSP_TLS uint32_t _sysp_gensym = 0x80000000;~%~%")

  ;; Symbol table for printing
  (let ((max-id *symbol-counter*))
    (format out "static const char* _sym_names[~d] = {~%" (1+ max-id))
    (format out "    \"\"")
    (loop for i from 1 to max-id do
      (let ((name nil))
        (maphash (lambda (n id) (when (= id i) (setf name n))) *symbol-table*)
        (format out ",~%    \"~a\"" (or name ""))))
    (format out "~%};~%~%"))

  ;; Print function
  (format out "static void sysp_print_value(Value v) {~%")
  (format out "    switch (v.tag) {~%")
  (format out "    case VAL_NIL:~%")
  (format out "        printf(\"nil\");~%")
  (format out "        break;~%")
  (format out "    case VAL_INT:~%")
  (format out "        printf(\"%d\", v.as_int);~%")
  (format out "        break;~%")
  (format out "    case VAL_FLOAT:~%")
  (format out "        printf(\"%f\", v.as_float);~%")
  (format out "        break;~%")
  (format out "    case VAL_STR:~%")
  (format out "        printf(\"%s\", v.as_str);~%")
  (format out "        break;~%")
  (format out "    case VAL_SYM:~%")
  (format out "        if (v.as_sym < sizeof(_sym_names)/sizeof(_sym_names[0]))~%")
  (format out "            printf(\"%s\", _sym_names[v.as_sym]);~%")
  (format out "        else~%")
  (format out "            printf(\"g%u\", v.as_sym);~%")
  (format out "        break;~%")
  (format out "    case VAL_CONS: {~%")
  (format out "        printf(\"(\");~%")
  (format out "        sysp_print_value(v.as_cons->car);~%")
  (format out "        Value tail = v.as_cons->cdr;~%")
  (format out "        while (tail.tag == VAL_CONS) {~%")
  (format out "            printf(\" \");~%")
  (format out "            sysp_print_value(tail.as_cons->car);~%")
  (format out "            tail = tail.as_cons->cdr;~%")
  (format out "        }~%")
  (format out "        if (tail.tag != VAL_NIL) {~%")
  (format out "            printf(\" . \");~%")
  (format out "            sysp_print_value(tail);~%")
  (format out "        }~%")
  (format out "        printf(\")\");~%")
  (format out "        break;~%")
  (format out "    }~%")
  (format out "    }~%")
  (format out "}~%~%")

  ;; Symbol defines
  (format out "/* Symbol constants */~%")
  (maphash (lambda (name id)
             (format out "#define SYM_~a ~d~%"
                     (mangle-symbol-name name) id))
           *symbol-table*)
  (format out "~%"))

(defun emit-c (out-path)
  (with-open-file (out out-path :direction :output :if-exists :supersede)
    (format out "#include <stdio.h>~%")
    (format out "#include <stdlib.h>~%")
    (format out "#include <stdint.h>~%")   ; C99 fixed-width types
    (format out "#include <inttypes.h>~%") ; PRId64, PRIu64, etc.
    (format out "#include <stddef.h>~%")   ; size_t, ptrdiff_t
    (when *uses-value-type*
      (format out "#include <stdarg.h>~%"))
    (when *uses-threads*
      (format out "#include <pthread.h>~%"))
    (dolist (inc *includes*)
      (format out "#include <~a>~%" inc))
    (format out "~%")
    ;; Thread safety macros (always emitted — zero cost if single-threaded)
    (format out "/* Thread safety macros */~%")
    (format out "#ifndef SYSP_NO_THREADS~%")
    (format out "  #if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L && !defined(__STDC_NO_ATOMICS__)~%")
    (format out "    #include <stdatomic.h>~%")
    (format out "    #define RC_INC(x) atomic_fetch_add_explicit(&(x), 1, memory_order_relaxed)~%")
    (format out "    #define RC_DEC(x) atomic_fetch_sub_explicit(&(x), 1, memory_order_acq_rel)~%")
    (format out "    #define SYSP_TLS _Thread_local~%")
    (format out "  #elif defined(__GNUC__) || defined(__clang__)~%")
    (format out "    #define RC_INC(x) __sync_fetch_and_add(&(x), 1)~%")
    (format out "    #define RC_DEC(x) __sync_fetch_and_sub(&(x), 1)~%")
    (format out "    #define SYSP_TLS __thread~%")
    (format out "  #elif defined(_MSC_VER)~%")
    (format out "    #include <intrin.h>~%")
    (format out "    #define RC_INC(x) _InterlockedIncrement((long*)&(x))~%")
    (format out "    #define RC_DEC(x) _InterlockedDecrement((long*)&(x))~%")
    (format out "    #define SYSP_TLS __declspec(thread)~%")
    (format out "  #else~%")
    (format out "    #warning \"Unknown compiler: define RC_INC/RC_DEC or -DSYSP_NO_THREADS\"~%")
    (format out "    #define RC_INC(x) (++(x))~%")
    (format out "    #define RC_DEC(x) (--(x))~%")
    (format out "    #define SYSP_TLS~%")
    (format out "  #endif~%")
    (format out "#else~%")
    (format out "  #define RC_INC(x) (++(x))~%")
    (format out "  #define RC_DEC(x) (--(x))~%")
    (format out "  #define SYSP_TLS~%")
    (format out "#endif~%~%")
    ;; Condition system preamble (if needed)
    (when *uses-conditions*
      (emit-condition-preamble out))
    ;; Value type preamble (if needed)
    (when *uses-value-type*
      (emit-value-preamble out))
    ;; struct definitions & constants
    (dolist (s (nreverse *struct-defs*))
      (write-string s out)
      (terpri out))
    ;; generated type declarations
    (dolist (d (nreverse *type-decls*))
      (write-string d out)
      (terpri out))
    ;; forward declarations
    (dolist (fwd (nreverse *forward-decls*))
      (format out "~a~%" fwd))
    (when *forward-decls* (terpri out))
    ;; lambda forward declarations
    (dolist (fwd (nreverse *lambda-forward-decls*))
      (format out "~a~%" fwd))
    (when *lambda-forward-decls* (terpri out))
    ;; top-level variable declarations (after lambda forward decls, before functions)
    (dolist (v (nreverse *top-level-vars*))
      (write-string v out)
      (terpri out))
    ;; functions
    (dolist (f (nreverse *functions*))
      (write-string f out)
      (terpri out))))

(defun reset-state ()
  (setf *structs* (make-hash-table :test 'equal))
  (setf *enums* (make-hash-table :test 'equal))
  (setf *functions* nil)
  (setf *struct-defs* nil)
  (setf *lambda-counter* 0)
  (setf *temp-counter* 0)
  (setf *generated-types* (make-hash-table :test 'equal))
  (setf *type-decls* nil)
  (setf *forward-decls* nil)
  (setf *top-level-vars* nil)
  (setf *lambda-forward-decls* nil)
  (setf *global-env* (make-env))
  (setf *includes* nil)
  (setf *string-literals* nil)
  (setf *symbol-table* (make-hash-table :test 'equal))
  (setf *symbol-counter* 0)
  (setf *sysp-gensym-counter* #x80000000)
  (setf *uses-value-type* nil)
  (setf *macro-fns* (make-hash-table :test 'equal))
  (setf *interp-gensym-counter* 0)
  (setf *function-comments* nil)
  (setf *struct-comments* nil)
  (setf *var-comments* nil)
  (setf *type-aliases* (make-hash-table :test 'equal))
  (setf *name-overrides* (make-hash-table :test 'equal))
  (setf *poly-fns* (make-hash-table :test #'equal))
  (setf *mono-instances* (make-hash-table :test #'equal))
  (setf *included-files* (make-hash-table :test 'equal))
  (setf *direct-fns* (make-hash-table :test 'equal))
  (setf *env-counter* 0)
  (setf *spawn-counter* 0)
  (setf *uses-threads* nil)
  (setf *restart-counter* 0)
  (setf *handler-counter* 0)
  (setf *handler-wrap-counter* 0)
  (setf *uses-conditions* nil))

(defun compile-file-to-c (in-path out-path)
  (reset-state)
  (let* ((forms (read-sysp-file in-path))
         (abs-in (namestring (truename in-path)))
         (base-dir (make-pathname :directory (pathname-directory (truename in-path)))))
    ;; Mark main file as included so it won't be re-included
    (setf (gethash abs-in *included-files*) t)
    ;; Expand (use ...) forms before inference
    (setf forms (expand-uses forms base-dir))
    ;; Phase 1: Type inference (constraint generation + solving)
    (infer-toplevel forms)
    ;; Phase 2: Compilation (uses inferred types from *infer-env*)
    (compile-toplevel forms)
    (emit-c out-path)
    (format t "Compiled ~a -> ~a~%" in-path out-path)))

;;; === CLI Entry Point ===

(defun main ()
  (let ((args (cdr sb-ext:*posix-argv*)))
    (cond
      ;; --emit-header mode: sysp --emit-header input.sysp [output.sysph]
      ((and (>= (length args) 2) (string= (first args) "--emit-header"))
       (let* ((input (second args))
              (output (or (third args)
                          (concatenate 'string
                                       (subseq input 0 (position #\. input :from-end t))
                                       ".sysph"))))
         (emit-header input output)
         (format t "Header ~a -> ~a~%" input output)))
      ;; Normal compilation
      ((>= (length args) 1)
       (let* ((input (first args))
              (output (or (second args)
                          (concatenate 'string
                                       (subseq input 0 (position #\. input :from-end t))
                                       ".c"))))
         (compile-file-to-c input output)))
      (t
       (format *error-output* "Usage: sysp <input.sysp> [output.c]~%")
       (format *error-output* "       sysp --emit-header <input.sysp> [output.sysph]~%")
       (sb-ext:exit :code 1)))))

(main)
