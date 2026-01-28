;;;; sysp.lisp — Bootstrap compiler for Systems Lisp
;;;; Compiles .sysp files to C

(defpackage :sysp
  (:use :cl))
(in-package :sysp)

;;; === Types ===

(defstruct sysp-type
  (kind nil) ; :int :float :bool :void :str :char :struct :vector :tuple :fn :ptr :symbol :value :cons :unknown
  (name nil)
  (params nil)) ; type params (element types for vector/tuple, arg+ret for fn, pointee for ptr)

(defmacro deftypector (name kind)
  `(defun ,(intern (format nil "MAKE-~a-TYPE" (string-upcase name))) ()
     (make-sysp-type :kind ,kind)))

(deftypector int :int)
(deftypector long :long)
(deftypector long-long :long-long)
(deftypector float :float)
(deftypector double :double)
(deftypector void :void)
(deftypector bool :bool)
(deftypector str :str)
(deftypector char :char)
(deftypector u8 :u8)
(deftypector f32 :f32)
(deftypector symbol :symbol)
(deftypector value :value)
(deftypector cons :cons)
(deftypector nil :nil)  ; Empty list type

(defun make-ptr-type (pointee)
  (make-sysp-type :kind :ptr :params (list pointee)))

;; List type: (:list elem-type) - homogeneous, nil-terminated
(defun make-list-type (elem-type)
  (make-sysp-type :kind :list :params (list elem-type)))

;; Variadic type: (:variadic elem-type) - for rest params, incompatible with :list
(defun make-variadic-type (elem-type)
  (make-sysp-type :kind :variadic :params (list elem-type)))

;; Cons type: (:cons car-type cdr-type) - arbitrary pair
(defun make-cons-type (car-type cdr-type)
  (make-sysp-type :kind :cons :params (list car-type cdr-type)))

;; Struct type constructor
(defun make-struct-type (name)
  (make-sysp-type :kind :struct :name name))

;; Enum type constructor
(defun make-enum-type (name)
  (make-sysp-type :kind :enum :name name))

;; Function type constructor: (:fn (arg-types...) ret-type)
(defun make-fn-type (arg-types ret-type)
  (make-sysp-type :kind :fn :params (append arg-types (list ret-type))))

(defun make-vector-type (elem-type)
  (make-sysp-type :kind :vector :params (list elem-type)))

(defun make-tuple-type (elem-types)
  (make-sysp-type :kind :tuple :params elem-types))

(defun make-fn-type (arg-types ret-type)
  (make-sysp-type :kind :fn :params (append arg-types (list ret-type))))

(defun make-array-type (elem-type size)
  (make-sysp-type :kind :array :params (list elem-type size)))

(defun make-enum-type (name)
  (make-sysp-type :kind :enum :name name))

(defun make-struct-type (name)
  (make-sysp-type :kind :struct :name name))

;; NEW: Recursive list type - homogeneous, nil-terminated
(defun make-list-type (elem-type)
  (make-sysp-type :kind :list :params (list elem-type)))

;; NEW: Variadic type - distinct from list, compile-time only
(defun make-variadic-type (elem-type)
  (make-sysp-type :kind :variadic :params (list elem-type)))

;; NEW: Proper cons type with car and cdr types
(defun make-cons-type (car-type cdr-type)
  (make-sysp-type :kind :cons :params (list car-type cdr-type)))

(defun fn-type-ret (ft)
  (car (last (sysp-type-params ft))))

(defun fn-type-args (ft)
  (butlast (sysp-type-params ft)))

(defun type-equal-p (a b)
  (and (eq (sysp-type-kind a) (sysp-type-kind b))
       (equal (sysp-type-name a) (sysp-type-name b))
       (= (length (sysp-type-params a)) (length (sysp-type-params b)))
       (every #'type-equal-p
              (sysp-type-params a) (sysp-type-params b))))

;;; === Type Inference (Hindley-Milner) ===

;; Type variable counter
(defvar *tvar-counter* 0)

;; Temp variable counter for statement lifting
(defvar *tmp-counter* 0)

;; Pending statements to emit before current expression
(defvar *pending-stmts* nil)

;; Create a fresh type variable
(defun make-tvar ()
  (let ((id (incf *tvar-counter*)))
    (make-sysp-type :kind :tvar :name id :params nil)))
;; params slot used as binding: nil = free, (type) = bound

(defun tvar-id (tv) (sysp-type-name tv))
(defun tvar-bound (tv) (car (sysp-type-params tv)))
(defun tvar-bind! (tv type)
  (setf (sysp-type-params tv) (list type)))

(defun tvar-p (tp) (eq (sysp-type-kind tp) :tvar))

;; Follow type variable chains to find the concrete type (or unbound tvar)
(defun resolve-type (tp)
  (if (and (tvar-p tp) (tvar-bound tp))
      (let ((resolved (resolve-type (tvar-bound tp))))
        ;; Path compression: point directly to final target
        (tvar-bind! tp resolved)
        resolved)
      tp))

;; Occurs check: does tvar `tv` appear anywhere in `tp`?
(defun occurs-in-p (tv tp)
  (let ((tp (resolve-type tp)))
    (cond
      ((tvar-p tp) (= (tvar-id tv) (tvar-id tp)))
      ((sysp-type-params tp)
       (some (lambda (p) (occurs-in-p tv p)) (sysp-type-params tp)))
      (t nil))))

;; Numeric type checking and ranking for C-like promotion
(defun numeric-type-p (tp)
  "Check if a type is a numeric type (can participate in promotion)."
  (let ((kind (sysp-type-kind tp)))
    (member kind '(:int :long :long-long :float :double))))

(defun numeric-rank (tp)
  "Return the numeric rank of a type (higher = wider type)."
  (case (sysp-type-kind tp)
    (:int 1)
    (:long 2)
    (:long-long 3)
    (:float 4)
    (:double 5)
    (t 0)))

;; Unify two types. Returns t on success, nil on failure.
;; On failure, does NOT modify any bindings (unification is atomic per call).
;; For gradual typing: caller can fall back to :value on failure.
(defun unify (t1 t2)
  (let ((t1 (resolve-type t1))
        (t2 (resolve-type t2)))
    (cond
      ;; Same object or structurally equal
      ((eq t1 t2) t)
      ((type-equal-p t1 t2) t)

      ;; Type variable on left: bind it
      ((tvar-p t1)
       (if (occurs-in-p t1 t2)
           nil ; infinite type — fail
           (progn (tvar-bind! t1 t2) t)))

      ;; Type variable on right: bind it
      ((tvar-p t2)
       (if (occurs-in-p t2 t1)
           nil
           (progn (tvar-bind! t2 t1) t)))

      ;; :value unifies with anything (it's the Any type)
      ((eq (sysp-type-kind t1) :value) t)
      ((eq (sysp-type-kind t2) :value) t)

      ;; Same kind with params: unify pairwise
      ((and (eq (sysp-type-kind t1) (sysp-type-kind t2))
            (equal (sysp-type-name t1) (sysp-type-name t2))
            (= (length (sysp-type-params t1))
               (length (sysp-type-params t2))))
       (every #'unify (sysp-type-params t1) (sysp-type-params t2)))

      ;; List type compatibility:
      ;; (:list T) unifies with nil (empty list)
      ((and (eq (sysp-type-kind t1) :list) (eq (sysp-type-kind t2) :nil)) t)
      ((and (eq (sysp-type-kind t2) :list) (eq (sysp-type-kind t1) :nil)) t)

      ;; (:list T) unifies with (:cons T (:list T)) - homogeneous cons chain
      ((and (eq (sysp-type-kind t1) :list)
            (eq (sysp-type-kind t2) :cons))
       (let ((car-type (first (sysp-type-params t2)))
             (cdr-type (second (sysp-type-params t2))))
         (and (unify (first (sysp-type-params t1)) car-type)
              (unify t1 cdr-type))))  ; cdr should also be (:list T)
      ((and (eq (sysp-type-kind t2) :list)
            (eq (sysp-type-kind t1) :cons))
       (let ((car-type (first (sysp-type-params t1)))
             (cdr-type (second (sysp-type-params t1))))
         (and (unify (first (sysp-type-params t2)) car-type)
              (unify t2 cdr-type))))

      ;; Variadic is INCOMPATIBLE with list (explicitly fail)
      ;; This prevents accidental (sum-all '(1 2 3)) when variadic expected
      ((or (eq (sysp-type-kind t1) :variadic)
           (eq (sysp-type-kind t2) :variadic))
       nil)

      ;; Numeric type promotion (like C)
      ;; Integer promotion: int -> long -> long-long
      ;; Float promotion: float -> double
      ;; Mixed: integer promotes to float
      ((and (numeric-type-p t1) (numeric-type-p t2))
       ;; Allow unification if one can promote to the other
       (let ((rank1 (numeric-rank t1))
             (rank2 (numeric-rank t2)))
         ;; Can always unify if ranks are compatible
         ;; The result is the higher-ranked type
         t))

      ;; Incompatible types
      (t nil))))

;; Generalize: replace free tvars (not in env) with fresh quantified vars
;; Returns a type scheme: (:scheme (tvar-ids...) type)
(defun free-tvars (tp &optional (seen nil))
  "Collect all unbound type variable IDs in a type."
  (let ((tp (resolve-type tp)))
    (cond
      ((tvar-p tp)
       (if (member (tvar-id tp) seen) nil (list (tvar-id tp))))
      ((sysp-type-params tp)
       (reduce #'append
               (mapcar (lambda (p) (free-tvars p seen))
                       (sysp-type-params tp))
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
      scheme)) ; not a scheme, return as-is

(defun apply-subst (tp subst)
  "Replace tvar IDs in subst with their fresh tvars."
  (let ((tp (resolve-type tp)))
    (cond
      ((tvar-p tp)
       (let ((entry (assoc (tvar-id tp) subst)))
         (if entry (cdr entry) tp)))
      ((sysp-type-params tp)
       (make-sysp-type :kind (sysp-type-kind tp)
                       :name (sysp-type-name tp)
                       :params (mapcar (lambda (p) (apply-subst p subst))
                                       (sysp-type-params tp))))
      (t tp))))

;; Reset inference state (call before each compilation unit)
(defun reset-inference ()
  (setf *tvar-counter* 0))

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

;; === Inference Rule Macros ===

;; Simple inference rule: match symbol, return type
(defmacro definfer (sym ret-type)
  `((sym= head ,sym) ,ret-type))

;; Inference rule with function call
(defmacro definfer-call (sym fn)
  `((sym= head ,sym) (,fn form)))

;; Infer binary op with unification
(defmacro definfer-bin (sym)
  `((member (string head) '(,sym) :test #'string-equal)
    (let ((lt (infer-expr (second form)))
          (rt (infer-expr (third form))))
      (unify lt rt)
      lt)))

;; Infer comparison (returns bool)
(defmacro definfer-cmp (syms)
  `((member (string head) ',syms :test #'string-equal)
    (let ((lt (infer-expr (second form)))
          (rt (infer-expr (third form))))
      (unify lt rt)
      (make-bool-type))))

;; Resolve a type variable to its final concrete type, defaulting unbound tvars to :int
(defun resolve-or-default (tp)
  (let ((resolved (resolve-type tp)))
    (if (tvar-p resolved)
        (make-int-type)  ; unbound tvar defaults to int (gradual typing)
        (if (sysp-type-params resolved)
            (make-sysp-type :kind (sysp-type-kind resolved)
                           :name (sysp-type-name resolved)
                           :params (mapcar #'resolve-or-default
                                           (sysp-type-params resolved)))
            resolved))))

;; Infer the type of an expression, generating constraints via unification.
;; Returns the inferred type (may contain tvars until resolution).
(defun infer-expr (form)
  "Walk an expression form and return its inferred type."
  (cond
    ((null form) (make-nil-type))  ; nil is the empty list type
    ((integerp form) (make-int-type))
    ((floatp form) (make-float-type))
    ((stringp form) (make-str-type))
    ((symbolp form)
     (let ((name (string form)))
       (cond
         ((string-equal name "true") (make-bool-type))
         ((string-equal name "false") (make-bool-type))
         ((string-equal name "null") (make-ptr-type (make-void-type)))
         (t (or (infer-env-lookup name) (make-tvar))))))
    ((listp form) (infer-list form))
    (t (make-int-type))))

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
         (make-bool-type)))

      ;; Logical: result is bool
      ((member (string head) '("and" "or" "not") :test #'string-equal) (make-bool-type))

      ;; Bitwise: operands are int, result is int
      ((member (string head) '("bit-and" "bit-or" "bit-xor" "bit-not" "shl" "shr")
               :test #'string-equal) (make-int-type))

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
       (let ((result (make-int-type)))
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
         (let ((body-type (make-int-type)))
           (dolist (f body)
             (setf body-type (infer-expr f)))
           (let ((ret-type (or ret-ann body-type)))
             ;; Restore env
             (setf *infer-env* old-env)
             (make-fn-type param-types ret-type)))))

      ;; nil? : returns bool
      ((sym= head "nil?") (make-bool-type))

      ;; cons: creates a cons cell
      ;; If cdr is a (:list T), result is (:list T) (homogeneous)
      ;; Otherwise result is (:cons car-type cdr-type)
      ((sym= head "cons")
       (let ((car-type (infer-expr (second form)))
             (cdr-type (infer-expr (third form))))
         (cond
           ;; If cdr is nil, create a new list
           ((eq (sysp-type-kind cdr-type) :nil)
            (make-list-type car-type))
           ;; If cdr is already a list of same type, extend it
           ((and (eq (sysp-type-kind cdr-type) :list)
                 (unify car-type (first (sysp-type-params cdr-type))))
            cdr-type)
           ;; Otherwise create an improper cons
           (t (make-cons-type car-type cdr-type)))))

      ;; car: extracts car from cons or list
      ((sym= head "car")
       (let ((cons-type (infer-expr (second form)))
             (elem-tvar (make-tvar)))
         (cond
           ;; If it's a list, return the element type
           ((eq (sysp-type-kind cons-type) :list)
            (first (sysp-type-params cons-type)))
           ;; If it's a cons, return the car type
           ((eq (sysp-type-kind cons-type) :cons)
            (first (sysp-type-params cons-type)))
           ;; Otherwise unify with expected and return element
           (t (unify cons-type (make-cons-type elem-tvar (make-tvar)))
              elem-tvar))))

      ;; cdr: extracts cdr from cons or list
      ((sym= head "cdr")
       (let ((cons-type (infer-expr (second form)))
             (cdr-tvar (make-tvar)))
         (cond
           ;; If it's a list, return (:list elem) or nil
           ((eq (sysp-type-kind cons-type) :list)
            cons-type)  ; (:list T) cdr is (:list T) or nil
           ;; If it's a cons, return the cdr type
           ((eq (sysp-type-kind cons-type) :cons)
            (second (sysp-type-params cons-type)))
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
       (make-value-type))

      ;; Simple type returns
      ((sym= head "nil?") (make-bool-type))
      ((sym= head "sym") (make-value-type))
      ((sym= head "sym-eq?") (make-bool-type))
      ((sym= head "gensym") (make-value-type))

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
       (make-int-type))

      ;; Simple type returns for vector/array ops
      ((sym= head "vector-len") (make-int-type))
      ((sym= head "vector-set!") (make-void-type))
      ((sym= head "vector-push!") (make-void-type))
      ((sym= head "array-ref") (make-tvar))
      ((sym= head "array-set!") (make-void-type))
      ((sym= head "make-array") (make-tvar))

      ;; Function call: look up function type, unify args, return ret type
      (t (let* ((fn-name (string head))
                (fn-type (infer-env-lookup fn-name)))
           (if (and fn-type (eq (sysp-type-kind fn-type) :fn))
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

        ;; set!: unify target with value
        ((sym= head "set!")
         (let ((target-type (infer-env-lookup (string (second form))))
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
    (let ((body-type (make-int-type)))
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
                              (make-void-type)))
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
  (mutables nil)) ; list of mutable variable names (from let-mut)

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
  (member (sysp-type-kind tp) '(:value :cons)))

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
(defvar *uses-value-type* nil)  ; emit Value/Cons preamble if true
(defvar *macro-fns* (make-hash-table :test 'equal))  ; name -> (params body) for compile-time eval
(defvar *interp-gensym-counter* 0)

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

(defun make-sysp-readtable ()
  (let ((rt (copy-readtable nil)))
    (setf (readtable-case rt) :preserve)
    (set-syntax-from-char #\, #\Space rt)
    (set-macro-character #\[
      (lambda (stream char)
        (declare (ignore char))
        (read-delimited-list #\] stream t))
      nil rt)
    (set-syntax-from-char #\] #\) rt)
    ;; Backquote → (quasiquote ...)
    (set-macro-character #\`
      (lambda (stream char)
        (declare (ignore char))
        (list (intern "quasiquote" :sysp) (let ((*readtable* rt)) (read stream t nil t))))
      nil rt)
    ;; Tilde → (unquote ...) or (splice ...) if followed by @
    (set-macro-character #\~
      (lambda (stream char)
        (declare (ignore char))
        (let ((next (peek-char nil stream t nil t)))
          (if (char= next #\@)
              (progn (read-char stream t nil t)  ; consume @
                     (list (intern "splice" :sysp) (let ((*readtable* rt)) (read stream t nil t))))
              (list (intern "unquote" :sysp) (let ((*readtable* rt)) (read stream t nil t))))))
      nil rt)
    rt))

(defvar *sysp-readtable* (make-sysp-readtable))

(defun read-sysp-file (path)
  (let ((*readtable* *sysp-readtable*))
    (with-open-file (in path :direction :input)
      (let ((forms nil)
            (eof (gensym)))
        (loop for form = (read in nil eof)
              until (eq form eof)
              do (push form forms))
        (nreverse forms)))))

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

(defun parse-type-annotation (sym)
  (let ((name (string-downcase (symbol-name sym))))
    (cond
      ((string= name "int") (make-int-type))
      ((string= name "long") (make-long-type))
      ((string= name "long-long") (make-long-long-type))
      ((string= name "float") (make-float-type))
      ((string= name "double") (make-double-type))
      ((string= name "bool") (make-bool-type))
      ((string= name "void") (make-void-type))
      ((string= name "str") (make-str-type))
      ((string= name "char") (make-char-type))
      ((string= name "u8") (make-u8-type))
      ((string= name "f32") (make-f32-type))
      ((string= name "symbol") (make-symbol-type))
      ((string= name "value") (make-value-type))
      ((string= name "cons") (make-cons-type))
      ((string= name "nil") (make-nil-type))
      ;; Pointer shorthand: :ptr-int, :ptr-float, etc.
      ((and (> (length name) 4) (string= (subseq name 0 4) "ptr-"))
       (make-ptr-type (parse-type-annotation
                       (intern (string-upcase (subseq name 4)) :keyword))))
      (t (let ((sname (symbol-name sym)))
           (cond
             ((gethash sname *structs*) (make-struct-type sname))
             ((gethash sname *enums*) (make-enum-type sname))
             (t (make-sysp-type :kind :unknown :name sname))))))))


;;; === C Type Emission ===

(defun type-to-c (tp)
  (case (sysp-type-kind tp)
    (:int "int")
    (:long "long")
    (:long-long "long long")
    (:float "float")
    (:double "double")
    (:bool "int")
    (:void "void")
    (:str "const char*")
    (:char "char")
    (:u8 "unsigned char")
    (:f32 "float")
    (:ptr (format nil "~a*" (type-to-c (first (sysp-type-params tp)))))
    (:struct (sysp-type-name tp))
    (:enum (sysp-type-name tp))
    (:array (type-to-c (first (sysp-type-params tp))))  ; array decl handled specially
    (:vector (vector-type-c-name tp))
    (:tuple (tuple-type-c-name tp))
    (:fn (fn-type-c-name tp))
    (:symbol "Symbol")
    (:value "Value")
    (:cons "Value")  ; cons cells are Values (tagged)
    (:nil "Value")   ; nil is a Value
    (:list "Value")  ; lists are also Values (tagged cons chain)
    (:variadic "Value")  ; variadic rest compiles to Value at runtime
    (otherwise "int")))

(defun mangle-type-name (tp)
  (case (sysp-type-kind tp)
    (:int "int")
    (:long "long")
    (:long-long "longlong")
    (:float "float")
    (:double "double")
    (:bool "bool")
    (:str "str")
    (:char "char")
    (:u8 "u8")
    (:f32 "f32")
    (:ptr (format nil "ptr_~a" (mangle-type-name (first (sysp-type-params tp)))))
    (:struct (sysp-type-name tp))
    (:enum (sysp-type-name tp))
    (:array (format nil "arr_~a_~a" (mangle-type-name (first (sysp-type-params tp)))
                    (second (sysp-type-params tp))))
    (:vector (vector-type-c-name tp))
    (:tuple (tuple-type-c-name tp))
    (:fn (fn-type-c-name tp))
    (:symbol "sym")
    (:value "val")
    (:cons "val")
    (:nil "nil")
    (:list (format nil "list_~a" (mangle-type-name (first (sysp-type-params tp)))))
    (:variadic (format nil "var_~a" (mangle-type-name (first (sysp-type-params tp)))))
    (otherwise "unknown")))

(defun vector-type-c-name (tp)
  (let* ((elem (first (sysp-type-params tp)))
         (name (format nil "Vector_~a" (mangle-type-name elem))))
    (ensure-vector-type name elem)
    name))

(defun tuple-type-c-name (tp)
  (let* ((elems (sysp-type-params tp))
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
    (let ((arg-str (if arg-types
                       (format nil "~{~a~^, ~}" (mapcar #'type-to-c arg-types))
                       "void")))
      (push (format nil "typedef ~a (*~a)(~a);~%"
                    (type-to-c ret-type) name arg-str)
            *type-decls*))))

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
         (member head '("do" "if" "cond" "let" "let-mut") :test #'string-equal))))

;; Compile form so its value ends up assigned to target-var.
;; Returns (values type statements-list).
;; Recursively handles nested statement-like forms.
(defun compile-expr-returning (form env target)
  (if (statement-like-p form)
      ;; Statement-like: compile-stmt-returning returns stmts directly
      (compile-stmt-returning form env target)
      ;; Simple expression: isolate pending stmts, compile, assign to target
      (let ((*pending-stmts* nil))
        (multiple-value-bind (code type) (compile-expr form env)
          (values type
                  (append *pending-stmts*
                          (list (format nil "  ~a = ~a;" target code))))))))

;; Compile a statement-like form so its value is assigned to target.
;; Returns (values type statements-list).
(defun compile-stmt-returning (form env target)
  (let ((head (string (first form))))
    (cond
      ((string-equal head "if") (compile-if-stmt-returning form env target))
      ((string-equal head "do") (compile-do-stmt-returning form env target))
      ((string-equal head "cond") (compile-cond-stmt-returning form env target))
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
    ((null form) (values "0" (make-int-type)))
    ((integerp form) (values (format nil "~d" form) (make-int-type)))
    ((floatp form) (values (format nil "~f" form) (make-float-type)))
    ((stringp form) (values (format nil "~s" form) (make-str-type)))
    ((symbolp form)
     (let ((name (string form)))
       (cond
         ((string-equal name "true") (values "1" (make-bool-type)))
         ((string-equal name "false") (values "0" (make-bool-type)))
         ((string-equal name "null") (values "NULL" (make-ptr-type (make-void-type))))
         (t (let ((tp (env-lookup env name)))
              (if tp
                  (values (sanitize-name name) tp)
                  ;; Check if it's an enum variant
                  (let ((enum-info (lookup-enum-variant name)))
                    (if enum-info
                        (values (sanitize-name name)
                                (make-enum-type (car enum-info)))
                        (values (sanitize-name name)
                                (make-sysp-type :kind :unknown))))))))))
    ((listp form)
     ;; Try macro expansion first
     (multiple-value-bind (expanded was-expanded) (macroexpand-1-sysp form)
       (if was-expanded
           (compile-expr (macroexpand-all expanded) env)
           (compile-list form env))))
    (t (values (format nil "~a" form) (make-sysp-type :kind :unknown)))))

(defun sanitize-name (name)
  (let ((result (substitute #\_ #\- name)))
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

(defmacro defbinops (compiler-name &rest syms-ops)
  "Generate cond clauses for binary operators"
  `(cond
     ,@(loop for (sym op) in syms-ops
             collect `((sym= head ,sym) (,(intern compiler-name) ,op form env)))))

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
       (values (format nil ,pattern obj) (make-int-type)))))

(defmacro define-value-accessor (name c-fun ret-type)
  `(defun ,(intern (format nil "COMPILE-~a" name)) (form env)
     (setf *uses-value-type* t)
     (multiple-value-bind (code tp) (compile-expr (second form) env)
       (declare (ignore tp))
       (values (format nil ,(format nil "~a(~~a)" c-fun) code) (,ret-type)))))

;; === Compilation Rule Macros ===
;; These macros make the dispatch tables readable and declarative

(defmacro defbinop (sym op)
  `((sym= head ,sym) (compile-binop ,op form env)))

(defmacro deflogical (sym op)
  `((sym= head ,sym) (compile-logical ,op form env)))

;; Simple compile rules: just call a function with (form env)
(defmacro defcompile (sym fn)
  `((sym= head ,sym) (,fn form env)))

;; For operators with simple type returns
(defmacro defop (sym ret-type)
  `((sym= head ,sym)
    (multiple-value-bind (code tp) (compile-expr (second form) env)
      (declare (ignore tp))
      (values code (,ret-type)))))

;; For binary ops that need type-aware codegen
(defmacro defbin (sym c-op result-type-expr)
  `((sym= head ,sym)
    (multiple-value-bind (lhs lt) (compile-expr (second form) env)
      (multiple-value-bind (rhs rt) (compile-expr (third form) env)
        (declare (ignore rt))
        (values (format nil "(~a ~a ~a)" lhs ,c-op rhs) ,result-type-expr)))))

(defun compile-list (form env)
  (let ((head (first form)))
    (cond
      ;; Arithmetic
      ((sym= head "+") (compile-binop "+" form env))
      ((sym= head "-")
       (if (= (length form) 2)
           (compile-unary-minus form env)
           (compile-binop "-" form env)))
      ((sym= head "*") (compile-binop "*" form env))
      ((sym= head "/") (compile-binop "/" form env))
      ((sym= head "%") (compile-binop "%" form env))
      ((sym= head "mod") (compile-binop "%" form env))
      ;; Comparison
      ((sym= head "<") (compile-binop "<" form env))
      ((sym= head ">") (compile-binop ">" form env))
      ((sym= head "<=") (compile-binop "<=" form env))
      ((sym= head ">=") (compile-binop ">=" form env))
      ((sym= head "==") (compile-binop "==" form env))
      ((sym= head "!=") (compile-binop "!=" form env))
      ;; Logical (variadic)
      ((sym= head "and") (compile-logical "&&" form env))
      ((sym= head "or") (compile-logical "||" form env))
      ((sym= head "not") (compile-not form env))
      ;; Bitwise
      ((sym= head "bit-and") (compile-binop "&" form env))
      ((sym= head "bit-or") (compile-binop "|" form env))
      ((sym= head "bit-xor") (compile-binop "^" form env))
      ((sym= head "bit-not") (compile-bit-not form env))
      ((sym= head "shl") (compile-binop "<<" form env))
      ((sym= head "shr") (compile-binop ">>" form env))
      ;; Control flow
      ((sym= head "if") (compile-if-expr form env))
      ((sym= head "do") (compile-do-expr form env))
      ((sym= head "cond") (compile-cond-expr form env))
      ;; Data structures
      ((sym= head "get") (compile-get form env))
      ((sym= head "vector") (compile-vector form env))
      ((sym= head "vector-ref") (compile-vector-ref form env))
      ((sym= head "vector-set!") (compile-vector-set form env))
      ((sym= head "vector-push!") (compile-vector-push form env))
      ((sym= head "vector-len") (compile-vector-len form env))
      ((sym= head "tuple") (compile-tuple form env))
      ((sym= head "tuple-ref") (compile-tuple-ref form env))
      ((sym= head "lambda") (compile-lambda form env))
      ;; Arrays
      ((sym= head "array-ref") (compile-array-ref form env))
      ((sym= head "array-set!") (compile-array-set form env))
      ((sym= head "make-array") (compile-make-array form env))
      ;; Assignment
      ((sym= head "set!") (compile-set-expr form env))
      ;; Pointer ops
      ((sym= head "addr-of") (compile-addr-of form env))
      ((sym= head "deref") (compile-deref form env))
      ;; Type ops
      ((sym= head "cast") (compile-cast form env))
      ((sym= head "sizeof") (compile-sizeof form env))
      ;; Cons / Value ops
      ((sym= head "cons") (compile-cons form env))
      ((sym= head "car") (compile-car form env))
      ((sym= head "cdr") (compile-cdr form env))
      ((sym= head "nil?") (compile-nilp form env))
      ((sym= head "list") (compile-list-expr form env))
      ((sym= head "quote") (compile-quote form env))
      ((sym= head "quasiquote") (compile-quasiquote form env))
      ((sym= head "sym") (compile-sym-literal form env))
      ((sym= head "sym-eq?") (compile-sym-eq form env))
      ((sym= head "gensym") (compile-gensym-expr form env))
      ;; Otherwise: function/constructor call
      (t (compile-call form env)))))

(defun compile-binop (op form env)
  (multiple-value-bind (lhs lt) (compile-expr (second form) env)
    (multiple-value-bind (rhs rt) (compile-expr (third form) env)
      (declare (ignore rt))
      (let ((result-type
              (cond
                ((member op '("<" ">" "<=" ">=" "==" "!=" "&&" "||") :test #'string=)
                 (make-bool-type))
                ((member op '("&" "|" "^" "<<" ">>") :test #'string=)
                 (make-int-type))
                (t lt))))
        (values (format nil "(~a ~a ~a)" lhs op rhs) result-type)))))

(defun compile-logical (op form env)
  "(and a b c ...) or (or a b c ...) — variadic logical"
  (let* ((args (rest form))
         (compiled (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args)))
    (if (= (length compiled) 1)
        (values (first compiled) (make-bool-type))
        (values (format nil "(~a)"
                        (reduce (lambda (acc x) (format nil "~a ~a ~a" acc op x))
                                compiled))
                (make-bool-type)))))

(defun compile-unary-minus (form env)
  (multiple-value-bind (val tp) (compile-expr (second form) env)
    (values (format nil "(-~a)" val) tp)))

(defun compile-not (form env)
  (multiple-value-bind (val tp) (compile-expr (second form) env)
    (declare (ignore tp))
    (values (format nil "(!~a)" val) (make-bool-type))))

(defun compile-bit-not (form env)
  (multiple-value-bind (val tp) (compile-expr (second form) env)
    (declare (ignore tp))
    (values (format nil "(~~~a)" val) (make-int-type))))

(defun compile-if-expr (form env)
  "(if cond then else) or (if cond then else else-expr) -> ternary"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (multiple-value-bind (then-code then-type) (compile-expr (third form) env)
      ;; Check for else keyword (statement-style) vs positional (expression-style)
      (let ((else-form (if (and (fourth form) (symbolp (fourth form))
                                (sym= (fourth form) "else"))
                           (fifth form)    ; skip 'else' keyword
                           (fourth form)))) ; positional
        (if else-form
            (multiple-value-bind (else-code et) (compile-expr else-form env)
              (declare (ignore et))
              (values (format nil "(~a ? ~a : ~a)" cond-code then-code else-code)
                      then-type))
            (values (format nil "(~a ? ~a : 0)" cond-code then-code)
                    then-type))))))

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

(defun compile-cond-expr (form env)
  "(cond [test1 expr1] [test2 expr2] ... [else exprN]) -> nested ternary"
  (let ((clauses (rest form)))
    (compile-cond-clauses clauses env)))

(defun compile-cond-clauses (clauses env)
  (if (null clauses)
      (values "0" (make-int-type))
      (let ((clause (first clauses)))
        (if (and (symbolp (first clause)) (sym= (first clause) "else"))
            (compile-expr (second clause) env)
            (multiple-value-bind (test-code tt) (compile-expr (first clause) env)
              (declare (ignore tt))
              (multiple-value-bind (then-code then-type) (compile-expr (second clause) env)
                (multiple-value-bind (rest-code rt) (compile-cond-clauses (rest clauses) env)
                  (declare (ignore rt))
                  (values (format nil "(~a ? ~a : ~a)" test-code then-code rest-code)
                          then-type))))))))

(defun compile-if-stmt-returning (form env target)
  "(if cond then [else] else) -> if statement assigning to target"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let* ((else-form (if (and (fourth form) (symbolp (fourth form))
                               (sym= (fourth form) "else"))
                          (fifth form)
                          (fourth form))))
      (multiple-value-bind (then-type then-stmts)
          (compile-expr-returning (third form) env target)
        (multiple-value-bind (et else-stmts)
            (if else-form
                (compile-expr-returning else-form env target)
                (values then-type (list (format nil "  ~a = 0;" target))))
          (declare (ignore et))
          (let ((result (list (format nil "  if (~a) {" cond-code))))
            (dolist (s then-stmts) (setf result (append result (list (format nil "  ~a" s)))))
            (setf result (append result (list "  } else {")))
            (dolist (s else-stmts) (setf result (append result (list (format nil "  ~a" s)))))
            (setf result (append result (list "  }")))
            (values then-type result)))))))

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
        (result-type (make-int-type)))
    (dolist (clause clauses)
      (let ((test (first clause))
            (body (second clause)))
        (cond
          ((and (symbolp test) (sym= test "else"))
           (setf result (append result (list "  } else {")))
           (multiple-value-bind (type stmts) (compile-expr-returning body env target)
             (setf result-type type)
             (dolist (s stmts) (setf result (append result (list (format nil "  ~a" s)))))))
          (first-clause
           (multiple-value-bind (test-code tt) (compile-expr test env)
             (declare (ignore tt))
             (setf result (append result (list (format nil "  if (~a) {" test-code))))
             (multiple-value-bind (type stmts) (compile-expr-returning body env target)
               (setf result-type type)
               (dolist (s stmts) (setf result (append result (list (format nil "  ~a" s))))))
             (setf first-clause nil)))
          (t
           (multiple-value-bind (test-code tt) (compile-expr test env)
             (declare (ignore tt))
             (setf result (append result (list (format nil "  } else if (~a) {" test-code))))
             (multiple-value-bind (type stmts) (compile-expr-returning body env target)
               (setf result-type type)
               (dolist (s stmts) (setf result (append result (list (format nil "  ~a" s)))))))))))
    (setf result (append result (list "  }")))
    (values result-type result)))

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
  "(get struct field)"
  (multiple-value-bind (obj tp) (compile-expr (second form) env)
    (let* ((field-name (string (third form)))
           (field-type (if (and (eq (sysp-type-kind tp) :struct)
                                (gethash (sysp-type-name tp) *structs*))
                           (let ((fields (gethash (sysp-type-name tp) *structs*)))
                             (cdr (assoc field-name fields :test #'equal)))
                           (make-int-type))))
      (values (format nil "~a.~a" obj (sanitize-name field-name))
              (or field-type (make-int-type))))))

(defun compile-vector (form env)
  "(vector elem ...) - C99 compound literal with malloc helper"
  (let* ((elems (rest form))
         (compiled (mapcar (lambda (e) (multiple-value-list (compile-expr e env))) elems))
         (elem-type (if compiled (second (first compiled)) (make-int-type)))
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
  (if (eq (sysp-type-kind tp) :vector)
      (first (sysp-type-params tp))
      (make-int-type)))

(defun compile-vector-set (form env)
  "(vector-set! vec idx val)"
  (multiple-value-bind (vec vt) (compile-expr (second form) env)
    (multiple-value-bind (idx it) (compile-expr (third form) env)
      (declare (ignore it))
      (multiple-value-bind (val val-type) (compile-expr (fourth form) env)
        (declare (ignore val-type))
        (let ((elem-type (if (eq (sysp-type-kind vt) :vector)
                             (first (sysp-type-params vt))
                             (make-int-type))))
          (values (format nil "(~a.data[~a] = ~a)" vec idx val) elem-type))))))

(defun compile-vector-push (form env)
  "(vector-push! vec val) — push to dynamic vector (C99 compliant)"
  (multiple-value-bind (vec vt) (compile-expr (second form) env)
    (multiple-value-bind (val val-type) (compile-expr (third form) env)
      (declare (ignore val-type))
      (let* ((elem-type (if (eq (sysp-type-kind vt) :vector)
                            (first (sysp-type-params vt))
                            (make-int-type)))
             (c-vec (type-to-c vt))
             (c-elem (type-to-c elem-type))
             (helper-name (format nil "sysp_vecpush_~a" (mangle-type-name elem-type))))
        (ensure-vector-push-helper helper-name c-vec c-elem)
        (values (format nil "~a(&~a, ~a)" helper-name vec val)
                (make-void-type))))))

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
           (elem-type (if (eq (sysp-type-kind tt) :tuple)
                          (nth idx (sysp-type-params tt))
                          (make-int-type))))
      (values (format nil "~a._~d" tup idx) elem-type))))

(define-accessor array-ref "~a[~a]"
  (if (eq (sysp-type-kind tp) :array)
      (first (sysp-type-params tp))
      (make-int-type)))

(defun compile-array-set (form env)
  "(array-set! arr idx val)"
  (multiple-value-bind (arr at) (compile-expr (second form) env)
    (multiple-value-bind (idx it) (compile-expr (third form) env)
      (declare (ignore it))
      (multiple-value-bind (val vt) (compile-expr (fourth form) env)
        (declare (ignore vt))
        (let ((elem-type (if (eq (sysp-type-kind at) :array)
                             (first (sysp-type-params at))
                             (make-int-type))))
          (values (format nil "(~a[~a] = ~a)" arr idx val) elem-type))))))

(defun compile-make-array (form env)
  "(make-array :type size) — stack-allocated zero-init array"
  (declare (ignore env))
  (let* ((elem-type (parse-type-annotation (second form)))
         (size (third form))
         (arr-type (make-array-type elem-type size)))
    (values (format nil "{0}" ) arr-type)))

(defun compile-lambda (form env)
  "(lambda [params...] :ret-type body...)"
  (let* ((params-raw (second form))
         (rest-forms (cddr form))
         (params (parse-params params-raw))
         (ret-annotation (when (keywordp (first rest-forms))
                           (prog1 (parse-type-annotation (first rest-forms))
                             (setf rest-forms (cdr rest-forms)))))
         (body-forms rest-forms)
         (lambda-name (format nil "_lambda_~d" (incf *lambda-counter*)))
         (fn-env (make-env :parent env)))
    (dolist (p params)
      (env-bind fn-env (first p) (second p)))
    ;; Multi-expression body: all but last are statements, last is return value
    (let* ((all-but-last (butlast body-forms))
           (last-form (car (last body-forms))))
      (let ((*pending-stmts* nil))
        (multiple-value-bind (last-code last-type) (compile-expr last-form fn-env)
          (let* ((ret-type (or ret-annotation last-type))
                 (arg-types (mapcar #'second params))
                 (fn-type (make-fn-type arg-types ret-type))
                 (param-str (format nil "~{~a~^, ~}"
                                   (mapcar (lambda (p)
                                             (format nil "~a ~a"
                                                     (type-to-c (second p))
                                                     (sanitize-name (first p))))
                                           params)))
                 (body-stmts (append (or (when all-but-last (compile-body all-but-last fn-env)) nil)
                                     *pending-stmts*)))
            (push (format nil "static ~a ~a(~a);"
                          (type-to-c ret-type) lambda-name
                          (if params param-str "void"))
                  *lambda-forward-decls*)
            (push (format nil "static ~a ~a(~a) {~%~{~a~%~}  return ~a;~%}~%"
                          (type-to-c ret-type) lambda-name
                          (if params param-str "void")
                          (or body-stmts nil)
                          last-code)
                  *functions*)
            (values lambda-name fn-type)))))))


(defun compile-set-expr (form env)
  "(set! name expr) as expression"
  (let ((target (second form)))
    (cond
      ;; (set! (get struct field) val) -> struct.field = val
      ((and (listp target) (sym= (first target) "get"))
       (multiple-value-bind (obj tp) (compile-expr (second target) env)
         (declare (ignore tp))
         (let ((field (string (third target))))
           (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
             (values (format nil "(~a.~a = ~a)" obj (sanitize-name field) val-code)
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
    (let ((pointee (if (eq (sysp-type-kind tp) :ptr)
                       (first (sysp-type-params tp))
                       (make-int-type))))
      (values (format nil "(*~a)" code) pointee))))

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
                (make-int-type))
        (values (format nil "sizeof(~a)" (sanitize-name (string arg)))
                (make-int-type)))))

;;; === Value Type (cons cells, symbols, quote) ===

(defun wrap-as-value (code tp)
  "Wrap a compiled C expression as a Value based on its type"
  (setf *uses-value-type* t)
  (case (sysp-type-kind tp)
    (:int (format nil "val_int(~a)" code))
    (:float (format nil "val_float(~a)" code))
    (:f32 (format nil "val_float((double)~a)" code))
    (:str (format nil "val_str(~a)" code))
    (:symbol (format nil "val_sym(~a)" code))
    (:value code)  ; already a Value
    (:cons code)   ; cons is already a Value
    (:bool (format nil "val_int(~a)" code))
    (otherwise (format nil "val_int(~a)" code))))

(defun cons-arg-needs-retain-p (arg-form env)
  "Does this cons argument need val_retain? Yes if it's a local variable of Value type."
  (and (symbolp arg-form)
       (not (sym= arg-form "nil"))
       (let ((tp (env-lookup env (string arg-form))))
         (and tp (value-type-p tp)))))

(defun compile-cons (form env)
  "(cons x y)"
  (setf *uses-value-type* t)
  (multiple-value-bind (car-code car-type) (compile-expr (second form) env)
    (multiple-value-bind (cdr-code cdr-type) (compile-expr (third form) env)
      (let ((car-val (wrap-as-value car-code car-type))
            (cdr-val (wrap-as-value cdr-code cdr-type)))
        ;; If args are local variables, retain them (cons shares ownership)
        (when (cons-arg-needs-retain-p (second form) env)
          (setf car-val (format nil "val_retain(~a)" car-val)))
        (when (cons-arg-needs-retain-p (third form) env)
          (setf cdr-val (format nil "val_retain(~a)" cdr-val)))
        (values (format nil "val_cons(make_cons(~a, ~a))" car-val cdr-val)
                (make-value-type))))))

(define-value-accessor car "sysp_car" make-value-type)
(define-value-accessor cdr "sysp_cdr" make-value-type)
(define-value-accessor nilp "sysp_nilp" make-bool-type)

(defun compile-list-expr (form env)
  "(list x y z ...) -> nested cons"
  (setf *uses-value-type* t)
  (if (null (rest form))
      (values "val_nil()" (make-value-type))
      (let ((elems (rest form)))
        (labels ((build (items)
                   (if (null items)
                       "val_nil()"
                       (multiple-value-bind (code tp) (compile-expr (first items) env)
                         (let ((val (wrap-as-value code tp)))
                           ;; Retain if variable (same logic as compile-cons)
                           (when (cons-arg-needs-retain-p (first items) env)
                             (setf val (format nil "val_retain(~a)" val)))
                           (format nil "val_cons(make_cons(~a, ~a))"
                                   val (build (rest items))))))))
          (values (build elems) (make-value-type))))))

(defun compile-quote (form env)
  "(quote datum) — compile quoted literal to runtime Value"
  (declare (ignore env))
  (setf *uses-value-type* t)
  (values (compile-quoted-datum (second form)) (make-value-type)))

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
  (values (compile-qq (second form) env) (make-value-type)))

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
             (let ((val (if (member (sysp-type-kind tp) '(:value :cons))
                            code
                            (wrap-as-value code tp))))
               (format nil "sysp_append(~a, ~a)" val rest-code))))
          ;; (unquote x) → evaluate and cons
          ((and (listp first-item) (symbolp (first first-item))
                (string-equal (symbol-name (first first-item)) "unquote"))
           (multiple-value-bind (code tp) (compile-expr (second first-item) env)
             (let ((val (wrap-as-value code tp)))
               ;; Retain if variable (same logic as compile-cons/compile-list-expr)
               (when (cons-arg-needs-retain-p (second first-item) env)
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
    (values (format nil "~d" id) (make-symbol-type))))

(defun compile-sym-eq (form env)
  "(sym-eq? a b) — compare two Values as symbols"
  (setf *uses-value-type* t)
  (multiple-value-bind (a-code at) (compile-expr (second form) env)
    (declare (ignore at))
    (multiple-value-bind (b-code bt) (compile-expr (third form) env)
      (declare (ignore bt))
      (values (format nil "sysp_sym_eq(~a, ~a)" a-code b-code) (make-bool-type)))))

(defun compile-gensym-expr (form env)
  "(gensym) — generate a unique symbol at runtime"
  (declare (ignore form env))
  (setf *uses-value-type* t)
  (values "val_sym(_sysp_gensym++)" (make-value-type)))

(defun compile-call (form env)
  "Compile a function call, handling variadic functions."
  (let* ((fn-name (string (first form)))
         (args (rest form)))
    (if (gethash fn-name *structs*)
        (compile-struct-construct fn-name args env)
        (let* ((fn-type (env-lookup env fn-name))
               (fn-arg-types (when (and fn-type (eq (sysp-type-kind fn-type) :fn))
                               (fn-type-args fn-type)))
               (ret-type (if fn-type (fn-type-ret fn-type) (make-int-type)))
               (variadic-p (and fn-arg-types (> (length fn-arg-types) 0)
                                (eq (sysp-type-kind (car (last fn-arg-types))) :value)))
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
                  (values (format nil "~a(~{~a~^, ~})" (sanitize-name fn-name) all-args)
                          ret-type)))
              ;; Non-variadic: compile all args directly
              (let ((compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args)))
                (values (format nil "~a(~{~a~^, ~})" (sanitize-name fn-name) compiled-args)
                        ret-type)))))))

(defun compile-struct-construct (name args env)
  (let ((compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args)))
    (values (format nil "(~a){~{~a~^, ~}}" name compiled-args)
            (make-struct-type name))))

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
    ((and (listp form) (sym= (first form) "block"))
     (compile-block-stmt form env))
    ((and (listp form) (sym= (first form) "do"))
     ;; do as statement: just compile all sub-forms as statements
     (compile-body (rest form) env))
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
               ;; Copying a Value variable needs retain (variable ref = shared ownership)
               ;; Fresh allocations (cons, list, quote, car, cdr) already have correct refcount
               (needs-retain (and *uses-value-type*
                                 (value-type-p final-type)
                                 (symbolp init-form)
                                 (not (sym= init-form "nil"))
                                 (env-lookup env (string init-form)))))
          (env-bind env name final-type)
          (when is-mut (env-mark-mutable env name))
          ;; Track Value-typed locals for release at scope exit
          (when (and *uses-value-type* (value-type-p final-type))
            (env-add-release env c-name))
          (let ((decl (if (eq (sysp-type-kind final-type) :array)
                          (list (format nil "  ~a ~a[~a] = ~a;"
                                        (type-to-c (first (sysp-type-params final-type)))
                                        c-name
                                        (second (sysp-type-params final-type))
                                        init-code))
                          (if needs-retain
                              (list (format nil "  ~a ~a = val_retain(~a);"
                                            (type-to-c final-type) c-name init-code))
                              (list (format nil "  ~a ~a = ~a;"
                                            (type-to-c final-type) c-name init-code))))))
            (append lifted-stmts decl)))))))

(defun format-print-arg (val-code val-type)
  "Return format string and arg for a typed value"
  (case (sysp-type-kind val-type)
    (:float (values "%f" val-code))
    (:f32 (values "%f" val-code))
    (:str (values "%s" val-code))
    (:char (values "%c" val-code))
    (:u8 (values "%u" val-code))
    (:bool (values "%s" (format nil "(~a ? \"true\" : \"false\")" val-code)))
    ((:value :cons) (values :value-print val-code))
    (otherwise (values "%d" val-code))))

(defun compile-print-stmt (form env)
  "(print expr) — print without newline"
  (multiple-value-bind (val-code val-type) (compile-expr (second form) env)
    (multiple-value-bind (fmt arg) (format-print-arg val-code val-type)
      (if (eq fmt :value-print)
          (list (format nil "  sysp_print_value(~a);" arg))
          (list (format nil "  printf(\"~a\", ~a);" fmt arg))))))

(defun compile-println-stmt (form env)
  "(println expr) or (println) — print with newline"
  (if (null (rest form))
      (list "  printf(\"\\n\");")
      (multiple-value-bind (val-code val-type) (compile-expr (second form) env)
        (multiple-value-bind (fmt arg) (format-print-arg val-code val-type)
          (if (eq fmt :value-print)
              (list (format nil "  sysp_print_value(~a); printf(\"\\n\");" arg))
              (list (format nil "  printf(\"~a\\n\", ~a);" fmt arg)))))))

(defun compile-if-stmt (form env)
  "(if cond then-body...) or (if cond then-body... else else-body...)"
  ;; Find the else keyword position
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let* ((rest (cddr form))
           (else-pos (position-if (lambda (x) (and (symbolp x) (sym= x "else"))) rest))
           (then-forms (if else-pos (subseq rest 0 else-pos) rest))
           (else-forms (when else-pos (subseq rest (1+ else-pos)))))
      (let ((then-env (make-env :parent env))
            (else-env (make-env :parent env)))
        (let ((result (list (format nil "  if (~a) {" cond-code))))
          (dolist (s (compile-body then-forms then-env))
            (push (format nil "  ~a" s) result))
          (push "  }" result)
          (when else-forms
            (setf (car result) "  } else {")
            (dolist (s (compile-body else-forms else-env))
              (push (format nil "  ~a" s) result))
            (push "  }" result))
          (nreverse result))))))

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
    (env-bind body-env var-name (make-int-type))
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

(defun parse-params (param-list)
  "Parse parameters, handling [a :int & rest] for variadic functions.
   Returns (values fixed-params rest-param) where rest-param is nil or (name type)."
  (let ((fixed nil)
        (rest nil)
        (lst (if (listp param-list) param-list nil))
        (in-rest nil))
    (loop while lst do
      (let ((item (pop lst)))
        (cond
          ;; & indicates rest args follow
          ((and (symbolp item) (string= (string item) "&"))
           (setf in-rest t))
          ;; Regular parameter
          (t
           (let* ((name (string item))
                  (type (if (and lst (keywordp (first lst)))
                            (let ((result (parse-type-from-list lst)))
                              (setf lst (cdr result))
                              (car result))
                            (make-int-type))))
             (if in-rest
                 (setf rest (list name type))
                 (push (list name type) fixed)))))))
    (values (nreverse fixed) rest)))

(defun parse-params-with-inference (param-list inferred-arg-types)
  "Like parse-params but uses inferred types for unannotated parameters."
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
                                (make-int-type)))))
             (if in-rest
                 ;; Rest params are always Value type (internal implementation detail)
                 (setf rest (list name (make-value-type)))
                 (push (list name type) fixed)))
           (incf inf-idx)))))
    (values (nreverse fixed) rest)))

(defun params-all (fixed rest)
  "Combine fixed and rest params for type registration."
  (if rest (append fixed (list rest)) fixed))

(defun compile-struct (form)
  "(struct Name [field :type, ...])"
  (let* ((name (string (second form)))
         (fields-raw (third form))
         (fields (multiple-value-bind (fixed rest) (parse-params fields-raw)
                   (declare (ignore rest))
                   fixed)))
    (setf (gethash name *structs*)
          (mapcar (lambda (f) (cons (first f) (second f))) fields))
    (push (format nil "typedef struct {~%~{  ~a ~a;~%~}} ~a;~%"
                  (loop for f in fields
                        append (list (type-to-c (second f)) (sanitize-name (first f))))
                  name)
          *struct-defs*)))

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

(defun compile-defn (form)
  "(defn name [params] :ret-type body...) - supports variadic [& rest]"
  (let* ((name (string (second form)))
         (params-raw (third form))
         (rest-forms (cdddr form))
         ;; Look up inferred function type (from pre-pass)
         (inferred-fn-type (infer-env-lookup name))
         (inferred-arg-types (when (and inferred-fn-type
                                        (eq (sysp-type-kind inferred-fn-type) :fn))
                               (fn-type-args inferred-fn-type)))
         (inferred-ret-type (when (and inferred-fn-type
                                       (eq (sysp-type-kind inferred-fn-type) :fn))
                              (fn-type-ret inferred-fn-type)))
         ;; Parse params, handling & for variadic
         (params-fixed nil)
         (params-rest nil)
         (_ (multiple-value-setq (params-fixed params-rest)
              (parse-params-with-inference params-raw inferred-arg-types)))
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
           (ret-type (or ret-annotation inferred-ret-type (make-int-type)))
           (fn-type (make-fn-type arg-types ret-type)))
      (env-bind *global-env* name fn-type))
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
           (ret-type (or ret-annotation inferred-ret-type (make-int-type)))
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
        (if (eq (sysp-type-kind ret-type) :void)
            ;; Void: last form is just another statement, no return
            (progn
              (setf stmts (append stmts (compile-stmt last-form env)))
              (let ((releases (when *uses-value-type* (emit-releases env))))
                (when releases
                  (setf return-stmt (format nil "~{~a~%~}" releases)))))
            ;; Non-void: last form is return value
            (let ((*pending-stmts* nil))
              (multiple-value-bind (last-code lt) (compile-expr last-form env)
                (declare (ignore lt))
                ;; Any statements lifted from the return expression
                (when *pending-stmts*
                  (setf stmts (append stmts *pending-stmts*)))
                (let* ((releases (when *uses-value-type* (emit-releases env)))
                       (ret-var (and (symbolp last-form)
                                     (member (sanitize-name (string last-form))
                                             (env-releases env) :test #'equal))))
                  (setf return-stmt
                        (if (and ret-var *uses-value-type* releases)
                            (format nil "  val_retain(~a);~%~{~a~%~}  return ~a;~%"
                                    (sanitize-name (string last-form))
                                    releases
                                    last-code)
                            (if (and *uses-value-type* releases)
                                (format nil "~{~a~%~}  return ~a;~%" releases last-code)
                                (format nil "  return ~a;~%" last-code))))))))
          (let ((body-stmts (if uses-recur
                                  (cons "  _recur_top: ;" (or stmts nil))
                                  (or stmts nil))))
            (push (format nil "~a ~a(~a) {~%~{~a~%~}~@[~a~]}~%"
                          (type-to-c ret-type)
                          c-name
                          (if (string= param-str "") "void" param-str)
                          body-stmts
                          return-stmt)
                  *functions*))
          ;; Forward declaration (skip for main)
          (unless (string= c-name "main")
            (push (format nil "~a ~a(~a);"
                          (type-to-c ret-type) c-name
                          (if (string= param-str "") "void" param-str))
                  *forward-decls*)))))))

(defun compile-extern (form)
  "(extern name [params] :ret-type) — declare external C function"
  (let* ((name (string (second form)))
         (params-raw (third form))
         (rest-forms (cdddr form))
         (params (parse-params params-raw))
         (ret-annotation (when (keywordp (first rest-forms))
                           (parse-type-annotation (first rest-forms))))
         (ret-type (or ret-annotation (make-int-type)))
         (arg-types (mapcar #'second params))
         (fn-type (make-fn-type arg-types ret-type)))
    (env-bind *global-env* name fn-type)))

(defun compile-include (form)
  "(include \"header.h\")"
  (let ((header (second form)))
    (pushnew (if (stringp header) header (string header))
             *includes* :test #'string=)))

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

(defun compile-toplevel (forms)
  (dolist (form forms)
    (when (listp form)
      ;; Handle defmacro and defn-ct first (no C emission)
      (cond
        ((sym= (first form) "defmacro") (compile-defmacro form))
        ((sym= (first form) "defn-ct") (compile-defn-ct form))
        (t
         ;; Expand macros, then compile
         (let ((expanded (macroexpand-all form)))
           (when (listp expanded)
             (cond
               ((sym= (first expanded) "struct") (compile-struct expanded))
               ((sym= (first expanded) "foreign-struct") (compile-foreign-struct expanded))
               ((sym= (first expanded) "enum") (compile-enum expanded))
               ((sym= (first expanded) "defn") (compile-defn expanded))
               ((sym= (first expanded) "extern") (compile-extern expanded))
               ((sym= (first expanded) "include") (compile-include expanded))
               ((sym= (first expanded) "let") (compile-toplevel-let expanded nil))
               ((sym= (first expanded) "let-mut") (compile-toplevel-let expanded t))
               ((sym= (first expanded) "const") (compile-toplevel-let expanded nil)) ; legacy alias
               (t (warn "Unknown top-level form: ~a" (first expanded)))))))))))

(defun emit-value-preamble (out)
  "Emit the Value/Cons/Symbol type system preamble"
  (format out "/* === Value Type System === */~%")
  (format out "typedef uint32_t Symbol;~%")
  (format out "typedef struct Cons Cons;~%")
  (format out "typedef enum { VAL_NIL, VAL_INT, VAL_FLOAT, VAL_STR, VAL_SYM, VAL_CONS } ValueTag;~%")
  (format out "typedef struct { ValueTag tag; union { int as_int; double as_float; const char* as_str; Symbol as_sym; Cons* as_cons; }; } Value;~%")
  (format out "struct Cons { Value car; Value cdr; int refcount; };~%")
  (format out "static Value val_nil(void) { return (Value){.tag = VAL_NIL}; }~%")
  (format out "static Value val_int(int x) { Value v = {.tag = VAL_INT}; v.as_int = x; return v; }~%")
  (format out "static Value val_float(double x) { Value v = {.tag = VAL_FLOAT}; v.as_float = x; return v; }~%")
  (format out "static Value val_str(const char* x) { Value v = {.tag = VAL_STR}; v.as_str = x; return v; }~%")
  (format out "static Value val_sym(Symbol x) { Value v = {.tag = VAL_SYM}; v.as_sym = x; return v; }~%")
  (format out "static Value val_cons(Cons* x) { Value v = {.tag = VAL_CONS}; v.as_cons = x; return v; }~%")
  (format out "static Cons* make_cons(Value car, Value cdr) { Cons* c = malloc(sizeof(Cons)); c->car = car; c->cdr = cdr; c->refcount = 1; return c; }~%")
  ;; Refcounting (before car/cdr which use val_retain)
  (format out "static Value val_retain(Value v) { if(v.tag == VAL_CONS && v.as_cons) v.as_cons->refcount++; return v; }~%")
  (format out "static void val_release(Value v) { if(v.tag == VAL_CONS && v.as_cons && --v.as_cons->refcount == 0) { val_release(v.as_cons->car); val_release(v.as_cons->cdr); free(v.as_cons); } }~%")
  (format out "static Value sysp_car(Value v) { return val_retain(v.as_cons->car); }~%")
  (format out "static Value sysp_cdr(Value v) { return val_retain(v.as_cons->cdr); }~%")
  (format out "static int sysp_nilp(Value v) { return v.tag == VAL_NIL; }~%")
  (format out "static int sysp_sym_eq(Value a, Value b) { return a.tag == VAL_SYM && b.tag == VAL_SYM && a.as_sym == b.as_sym; }~%")
  ;; sysp_append: use direct field access instead of sysp_car/sysp_cdr to avoid double-retain
  (format out "static Value sysp_append(Value lst, Value tail) { if(lst.tag == VAL_NIL) return val_retain(tail); return val_cons(make_cons(val_retain(lst.as_cons->car), sysp_append(lst.as_cons->cdr, tail))); }~%")
  ;; sysp_list: build a list from n arguments (for variadic functions)
  (format out "static Value sysp_list(int n, ...) {~%")
  (format out "  va_list args;~%")
  (format out "  va_start(args, n);~%")
  (format out "  Value result = val_nil();~%")
  (format out "  Value* values = malloc(n * sizeof(Value));~%")
  (format out "  for(int i = 0; i < n; i++) values[i] = va_arg(args, Value);~%")
  (format out "  va_end(args);~%")
  (format out "  for(int i = n - 1; i >= 0; i--) result = val_cons(make_cons(val_retain(values[i]), result));~%")
  (format out "  free(values);~%")
  (format out "  return result;~%")
  (format out "}~%")
  (format out "static uint32_t _sysp_gensym = 0x80000000;~%")
  ;; Emit symbol name table for printing (before print_value which uses it)
  (let ((max-id *symbol-counter*))
    (format out "static const char* _sym_names[~d] = {\"\"" (1+ max-id))
    (loop for i from 1 to max-id do
      (let ((name nil))
        (maphash (lambda (n id) (when (= id i) (setf name n))) *symbol-table*)
        (format out ", \"~a\"" (or name ""))))
    (format out "};~%"))
  (format out "static void sysp_print_value(Value v) {~%")
  (format out "  switch(v.tag) {~%")
  (format out "    case VAL_NIL: printf(\"nil\"); break;~%")
  (format out "    case VAL_INT: printf(\"%d\", v.as_int); break;~%")
  (format out "    case VAL_FLOAT: printf(\"%f\", v.as_float); break;~%")
  (format out "    case VAL_STR: printf(\"%s\", v.as_str); break;~%")
  (format out "    case VAL_SYM: if(v.as_sym < sizeof(_sym_names)/sizeof(_sym_names[0])) printf(\"%s\", _sym_names[v.as_sym]); else printf(\"g%u\", v.as_sym); break;~%")
  (format out "    case VAL_CONS: printf(\"(\"); sysp_print_value(v.as_cons->car); Value tail = v.as_cons->cdr; while(tail.tag == VAL_CONS) { printf(\" \"); sysp_print_value(tail.as_cons->car); tail = tail.as_cons->cdr; } if(tail.tag != VAL_NIL) { printf(\" . \"); sysp_print_value(tail); } printf(\")\"); break;~%")
  (format out "  }~%}~%")
  ;; Emit symbol table as defines
  (maphash (lambda (name id)
             (format out "#define SYM_~a ~d~%"
                     (mangle-symbol-name name) id))
           *symbol-table*)
  (format out "~%"))

(defun emit-c (out-path)
  (with-open-file (out out-path :direction :output :if-exists :supersede)
    (format out "#include <stdio.h>~%")
    (format out "#include <stdlib.h>~%")
    (when *uses-value-type*
      (format out "#include <stdint.h>~%")
      (format out "#include <stdarg.h>~%"))
    (dolist (inc *includes*)
      (format out "#include <~a>~%" inc))
    (format out "~%")
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
  (setf *interp-gensym-counter* 0))

(defun compile-file-to-c (in-path out-path)
  (reset-state)
  (let ((forms (read-sysp-file in-path)))
    ;; Phase 1: Type inference (constraint generation + solving)
    (infer-toplevel forms)
    ;; Phase 2: Compilation (uses inferred types from *infer-env*)
    (compile-toplevel forms)
    (emit-c out-path)
    (format t "Compiled ~a -> ~a~%" in-path out-path)))

;;; === CLI Entry Point ===

(defun main ()
  (let ((args (cdr sb-ext:*posix-argv*)))
    (when (< (length args) 1)
      (format *error-output* "Usage: sysp <input.sysp> [output.c]~%")
      (sb-ext:exit :code 1))
    (let* ((input (first args))
           (output (or (second args)
                       (concatenate 'string
                                    (subseq input 0 (position #\. input :from-end t))
                                    ".c"))))
      (compile-file-to-c input output))))

(main)
