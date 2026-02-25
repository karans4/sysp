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
(defun make-vector-type (elem-type) `(:generic "Vector" ,elem-type))
(defun make-tuple-type (elem-types) `(:tuple ,@elem-types))
(defun make-array-type (elem-type size) `(:array ,elem-type ,size))
(defun make-hashmap-type (key-type val-type) `(:generic "HashMap" ,key-type ,val-type))
(defun make-generic-type (name &rest type-args) `(:generic ,name ,@type-args))

;; Vector/HashMap type predicates (these are now generic structs)
(defun vector-type-p (tp)
  "Check if TP is a Vector type: (:generic \"Vector\" elem-type)"
  (and (consp tp) (eq (car tp) :generic) (equal (second tp) "Vector")))
(defun vector-elem-type (tp)
  "Extract element type from a Vector type"
  (third tp))
(defun hashmap-type-p (tp)
  "Check if TP is a HashMap type: (:generic \"HashMap\" key-type val-type)"
  (and (consp tp) (eq (car tp) :generic) (equal (second tp) "HashMap")))
(defun hashmap-key-type (tp) (third tp))
(defun hashmap-val-type (tp) (fourth tp))
;; String type helper: :str is now (:ptr :char) everywhere
(defun str-type-p (tp)
  "Check if TP is a string type: (:ptr :char)"
  (and (consp tp) (eq (car tp) :ptr) (eq (second tp) :char)))

(defun make-rc-type (inner) `(:rc ,inner))
(defun rc-type-p (tp) (and (consp tp) (eq (car tp) :rc)))
(defun rc-inner-type (tp) (second tp))

;; Multiple return values: (:values T1 T2 ...) — struct-based MRV
(defun make-values-type (elem-types) `(:values ,@elem-types))
(defun values-type-p (tp) (and (consp tp) (eq (car tp) :values)))
(defun values-type-elems (tp) (cdr tp))

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
;; Pending string frees to emit after current statement
;; Each entry is a C variable name (temp) holding an allocated string
(defvar *pending-string-frees* nil)

;; Track functions auto-generalized by inference (no explicit :? annotation)
(defvar *auto-poly-fns* (make-hash-table :test #'equal))

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

(defun integer-type-p (tp)
  "Check if type is an integer (not float)."
  (member (resolve-type tp) '(:int :i8 :i16 :i32 :i64
                               :uint :u8 :u16 :u32 :u64
                               :long :long-long :ulong :ulong-long
                               :char :uchar :short :ushort
                               :size :ptrdiff :intptr :uintptr)))

(defun maybe-coerce (code from-type to-type)
  "Wrap code in a C cast if from-type and to-type are different numeric types.
   Handles int→float, float→int, int→int promotions, and Vector→ptr (.data)."
  (let ((from (resolve-type from-type))
        (to (resolve-type to-type)))
    (cond
      ;; Vector→ptr: extract .data field
      ((and to (vector-type-p from) (eq (type-kind to) :ptr))
       (format nil "~a.data" code))
      ;; Numeric coercion
      ((and to (not (eq from to))
              (numeric-type-p from) (numeric-type-p to))
       (format nil "((~a)~a)" (type-to-c to) code))
      (t code))))

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
(defvar *infer-structs* (make-hash-table :test #'equal))
(defvar *infer-locals* (make-hash-table :test #'equal))  ; "fn:var" -> resolved type

(defun infer-env-lookup (name)
  (let* ((resolved (resolve-name name))
         (entry (assoc resolved *infer-env* :test #'equal)))
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
    ((stringp form) '(:ptr :char))
    ((symbolp form)
     (let ((name (string form)))
       (cond
         ((string-equal name "true") :bool)
         ((string-equal name "false") :bool)
         ((string-equal name "null") (make-ptr-type :void))
         (t (or (infer-env-lookup name)
                ;; Dot syntax: expand a.b to (get a b) and infer that
                (when (find #\. name)
                  (let ((expanded (expand-dot-symbol form)))
                    (when expanded (infer-expr expanded))))
                (make-tvar))))))
    ((listp form) (infer-list form))
    (t :int)))

(defun subst-type-params-infer (type-form subst-table)
  "Substitute type parameters during inference. Works on annotation forms (keywords/lists).
   Returns a resolved type s-expr."
  (cond
    ((keywordp type-form)
     (let* ((name (symbol-name type-form))
            (replacement (gethash name subst-table)))
       (if replacement replacement
           (parse-type-annotation type-form))))
    ((and (listp type-form) (keywordp (car type-form)))
     (let ((head (symbol-name (car type-form))))
       (cond
         ((string-equal head "ptr")
          (make-ptr-type (subst-type-params-infer (second type-form) subst-table)))
         ((gethash head *generic-structs*)
          `(:generic ,head ,@(mapcar (lambda (a) (subst-type-params-infer a subst-table)) (cdr type-form))))
         (t (parse-type-expr type-form)))))
    (t type-form)))

(defun infer-bind-type-params (type-form concrete-type subst-table)
  "Bind type parameters during inference. E.g. :T with :int → T→:int."
  (cond
    ((keywordp type-form)
     (let ((name (symbol-name type-form)))
       (when (and (> (length name) 0) (upper-case-p (char name 0)))
         ;; Check it's not a primitive type keyword
         (unless (or (member name '("Vector" "HashMap" "ptr" "fn" "array" "cons" "list"
                                    "tuple" "values" "union" "struct" "enum") :test #'string-equal)
                     (gethash (string-downcase name) *primitive-type-map*))
           (let ((existing (gethash name subst-table)))
             (if existing
                 (unify existing concrete-type)
                 (setf (gethash name subst-table) concrete-type)))))))
    ((and (listp type-form) (keywordp (car type-form)))
     (let ((head (symbol-name (car type-form))))
       (cond
         ((string-equal head "ptr")
          (when (eq (type-kind concrete-type) :ptr)
            (infer-bind-type-params (second type-form) (second concrete-type) subst-table))))))))

;; Tables for simple infer-list dispatch
;; :infer-all = infer all args then return type; :infer-none = return type directly
(defparameter *infer-all-return*
  `(("str-concat" . (:ptr :char)) ("str-slice" . (:ptr :char)) ("str-upper" . (:ptr :char))
    ("str-lower" . (:ptr :char)) ("str-from-int" . (:ptr :char)) ("str-from-float" . (:ptr :char))
    ("str-join" . (:ptr :char)) ("str-trim" . (:ptr :char)) ("str-replace" . (:ptr :char))
    ("sizeof-val" . :int)))

(defparameter *infer-none-return*
  '(("nil?" . :bool) ("null?" . :bool) ("sym" . :value) ("sym-eq?" . :bool)
    ("gensym" . :value) ("sizeof" . :int) ("fmt" . (:ptr :char))
    ("quote" . :value) ("quasiquote" . :value)))

(defun infer-list (form)
  "Infer the type of a list expression."
  (let ((head (first form)))
    (unless (symbolp head)
      (return-from infer-list (make-tvar)))
    ;; Fast table lookups for simple cases
    (let ((all-ret (cdr (assoc (string head) *infer-all-return* :test #'string-equal))))
      (when all-ret
        (dolist (e (cdr form)) (infer-expr e))
        (return-from infer-list all-ret)))
    (let ((none-ret (cdr (assoc (string head) *infer-none-return* :test #'string-equal))))
      (when none-ret (return-from infer-list none-ret)))
    (cond
      ;; Arithmetic: promote result type
      ((member (string head) '("+" "-" "*" "/" "%" "mod") :test #'string-equal)
       (if (and (= (length form) 2) (string-equal (string head) "-"))
           ;; Unary minus
           (infer-expr (second form))
           ;; Fold left over all args, promoting numeric types
           (let ((result-type (infer-expr (second form))))
             (dolist (arg (cddr form))
               (let* ((rt (infer-expr arg))
                      (r (resolve-type result-type))
                      (a (resolve-type rt)))
                 (cond
                   ;; Both concrete numerics: promote without unifying
                   ((and (not (tvar-p r)) (not (tvar-p a))
                         (numeric-type-p r) (numeric-type-p a))
                    (unless (equal r a)
                      (setf result-type (sysp-arithmetic-type r a))))
                   ;; One is tvar: unify (needed for type propagation)
                   ((tvar-p r) (unify result-type rt))
                   ((tvar-p a) (unify rt result-type))
                   ;; Both concrete non-numeric: just unify
                   (t (unify result-type rt)))))
             result-type)))

      ;; Comparison: operands unify, result is bool. Chained: (< a b c) all unify.
      ((member (string head) '("<" ">" "<=" ">=" "==" "!=") :test #'string-equal)
       (let ((first-type (infer-expr (second form))))
         (dolist (arg (cddr form))
           (unify first-type (infer-expr arg)))
         :bool))

      ;; Logical: infer sub-expressions, result is bool
      ((member (string head) '("and" "or" "not") :test #'string-equal)
       (dolist (arg (cdr form)) (infer-expr arg))
       :bool)

      ;; Bitwise: walk operands, return :int (C semantics: bitwise ops produce int)
      ((member (string head) '("bit-and" "bit-or" "bit-xor" "bit-not" "shl" "shr"
                                "&" "|" "^" "~" "<<" ">>")
               :test #'string-equal)
       (dolist (arg (cdr form)) (infer-expr arg))
       :int)

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
       (let ((result :int)
             (subforms (cdr form)))
         (dolist (f (butlast subforms))
           (infer-stmt f))
         (when (car (last subforms))
           (setf result (infer-expr (car (last subforms)))))
         result))

      ;; Generic struct constructor: infer type params from args
      ((and (symbolp head) (gethash (symbol-name head) *generic-structs*))
       (let* ((gname (symbol-name head))
              (entry (gethash gname *generic-structs*))
              (type-params (first entry))
              (fields-raw (second entry))
              ;; Infer arg types
              (arg-types (mapcar #'infer-expr (cdr form)))
              ;; Bind type params from field types
              (subst-table (make-hash-table :test 'equal))
              (field-idx 0)
              (lst (copy-list fields-raw)))
         (loop while lst do
           (pop lst)  ; field name
           (when (and lst (or (keywordp (first lst))
                              (and (listp (first lst)) (keywordp (car (first lst))))))
             (let ((type-form (pop lst)))
               (when (< field-idx (length arg-types))
                 (infer-bind-type-params type-form (nth field-idx arg-types) subst-table))
               (incf field-idx))))
         (let ((concrete-types (mapcar (lambda (tp)
                                         (or (gethash (symbol-name tp) subst-table) (make-tvar)))
                                       type-params)))
           `(:generic ,gname ,@concrete-types))))

      ;; Vector: all elements unify, result is vector of element type
      ((and (symbolp head) (string= (symbol-name head) "Vector"))
       (let ((elem-type (make-tvar)))
         (dolist (e (cdr form))
           (unify elem-type (infer-expr e)))
         (make-vector-type elem-type)))

      ;; tuple: result is tuple of element types
      ((sym= head "tuple")
       (make-tuple-type (mapcar #'infer-expr (cdr form))))

      ;; tuple-ref: can't statically resolve
      ((sym= head "tuple-ref") (make-tvar))

      ;; nth: generic indexing — dispatch on collection type
      ((sym= head "nth")
       (let ((coll-type (infer-expr (second form))))
         (when (third form) (infer-expr (third form)))
         (cond
           ((vector-type-p coll-type) (vector-elem-type coll-type))
           ((eq (type-kind coll-type) :tuple) (make-tvar))
           ((eq (type-kind coll-type) :array) (second coll-type))
           ((eq (type-kind coll-type) :ptr) (second coll-type))
           (t (let ((elem (make-tvar)))
                (unify coll-type (make-ptr-type elem))
                elem)))))

      ;; HashMap: result is (:hashmap K V)
      ((and (symbolp head) (string= (symbol-name head) "HashMap"))
       (if (null (cdr form))
           (make-hashmap-type '(:ptr :char) :int)  ; empty map defaults to str->int
           (let ((key-type (infer-expr (second form)))
                 (val-type (infer-expr (third form))))
             ;; Infer remaining pairs too
             (loop for (k v) on (cdddr form) by #'cddr
                   when k do (unify key-type (infer-expr k))
                   when v do (unify val-type (infer-expr v)))
             (make-hashmap-type key-type val-type))))

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
                    (type (cond
                            ((and lst (keywordp (first lst)))
                             (let ((result (parse-type-from-list lst)))
                               (setf lst (cdr result))
                               (car result)))
                            ((and lst (listp (first lst)) (keywordp (car (first lst))))
                             (parse-type-expr (pop lst)))
                            (t (make-tvar)))))
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

      ;; str-split: returns Vector of str (not a simple constant type)
      ((sym= head "str-split") (infer-expr (second form)) (infer-expr (third form)) (make-vector-type '(:ptr :char)))

      ;; get: struct field access — resolve from struct definition
      ((sym= head "get")
       (let* ((obj-type (resolve-type (infer-expr (second form))))
              (field-name (string (third form)))
              ;; Find struct name: (:struct "CPU"), (:ptr (:struct "CPU")), (:generic ...), or direct
              (struct-name (cond
                             ((and (consp obj-type) (eq (car obj-type) :struct))
                              (second obj-type))
                             ((and (consp obj-type) (eq (car obj-type) :ptr)
                                   (consp (second obj-type)) (eq (car (second obj-type)) :struct))
                              (second (second obj-type)))
                             ((and (consp obj-type) (eq (car obj-type) :generic))
                              ;; Generic struct: look up field from template with substituted types
                              (second obj-type))
                             (t nil)))
              ;; (Vector/HashMap field types now resolved via generic-field-type below)
              ;; For generic types, resolve field type with type param substitution
              (generic-field-type
               (when (and (consp obj-type) (eq (car obj-type) :generic))
                 (let* ((gname (second obj-type))
                        (concrete-types (cddr obj-type))
                        (entry (gethash gname *generic-structs*)))
                   (when entry
                     (let* ((type-params (first entry))
                            (fields-raw (second entry))
                            (subst-table (make-hash-table :test 'equal)))
                       ;; Build substitution table
                       (loop for tp in type-params
                             for ct in concrete-types
                             do (setf (gethash (symbol-name tp) subst-table) ct))
                       ;; Find the field and substitute
                       (let ((lst (copy-list fields-raw)))
                         (loop while lst do
                           (let ((fname (string (pop lst))))
                             (when (and lst (or (keywordp (first lst))
                                                (and (listp (first lst)) (keywordp (car (first lst))))))
                               (let ((type-form (pop lst)))
                                 (when (string-equal fname field-name)
                                   (return (subst-type-params-infer type-form subst-table)))))))))))))
              ;; If obj is a tvar, try to find a struct with this field (reverse lookup)
              (struct-name (or struct-name
                               (when (tvar-p obj-type)
                                 (block found
                                   (maphash (lambda (sname fields)
                                              (when (and (listp fields)
                                                         (assoc field-name fields :test #'equal))
                                                (return-from found sname)))
                                            *infer-structs*)
                                   nil))))
              (fields (when struct-name (gethash struct-name *infer-structs*)))
              (field-type (when (and fields (listp fields))
                            (cdr (assoc field-name fields :test #'equal)))))
         ;; Don't unify object type — it might be struct or ptr-to-struct
         ;; Let call-site types determine the concrete param type
         (or generic-field-type field-type (make-tvar))))

      ;; set!: infer target and value, return the assigned type
      ((sym= head "set!")
       (infer-expr (second form))  ;; target (may trigger struct lookup via dot syntax)
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
       (when (third form) (infer-expr (third form)))
       (if (listp (second form))
           (parse-type-expr (second form))
           (parse-type-annotation (second form))))

      ;; values: multiple return values
      ((sym= head "values")
       (make-values-type (mapcar #'infer-expr (cdr form))))

      ;; let-values: destructure MRV
      ((sym= head "let-values")
       (let* ((bindings (second form))  ; ([x y] (f))
              (names (first bindings))
              (init-form (second bindings))
              (init-type (infer-expr init-form))
              (old-env *infer-env*))
         ;; Bind each name to its component type
         (if (values-type-p init-type)
             (loop for name in names
                   for tp in (values-type-elems init-type)
                   do (infer-env-bind (string name) tp))
             ;; If not a values type, treat as single value
             (when names
               (infer-env-bind (string (first names)) init-type)))
         ;; Infer body
         (let ((result :void))
           (dolist (f (cddr form))
             (setf result (infer-expr f)))
           result)))

      ;; asm!: void in stmt position; in expr position, :out type if given
      ((sym= head "asm!")
       (let ((rest (cddr form)))
         ;; Look for :out keyword to determine return type
         (loop for (k v) on rest by #'cddr
               when (and (keywordp k) (string-equal (string k) "OUT"))
               do (return-from infer-list
                    (if (listp v)
                        (parse-type-annotation (second v))  ; [name :type]
                        (parse-type-annotation v))))
         :void))

      ((sym= head "array-ref")
       (let ((elem (make-tvar))
             (arr-type (infer-expr (second form))))
         (when (third form) (infer-expr (third form)))
         (unify arr-type (make-ptr-type elem))
         elem))
      ((sym= head "array-set!")
       (let ((elem (make-tvar))
             (arr-type (infer-expr (second form))))
         (when (third form) (infer-expr (third form)))
         (unify arr-type (make-ptr-type elem))
         (when (fourth form) (unify elem (infer-expr (fourth form))))
         :void))
      ;; ptr-set!: (ptr-set! p val) or (ptr-set! p idx val)
      ((sym= head "ptr-set!")
       (let ((ptr-type (infer-expr (second form))))
         (if (fourth form)
             ;; (ptr-set! p idx val) — indexed
             (progn
               (infer-expr (third form))
               (infer-expr (fourth form)))
             ;; (ptr-set! p val)
             (infer-expr (third form)))
         ;; Unify pointer elem type with value
         (let ((elem (make-tvar)))
           (unify ptr-type (make-ptr-type elem))
           elem)))
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
      ((sym= head "ptr-deref")
       ;; (ptr-deref p) or (ptr-deref p idx) — infer pointer, return element type
       (let ((ptr-type (infer-expr (second form)))
             (elem-tvar (make-tvar)))
         (when (third form) (infer-expr (third form)))  ;; index
         (unify ptr-type (make-ptr-type elem-tvar))
         elem-tvar))

      ;; Statement-only forms in expression position: infer bodies, return :void
      ((or (sym= head "when") (sym= head "unless") (sym= head "while") (sym= head "for"))
       (infer-stmt form)
       :void)

      ;; Trait method call: look up trait, infer self type, return method ret type
      ((and (symbolp head) (gethash (symbol-name head) *method-to-trait*))
       (let* ((method-name (symbol-name head))
              (trait-name (gethash method-name *method-to-trait*))
              (trait-entry (gethash trait-name *traits*))
              (trait-methods (second trait-entry))
              (method-sig (find method-name trait-methods :key #'first :test #'equal)))
         ;; Infer all args
         (let ((arg-types (mapcar #'infer-expr (cdr form))))
           (if (and method-sig (third method-sig))
               ;; Has return type annotation — resolve with trait's type params
               (let* ((self-type (first arg-types))
                      (ret-ann (third method-sig))
                      ;; Check if return type is a type param
                      (trait-type-params (first trait-entry))
                      (subst-table (make-hash-table :test 'equal)))
                 ;; Build substitution from self-type if it's a generic struct
                 (when (and (consp self-type) (eq (car self-type) :generic)
                            (gethash (second self-type) *generic-structs*))
                   (let ((entry (gethash (second self-type) *generic-structs*)))
                     (loop for tp in (first entry)
                           for ct in (cddr self-type)
                           do (setf (gethash (symbol-name tp) subst-table) ct))))
                 ;; Also try to bind trait type params
                 (when (and trait-type-params (consp self-type) (eq (car self-type) :generic))
                   (loop for tp in trait-type-params
                         for ct in (cddr self-type)
                         do (setf (gethash (symbol-name tp) subst-table) ct)))
                 ;; Substitute in return type
                 (let ((replacement (gethash (symbol-name ret-ann) subst-table)))
                   (or replacement (parse-type-annotation ret-ann))))
               ;; No return type — return tvar
               (make-tvar)))))

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
                (type-ann (cond
                            ((keywordp (first rest))
                             (prog1 (parse-type-annotation (first rest))
                               (setf rest (cdr rest))))
                            ((and (listp (first rest)) (keywordp (car (first rest))))
                             (prog1 (parse-type-expr (first rest))
                               (setf rest (cdr rest))))
                            (t nil)))
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
        ((member (string head) '("when" "unless" "while") :test #'string-equal)
         (infer-expr (second form))
         (dolist (f (cddr form)) (infer-stmt f))
         :void)
        ((sym= head "for")
         ;; (for [var start end] body...) — bind loop var to int, infer body
         (let ((binding (second form)))
           (when (and (listp binding) (>= (length binding) 3))
             (let ((var-name (string (first binding))))
               (infer-expr (second binding))  ;; start
               (infer-expr (third binding))   ;; end
               (infer-env-bind var-name :int)))
           (dolist (f (cddr form))
             (infer-stmt f)))
         :void)
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

        ;; let-array: register name as pointer type
        ((sym= head "let-array")
         (let* ((rest (cdr form))
                (_ (when (stringp (first rest)) (setf rest (cdr rest))))
                (name (string (first rest)))
                (type-ann (parse-type-annotation (second rest))))
           (declare (ignore _))
           (infer-env-bind name (make-ptr-type type-ann))))

        ;; set!: unify target with value
        ((sym= head "set!")
         (let* ((target (second form))
                (target-type (if (symbolp target)
                                 (infer-env-lookup (string target))
                                 (infer-expr target)))
                (val-type (infer-expr (third form))))
           (when target-type
             (unify target-type val-type))))

        ;; return/print/println: infer the expression
        ((member (string head) '("return" "print" "println") :test #'string-equal)
         (when (second form) (infer-expr (second form))))
        ;; printf: infer all arg expressions (skip format string)
        ((sym= head "printf") (dolist (arg (cddr form)) (infer-expr arg)))
        ;; recur: infer arguments
        ((sym= head "recur") (dolist (arg (cdr form)) (infer-expr arg)))
        ;; do block as statement
        ((sym= head "do") (dolist (f (cdr form)) (infer-stmt f)))

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
         (ret-annotation (when (type-annotation-form-p (first rest-forms))
                           (prog1 (parse-ret-annotation (first rest-forms))
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
             (free (reduce #'append
                           (mapcar #'free-tvars (cons ret-type param-types))
                           :initial-value nil)))
        ;; Save resolved local types for compile phase
        (dolist (entry *infer-env*)
          (unless (assoc (car entry) old-env :test #'equal)
            (let ((resolved (resolve-or-default (cdr entry))))
              (setf (gethash (format nil "~a:~a" name (car entry)) *infer-locals*) resolved))))
        ;; Restore env but keep function binding
        (setf *infer-env* old-env)
        (if (and free (not (string-equal name "main")))
            ;; Free tvars remain — auto-generalize as polymorphic
            (progn
              (setf (gethash name *auto-poly-fns*) t)
              (infer-env-bind name :poly)
              :poly)
            ;; No free tvars — resolve and register concrete type
            (let* ((resolved-params (mapcar #'resolve-or-default param-types))
                   (resolved-ret (resolve-or-default ret-type))
                   (fn-type (make-fn-type resolved-params resolved-ret)))
              (infer-env-bind name fn-type)
              fn-type))))))

;; Run inference on all top-level forms (pre-pass before compilation)
(defun infer-toplevel (forms)
  "Run type inference on all top-level forms. Populates *infer-env*."
  (setf *infer-env* nil)
  (clrhash *infer-structs*)
  (clrhash *infer-locals*)
  (reset-inference)
  (dolist (form forms)
    (when (listp form)
      (cond
        ((sym= (first form) "defn")
         (infer-defn form))
        ((or (sym= (first form) "struct") (sym= (first form) "foreign-struct"))
         ;; Register struct name and constructor type
         (let* ((is-struct (sym= (first form) "struct"))
                (has-attr (and is-struct (stringp (second form))))
                (name-form (cond (has-attr (third form))
                                 (is-struct (second form))
                                 (t (second form))))
                ;; Check for generic struct: name-form is a list like (Pair :T :U)
                (is-generic (and is-struct (listp name-form) (> (length name-form) 1))))
           (if is-generic
               ;; Generic struct — store template for later instantiation
               (let ((name (string (first name-form)))
                     (type-params (rest name-form))
                     (fields-raw (cond (has-attr (fourth form))
                                       (is-struct (third form))
                                       (t (third form)))))
                 (setf (gethash name *generic-structs*)
                       (list type-params (if (listp fields-raw) fields-raw nil))))
               ;; Concrete struct — original behavior
               (let* ((name (string name-form))
                      (fields-raw (cond (has-attr (fourth form))
                                        (is-struct (third form))
                                        (t (third form))))
                      (field-types nil)
                      (field-alist nil))
                 (let ((lst (if (listp fields-raw) (copy-list fields-raw) nil)))
                   (loop while lst do
                     (let ((fname (string (pop lst))))  ; field name
                       (when (and lst (keywordp (first lst)))
                         (let ((result (parse-type-from-list lst)))
                           (push (car result) field-types)
                           (push (cons fname (car result)) field-alist)
                           (setf lst (cdr result)))))))
                 (setf field-types (nreverse field-types))
                 (setf field-alist (nreverse field-alist))
                 ;; Register struct fields for inference (get/set! resolution)
                 (setf (gethash name *infer-structs*) field-alist)
                 (unless (gethash name *structs*)
                   (setf (gethash name *structs*) :infer-placeholder))
                 (when is-struct
                   (infer-env-bind name (make-fn-type field-types (make-struct-type name))))))))
        ((sym= (first form) "enum")
         ;; Register enum variants as :int in inference env
         (let ((variants (cddr form)))
           (dolist (v variants)
             (when (listp v)
               (infer-env-bind (string (first v)) :int)))))
        ((sym= (first form) "deftrait")
         ;; Register trait and method signatures
         (compile-deftrait form))
        ((sym= (first form) "impl")
         ;; Store impl templates
         (compile-impl form))
        ((and (or (sym= (first form) "let") (sym= (first form) "let-mut"))
              (not (listp (second form))))  ; top-level let/let-mut
         ;; Register top-level constant with inferred or annotated type
         (let* ((name (string (second form)))
                (rest (cddr form))
                (type (if (keywordp (first rest))
                          (parse-type-annotation (first rest))
                          (when (first rest) (infer-expr (first rest))))))
           (when type (infer-env-bind name type))))
        ((sym= (first form) "extern")
         ;; Register extern function type
         (let* ((name (string (second form)))
                (params-raw (third form))
                (rest (cdddr form))
                (ret-type (if (type-annotation-form-p (first rest))
                              (parse-ret-annotation (first rest))
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
           (infer-env-bind name (make-fn-type param-types ret-type))))
        ((sym= (first form) "extern-var")
         ;; Register extern variable type
         (let* ((name (string (second form)))
                (tp (parse-type-annotation (third form))))
           (infer-env-bind name tp)))
        ;; export — no inference needed
        ((sym= (first form) "export") nil)))))

;;; === Environment ===

(defstruct env
  (bindings nil)  ; alist of (name . type)
  (parent nil)
  (releases nil)  ; list of C variable names needing val_release at scope exit
  (mutables nil)  ; list of mutable variable names (from let-mut)
  (rc-releases nil)  ; list of (c-name . inner-type) for RC release at scope exit
  (data-releases nil)) ; list of (c-name . kind) for vector/hashmap free at scope exit

(defun env-lookup (env name)
  (let ((resolved (resolve-name name)))
    (if (null env) nil
        (let ((found (assoc resolved (env-bindings env) :test #'equal)))
          (if found (cdr found)
              (env-lookup (env-parent env) resolved))))))

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

(defun env-add-data-release (env c-name type)
  "Record a variable for recursive drop at scope exit. TYPE is the full sysp type."
  (push (cons c-name type) (env-data-releases env)))

(defun type-needs-drop-p (tp)
  "Does this type own heap data that needs freeing on drop?"
  (let ((kind (type-kind tp)))
    (or (str-type-p tp)
        (eq kind :rc)
        ;; Vector: has owned data pointer
        (vector-type-p tp)
        ;; HashMap: has owned keys/vals/occ pointers
        (hashmap-type-p tp)
        ;; Generic/plain structs: check if any field needs drop
        (and (member kind '(:generic :struct))
             (let* ((sname (if (eq kind :generic)
                               (instantiate-generic-struct (second tp) (cddr tp))
                               (second tp)))
                    (fields (gethash sname *structs*)))
               (and (listp fields)
                    (some (lambda (f) (type-needs-drop-p (cdr f))) fields)))))))

(defun emit-drop (c-expr tp &optional (indent "  "))
  "Generate C statements to recursively drop a value of type TP.
   Walks the type structure: frees pointer fields, decrements RC, recurses into structs."
  (let ((kind (type-kind tp)))
    (cond
      ;; String ((:ptr :char)): free the char*
      ((str-type-p tp)
       (list (format nil "~afree((char*)~a);" indent c-expr)))
      ;; Vector: free backing data array
      ((vector-type-p tp)
       (list (format nil "~aif (~a.cap > 0) free(~a.data);" indent c-expr c-expr)))
      ;; HashMap: free backing arrays
      ((hashmap-type-p tp)
       (list (format nil "~aif (~a.cap > 0) { free(~a.keys); free(~a.vals); free(~a.occ); }"
                     indent c-expr c-expr c-expr c-expr)))
      ;; Generic/plain struct: drop each field that needs it
      ((member kind '(:generic :struct))
       (let* ((sname (if (eq kind :generic)
                         (instantiate-generic-struct (second tp) (cddr tp))
                         (second tp)))
              (fields (gethash sname *structs*)))
         (when (listp fields)
           (mapcan (lambda (f)
                     (when (type-needs-drop-p (cdr f))
                       (emit-drop (format nil "~a.~a" c-expr (sanitize-name (car f)))
                                   (cdr f) indent)))
                   fields))))
      (t nil))))

(defun emit-data-releases (env)
  "Generate recursive drop code for all owned data at scope exit."
  (mapcan (lambda (entry)
            (emit-drop (car entry) (cdr entry)))
          (env-data-releases env)))

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
(defvar *sysp-modules* (make-hash-table :test 'equal))  ; module-name -> list of exported symbol names
(defvar *imports* (make-hash-table :test 'equal))  ; qualified-or-bare name -> real (unqualified) name
(defvar *current-fn-name* nil)  ; for recur: name of function being compiled
(defvar *current-let-target* nil)  ; for escape analysis: name of let variable being initialized
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
(defvar *defn-wrappers* (make-hash-table :test 'equal))  ; c-name -> wrapper-name (defn→Fn wrapper dedup)
(defvar *raw-lambda-names* (make-hash-table :test 'equal))  ; var-name -> plain-C-lambda-name (non-capturing lambdas)
(defvar *extern-fns* (make-hash-table :test 'equal))  ; names of extern C functions (for C interop checks)
(defvar *env-counter* 0)  ; counter for closure env structs
(defvar *interp-gensym-counter* 0)
(defvar *spawn-counter* 0)    ; counter for spawn sites
(defvar *uses-threads* nil)   ; emit #include <pthread.h> if true
(defvar *restart-counter* 0)  ; counter for restart-case sites
(defvar *handler-counter* 0)  ; counter for handler-bind sites
(defvar *handler-wrap-counter* 0) ; counter for handler wrapper functions
(defvar *uses-conditions* nil)
(defvar *exports* nil)  ; hash table of exported names, nil = export all
(defvar *escape-info* (make-hash-table :test 'equal))  ; "fn.var" -> :local or :escapes
(defvar *current-escape-fn* nil)  ; fn name during escape analysis ; emit condition system preamble if true
;; Generic structs state
(defvar *generic-structs* (make-hash-table :test 'equal))  ; name -> (type-params fields-raw)
(defvar *generic-struct-instances* (make-hash-table :test 'equal))  ; mangled-name -> t (dedup)
;; Traits state
(defvar *traits* (make-hash-table :test 'equal))  ; name -> (type-params method-signatures)
(defvar *trait-impls* (make-hash-table :test 'equal))  ; "Trait:Type" -> hash of method-name -> defn-form
(defvar *method-to-trait* (make-hash-table :test 'equal))  ; method-name -> trait-name

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

;;; === Error Reporting with Source Locations ===

;; Forward declare — actual defvar is in parser section
(defvar *source-locations*)

(defun sysp-error (form fmt &rest args)
  "Signal an error with source location if available for form."
  (let ((loc (and (boundp '*source-locations*) (consp form)
                  (gethash form *source-locations*))))
    (if loc
        (error "~a:~d:~d: ~a" (first loc) (second loc) (third loc)
               (apply #'format nil fmt args))
        (error "sysp: ~a" (apply #'format nil fmt args)))))

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
              ;; Unquote (~expr, ~@expr) vs bit-not operator (~ expr — space after)
              ((char= c #\~)
               (let ((next-c (if (< (1+ (pstate-pos ps)) (length (pstate-source ps)))
                                 (char (pstate-source ps) (1+ (pstate-pos ps)))
                                 nil)))
                 (if (or (null next-c) (member next-c '(#\Space #\Newline #\Tab #\) #\])))
                     ;; Space/delimiter after ~ : it's the bit-not symbol
                     (progn (ps-advance ps) (intern "~" :sysp))
                     ;; No space: unquote
                     (progn
                       (ps-advance ps)
                       (if (and (not (ps-eof-p ps)) (char= (ps-peek ps) #\@))
                           (progn (ps-advance ps)
                                  (multiple-value-bind (inner has) (ps-read-form ps)
                                    (declare (ignore has))
                                    (list (intern "splice" :sysp) inner)))
                           (multiple-value-bind (inner has) (ps-read-form ps)
                             (declare (ignore has))
                             (list (intern "unquote" :sysp) inner)))))))
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

(defun resolve-name (name)
  "Resolve a possibly-qualified name via *imports*. foo.bar → real unqualified name."
  (or (gethash name *imports*) name))

(defun split-string (str sep)
  "Split STR on character SEP, return list of substrings."
  (let ((parts nil) (start 0))
    (loop for i from 0 below (length str)
          when (char= (char str i) sep)
          do (push (subseq str start i) parts)
             (setf start (1+ i)))
    (push (subseq str start) parts)
    (nreverse parts)))

(defun expand-dot-symbol (form)
  "Expand a.b.c → (GET (GET a b) c). Returns nil if not a dot expression."
  (let* ((name (string form))
         (parts (split-string name #\.)))
    (when (and (> (length parts) 1)
               (every (lambda (p) (plusp (length p))) parts))
      (let ((result (intern (first parts))))
        (dolist (field (rest parts))
          (setf result (list (intern "GET") result (intern field))))
        result))))

(defun collect-module-names (forms)
  "Scan top-level forms for exported names (defn, struct, enum, const, defmacro, etc)."
  (let ((names nil))
    (dolist (form forms)
      (when (listp form)
        (let ((head (first form)))
          (cond
            ((sym= head "defn") (push (string (second form)) names))
            ((sym= head "defn-ct") (push (string (second form)) names))
            ((sym= head "struct")
             (push (string (if (and (listp (second form))
                                    (sym= (first (second form)) "generic"))
                               (third form)
                               (second form)))
                   names))
            ((sym= head "enum") (push (string (second form)) names))
            ((or (sym= head "const") (sym= head "let"))
             (push (string (second form)) names))
            ((sym= head "defmacro") (push (string (second form)) names))
            ((sym= head "extern") (push (string (second form)) names))
            ((sym= head "deftype") (push (string (second form)) names))))))
    (nreverse names)))

(defun parse-use-options (form)
  "Parse (use module ...) options. Returns (values module-name mode only-list).
   mode is :all, :qualified, or :only."
  (let* ((module-sym (second form))
         (module-name (string-downcase (string module-sym)))
         (opts (cddr form))
         (mode :all)
         (only-list nil))
    (when opts
      (let ((first-opt (first opts)))
        (cond
          ((and (keywordp first-opt) (string-equal (string first-opt) "ALL"))
           (setf mode :all))
          ((and (keywordp first-opt) (string-equal (string first-opt) "QUALIFIED"))
           (setf mode :qualified))
          ((and (keywordp first-opt) (string-equal (string first-opt) "AS"))
           ;; (use foo :as foo) = qualified
           (setf mode :qualified))
          ((and (keywordp first-opt) (string-equal (string first-opt) "ONLY"))
           (setf mode :only)
           (let ((names-form (second opts)))
             (when (listp names-form)
               (setf only-list (mapcar (lambda (s) (string s)) names-form))))))))
    (values module-name mode only-list)))

(defun register-module-imports (module-name names mode only-list)
  "Register names in *imports* based on import mode."
  ;; Always register qualified names (module.name → name)
  (dolist (name names)
    (setf (gethash (format nil "~a.~a" module-name name) *imports*) name))
  ;; Register unqualified based on mode
  (case mode
    (:all
     (dolist (name names)
       (setf (gethash name *imports*) name)))
    (:qualified
     ;; No unqualified imports — only module.name entries (already done above)
     nil)
    (:only
     (dolist (name only-list)
       (when (member name names :test #'equal)
         (setf (gethash name *imports*) name))))))

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
                                   (t (sysp-error form "use: argument must be a string or symbol, got ~s" arg))))
                       (abs-path (namestring (truename resolved))))
                  (if (gethash abs-path *included-files*)
                      ;; Already included — but still parse options for import registration
                      ;; (module names already in *sysp-modules* from first inclusion)
                      (let ((module-name (string-downcase (string arg))))
                        (multiple-value-bind (mn mode only-list) (parse-use-options form)
                          (declare (ignore mn))
                          (let ((names (gethash module-name *sysp-modules*)))
                            (when names
                              (register-module-imports module-name names mode only-list))))
                        nil)
                      (progn
                        (setf (gethash abs-path *included-files*) t)
                        (let* ((child-forms (read-sysp-forms abs-path))
                               (child-dir (make-pathname :directory (pathname-directory abs-path)))
                               (expanded (expand-uses child-forms child-dir))
                               (module-name (string-downcase (string arg)))
                               (names (collect-module-names expanded)))
                          ;; Register module and its imports
                          (setf (gethash module-name *sysp-modules*) names)
                          (multiple-value-bind (mn mode only-list) (parse-use-options form)
                            (declare (ignore mn))
                            (register-module-imports module-name names mode only-list))
                          expanded))))
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
      ;; (defn-ct/defmacro name [params] body...)
      ((or (sym= head "defn-ct") (sym= head "defmacro"))
       (format nil "(~a ~a ~a~{ ~a~})"
               (serialize-atom head) (serialize-atom (second form))
               (serialize-params (third form))
               (mapcar #'serialize-atom-or-form (cdddr form))))
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
    ;; Collect export declarations (if any)
    (let ((exports nil))
      (dolist (form forms)
        (when (and (listp form) (sym= (first form) "export"))
          (unless exports
            (setf exports (make-hash-table :test 'equal)))
          (dolist (name (rest form))
            (setf (gethash (string name) exports) t))))
    (with-open-file (out out-path :direction :output :if-exists :supersede)
      (format out ";; ~a -- auto-generated header~%" (file-namestring out-path))
      (format out ";; Source: ~a~%~%" (file-namestring in-path))
      (dolist (form forms)
        (when (listp form)
          (let ((head (first form)))
            (cond
              ;; export — skip (metadata, not code)
              ((sym= head "export") nil)
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
              ;; extern / extern-var — verbatim
              ((or (sym= head "extern") (sym= head "extern-var"))
               (format out "~a~%" (serialize-form form)))
              ;; defn — check exports, private prefix, poly/mono
              ((sym= head "defn")
               (let ((name (string (second form))))
                 ;; Skip if exports list exists and name not in it
                 (unless (or (and exports (not (gethash name exports)))
                             (and (> (length name) 0) (char= (char name 0) #\_)))
                   (if (defn-is-poly-p form)
                       ;; Poly: emit verbatim (needs body for monomorphization)
                       (format out "~a~%" (serialize-form form))
                       ;; Mono: strip body -> extern
                       (let* ((params (third form))
                              (rest (cdddr form))
                              (ret-ann (when (type-annotation-form-p (first rest)) (first rest))))
                         (format out "(extern ~a ~a~a)~%"
                                 (serialize-atom (second form))
                                 (serialize-params params)
                                 (if ret-ann
                                     (format nil " ~a" (if (listp ret-ann)
                                                           (serialize-form ret-ann)
                                                           (serialize-atom ret-ann)))
                                     "")))))))
              ;; c-decl — skip (raw C, not part of sysp API)
              ((sym= head "c-decl") nil)
              ;; use — skip (already expanded)
              ((sym= head "use") nil)))))))))

;;; === Macro System ===

(defun macroexpand-1-sysp (form)
  "Expand one macro call. Returns (values expanded-form expanded-p)"
  (if (and (listp form) (symbolp (first form)))
      (let ((expander (gethash (string-downcase (resolve-name (string (first form)))) *macros*)))
        (if expander
            (let ((expanded (funcall expander form)))
              ;; Propagate source location from original form to expanded form
              (when (and (consp expanded) (gethash form *source-locations*))
                (setf (gethash expanded *source-locations*)
                      (gethash form *source-locations*)))
              (values expanded t))
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
            ;; Not a macro — recurse into subforms, preserving identity if unchanged
            (let* ((new-elems (mapcar #'macroexpand-all form))
                   (changed (loop for o in form for n in new-elems
                                  thereis (not (eq o n)))))
              (if changed
                  ;; Propagate source location to new list
                  (let ((result new-elems)
                        (loc (gethash form *source-locations*)))
                    (when loc (setf (gethash result *source-locations*) loc))
                    result)
                  form))))))

(defun gsym (prefix)
  "Generate a unique sysp temp symbol with given prefix."
  (intern (format nil "_~a~d" prefix (incf *sysp-gensym-counter*))))

(defun vec-collect-macro (vec-expr loop-body-fn)
  "Generate a macro expansion that creates a result vector, loops over vec-expr,
   and calls loop-body-fn with (result-sym vref-sym idx-sym) to get the loop body forms.
   Returns the (do ...) form."
  (let ((vref (gsym "v")) (result (gsym "r")) (idx (gsym "i")))
    (list 'do
          (list 'let vref vec-expr)
          (list 'let-mut result (list '|Vector|))
          (list* 'for (list idx 0 (list 'len vref))
                 (funcall loop-body-fn result vref idx))
          result)))

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
  (setf (gethash "dotimes" *macros*)
        (lambda (form) (list* 'for (list (first (second form)) 0 (second (second form))) (cddr form))))
  (setf (gethash "inc!" *macros*) (lambda (f) (list 'set! (second f) (list '+ (second f) 1))))
  (setf (gethash "dec!" *macros*) (lambda (f) (list 'set! (second f) (list '- (second f) 1))))
  ;; Collection mutation macros — expand to library poly-fn calls with addr-of
  (setf (gethash "vector-push!" *macros*)
        (lambda (f) (list '_vector-push-impl (list 'addr-of (second f)) (third f))))
  (setf (gethash "hash-set!" *macros*)
        (lambda (f) (list '_hash-set-impl (list 'addr-of (second f)) (third f) (fourth f))))
  (setf (gethash "hash-del!" *macros*)
        (lambda (f) (list '_hash-del-impl (list 'addr-of (second f)) (third f))))
  ;; for-each: (for-each [x vec] body...) => vector iteration
  ;;           (for-each [k v m] body...)  => hash map iteration
  (setf (gethash "for-each" *macros*)
        (lambda (form)
          (let* ((spec (second form))
                 (body (cddr form)))
            (if (= (length spec) 3)
                ;; Hash map: [k v m] => iterate keys, look up values
                (let ((k (first spec))
                      (v (second spec))
                      (m (third spec))
                      (fm (intern (format nil "_fm~d" (incf *sysp-gensym-counter*))))
                      (fk (intern (format nil "_fk~d" (incf *sysp-gensym-counter*))))
                      (fi (intern (format nil "_fi~d" (incf *sysp-gensym-counter*)))))
                  (list 'do
                        (list 'let fm m)
                        (list 'let fk (list 'hash-keys fm))
                        (list* 'for (list fi 0 (list 'len fk))
                               (list 'let k (list 'vector-ref fk fi))
                               (list 'let v (list 'hash-get fm k))
                               body)))
                ;; Vector: [x vec] => iterate with index
                (let ((var (first spec))
                      (collection (second spec))
                      (idx (intern (format nil "_fe~d" (incf *sysp-gensym-counter*)))))
                  (list 'do
                        (list* 'for (list idx 0 (list 'len collection))
                               (cons (list 'let var (list 'vector-ref collection idx))
                                     body))))))))
  ;; map, filter, reduce: now real poly defn functions in lib/core.sysp
  ;; keep: alias for filter (also in core.sysp now)
  ;; (removed macro definitions — these are now first-class HOFs)
  ;; Simple aliases: (alias a b c) => (target a b c)
  (dolist (alias '(("assoc!" hash-set! 3) ("dissoc!" hash-del! 2) ("contains?" hash-has? 2)))
    (let ((target (second alias)) (arity (third alias)))
      (setf (gethash (first alias) *macros*)
            (if (= arity 2)
                (lambda (form) (list target (second form) (third form)))
                (lambda (form) (list target (second form) (third form) (fourth form)))))))
  ;; merge!: capture keys once, iterate, free temp vector
  (setf (gethash "merge!" *macros*)
        (lambda (form)
          (let ((k (intern (format nil "_mk~d" (incf *sysp-gensym-counter*))))
                (kv (intern (format nil "_mkv~d" (incf *sysp-gensym-counter*))))
                (idx (intern (format nil "_mi~d" (incf *sysp-gensym-counter*)))))
            (list 'do
                  (list 'let kv (list 'hash-keys (third form)))
                  (list 'for (list idx 0 (list 'len kv))
                        (list 'let k (list 'vector-ref kv idx))
                        (list 'hash-set! (second form) k (list 'hash-get (third form) k)))))))

  ;; === Clojure-style collection predicates ===
  ;; some: (some pred vec) — returns 1 if any element matches
  (setf (gethash "some" *macros*)
        (lambda (form)
          (let ((v (gsym "v")) (r (gsym "r")) (i (gsym "i")))
            (list 'do (list 'let v (third form)) (list 'let-mut r 0)
                  (list 'for (list i 0 (list 'len v))
                        (list 'when (list (second form) (list 'vector-ref v i))
                              (list 'set! r 1) '(break)))
                  r))))
  ;; every?: (every? pred vec)
  (setf (gethash "every?" *macros*)
        (lambda (form)
          (let ((v (gsym "v")) (r (gsym "r")) (i (gsym "i")))
            (list 'do (list 'let v (third form)) (list 'let-mut r 1)
                  (list 'for (list i 0 (list 'len v))
                        (list 'when (list 'not (list (second form) (list 'vector-ref v i)))
                              (list 'set! r 0) '(break)))
                  r))))
  (setf (gethash "not-any?" *macros*) (lambda (f) (list 'not (list 'some (second f) (third f)))))
  (setf (gethash "not-every?" *macros*) (lambda (f) (list 'not (list 'every? (second f) (third f)))))

  ;; === Selection macros (using vec-collect-macro helper) ===
  ;; remove: like filter but inverted predicate
  (setf (gethash "remove" *macros*)
        (lambda (form)
          (let ((pred (second form)))
            (vec-collect-macro (third form)
              (lambda (r v i)
                (let ((e (gsym "e")))
                  (list (list 'let e (list 'vector-ref v i))
                        (list 'when (list 'not (list pred e))
                              (list 'vector-push! r e)))))))))
  ;; take: (take n vec)
  (setf (gethash "take" *macros*)
        (lambda (form)
          (let* ((n (second form)) (vec (third form))
                 (tv (gsym "v")) (result (gsym "r")) (idx (gsym "i"))
                 (lim (gsym "l")))
            (list 'do (list 'let tv vec) (list 'let-mut result (list '|Vector|))
                  (list 'let lim (list 'if (list '< n (list 'len tv)) n (list 'len tv)))
                  (list 'for (list idx 0 lim) (list 'vector-push! result (list 'vector-ref tv idx)))
                  result))))
  ;; drop: (drop n vec)
  (setf (gethash "drop" *macros*)
        (lambda (form)
          (let* ((n (second form)) (dv (gsym "v")) (result (gsym "r")) (idx (gsym "i")))
            (list 'do (list 'let dv (third form)) (list 'let-mut result (list '|Vector|))
                  (list 'for (list idx n (list 'len dv))
                        (list 'vector-push! result (list 'vector-ref dv idx)))
                  result))))
  ;; take-while: (take-while pred vec)
  (setf (gethash "take-while" *macros*)
        (lambda (form)
          (let ((pred (second form)))
            (vec-collect-macro (third form)
              (lambda (r v i)
                (let ((e (gsym "e")))
                  (list (list 'let e (list 'vector-ref v i))
                        (list 'when (list 'not (list pred e)) '(break))
                        (list 'vector-push! r e))))))))
  ;; drop-while: (drop-while pred vec)
  (setf (gethash "drop-while" *macros*)
        (lambda (form)
          (let* ((pred (second form)) (v (gsym "v")) (r (gsym "r")) (i (gsym "i")) (d (gsym "d")))
            (list 'do (list 'let v (third form)) (list 'let-mut r (list '|Vector|)) (list 'let-mut d 1)
                  (list 'for (list i 0 (list 'len v))
                        (list 'when (list 'and d (list 'not (list pred (list 'vector-ref v i))))
                              (list 'set! d 0))
                        (list 'when (list 'not d) (list 'vector-push! r (list 'vector-ref v i))))
                  r))))

  ;; === Construction macros ===
  ;; range: (range n) or (range start end)
  (setf (gethash "range" *macros*)
        (lambda (form)
          (let ((r (gsym "r")) (i (gsym "i"))
                (start (if (= (length form) 2) 0 (second form)))
                (end (if (= (length form) 2) (second form) (third form))))
            (list 'do (list 'let-mut r (list '|Vector|))
                  (list 'for (list i start end) (list 'vector-push! r i)) r))))
  ;; repeat: (repeat n val)
  (setf (gethash "repeat" *macros*)
        (lambda (form)
          (let ((r (gsym "r")) (i (gsym "i")))
            (list 'do (list 'let-mut r (list '|Vector|))
                  (list 'for (list i 0 (second form)) (list 'vector-push! r (third form))) r))))
  ;; reverse: (reverse vec)
  (setf (gethash "reverse" *macros*)
        (lambda (form)
          (let ((v (gsym "v")) (r (gsym "r")) (i (gsym "i")) (n (gsym "n")))
            (list 'do (list 'let v (second form)) (list 'let-mut r (list '|Vector|))
                  (list 'let n (list 'len v))
                  (list 'for (list i 0 n)
                        (list 'vector-push! r (list 'vector-ref v (list '- (list '- n 1) i))))
                  r))))
  ;; concat: (concat v1 v2)
  (setf (gethash "concat" *macros*)
        (lambda (form)
          (let ((a (gsym "a")) (b (gsym "b")) (r (gsym "r")) (i (gsym "i")))
            (list 'do (list 'let a (second form)) (list 'let b (third form))
                  (list 'let-mut r (list '|Vector|))
                  (list 'for (list i 0 (list 'len a)) (list 'vector-push! r (list 'vector-ref a i)))
                  (list 'for (list i 0 (list 'len b)) (list 'vector-push! r (list 'vector-ref b i)))
                  r))))

  ;; === Access macros ===
  ;; first: (first vec) => (vector-ref vec 0)
  (setf (gethash "first" *macros*)
        (lambda (form) (list 'vector-ref (second form) 0)))
  (setf (gethash "last" *macros*)
        (lambda (form) (list 'vector-ref (second form) (list '- (list 'len (second form)) 1))))
  (setf (gethash "count" *macros*) (lambda (form) (list 'len (second form))))
  (setf (gethash "empty?" *macros*) (lambda (form) (list '== (list 'len (second form)) 0)))

  ;; === Hash-map dependent collection macros ===
  ;; distinct: (distinct vec) — deduplicate using hash-map as seen set
  (setf (gethash "distinct" *macros*)
        (lambda (form)
          (let ((v (gsym "v")) (r (gsym "r")) (s (gsym "s")) (i (gsym "i")) (e (gsym "e")))
            (list 'do (list 'let v (second form))
                  (list 'let-mut r (list '|Vector| (list 'vector-ref v 0)))
                  (list 'let-mut s (list '|HashMap| (list 'vector-ref v 0) 1))
                  (list 'for (list i 1 (list 'len v))
                        (list 'let e (list 'vector-ref v i))
                        (list 'when (list 'not (list 'hash-has? s e))
                              (list 'hash-set! s e 1) (list 'vector-push! r e)))
                  r))))
  ;; frequencies: (frequencies vec) — count occurrences
  (setf (gethash "frequencies" *macros*)
        (lambda (form)
          (let ((v (gsym "v")) (m (gsym "m")) (i (gsym "i")) (e (gsym "e")))
            (list 'do (list 'let v (second form))
                  (list 'let-mut m (list '|HashMap| (list 'vector-ref v 0) 1))
                  (list 'for (list i 1 (list 'len v))
                        (list 'let e (list 'vector-ref v i))
                        (list 'if (list 'hash-has? m e)
                              (list 'hash-set! m e (list '+ (list 'hash-get m e) 1))
                              (list 'hash-set! m e 1)))
                  m)))))

  ;; partial: (partial f a b) => (lambda [x] (f a b x))
  ;; Captures the first N args, remaining arg passed at call time
  (setf (gethash "partial" *macros*)
        (lambda (form)
          (let* ((f (second form))
                 (bound-args (cddr form))
                 (x (intern (format nil "_pa~d" (incf *sysp-gensym-counter*)))))
            (list 'lambda (list x) (append (list f) bound-args (list x))))))

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
     (let ((head (symbol-name (first form))))
       (cond
         ((string-equal head "ptr") (make-ptr-type (parse-type-expr (second form))))
         ((string-equal head "fn") (make-fn-type (mapcar #'parse-type-expr (second form))
                                                  (parse-type-expr (third form))))
         ((string-equal head "cons") (make-cons-type (parse-type-expr (second form))
                                                      (parse-type-expr (third form))))
         ((string-equal head "array") (make-array-type (parse-type-expr (second form)) (third form)))
         ((string-equal head "Vector") (make-vector-type (parse-type-expr (second form))))
         ((string-equal head "HashMap") (make-hashmap-type (parse-type-expr (second form))
                                                            (parse-type-expr (third form))))
         ((string= head "list") (make-list-type (parse-type-expr (second form))))
         ((string= head "tuple") (make-tuple-type (mapcar #'parse-type-expr (rest form))))
         ((string= head "values") (make-values-type (mapcar #'parse-type-expr (rest form))))
         ((string= head "union") `(:union ,@(mapcar #'parse-type-expr (rest form))))
         ((string= head "struct") (make-struct-type (string (second form))))
         ((string= head "enum") `(:enum ,(string (second form))))
         ;; Check if head is a generic struct name: (:Pair :int :str) → (:generic "Pair" :int :str)
         ((gethash head *generic-structs*)
          `(:generic ,head ,@(mapcar #'parse-type-expr (rest form))))
         (t form))))
    ;; List with non-keyword head: (Vector :T), (HashMap :K :V) etc.
    ((and (listp form) (symbolp (first form)))
     (let ((head (symbol-name (first form))))
       (cond
         ((gethash head *generic-structs*)
          `(:generic ,head ,@(mapcar #'parse-type-expr (rest form))))
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
                    ("void" . :void) ("bool" . :bool) ("str" . (:ptr :char))
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
      ;; Volatile shorthand: :volatile-int, :volatile-ptr-int, etc.
      ((and (> (length name) 9) (string= (subseq name 0 9) "volatile-"))
       `(:volatile ,(parse-type-annotation
                     (intern (subseq (symbol-name sym) 9) :keyword))))
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

;; Primitive type → C type string mapping (shared by type-to-c)
(defparameter *type-to-c-table*
  '((:char . "char") (:short . "short") (:int . "int") (:long . "long") (:long-long . "long long")
    (:uchar . "unsigned char") (:ushort . "unsigned short") (:uint . "unsigned int")
    (:ulong . "unsigned long") (:ulong-long . "unsigned long long")
    (:i8 . "int8_t") (:i16 . "int16_t") (:i32 . "int32_t") (:i64 . "int64_t")
    (:u8 . "uint8_t") (:u16 . "uint16_t") (:u32 . "uint32_t") (:u64 . "uint64_t")
    (:float . "float") (:double . "double") (:f32 . "float") (:f64 . "double")
    (:size . "size_t") (:ptrdiff . "ptrdiff_t") (:intptr . "intptr_t") (:uintptr . "uintptr_t")
    (:bool . "int") (:void . "void")
    (:symbol . "Symbol") (:value . "Value") (:cons . "Value") (:nil . "Value")
    (:list . "Value") (:variadic . "Value")))

(defun type-to-c (tp)
  (let ((prim (cdr (assoc (type-kind tp) *type-to-c-table*))))
    (if prim prim
      (case (type-kind tp)
        (:ptr (format nil "~a*" (type-to-c (second tp))))
        (:struct (second tp))
        (:enum (second tp))
        (:array (type-to-c (second tp)))
        (:tuple (tuple-type-c-name tp))
        (:fn (fn-type-c-name tp))
        (:union (union-type-c-name tp))
        (:volatile (format nil "volatile ~a" (type-to-c (second tp))))
        (:rc (format nil "_RC_~a*" (type-to-c (rc-inner-type tp))))
        (:future (format nil "_spawn_~a*" (third tp)))
        (:values (values-type-c-name tp))
        (:generic (instantiate-generic-struct (second tp) (cddr tp)))
        (otherwise "int")))))

(defparameter *mangle-type-table*
  '((:int . "int") (:char . "char") (:short . "short") (:long . "long") (:long-long . "longlong")
    (:uchar . "uchar") (:ushort . "ushort") (:uint . "uint") (:ulong . "ulong") (:ulong-long . "ulonglong")
    (:i8 . "i8") (:i16 . "i16") (:i32 . "i32") (:i64 . "i64")
    (:u8 . "u8") (:u16 . "u16") (:u32 . "u32") (:u64 . "u64")
    (:size . "size") (:ptrdiff . "ptrdiff") (:intptr . "intptr") (:uintptr . "uintptr")
    (:float . "float") (:double . "double") (:f32 . "f32") (:f64 . "f64")
    (:bool . "bool") (:void . "void") (:symbol . "sym")
    (:value . "val") (:cons . "cons") (:nil . "nil")))

(defun mangle-type-name (tp)
  (let ((prim (cdr (assoc (type-kind tp) *mangle-type-table*))))
    (if prim prim
      (case (type-kind tp)
        (:ptr (if (eq (second tp) :char) "str"
                   (format nil "ptr_~a" (mangle-type-name (second tp)))))
        (:struct (second tp)) (:enum (second tp))
        (:array (format nil "arr_~a_~a" (mangle-type-name (second tp)) (third tp)))
        (:tuple (tuple-type-c-name tp)) (:fn (fn-type-c-name tp))
        (:list (format nil "list_~a" (mangle-type-name (second tp))))
        (:variadic (format nil "var_~a" (mangle-type-name (second tp))))
        (:values (values-type-c-name tp))
        (:union (format nil "Union_~{~a~^_~}" (mapcar #'mangle-type-name (cdr tp))))
        (:rc (format nil "rc_~a" (mangle-type-name (rc-inner-type tp))))
        (:future (format nil "future_~a" (mangle-type-name (second tp))))
        (:generic (format nil "~a~{_~a~}" (second tp) (mapcar #'mangle-type-name (cddr tp))))
        (otherwise (warn "mangle-type-name: unhandled type ~a" tp) "unknown")))))

(defun vector-type-c-name (tp)
  "Get C type name for a Vector type, ensuring the struct is instantiated.
   Works with both old (:vector elem) and new (:generic \"Vector\" elem) format."
  (let ((elem (if (vector-type-p tp) (vector-elem-type tp) (second tp))))
    (instantiate-generic-struct "Vector" (list elem))))

(defun hashmap-type-c-name (tp)
  "Get C type name for a HashMap type, ensuring the struct is instantiated.
   Works with both old (:hashmap k v) and new (:generic \"HashMap\" k v) format."
  (let ((key-type (if (hashmap-type-p tp) (hashmap-key-type tp) (second tp)))
        (val-type (if (hashmap-type-p tp) (hashmap-val-type tp) (third tp))))
    (instantiate-generic-struct "HashMap" (list key-type val-type))))

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

(defun values-type-c-name (tp)
  (let* ((elems (values-type-elems tp))
         (name (format nil "Vals_~{~a~^_~}" (mapcar #'mangle-type-name elems))))
    (ensure-values-struct name elems)
    name))

;;; === Generated Type Structs ===

(defun ensure-values-struct (name elem-types)
  "Generate C struct for multiple return values: typedef struct { T0 _0; T1 _1; ... } Vals_T0_T1;"
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    (let ((fields (loop for tp in elem-types
                        for i from 0
                        collect (format nil "  ~a _~d;" (type-to-c tp) i))))
      (push (format nil "typedef struct {~%~{~a~%~}} ~a;~%" fields name)
            *type-decls*))))

(defun instantiate-generic-struct (struct-name concrete-types)
  "Instantiate a generic struct with concrete types. Returns the mangled C name.
   E.g. (instantiate-generic-struct \"Pair\" '(:int :str)) → \"Pair_int_str\""
  (let* ((entry (gethash struct-name *generic-structs*))
         (type-params (first entry))
         (fields-raw (second entry))
         (mangled (format nil "~a~{_~a~}" struct-name (mapcar #'mangle-type-name concrete-types))))
    (unless (gethash mangled *generic-struct-instances*)
      (setf (gethash mangled *generic-struct-instances*) t)
      ;; Build substitution table: type-param-name → concrete-type
      (let ((subst-table (make-hash-table :test 'equal)))
        (loop for param in type-params
              for concrete in concrete-types
              do (setf (gethash (symbol-name param) subst-table) concrete))
        ;; Substitute type params in field definitions
        (let ((concrete-fields nil)
              (lst (copy-list fields-raw)))
          (loop while lst do
            (let* ((fname (pop lst))
                   (fname-str (string-downcase (string fname))))
              ;; Parse the type annotation from the remaining list
              (when (and lst (or (keywordp (first lst))
                                 (and (listp (first lst)) (keywordp (car (first lst))))))
                (let* ((type-form (pop lst))
                       (concrete-type (subst-type-params type-form subst-table)))
                  (push (cons fname-str concrete-type) concrete-fields)))))
          (setf concrete-fields (nreverse concrete-fields))
          ;; Register in *structs* with concrete field types
          (setf (gethash mangled *structs*) concrete-fields)
          ;; Emit C struct typedef
          (unless (gethash mangled *generated-types*)
            (setf (gethash mangled *generated-types*) t)
            (push (format nil "typedef struct ~a ~a;~%" mangled mangled) *struct-defs*)
            (push (format nil "struct ~a {~%~{  ~a ~a;~%~}};~%"
                          mangled
                          (loop for (fname . ftype) in concrete-fields
                                append (list (type-to-c ftype) (sanitize-name fname))))
                  *struct-defs*))
          ;; Auto-generate helpers for known collection types
          (generate-collection-helpers struct-name concrete-types mangled concrete-fields))))
    mangled))

(defun generate-collection-helpers (struct-name concrete-types mangled fields)
  "Auto-generate C helper functions for Vector and HashMap via runtime macros."
  (cond
    ((equal struct-name "Vector")
     (let* ((elem-type (first concrete-types))
            (c-elem (type-to-c elem-type))
            (mk (mangle-type-name elem-type))
            (guard (format nil "_vechelpers_~a" mk))
            (va-promote (if (member c-elem '("char" "unsigned char" "short" "float") :test #'string=)
                            (if (string= c-elem "float") "double" "int")
                            c-elem)))
       (unless (gethash guard *generated-types*)
         (setf (gethash guard *generated-types*) t)
         (pushnew "stdarg.h" *includes* :test #'string=)
         (pushnew "runtime/vector.h" *includes* :test #'string=)
         (push (format nil "SYSP_VECTOR_PUSH(~a, ~a, ~a)~%SYSP_VECTOR_MAKE(~a, ~a, ~a, ~a)~%"
                       mangled c-elem mk mangled c-elem va-promote mk)
               *functions*))))
    ((equal struct-name "HashMap")
     (let* ((key-type (first concrete-types))
            (val-type (second concrete-types))
            (ck (type-to-c key-type))
            (cv (type-to-c val-type))
            (mk (mangle-type-name key-type))
            (mv (mangle-type-name val-type))
            (is-str-key (str-type-p key-type))
            (vec-k-name (vector-type-c-name (make-vector-type key-type)))
            (vec-v-name (vector-type-c-name (make-vector-type val-type)))
            (push-k (format nil "sysp_vecpush_~a" mk))
            (push-v (format nil "sysp_vecpush_~a" mv))
            (key-eq (if is-str-key "strcmp(m->keys[h], key) == 0" "m->keys[h] == key"))
            (hash-expr (if is-str-key "_sysp_hash_str(key)"
                           (format nil "_sysp_hash_int(*(unsigned int*)&key)")))
            (rehash-expr (if is-str-key "_sysp_hash_str(ok[i])"
                             (format nil "_sysp_hash_int(*(unsigned int*)&ok[i])"))))
       (pushnew "runtime/hashmap.h" *includes* :test #'string=)
       (push (format nil "SYSP_HASHMAP_GROW(~a, ~a, ~a, ~a, ~a, ~a)
SYSP_HASHMAP_SET(~a, ~a, ~a, ~a, ~a, ~a, ~a)
SYSP_HASHMAP_GET(~a, ~a, ~a, ~a, ~a, ~a, ~a)
SYSP_HASHMAP_HAS(~a, ~a, ~a, ~a, ~a, ~a)
SYSP_HASHMAP_DEL(~a, ~a, ~a, ~a, ~a, ~a)
SYSP_HASHMAP_KEYS(~a, ~a, ~a, ~a, ~a)
SYSP_HASHMAP_VALS(~a, ~a, ~a, ~a, ~a)~%"
                     mk mv mangled ck cv rehash-expr
                     mk mv mangled ck cv hash-expr key-eq
                     mk mv mangled ck cv hash-expr key-eq
                     mk mv mangled ck hash-expr key-eq
                     mk mv mangled ck hash-expr key-eq
                     mk mv mangled vec-k-name push-k
                     mk mv mangled vec-v-name push-v)
             *functions*)))
    (t nil)))

(defun subst-type-params (type-form subst-table)
  "Substitute type parameters in a type form using a substitution table.
   Handles keyword types (:T → concrete) and compound types ((:ptr :T) → (:ptr concrete))."
  (cond
    ((keywordp type-form)
     (let ((replacement (gethash (symbol-name type-form) subst-table)))
       (if replacement replacement
           (parse-type-annotation type-form))))
    ((and (listp type-form) (keywordp (car type-form)))
     ;; Compound type — recursively substitute
     (let ((head (symbol-name (car type-form))))
       (cond
         ((string-equal head "ptr")
          (make-ptr-type (subst-type-params (second type-form) subst-table)))
         ((string-equal head "fn")
          (make-fn-type (mapcar (lambda (p) (subst-type-params p subst-table)) (second type-form))
                        (subst-type-params (third type-form) subst-table)))
         ((string-equal head "array")
          (make-array-type (subst-type-params (second type-form) subst-table) (third type-form)))
         ;; Check if head is a generic struct name
         ((gethash head *generic-structs*)
          (let ((concrete-args (mapcar (lambda (a) (subst-type-params a subst-table)) (cdr type-form))))
            `(:generic ,head ,@concrete-args)))
         (t (cons (car type-form) (mapcar (lambda (x) (subst-type-params x subst-table)) (cdr type-form)))))))
    (t type-form)))

;; ensure-vector-type removed — Vector is now a generic struct, instantiated via instantiate-generic-struct

(defun ensure-tuple-type (name elem-types)
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    (let ((fields (loop for tp in elem-types
                        for i from 0
                        collect (format nil "  ~a _~d;" (type-to-c tp) i))))
      (push (format nil "typedef struct {~%~{~a~%~}} ~a;~%" fields name)
            *type-decls*))))

;; ensure-hashmap-type removed — HashMap is now a generic struct, instantiated via instantiate-generic-struct
;; C helpers are generated by generate-collection-helpers called from instantiate-generic-struct

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

;; ensure-vector-helper removed — now generated by generate-collection-helpers

(defun wrap-as-union (code concrete-type union-type)
  "Generate C code to wrap a concrete value into a union type.
   e.g., (wrap-as-union \"42\" :int (:union :int :str)) → \"Union_int_str_from_int(42)\""
  (if (union-type-p union-type)
      (let ((union-name (ensure-union-type union-type))
            (mname (mangle-type-name concrete-type)))
        (format nil "~a_from_~a(~a)" union-name mname code))
      code))

;; ensure-vector-push-helper removed — now generated by generate-collection-helpers

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
  ;; Expand macros before checking statement-like-p (macros may expand to do/if/etc)
  (when (and (listp form) (symbolp (first form)))
    (multiple-value-bind (expanded was-expanded) (macroexpand-1-sysp form)
      (when was-expanded
        (return-from compile-expr (compile-expr (macroexpand-all expanded) env)))))
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
    ((stringp form) (values (format nil "~s" form) '(:ptr :char)))
    ((symbolp form)
     (let* ((raw-name (string form))
            (name (resolve-name raw-name)))
       (cond
         ((string-equal name "true") (values "1" :bool))
         ((string-equal name "false") (values "0" :bool))
         ((string-equal name "null") (values "NULL" (make-ptr-type :void)))
         (t (let ((tp (env-lookup env name)))
              (cond
                (tp (values (sanitize-name name) tp))
                ;; Dot syntax: a.b.c → (get (get a b) c) when not a module-qualified import
                ((and (string= name raw-name) (find #\. raw-name))
                 (let ((expanded (expand-dot-symbol form)))
                   (if expanded
                       (return-from compile-expr-inner (compile-expr expanded env))
                       ;; Bad dot expression, fall through to unknown
                       (values (sanitize-name name) :unknown))))
                ;; Check if it's an enum variant
                (t (let ((enum-info (lookup-enum-variant name)))
                     (if enum-info
                         (values (sanitize-name name)
                                 (make-enum-type (car enum-info)))
                         (values (sanitize-name name)
                                 :unknown))))))))))
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
    ("bit-and" . "&") ("bit-or" . "|") ("bit-xor" . "^") ("shl" . "<<") ("shr" . ">>")
    ("&" . "&") ("|" . "|") ("^" . "^") ("<<" . "<<") (">>" . ">>")))

(defparameter *logical-ops* '(("and" . "&&") ("or" . "||")))

(defparameter *expr-dispatch*
  '(("if" . compile-if-expr) ("do" . compile-do-expr) ("cond" . compile-cond-expr)
    ("get" . compile-get) ("Vector" . compile-vector)
    ("HashMap" . compile-hash-map)
    ("tuple" . compile-tuple) ("tuple-ref" . compile-tuple-ref)
    ("lambda" . compile-lambda)
    ("array-ref" . compile-array-ref) ("array-set!" . compile-array-set)
    ("make-array" . compile-make-array)
    ("set!" . compile-set-expr)
    ("addr-of" . compile-addr-of) ("deref" . compile-deref)
    ("cast" . compile-cast) ("sizeof" . compile-sizeof) ("sizeof-val" . compile-sizeof-val)
    ("runtype" . compile-runtype) ("as" . compile-as)
    ("cons" . compile-cons) ("car" . compile-car) ("cdr" . compile-cdr)
    ("nil?" . compile-nilp) ("list" . compile-list-expr)
    ("quote" . compile-quote) ("quasiquote" . compile-quasiquote)
    ("sym" . compile-sym-literal) ("sym-eq?" . compile-sym-eq)
    ("gensym" . compile-gensym-expr)
    ("not" . compile-not) ("bit-not" . compile-bit-not) ("~" . compile-bit-not)
    ("match" . compile-match-expr)
    ("new" . compile-new-expr)
    ("ptr-alloc" . compile-ptr-alloc)
    ("ptr-deref" . compile-ptr-deref)
    ("ptr-set!" . compile-ptr-set-expr)
    ("null?" . compile-null-check)
    ("spawn" . compile-spawn)
    ("await" . compile-await)
    ("restart-case" . compile-restart-case)
    ("handler-bind" . compile-handler-bind)
    ("signal" . compile-signal)
    ("invoke-restart" . compile-invoke-restart)
    ("c-expr" . compile-c-expr)
    ("c-tmpl" . compile-c-tmpl-expr)
    ("ptr+" . compile-ptr-add)
    ("ptr-to" . compile-ptr-to)
    ("str-concat" . compile-str-concat)
    ("str-slice" . compile-str-slice) ("str-upper" . compile-str-upper)
    ("str-lower" . compile-str-lower) ("str-split" . compile-str-split)
    ("str-from-int" . compile-str-from-int) ("str-from-float" . compile-str-from-float)
    ("str-join" . compile-str-join)
    ("str-trim" . compile-str-trim) ("str-replace" . compile-str-replace)
    ("fmt" . compile-fmt)
    ("nth" . compile-nth)
    ("asm!" . compile-asm-expr)
    ("values" . compile-values-expr)))

(defun compile-list (form env)
  (let* ((head (first form))
         (name (when (symbolp head) (symbol-name head))))
    (unless name (return-from compile-list (compile-call form env)))
    (let ((binop (cdr (assoc name *binop-ops* :test #'string-equal))))
      (when binop
        (return-from compile-list
          (cond
            ((and (string= binop "-") (= (length form) 2))
             (compile-unary-minus form env))
            ((and (> (length (rest form)) 2)
                  (member binop '("<" ">" "<=" ">=" "==" "!=") :test #'string=))
             (compile-chained-comparison binop form env))
            ((> (length (rest form)) 2)
             (compile-binop-variadic binop form env))
            (t (compile-binop binop form env))))))
    (let ((logical (cdr (assoc name *logical-ops* :test #'string-equal))))
      (when logical
        (return-from compile-list (compile-logical logical form env))))
    (let ((handler (cdr (assoc name *expr-dispatch* :test #'string-equal))))
      (when handler
        (return-from compile-list (funcall handler form env))))
    (cond
      ((sym= head "recur")
       (sysp-error form "recur must be in tail position (last expression of a function, or branch of if/cond in tail position)"))
      ((sym= head "return")
       (sysp-error form "return cannot be used as an expression"))
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
                ;; Bitwise operators: use arithmetic promotion (u8 & u8 → u8)
                ((member op '("&" "|" "^" "<<" ">>") :test #'string=)
                 (sysp-arithmetic-type lt rt))
                ;; Arithmetic operators: use C99 promotion rules
                (t (sysp-arithmetic-type lt rt)))))
        (values (format nil "(~a ~a ~a)" lhs op rhs) result-type)))))

(defun compile-binop-variadic (op form env)
  "(+ a b c ...) — fold left: ((a + b) + c) + ..."
  (let ((args (rest form)))
    (multiple-value-bind (acc acc-type) (compile-expr (first args) env)
      (dolist (arg (rest args))
        (multiple-value-bind (rhs rt) (compile-expr arg env)
          (setf acc-type
                (cond
                  ((member op '("<" ">" "<=" ">=" "==" "!=" "&&" "||") :test #'string=) :bool)
                  ((member op '("&" "|" "^" "<<" ">>") :test #'string=) (sysp-arithmetic-type acc-type rt))
                  (t (sysp-arithmetic-type acc-type rt))))
          (setf acc (format nil "(~a ~a ~a)" acc op rhs))))
      (values acc acc-type))))

(defun compile-chained-comparison (op form env)
  "(< a b c) → ((a < b) && (b < c)) with b evaluated once via temp"
  (let* ((args (rest form))
         (pairs nil))
    ;; Compile all args, use temps for middle ones to avoid double evaluation
    (let ((compiled-args
            (loop for arg in args
                  collect (multiple-value-bind (code tp) (compile-expr arg env)
                            (declare (ignore tp))
                            code))))
      ;; For middle args (not first, not last), lift to temp var
      (let ((safe-args
              (loop for (code . rest) on compiled-args
                    for i from 0
                    collect (if (and (> i 0) rest)  ; middle arg
                                (let ((tmp (fresh-tmp)))
                                  (push (format nil "  int ~a = ~a;" tmp code) *pending-stmts*)
                                  tmp)
                                code))))
        ;; Build chained pairs: (a < b) && (b < c) && ...
        (loop for (a b) on safe-args
              while b
              collect (format nil "(~a ~a ~a)" a op b) into chain
              finally (return (values (format nil "(~a)" (format nil "~{~a~^ && ~}" chain))
                                      :bool)))))))

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
             (:elif-cond (sysp-error f "elif without body before next elif")))
           (setf state :elif-cond current nil))
          ((and (symbolp f) (sym= f "else"))
           (case state
             (:then (setf then-forms (nreverse current)))
             (:elif-body (push (cons elif-cond (nreverse current)) elifs))
             (:elif-cond (sysp-error f "elif without body before else")))
           (setf state :else current nil))
          ((eq state :elif-cond)
           (setf elif-cond f state :elif-body current nil))
          (t (push f current))))
      (when (eq state :elif-cond)
        (sysp-error elif-cond "elif at end of if without condition/body"))
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
              (let ((result-type (cond
                                     ((type-equal-p then-type else-type) then-type)
                                     ;; Numeric types: promote instead of union
                                     ((and (numeric-type-p then-type) (numeric-type-p else-type))
                                      (sysp-arithmetic-type then-type else-type))
                                     (t (make-union-type (list then-type else-type))))))
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
  "(new StructName args...) -- RC-managed heap allocation or stack allocation (escape analysis).
   Returns (:rc (:struct Name)) for heap, (:struct Name) for stack."
  (let* ((struct-name (string (second form)))
         (args (cddr form))
         (inner-type (make-struct-type struct-name))
         (compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args))
         ;; Check escape analysis: if bound to a non-escaping let, stack-allocate
         (stack-p (and *current-fn-name* *current-let-target*
                       (escape-local-p *current-fn-name* *current-let-target*))))
    (if stack-p
        ;; Stack allocation: plain compound literal, struct type
        (values (format nil "(~a){~{~a~^, ~}}" struct-name compiled-args)
                inner-type)
        ;; Heap allocation: RC-managed
        (let* ((rc-type (make-rc-type inner-type))
               (rc-c-name (ensure-rc-type inner-type))
               (mname (mangle-type-name inner-type)))
          (declare (ignore rc-c-name))
          (values (format nil "_rc_~a_new((~a){~{~a~^, ~}})"
                          mname struct-name compiled-args)
                  rc-type)))))

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

(defun compile-ptr-set-expr (form env)
  "(ptr-set! p val) or (ptr-set! p i val) as expression — returns the assigned value."
  (let ((args (rest form)))
    (if (= (length args) 3)
        ;; (ptr-set! p i val) → (p[i] = val)
        (multiple-value-bind (p-code pt) (compile-expr (first args) env)
          (multiple-value-bind (i-code it) (compile-expr (second args) env)
            (declare (ignore it))
            (multiple-value-bind (v-code vt) (compile-expr (third args) env)
              (let* ((elem-type (when (and (consp pt) (eq (car pt) :ptr)) (second pt)))
                     (coerced (if elem-type (maybe-coerce v-code vt elem-type) v-code)))
                (values (format nil "(~a[~a] = ~a)" p-code i-code coerced)
                        (or elem-type vt))))))
        ;; (ptr-set! p val) → (*p = val)
        (multiple-value-bind (p-code pt) (compile-expr (first args) env)
          (multiple-value-bind (v-code vt) (compile-expr (second args) env)
            (let* ((elem-type (when (and (consp pt) (eq (car pt) :ptr)) (second pt)))
                   (coerced (if elem-type (maybe-coerce v-code vt elem-type) v-code)))
              (values (format nil "(*~a = ~a)" p-code coerced)
                      (or elem-type vt))))))))

(defun compile-ptr-set-stmt (form env)
  "(ptr-set! p val) → *p = val; or (ptr-set! p i val) → p[i] = val;"
  (let ((*pending-stmts* nil)
        (args (rest form)))
    (if (= (length args) 3)
        ;; (ptr-set! p i val)
        (multiple-value-bind (p-code pt) (compile-expr (first args) env)
          (multiple-value-bind (i-code it) (compile-expr (second args) env)
            (declare (ignore it))
            (multiple-value-bind (v-code vt) (compile-expr (third args) env)
              (let* ((elem-type (when (and (consp pt) (eq (car pt) :ptr)) (second pt)))
                     (coerced (if elem-type (maybe-coerce v-code vt elem-type) v-code)))
                (append *pending-stmts*
                        (list (format nil "  ~a[~a] = ~a;" p-code i-code coerced)))))))
        ;; (ptr-set! p val)
        (multiple-value-bind (p-code pt) (compile-expr (first args) env)
          (multiple-value-bind (v-code vt) (compile-expr (second args) env)
            (let* ((elem-type (when (and (consp pt) (eq (car pt) :ptr)) (second pt)))
                   (coerced (if elem-type (maybe-coerce v-code vt elem-type) v-code)))
              (append *pending-stmts*
                      (list (format nil "  *~a = ~a;" p-code coerced)))))))))

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
                  (let ((result-type (cond ((type-equal-p then-type rest-type) then-type)
                                           ((and (numeric-type-p then-type) (numeric-type-p rest-type))
                                            (sysp-arithmetic-type then-type rest-type))
                                           (t (make-union-type (list then-type rest-type))))))
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
                                           ((and (numeric-type-p a) (numeric-type-p b))
                                            (sysp-arithmetic-type a b))
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
            ;; Emit data releases for do-block scope, skipping the return variable
            ;; (it's been assigned to target and ownership transfers to caller)
            (let* ((return-cname (when (symbolp last-form)
                                   (sanitize-name (string last-form))))
                   (releases (if return-cname
                                 (remove-if (lambda (entry)
                                              (string= (car entry) return-cname))
                                            (env-data-releases new-env))
                                 (env-data-releases new-env)))
                   (release-stmts (mapcan
                                   (lambda (entry)
                                     (let ((c-name (car entry))
                                           (tp (cdr entry)))
                                       (emit-drop c-name tp)))
                                   releases)))
              (values type (append body-stmts last-stmts release-stmts))))))))

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
                         ((every #'numeric-type-p clause-types)
                          (reduce #'sysp-arithmetic-type clause-types))
                         (t (make-union-type clause-types)))))
      (values result-type result))))

(defun compile-let-stmt-returning (form env target)
  "(let name [type] init body...) -> let decl + body, last expr assigned to target"
  ;; Reuse compile-let-stmt for the binding, then compile-expr-returning for the body
  (let* ((let-stmts (compile-let-stmt form env))
         ;; Body forms: everything after (let name [type] init)
         (rest (cddr form))
         (rest (if (or (keywordp (first rest))
                       (and (listp (first rest)) (keywordp (car (first rest)))))
                   (cdr rest) rest))  ; skip type annotation
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
  "(get struct field) — auto-derefs through RC wrapper, pointer-to-struct, and generic structs"
  (multiple-value-bind (obj tp) (compile-expr (second form) env)
    (let* ((field-name (string (third form)))
           ;; For RC types, look up the inner struct
           (is-rc (rc-type-p tp))
           ;; For pointer-to-struct, auto-deref
           (is-ptr-struct (and (not is-rc)
                               (eq (type-kind tp) :ptr)
                               (consp (second tp))
                               (member (type-kind (second tp)) '(:struct :generic))))
           (struct-type (cond (is-rc (rc-inner-type tp))
                              (is-ptr-struct (second tp))
                              (t tp)))
           ;; Handle generic struct types (Vector/HashMap are now generic structs)
           (struct-name (cond
                          ((eq (type-kind struct-type) :struct) (second struct-type))
                          ((eq (type-kind struct-type) :generic)
                           ;; Instantiate and use mangled name
                           (instantiate-generic-struct (second struct-type) (cddr struct-type)))
                          (t nil)))
           (field-type (if (and struct-name (gethash struct-name *structs*))
                           (let ((fields (gethash struct-name *structs*)))
                             (cdr (assoc field-name fields :test #'equal)))
                           :int)))
      (cond
        (is-rc
         (values (format nil "~a->data.~a" obj (sanitize-name field-name))
                 (or field-type :int)))
        (is-ptr-struct
         (values (format nil "~a->~a" obj (sanitize-name field-name))
                 (or field-type :int)))
        (t
         (values (format nil "~a.~a" obj (sanitize-name field-name))
                 (or field-type :int)))))))

(defun compile-vector (form env)
  "(Vector elem ...) - stack compound literal if non-escaping, heap if escaping"
  (let* ((elems (rest form))
         (compiled (mapcar (lambda (e) (multiple-value-list (compile-expr e env))) elems))
         (elem-type (cond
                      (compiled (second (first compiled)))
                      ;; Empty vector: check inferred type of let target
                      ((and *current-fn-name* *current-let-target*
                            (let ((inferred (gethash (format nil "~a:~a" *current-fn-name* *current-let-target*)
                                                     *infer-locals*)))
                              (when (and inferred (vector-type-p inferred))
                                (vector-elem-type inferred)))))
                      (t :int)))
         (vec-type (make-vector-type elem-type))
         (c-name (type-to-c vec-type))
         (c-elem (type-to-c elem-type))
         (n (length elems))
         ;; Escape analysis: stack-allocate if bound to a non-escaping let
         (stack-p (and *current-fn-name* *current-let-target*
                       (escape-local-p *current-fn-name* *current-let-target*))))
    (if (= n 0)
        ;; Empty vector: zero-initialize (cap=0, NULL data)
        (values (format nil "(~a){NULL, 0, 0}" c-name) vec-type)
        (if stack-p
            ;; Non-escaping: C99 compound literal, cap=0 marks stack-allocated
            (values (format nil "(~a){(~a[]){~{~a~^, ~}}, ~d, 0}"
                            c-name c-elem (mapcar #'first compiled) n)
                    vec-type)
            ;; Escaping or unknown: heap-allocate via helper
            (let ((helper-name (format nil "sysp_mkvec_~a" (mangle-type-name elem-type))))
              ;; Helper is auto-generated by generate-collection-helpers
              ;; Just ensure the type is instantiated
              (vector-type-c-name vec-type)
              (values (format nil "~a(~d~{, ~a~})" helper-name n (mapcar #'first compiled))
                      vec-type))))))

(define-accessor vector-ref "~a.data[~a]"
  (if (vector-type-p tp)
      (vector-elem-type tp)
      :int))

;;; === Hash Map Operations ===

(defun compile-hash-map (form env)
  "(hash-map) or (hash-map k1 v1 k2 v2 ...)"
  (let ((args (rest form)))
    (if (null args)
        ;; Empty: infer from context or default to str->int
        (let* ((key-type '(:ptr :char)) (val-type :int)
               (hm-type (make-hashmap-type key-type val-type))
               (c-name (type-to-c hm-type)))
          (values (format nil "(~a){NULL, NULL, NULL, 0, 0}" c-name) hm-type))
        ;; Non-empty: compile k/v pairs, infer types from first pair
        (let* ((pairs (loop for (k v) on args by #'cddr
                            collect (list (multiple-value-list (compile-expr k env))
                                         (multiple-value-list (compile-expr v env)))))
               (key-type (second (first (first pairs))))
               (val-type (second (second (first pairs))))
               (hm-type (make-hashmap-type key-type val-type))
               (c-name (type-to-c hm-type))
               (mk (mangle-type-name key-type))
               (mv (mangle-type-name val-type))
               (tmp (fresh-tmp))
               (set-stmts nil))
          ;; Statement-lift: create map, then set all pairs
          ;; Build set stmts in forward order
          (dolist (pair pairs)
            (push (format nil "  _hm_set_~a_~a(&~a, ~a, ~a);" mk mv tmp
                          (first (first pair)) (first (second pair)))
                  set-stmts))
          ;; Push in reverse: set stmts first (so they end up after decl), decl last (so it appears first)
          (dolist (s set-stmts)
            (push s *pending-stmts*))
          (push (format nil "  ~a ~a = (~a){NULL, NULL, NULL, 0, 0};" c-name tmp c-name) *pending-stmts*)
          (values tmp hm-type)))))

;;; === String Builtins ===

(defun ensure-string-helpers ()
  "Include the string runtime header."
  (pushnew "runtime/string.h" *includes* :test #'string=))

;;; === Printable / Show Auto-Derivation ===

(defun type-to-show-format (tp)
  "Return printf format specifier for a primitive type, or nil for complex types needing show_X()."
  (if (str-type-p tp) "%s"
    (case (type-kind tp)
      (:char "%c")
      (:short "%hd")
      (:int "%d")
      (:long "%ld")
      (:long-long "%lld")
      (:uchar "%u")
      (:ushort "%hu")
      (:uint "%u")
      (:ulong "%lu")
      (:ulong-long "%llu")
      (:i8 "%\" PRId8 \"")
      (:i16 "%\" PRId16 \"")
      (:i32 "%\" PRId32 \"")
      (:i64 "%\" PRId64 \"")
      (:u8 "%\" PRIu8 \"")
      (:u16 "%\" PRIu16 \"")
      (:u32 "%\" PRIu32 \"")
      (:u64 "%\" PRIu64 \"")
      (:float "%g")
      (:f32 "%g")
      (:double "%g")
      (:f64 "%g")
      (:size "%zu")
      (:bool "%s")
      (otherwise nil))))

(defun ensure-show-helper (tp)
  "Ensure a show_TypeName C function exists for type TP. Auto-generates for primitives, structs, vectors, hashmaps."
  (let* ((mangled (mangle-type-name tp))
         (fn-name (format nil "show_~a" mangled))
         (guard-key (format nil "_show_~a" mangled)))
    (unless (gethash guard-key *generated-types*)
      (setf (gethash guard-key *generated-types*) t)
      (pushnew "runtime/show.h" *includes* :test #'string=)
      (let ((kind (type-kind tp)))
        (cond
          ;; Primitives handled by runtime/show.h (char, str/ptr-char, bool are static functions)
          ((or (member kind '(:char :bool)) (str-type-p tp)) nil) ; already in show.h
          ((member kind '(:int :long :long-long :short :uchar :ushort :uint :ulong :ulong-long :size))
           (push (format nil "SYSP_SHOW_SNPRINTF(~a, ~a, \"~a\")~%" fn-name (type-to-c tp) (type-to-show-format tp)) *functions*))
          ((member kind '(:float :double :f32 :f64))
           (push (format nil "SYSP_SHOW_SNPRINTF(~a, ~a, \"%g\")~%" fn-name (type-to-c tp)) *functions*))
          ((member kind '(:i8 :i16 :i32 :i64 :u8 :u16 :u32 :u64))
           (pushnew "inttypes.h" *includes* :test #'string=)
           (push (format nil "SYSP_SHOW_PRI(~a, ~a, ~a)~%" fn-name (type-to-c tp)
                         (case kind
                           (:i8 "\"%\" PRId8") (:i16 "\"%\" PRId16") (:i32 "\"%\" PRId32") (:i64 "\"%\" PRId64")
                           (:u8 "\"%\" PRIu8") (:u16 "\"%\" PRIu16") (:u32 "\"%\" PRIu32") (:u64 "\"%\" PRIu64")))
                 *functions*))

          ;; --- Struct show ---
          ((eq kind :struct)
           (let* ((struct-name (second tp))
                  (fields (gethash struct-name *structs*))
                  (c-struct (type-to-c tp))
                  (arg-parts nil) (complex-decls nil) (complex-frees nil) (fi 0))
             (unless fields (error "ensure-show-helper: unknown struct ~a" struct-name))
             (dolist (f fields)
               (unless (type-to-show-format (cdr f)) (ensure-show-helper (cdr f))))
             ;; Build format string and args in one pass
             (let ((fmt-str (with-output-to-string (s)
                              (write-string struct-name s) (write-char #\{ s)
                              (let ((i 0))
                                (dolist (f fields)
                                  (when (> i 0) (write-string ", " s))
                                  (write-string (car f) s) (write-string ": " s)
                                  (let* ((ftype (cdr f)) (prim-fmt (type-to-show-format ftype))
                                         (acc (format nil "self.~a" (sanitize-name (car f)))))
                                    (if prim-fmt
                                        (progn (write-string prim-fmt s)
                                               (push (if (eq (type-kind ftype) :bool)
                                                         (format nil "(~a ? \"true\" : \"false\")" acc) acc)
                                                     arg-parts))
                                        (let ((tmp (format nil "_f~d" fi)))
                                          (write-string "%s" s)
                                          (push (format nil "  const char* ~a = show_~a(~a);~%" tmp (mangle-type-name ftype) acc) complex-decls)
                                          (push tmp arg-parts)
                                          (push (format nil "  free((char*)~a);~%" tmp) complex-frees))))
                                  (incf i) (incf fi)))
                              (write-char #\} s)))
                   (args-str (format nil "~{~a~^, ~}" (nreverse arg-parts))))
               (push (format nil "static const char* ~a(~a self) {~%~{~a~}  int _len = snprintf(NULL, 0, \"~a\", ~a);~%  char* _buf = malloc(_len + 1);~%  snprintf(_buf, _len + 1, \"~a\", ~a);~%~{~a~}  return _buf;~%}~%"
                             fn-name c-struct (nreverse complex-decls)
                             fmt-str args-str fmt-str args-str (nreverse complex-frees))
                     *functions*))))

          ;; --- Generic struct (instantiated) --- handles Vector/HashMap show via macros
          ((eq kind :generic)
           (let* ((struct-name (second tp))
                  (type-args (cddr tp))
                  (mangled-struct (instantiate-generic-struct struct-name type-args))
                  (concrete-tp (make-struct-type mangled-struct)))
             (cond
               ((equal struct-name "Vector")
                (let ((elem-type (first type-args)))
                  (ensure-show-helper elem-type)
                  (pushnew "runtime/vector.h" *includes* :test #'string=)
                  (push (format nil "SYSP_VECTOR_SHOW(~a, show_~a, ~a)~%"
                                mangled-struct (mangle-type-name elem-type) fn-name)
                        *functions*)))
               ((equal struct-name "HashMap")
                (let ((key-type (first type-args))
                      (val-type (second type-args)))
                  (ensure-show-helper key-type)
                  (ensure-show-helper val-type)
                  (pushnew "runtime/hashmap.h" *includes* :test #'string=)
                  (push (format nil "SYSP_HASHMAP_SHOW(~a, show_~a, show_~a, ~a)~%"
                                mangled-struct (mangle-type-name key-type)
                                (mangle-type-name val-type) fn-name)
                        *functions*)))
               (t
                (ensure-show-helper concrete-tp)
                (unless (string= fn-name (format nil "show_~a" mangled-struct))
                  (push (format nil "static const char* ~a(~a self) { return show_~a(self); }~%"
                                fn-name (type-to-c tp) mangled-struct)
                        *functions*))))))

          (t (warn "ensure-show-helper: unhandled type ~a" tp)))))))  ;; cond+let+unless+let*+defun

(defun ensure-str-split-helper ()
  "Emit C helper for str-split. Returns Vector_str."
  (unless (gethash "_sysp_str_split" *generated-types*)
    (setf (gethash "_sysp_str_split" *generated-types*) t)
    (ensure-string-helpers)
    ;; Ensure Vector_str type exists
    (let* ((vec-type (make-vector-type '(:ptr :char)))
           (c-vec (type-to-c vec-type))  ;; triggers instantiate-generic-struct → generate-collection-helpers
           (push-name "sysp_vecpush_str"))
      ;; str-split: split on delimiter, return Vector_str
      (push (format nil "static ~a _sysp_str_split(const char* s, const char* delim) { ~a r = {NULL, 0, 0}; int dlen = strlen(delim); if (dlen == 0) { for (int i = 0; s[i]; i++) { char* c = malloc(2); c[0] = s[i]; c[1] = 0; ~a(&r, c); } return r; } const char* p = s; while (1) { const char* f = strstr(p, delim); if (!f) { int n = strlen(p); char* c = malloc(n + 1); memcpy(c, p, n + 1); ~a(&r, c); break; } int n = f - p; char* c = malloc(n + 1); memcpy(c, p, n); c[n] = 0; ~a(&r, c); p = f + dlen; } return r; }~%"
                    c-vec c-vec push-name push-name push-name)
            *functions*))))

;; Macro for defining simple string compile functions
(defmacro define-str-1 (name c-fmt ret-type &key alloc include)
  "Define a unary string function compiler: (name arg) -> c-fmt with ~a for arg."
  `(defun ,(intern (format nil "COMPILE-STR-~a" name)) (form env)
     ,@(when include `((pushnew ,include *includes* :test #'string=)))
     ,@(when (eq alloc :string) '((ensure-string-helpers)))
     (multiple-value-bind (a at) (compile-expr (second form) env)
       (declare (ignore at))
       (values ,(if (eq alloc :string)
                    `(lift-string-alloc (format nil ,c-fmt a))
                    `(format nil ,c-fmt a))
               ,ret-type))))

(defmacro define-str-2 (name c-fmt ret-type &key alloc include)
  "Define a binary string function compiler: (name a b) -> c-fmt with two ~a."
  `(defun ,(intern (format nil "COMPILE-STR-~a" name)) (form env)
     ,@(when include `((pushnew ,include *includes* :test #'string=)))
     ,@(when (eq alloc :string) '((ensure-string-helpers)))
     (multiple-value-bind (a at) (compile-expr (second form) env)
       (declare (ignore at))
       (multiple-value-bind (b bt) (compile-expr (third form) env)
         (declare (ignore bt))
         (values ,(if (eq alloc :string)
                      `(lift-string-alloc (format nil ,c-fmt a b))
                      `(format nil ,c-fmt a b))
                 ,ret-type)))))

(define-str-1 len "(int)strlen(~a)" :int :include "string.h")
(define-str-2 eq "(strcmp(~a, ~a) == 0)" :bool :include "string.h")
(define-str-2 contains "(strstr(~a, ~a) != NULL)" :bool :include "string.h")
(define-str-1 upper "_sysp_str_upper(~a)" '(:ptr :char) :alloc :string)
(define-str-1 lower "_sysp_str_lower(~a)" '(:ptr :char) :alloc :string)
(define-str-1 trim "_sysp_str_trim(~a)" '(:ptr :char) :alloc :string)
(define-str-1 from-int "_sysp_str_from_int(~a)" '(:ptr :char) :alloc :string)
(define-str-1 from-float "_sysp_str_from_float(~a)" '(:ptr :char) :alloc :string)
(define-str-2 concat "_sysp_str_concat(~a, ~a)" '(:ptr :char) :alloc :string)

(defun compile-str-ref (form env)
  (multiple-value-bind (s st) (compile-expr (second form) env)
    (declare (ignore st))
    (multiple-value-bind (i it) (compile-expr (third form) env)
      (declare (ignore it))
      (values (format nil "~a[~a]" s i) :char))))

(defun compile-str-find (form env)
  (pushnew "string.h" *includes* :test #'string=)
  (multiple-value-bind (s st) (compile-expr (second form) env)
    (declare (ignore st))
    (multiple-value-bind (sub subt) (compile-expr (third form) env)
      (declare (ignore subt))
      (let ((tmp (fresh-tmp))
            (ptr-tmp (fresh-tmp)))
        (push (format nil "  int ~a = ~a ? (int)(~a - ~a) : -1;" tmp ptr-tmp ptr-tmp s) *pending-stmts*)
        (push (format nil "  const char* ~a = strstr(~a, ~a);" ptr-tmp s sub) *pending-stmts*)
        (values tmp :int)))))

(defun lift-string-alloc (c-expr)
  "Statement-lift an allocating string expression to a temp variable.
   Appends to end of *pending-stmts* (not push) so inner allocations
   appear before outer ones that depend on them in the output.
   Registers the temp for deferred free (cleaned up at statement boundary).
   Returns the temp name."
  (let ((tmp (fresh-tmp)))
    (setf *pending-stmts* (append *pending-stmts*
                                  (list (format nil "  const char* ~a = ~a;" tmp c-expr))))
    (push tmp *pending-string-frees*)
    tmp))

(defun compile-str-slice (form env)
  (ensure-string-helpers)
  (multiple-value-bind (s st) (compile-expr (second form) env)
    (declare (ignore st))
    (multiple-value-bind (start start-t) (compile-expr (third form) env)
      (declare (ignore start-t))
      (multiple-value-bind (end end-t) (compile-expr (fourth form) env)
        (declare (ignore end-t))
        (values (lift-string-alloc (format nil "_sysp_str_slice(~a, ~a, ~a)" s start end)) '(:ptr :char))))))

(defun compile-str-split (form env)
  "(str-split s delim)"
  (ensure-str-split-helper)
  (multiple-value-bind (s st) (compile-expr (second form) env)
    (declare (ignore st))
    (multiple-value-bind (d dt) (compile-expr (third form) env)
      (declare (ignore dt))
      (values (format nil "_sysp_str_split(~a, ~a)" s d)
              (make-vector-type '(:ptr :char))))))


(defun compile-str-starts (form env)
  (pushnew "string.h" *includes* :test #'string=)
  (multiple-value-bind (s st) (compile-expr (second form) env)
    (declare (ignore st))
    (multiple-value-bind (pfx pt) (compile-expr (third form) env)
      (declare (ignore pt))
      (values (format nil "(strncmp(~a, ~a, strlen(~a)) == 0)" s pfx pfx) :bool))))

(defun compile-str-ends (form env)
  "(str-ends? s suffix)"
  (pushnew "string.h" *includes* :test #'string=)
  (multiple-value-bind (s st) (compile-expr (second form) env)
    (declare (ignore st))
    (multiple-value-bind (sfx pt) (compile-expr (third form) env)
      (declare (ignore pt))
      (let ((tmp-slen (fresh-tmp))
            (tmp-flen (fresh-tmp)))
        (push (format nil "  int ~a = strlen(~a);" tmp-flen sfx) *pending-stmts*)
        (push (format nil "  int ~a = strlen(~a);" tmp-slen s) *pending-stmts*)
        (values (format nil "(~a >= ~a && strcmp(~a + ~a - ~a, ~a) == 0)"
                        tmp-slen tmp-flen s tmp-slen tmp-flen sfx) :bool)))))

;; str-replace has 3 args, can't use define-str-2
(defun compile-str-replace (form env)
  (ensure-string-helpers)
  (multiple-value-bind (s st) (compile-expr (second form) env)
    (declare (ignore st))
    (multiple-value-bind (old ot) (compile-expr (third form) env)
      (declare (ignore ot))
      (multiple-value-bind (new-s nt) (compile-expr (fourth form) env)
        (declare (ignore nt))
        (values (lift-string-alloc (format nil "_sysp_str_replace(~a, ~a, ~a)" s old new-s)) '(:ptr :char))))))

(defun compile-str-join (form env)
  "(str-join vec delim)"
  (ensure-string-helpers)
  (multiple-value-bind (v vt) (compile-expr (second form) env)
    (declare (ignore vt))
    (multiple-value-bind (d dt) (compile-expr (third form) env)
      (declare (ignore dt))
      (values (lift-string-alloc (format nil "_sysp_str_join(~a.data, ~a.len, ~a)" v v d)) '(:ptr :char)))))

(defun parse-fmt-string (fmt-str)
  "Parse a format string into segments. Returns list of (:lit \"text\") and (:expr \"code\").
   {expr} interpolates, {{ and }} are literal braces."
  (let ((segments nil)
        (i 0)
        (len (length fmt-str))
        (buf (make-string-output-stream)))
    (loop while (< i len) do
      (let ((c (char fmt-str i)))
        (cond
          ;; {{ → literal {
          ((and (char= c #\{) (< (1+ i) len) (char= (char fmt-str (1+ i)) #\{))
           (write-char #\{ buf)
           (incf i 2))
          ;; }} → literal }
          ((and (char= c #\}) (< (1+ i) len) (char= (char fmt-str (1+ i)) #\}))
           (write-char #\} buf)
           (incf i 2))
          ;; { → start of interpolation
          ((char= c #\{)
           ;; Flush literal buffer
           (let ((lit (get-output-stream-string buf)))
             (when (> (length lit) 0)
               (push (list :lit lit) segments)))
           ;; Find matching } (handle nested parens for expressions)
           (incf i)
           (let ((expr-buf (make-string-output-stream))
                 (depth 0))
             (loop while (and (< i len)
                              (not (and (char= (char fmt-str i) #\}) (= depth 0)))) do
               (let ((ec (char fmt-str i)))
                 (cond ((char= ec #\() (incf depth))
                       ((char= ec #\)) (decf depth)))
                 (write-char ec expr-buf)
                 (incf i)))
             (when (< i len) (incf i))  ; skip closing }
             (push (list :expr (get-output-stream-string expr-buf)) segments)))
          ;; Normal char
          (t (write-char c buf)
             (incf i)))))
    ;; Flush remaining literal
    (let ((lit (get-output-stream-string buf)))
      (when (> (length lit) 0)
        (push (list :lit lit) segments)))
    (nreverse segments)))

(defun compile-fmt (form env)
  "(fmt \"hello {name}, you are {age}\") → chain of str-concat with auto-conversion.
   {expr} interpolates: strings used directly, ints → str-from-int, floats → str-from-float."
  (ensure-string-helpers)
  (let* ((fmt-str (second form))
         (segments (parse-fmt-string fmt-str)))
    (if (null segments)
        ;; Empty format string
        (values "\"\"" '(:ptr :char))
        ;; Build chain of str-concat calls
        (let ((parts nil))
          ;; Compile each segment to a C expression
          (dolist (seg segments)
            (ecase (first seg)
              (:lit
               (push (format nil "~s" (second seg)) parts))
              (:expr
               (let* ((expr-str (second seg))
                      ;; Parse the expression string using sysp reader
                      (expr-form (with-input-from-string (s expr-str)
                                   (let ((*readtable* (copy-readtable nil)))
                                     (setf (readtable-case *readtable*) :preserve)
                                     (read s)))))
                 (multiple-value-bind (code tp) (compile-expr expr-form env)
                   ;; Auto-convert non-strings
                   (cond
                     ((str-type-p tp) (push code parts))
                     ((member tp '(:int :i8 :i16 :i32 :i64 :u8 :u16 :u32 :u64
                                   :char :short :long :long-long :size))
                      (push (lift-string-alloc (format nil "_sysp_str_from_int(~a)" code)) parts))
                     ((member tp '(:float :double :f32 :f64))
                      (push (lift-string-alloc (format nil "_sysp_str_from_float(~a)" code)) parts))
                     ((eq tp :bool)
                      (push (format nil "(~a ? \"true\" : \"false\")" code) parts))
                     (t (push code parts))))))))
          (setf parts (nreverse parts))
          (if (= (length parts) 1)
              ;; Single part — just return it
              (values (first parts) '(:ptr :char))
              ;; Multiple parts — chain str-concat, lifting each to a temp
              (let ((result (first parts)))
                (dolist (p (rest parts))
                  (setf result (lift-string-alloc
                                (format nil "_sysp_str_concat(~a, ~a)" result p))))
                (values result '(:ptr :char))))))))

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

(defun compile-values-expr (form env)
  "(values a b ...) — multiple return values as struct compound literal"
  (let* ((elems (rest form))
         (compiled (mapcar (lambda (e) (multiple-value-list (compile-expr e env))) elems))
         (elem-types (mapcar #'second compiled))
         (vals-type (make-values-type elem-types))
         (c-name (type-to-c vals-type)))
    (values (format nil "(~a){~{~a~^, ~}}"
                    c-name (mapcar #'first compiled))
            vals-type)))

(defun compile-let-values-stmt (form env)
  "(let-values [(x y) (f args...)] body...)
   Destructure a values-returning call into individual bindings."
  (let* ((bindings (second form))
         (names (mapcar #'string (first bindings)))
         (init-form (second bindings))
         (body-forms (cddr form))
         (*pending-stmts* nil)
         (*pending-string-frees* nil))
    (multiple-value-bind (init-code init-type) (compile-expr init-form env)
      (let* ((lifted-stmts *pending-stmts*)
             (elem-types (if (values-type-p init-type)
                             (values-type-elems init-type)
                             ;; Fallback: single value in first binding
                             (list init-type)))
             (tmp (fresh-tmp))
             (c-vals-type (type-to-c init-type))
             ;; Declare temp for the values struct
             (tmp-decl (format nil "  ~a ~a = ~a;" c-vals-type tmp init-code))
             ;; Destructure into individual vars
             (var-decls (loop for name in names
                              for tp in elem-types
                              for i from 0
                              collect (progn
                                        (env-bind env name tp)
                                        (format nil "  ~a ~a = ~a._~d;"
                                                (type-to-c tp)
                                                (sanitize-name name)
                                                tmp i))))
             ;; Compile body
             (body-stmts (when body-forms (compile-body body-forms env))))
        (append lifted-stmts
                (list tmp-decl)
                var-decls
                (or body-stmts nil))))))

(defun compile-nth (form env)
  "(nth coll idx) — generic indexing: dispatches on inferred type.
   (:vector T) -> coll.data[idx], (:tuple ...) -> coll._N (literal N),
   :str -> coll[idx], (:array T N) -> coll[idx]"
  (multiple-value-bind (coll coll-type) (compile-expr (second form) env)
    (let ((idx-form (third form)))
      (cond
       ((vector-type-p coll-type)
        (multiple-value-bind (idx-code it) (compile-expr idx-form env)
          (declare (ignore it))
          (values (format nil "~a.data[~a]" coll idx-code)
                  (vector-elem-type coll-type))))
       (t
       (case (type-kind coll-type)
        (:tuple
         ;; Tuple requires literal integer index
         (let* ((idx (if (numberp idx-form) idx-form
                         (error "nth on tuple requires literal index, got ~a" idx-form)))
                (elem-type (nth (1+ idx) coll-type)))
           (values (format nil "~a._~d" coll idx) (or elem-type :int))))
        (:array
         (multiple-value-bind (idx-code it) (compile-expr idx-form env)
           (declare (ignore it))
           (values (format nil "~a[~a]" coll idx-code) (second coll-type))))
        (:ptr
         ;; Pointer/C-array indexing (let-array registers as (:ptr T))
         (multiple-value-bind (idx-code it) (compile-expr idx-form env)
           (declare (ignore it))
           (values (format nil "~a[~a]" coll idx-code) (second coll-type))))
        (otherwise
         ;; Fallback: treat as vector-ref for backward compat
         (multiple-value-bind (idx-code it) (compile-expr idx-form env)
           (declare (ignore it))
           (values (format nil "~a.data[~a]" coll idx-code) :int)))))))))

(defun compile-array-literal (form env)
  "(array :type val1 val2 ...) — C compound literal: (type[]){val1, val2, ...}
   Returns (:ptr type)."
  (let* ((elem-type (if (listp (second form))
                        (parse-type-expr (second form))
                        (parse-type-annotation (second form))))
         (vals (cddr form))
         (compiled-vals (mapcar (lambda (v)
                                  (first (multiple-value-list (compile-expr v env))))
                                vals))
         (c-type (type-to-c elem-type)))
    (values (format nil "(~a[]){~{~a~^, ~}}" c-type compiled-vals)
            (make-ptr-type elem-type))))

(defun compile-array-ref (form env)
  "(array-ref arr idx...) — multi-index: arr[i], arr[i][j], arr[i][j][k]"
  (multiple-value-bind (arr tp) (compile-expr (second form) env)
    (let* ((indices (cddr form))
           (compiled-indices (mapcar (lambda (idx)
                                      (multiple-value-bind (code it) (compile-expr idx env)
                                        (declare (ignore it))
                                        code))
                                    indices))
           (indexing (format nil "~{[~a]~}" compiled-indices))
           (elem-type (if (eq (type-kind tp) :array) (second tp) :int)))
      (values (format nil "~a~a" arr indexing) elem-type))))

(defun compile-array-set (form env)
  "(array-set! arr idx... val) — multi-index: arr[i] = v, arr[i][j] = v"
  (multiple-value-bind (arr at) (compile-expr (second form) env)
    (let* ((rest-args (cddr form))
           ;; Last arg is the value, everything before is indices
           (indices (butlast rest-args))
           (val-form (car (last rest-args)))
           (compiled-indices (mapcar (lambda (idx)
                                      (multiple-value-bind (code it) (compile-expr idx env)
                                        (declare (ignore it))
                                        code))
                                    indices))
           (indexing (format nil "~{[~a]~}" compiled-indices)))
      (multiple-value-bind (val vt) (compile-expr val-form env)
        (declare (ignore vt))
        (let ((elem-type (if (eq (type-kind at) :array) (second at) :int)))
          (values (format nil "(~a~a = ~a)" arr indexing val) elem-type))))))

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
   Non-capturing lambdas get plain C signatures (C-interop friendly).
   Capturing lambdas get void* _ctx + env struct. Both produce Fn fat pointers."
  (let* ((params-raw (second form))
         (rest-forms (cddr form))
         (params (parse-params params-raw))
         (ret-annotation (when (type-annotation-form-p (first rest-forms))
                           (prog1 (parse-ret-annotation (first rest-forms))
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
           (uses-recur (form-uses-recur-p body-forms))
           (result-code nil)
           (result-type nil)
           (env-decl-stmt nil))
      (let ((*pending-stmts* nil)
            (*current-fn-params* params)
            (*current-fn-name* lambda-name))
        (multiple-value-bind (last-code last-type) (compile-expr last-form fn-env)
          (let* ((ret-type (or ret-annotation last-type))
                 (arg-types (mapcar #'second params))
                 (fn-type (make-fn-type arg-types ret-type))
                 (fn-c-type (fn-type-c-name fn-type))
                 (user-param-str (format nil "~{~a~^, ~}"
                                        (mapcar (lambda (p)
                                                  (format nil "~a ~a"
                                                          (type-to-c (second p))
                                                          (sanitize-name (first p))))
                                                params)))
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
                 (all-body (append env-stmts
                                   (if uses-recur
                                       (cons "  _recur_top: ;" body-stmts)
                                       body-stmts))))
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
            (if capturing-p
                ;; === Capturing lambda: void* _ctx as first param ===
                (let ((c-param-str (if (string= user-param-str "")
                                       "void* _ctx"
                                       (format nil "void* _ctx, ~a" user-param-str))))
                  ;; Forward decl
                  (push (format nil "static ~a ~a(~a);"
                                (type-to-c ret-type) lambda-name c-param-str)
                        *lambda-forward-decls*)
                  ;; Function body
                  (push (format nil "static ~a ~a(~a) {~%~{~a~%~}  return ~a;~%}~%"
                                (type-to-c ret-type) lambda-name c-param-str
                                (or all-body nil) last-code-fixed)
                        *functions*)
                  ;; Fn struct with env
                  (let ((env-var (format nil "_ctx_~d" *env-counter*)))
                    (setf env-decl-stmt
                          (format nil "  ~a ~a = {~{~a~^, ~}};"
                                  env-struct-name env-var
                                  (mapcar (lambda (cap) (sanitize-name (car cap))) captures)))
                    (setf result-code
                          (format nil "(~a){~a, &~a}" fn-c-type lambda-name env-var))))
                ;; === Non-capturing lambda: plain C signature + wrapper ===
                (let* ((plain-param-str (if (string= user-param-str "") "void" user-param-str))
                       (wrap-name (format nil "~a_wrap" lambda-name))
                       (wrap-param-str (if (string= user-param-str "")
                                           "void* _ctx"
                                           (format nil "void* _ctx, ~a" user-param-str)))
                       (call-args (format nil "~{~a~^, ~}"
                                          (mapcar (lambda (p) (sanitize-name (first p))) params))))
                  ;; Forward decls for both
                  (push (format nil "static ~a ~a(~a);"
                                (type-to-c ret-type) lambda-name plain-param-str)
                        *lambda-forward-decls*)
                  (push (format nil "static ~a ~a(~a);"
                                (type-to-c ret-type) wrap-name wrap-param-str)
                        *lambda-forward-decls*)
                  ;; Plain function body (no void* _ctx)
                  (push (format nil "static ~a ~a(~a) {~%~{~a~%~}  return ~a;~%}~%"
                                (type-to-c ret-type) lambda-name plain-param-str
                                (or all-body nil) last-code-fixed)
                        *functions*)
                  ;; Thin wrapper that ignores _ctx and forwards
                  (push (format nil "static ~a ~a(~a) {~%  return ~a(~a);~%}~%"
                                (type-to-c ret-type) wrap-name wrap-param-str
                                lambda-name call-args)
                        *functions*)
                  ;; Fn struct uses wrapper
                  (setf result-code
                        (format nil "(~a){~a, NULL}" fn-c-type wrap-name))
                  ;; Record raw name for C interop
                  (setf (gethash lambda-name *raw-lambda-names*) lambda-name)))
            (setf result-type fn-type))))
      ;; Now back in outer scope — push env decl to OUTER *pending-stmts*
      (when env-decl-stmt
        (push env-decl-stmt *pending-stmts*))
      (values result-code result-type lambda-name))))

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
      (sysp-error form "await: expected future type, got ~a" fut-type))
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
      ;; (set! (get struct field) val) -> struct.field = val (or ->data.field for RC, -> for ptr-to-struct)
      ((and (listp target) (sym= (first target) "get"))
       (multiple-value-bind (obj tp) (compile-expr (second target) env)
         (let* ((field (string (third target)))
                (is-rc (rc-type-p tp))
                (is-ptr-struct (and (not is-rc)
                                    (eq (type-kind tp) :ptr)
                                    (consp (second tp))
                                    (member (type-kind (second tp)) '(:struct :generic))))
                (accessor (cond (is-rc
                                 (format nil "~a->data.~a" obj (sanitize-name field)))
                                (is-ptr-struct
                                 (format nil "~a->~a" obj (sanitize-name field)))
                                (t
                                 (format nil "~a.~a" obj (sanitize-name field))))))
           (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
             (let* ((struct-type (cond (is-rc (rc-inner-type tp))
                                       (is-ptr-struct (second tp))
                                       (t tp)))
                    (struct-name (cond
                                  ((eq (type-kind struct-type) :struct) (second struct-type))
                                  ((eq (type-kind struct-type) :generic)
                                   (instantiate-generic-struct (second struct-type) (cddr struct-type)))
                                  (t nil)))
                    (field-type (when struct-name
                                  (cdr (assoc field (gethash struct-name *structs*) :test #'equal))))
                    (coerced (if field-type (maybe-coerce val-code val-type field-type) val-code)))
               (values (format nil "(~a = ~a)" accessor coerced)
                       (or field-type val-type)))))))
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
      ;; (set! (hash-get m k) val) -> hash-set!(m, k, val)
      ((and (listp target) (sym= (first target) "hash-get"))
       (compile-expr (list (intern "hash-set!") (second target) (third target) (third form)) env))
      ;; Dot syntax: (set! a.b val) → (set! (get a b) val)
      ((and (symbolp target) (find #\. (string target)))
       (let ((expanded (expand-dot-symbol target)))
         (if expanded
             (compile-set-expr (list (intern "SET!") expanded (third form)) env)
             (sysp-error form "invalid dot syntax in set! target: ~a" target))))
      ;; simple variable
      (t (let ((name (string target)))
           (when (and (env-lookup env name) (not (env-mutable-p env name)))
             (sysp-error form "cannot set! immutable variable '~a' (use let-mut for mutable bindings)" name))
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
  "(cast :type expr) or (cast (:ptr :type) expr)"
  (let ((target-type (if (listp (second form))
                         (parse-type-expr (second form))
                         (parse-type-annotation (second form)))))
    (multiple-value-bind (code tp) (compile-expr (third form) env)
      ;; Vector→ptr cast: extract .data
      (let ((src-code (if (and (vector-type-p (resolve-type tp))
                               (eq (type-kind target-type) :ptr))
                          (format nil "~a.data" code)
                          code)))
        (values (format nil "((~a)~a)" (type-to-c target-type) src-code) target-type)))))

(defun compile-sizeof (form env)
  "(sizeof :type) or (sizeof expr)"
  (declare (ignore env))
  (let ((arg (second form)))
    (if (keywordp arg)
        (values (format nil "sizeof(~a)" (type-to-c (parse-type-annotation arg)))
                :int)
        (values (format nil "sizeof(~a)" (sanitize-name (string arg)))
                :int))))

(defun compile-sizeof-val (form env)
  "(sizeof-val expr) — compile expr for type inference, emit sizeof(C_TYPE)"
  (multiple-value-bind (code tp) (compile-expr (second form) env)
    (declare (ignore code))
    (values (format nil "sizeof(%s)" (type-to-c tp)) :int)))

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
    (:ptr (if (str-type-p tp) (format nil "val_str(~a)" code)
               (format nil "val_int(~a)" code)))
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
  "Get the C name for a function, checking overrides first. Resolves qualified names."
  (let ((resolved (resolve-name fn-name)))
    (or (gethash resolved *name-overrides*)
        (sanitize-name resolved))))

(defun wrap-defn-as-fn (c-name fn-type)
  "Generate a static wrapper so a defn (no void* ctx) can be used as an Fn struct.
   Returns the Fn struct literal string. Deduplicates by c-name."
  (let* ((arg-types (fn-type-args fn-type))
         (ret-type (fn-type-ret fn-type))
         (fn-c-type (fn-type-c-name fn-type))
         (wrapper-name (gethash c-name *defn-wrappers*)))
    (unless wrapper-name
      (setf wrapper-name (format nil "_wrap_~a" c-name))
      (setf (gethash c-name *defn-wrappers*) wrapper-name)
      ;; Generate: static ret wrapper(void* _ctx, args...) { (void)_ctx; return name(args...); }
      (let* ((param-names (loop for i from 0 below (length arg-types)
                                collect (format nil "_a~d" i)))
             (c-params (format nil "void* _ctx~{, ~a ~a~}"
                               (mapcan (lambda (tp pn) (list (type-to-c tp) pn))
                                       arg-types param-names)))
             (call-args (format nil "~{~a~^, ~}" param-names))
             (body (if (eq ret-type :void)
                       (format nil "  (void)_ctx; ~a(~a);" c-name call-args)
                       (format nil "  (void)_ctx; return ~a(~a);" c-name call-args))))
        (push (format nil "static ~a ~a(~a);" (type-to-c ret-type) wrapper-name c-params)
              *lambda-forward-decls*)
        (push (format nil "static ~a ~a(~a) {~%~a~%}~%" (type-to-c ret-type) wrapper-name c-params body)
              *functions*)))
    (format nil "(~a){~a, NULL}" fn-c-type wrapper-name)))

(defun compile-call (form env)
  "Compile a function call, handling variadic and polymorphic functions."
  (let* ((raw-name (resolve-name (string (first form))))
         ;; Normalize: CL macros produce UPPERCASE symbols, sysp parser preserves case
         (fn-name (if (gethash raw-name *poly-fns*) raw-name
                      (let ((lower (string-downcase raw-name)))
                        (if (gethash lower *poly-fns*) lower raw-name))))
         (args (rest form)))
    ;; Check for polymorphic function — instantiate with concrete types
    (when (gethash fn-name *poly-fns*)
      (let* ((compiled-args-data (mapcar (lambda (a) (multiple-value-list (compile-expr a env))) args))
             (arg-codes (mapcar #'first compiled-args-data))
             (arg-types (mapcar #'second compiled-args-data))
             ;; Auto-wrap: if arg is a defn name with (:fn ...) type, wrap as Fn struct
             (wrapped-codes
              (mapcar (lambda (arg code tp)
                        (if (and (symbolp arg)
                                 (gethash (resolve-name (string arg)) *direct-fns*)
                                 (consp tp) (eq (car tp) :fn))
                            (wrap-defn-as-fn code tp)
                            code))
                      args arg-codes arg-types))
             (mangled (instantiate-poly-fn fn-name arg-types))
             ;; Look up the instantiated function's return type
             (inst-fn-type (env-lookup *global-env* mangled))
             (ret-type (if (and inst-fn-type (eq (type-kind inst-fn-type) :fn))
                           (fn-type-ret inst-fn-type)
                           (first arg-types))))  ; fallback for identity-like
        (return-from compile-call
          (values (format nil "~a(~{~a~^, ~})" mangled wrapped-codes) ret-type))))
    ;; Check for generic struct constructor (try original case and lowercase)
    (let ((gs-name (or (and (gethash fn-name *generic-structs*) fn-name)
                       (let ((lower (string-downcase fn-name)))
                         (and (gethash lower *generic-structs*) lower)))))
      (when gs-name
        (return-from compile-call
          (compile-generic-struct-construct gs-name args env))))
    ;; Check for trait method call (try original case and lowercase)
    (let ((tm-name (or (and (gethash fn-name *method-to-trait*) fn-name)
                       (let ((lower (string-downcase fn-name)))
                         (and (gethash lower *method-to-trait*) lower)))))
      (when tm-name
        (return-from compile-call
          (compile-trait-method-call tm-name args env))))
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
              (let ((compiled-args-with-types
                      (mapcar (lambda (a) (multiple-value-list (compile-expr a env))) args))
                    (is-fn-var (and (not (gethash fn-name *direct-fns*))
                                    fn-type
                                    (eq (type-kind fn-type) :fn))))
                ;; Auto-coerce args to match parameter types (e.g. int → size_t)
                ;; For extern calls: substitute raw lambda names for C interop
                (let ((is-extern (gethash fn-name *direct-fns*))
                      (compiled-args
                        (loop for (code tp) in compiled-args-with-types
                              for arg in args
                              for i from 0
                              collect
                              (let ((expected (when (and fn-arg-types (< i (length fn-arg-types)))
                                                (nth i fn-arg-types)))
                                    (raw-name (when (symbolp arg)
                                                (gethash (string arg) *raw-lambda-names*))))
                                ;; C interop: pass raw function name for non-capturing lambdas
                                (if (and raw-name (gethash fn-name *extern-fns*)
                                         expected (eq (type-kind tp) :fn))
                                    raw-name
                                    ;; Error: capturing lambda passed to extern C function
                                    (progn
                                      (when (and (gethash fn-name *extern-fns*)
                                                 (not raw-name)
                                                 (symbolp arg)
                                                 (eq (type-kind tp) :fn)
                                                 (not (gethash (resolve-name (string arg)) *direct-fns*)))
                                        (error "Cannot pass capturing closure '~a' to C function '~a'. ~
                                                Only non-capturing lambdas and defn functions are C-compatible."
                                               (string arg) fn-name))
                                      (if expected
                                          (maybe-coerce code tp expected)
                                          code)))))))
                  (if is-fn-var
                      ;; Call through Fn struct: f.fn(f.env, args...)
                      (let ((c-name (sanitize-name fn-name)))
                        (values (format nil "~a.fn(~a.env~{, ~a~})"
                                        c-name c-name compiled-args)
                                ret-type))
                      ;; Direct function call
                      (values (format nil "~a(~{~a~^, ~})" (c-fn-name fn-name) compiled-args)
                              ret-type)))))))))

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

(defun compile-generic-struct-construct (name args env)
  "Compile generic struct construction — infer type params from args, instantiate, emit literal."
  (let* ((entry (gethash name *generic-structs*))
         (type-params (first entry))
         (fields-raw (second entry))
         ;; Compile all args first to get their types
         (compiled-args-data (mapcar (lambda (a) (multiple-value-list (compile-expr a env))) args))
         (arg-codes (mapcar #'first compiled-args-data))
         (arg-types (mapcar #'second compiled-args-data))
         ;; Build substitution table by matching arg types to field type params
         (subst-table (make-hash-table :test 'equal))
         (field-idx 0))
    ;; Walk fields-raw to match type params to concrete arg types
    (let ((lst (copy-list fields-raw)))
      (loop while lst do
        (pop lst)  ; field name
        (when (and lst (or (keywordp (first lst))
                           (and (listp (first lst)) (keywordp (car (first lst))))))
          (let ((type-form (pop lst)))
            ;; If this type-form is a type parameter keyword, bind it
            (when (< field-idx (length arg-types))
              (bind-type-params type-form (nth field-idx arg-types) subst-table))
            (incf field-idx)))))
    ;; Compute concrete types for each type param
    (let* ((concrete-types (mapcar (lambda (tp)
                                     (or (gethash (symbol-name tp) subst-table) :int))
                                   type-params))
           (mangled (instantiate-generic-struct name concrete-types))
           (result-type `(:generic ,name ,@concrete-types)))
      ;; Check if named initialization (first arg is keyword)
      (if (and args (keywordp (first args)))
          ;; Named initialization — re-compile as we consumed args already
          ;; But we already have compiled data, just use positional from the keyword pairs
          (let ((inits nil)
                (remaining args)
                (code-idx 0))
            (loop while remaining do
              (let* ((field-kw (pop remaining))
                     (field-name (string-downcase (symbol-name field-kw)))
                     (_ (pop remaining)))
                (declare (ignore _))
                (push (format nil ".~a = ~a" (sanitize-name field-name) (nth code-idx arg-codes)) inits)
                (incf code-idx)))
            (values (format nil "(~a){~{~a~^, ~}}" mangled (nreverse inits)) result-type))
          ;; Positional initialization
          (values (format nil "(~a){~{~a~^, ~}}" mangled arg-codes) result-type)))))

(defun bind-type-params (type-form concrete-type subst-table)
  "Try to bind type parameters in type-form to concrete-type.
   E.g. if type-form is :T and concrete-type is :int, binds T→:int."
  (cond
    ((keywordp type-form)
     (let ((name (symbol-name type-form)))
       ;; Type params start with uppercase letter
       (when (and (> (length name) 0) (upper-case-p (char name 0))
                  (not (gethash name *primitive-type-map*)))
         (setf (gethash name subst-table) concrete-type))))
    ((and (listp type-form) (keywordp (car type-form)))
     ;; Compound type — recursively extract
     (let ((head (symbol-name (car type-form))))
       (cond
         ((string-equal head "ptr")
          (when (eq (type-kind concrete-type) :ptr)
            (bind-type-params (second type-form) (second concrete-type) subst-table)))
         ;; Could add more patterns here (fn, array, etc.)
         )))))

(defun compile-trait-method-call (method-name args env)
  "Compile a trait method call. Resolves concrete type of first arg, finds impl, monomorphizes."
  (let* ((trait-name (gethash method-name *method-to-trait*))
         ;; Compile first arg to get its concrete type
         (compiled-args-data (mapcar (lambda (a) (multiple-value-list (compile-expr a env))) args))
         (arg-codes (mapcar #'first compiled-args-data))
         (arg-types (mapcar #'second compiled-args-data))
         (self-type (first arg-types))
         ;; Determine the type name for impl lookup
         (type-name (cond
                      ((eq (type-kind self-type) :struct) (second self-type))
                      ((eq (type-kind self-type) :generic) (second self-type))
                      (t (mangle-type-name self-type))))
         (impl-key (format nil "~a:~a" trait-name type-name))
         (method-table (gethash impl-key *trait-impls*)))
    (unless method-table
      (error "No impl of trait ~a for type ~a (key: ~a)" trait-name type-name impl-key))
    (let ((defn-form (gethash method-name method-table)))
      (unless defn-form
        (error "Method ~a not found in impl ~a" method-name impl-key))
      ;; Monomorphize: if the impl is generic (e.g. for (Vector :T)),
      ;; we need to substitute concrete type params
      (let* ((mangled-name (trait-method-mangled-name method-name self-type))
             ;; Check if already instantiated
             (already (gethash mangled-name *mono-instances*)))
        (unless already
          (setf (gethash mangled-name *mono-instances*) t)
          ;; Build concrete defn by substituting type params in the template
          (let ((concrete-defn (subst-trait-defn defn-form mangled-name self-type)))
            ;; Run inference + compile
            (let ((saved-auto-poly (make-hash-table :test 'equal)))
              (maphash (lambda (k v) (setf (gethash k saved-auto-poly) v)) *auto-poly-fns*)
              (infer-defn concrete-defn)
              (setf *auto-poly-fns* saved-auto-poly))
            (compile-defn concrete-defn)))
        ;; Look up return type
        (let* ((inst-fn-type (env-lookup *global-env* mangled-name))
               (ret-type (if (and inst-fn-type (eq (type-kind inst-fn-type) :fn))
                             (fn-type-ret inst-fn-type)
                             :int)))
          (values (format nil "~a(~{~a~^, ~})" mangled-name arg-codes) ret-type))))))

(defun trait-method-mangled-name (method-name self-type)
  "Generate mangled name for a trait method instantiation."
  (format nil "~a_~a" (sanitize-name method-name) (mangle-type-name self-type)))

(defun subst-trait-defn (defn-form mangled-name self-type)
  "Create a concrete defn form from a trait impl template.
   Renames the function to mangled-name and substitutes type params."
  (let* ((params-raw (third defn-form))
         (rest-forms (cdddr defn-form))
         ;; Build type substitution from the self type
         ;; If self-type is (:generic \"Vector\" :int), and impl is for (Vector :T),
         ;; then :T → :int
         (subst-table (make-hash-table :test 'equal)))
    ;; Extract type params from the impl's type annotation in the first param
    ;; Walk params to find the self parameter's type annotation
    (when (and (listp params-raw) (>= (length params-raw) 2))
      (let ((lst (copy-list params-raw)))
        ;; First param name
        (pop lst)
        ;; Check if next is a compound type annotation (list)
        (when (and lst (listp (first lst)))
          (let* ((type-ann (first lst))
                 (ann-name (symbol-name (car type-ann))))
            ;; If it's a generic struct, extract type params
            (when (gethash ann-name *generic-structs*)
              (let ((entry (gethash ann-name *generic-structs*)))
                (when (and entry (eq (type-kind self-type) :generic))
                  (loop for tp in (first entry)
                        for ct in (cddr self-type)
                        do (setf (gethash (symbol-name tp) subst-table) ct)))))))))
    ;; Build new params with substituted types
    (let ((new-params (subst-type-in-params params-raw subst-table))
          (new-body (cdddr defn-form))
          ;; Extract return type annotation
          (ret-ann (when (and rest-forms (keywordp (first rest-forms)))
                     (first rest-forms)))
          (body-forms (if (and rest-forms (keywordp (first rest-forms)))
                          (cdr rest-forms)
                          rest-forms)))
      ;; Substitute type params in return annotation if present
      (let ((new-ret (when ret-ann
                       (let ((replacement (gethash (symbol-name ret-ann) subst-table)))
                         (if replacement
                             (let ((tokens (type-to-annotation-tokens replacement)))
                               (if (= (length tokens) 1) (first tokens) tokens))
                             ret-ann)))))
        `(,(intern "defn" :sysp)
          ,(intern mangled-name :sysp)
          ,new-params
          ,@(when new-ret (list new-ret))
          ,@body-forms)))))

(defun subst-type-in-params (params-raw subst-table)
  "Substitute type parameters in a parameter list.
   E.g. [v (Vector :T) i :int] with T→:int becomes [v (Vector :int) i :int]"
  (let ((result nil)
        (lst (copy-list params-raw)))
    (loop while lst do
      (let ((item (pop lst)))
        (cond
          ;; Compound type annotation (list like (Vector :T) or (:ptr :char))
          ((listp item)
           (push (subst-type-in-ann item subst-table) result))
          ;; Keyword type annotation
          ((keywordp item)
           (let ((replacement (gethash (symbol-name item) subst-table)))
             (if replacement
                 (let ((tokens (type-to-annotation-tokens replacement)))
                   (dolist (tok tokens) (push tok result)))
                 (push item result))))
          ;; Symbol (param name) — keep as-is
          (t (push item result)))))
    (nreverse result)))

(defun subst-type-in-ann (form subst-table)
  "Substitute type params in a compound type annotation form like (Vector :T)."
  (if (listp form)
      (mapcar (lambda (x) (subst-type-in-ann x subst-table)) form)
      (if (keywordp form)
          (let ((replacement (gethash (symbol-name form) subst-table)))
            (if replacement
                (let ((tokens (type-to-annotation-tokens replacement)))
                  (if (= (length tokens) 1) (first tokens) form))
                form))
          form)))

;;; === Statement Compilation ===

(defun compile-body (forms env)
  "Compile a sequence of body forms, return list of C statement strings"
  (let ((stmts nil))
    (dolist (form forms)
      (let ((new-stmts (compile-stmt form env)))
        (setf stmts (append stmts new-stmts))))
    stmts))

(defparameter *stmt-dispatch*
  '(("let" . compile-let-stmt) ("let-mut" . compile-let-stmt)
    ("let-array" . compile-let-array-stmt)
    ("print" . compile-print-stmt) ("println" . compile-println-stmt) ("printf" . compile-printf-stmt)
    ("if" . compile-if-stmt) ("when" . compile-when-stmt) ("unless" . compile-unless-stmt)
    ("while" . compile-while-stmt) ("for" . compile-for-stmt)
    ("set!" . compile-set-stmt) ("return" . compile-return-stmt) ("recur" . compile-recur-stmt)
    ("cond" . compile-cond-stmt) ("match" . compile-match-stmt)
    ("block" . compile-block-stmt) ("do" . compile-block-stmt)
    ("ptr-free" . compile-ptr-free-stmt) ("ptr-set!" . compile-ptr-set-stmt)
    ("c-stmt" . compile-c-stmt) ("c-tmpl" . compile-c-tmpl-stmt)
    ("do-while" . compile-do-while-stmt) ("switch" . compile-switch-stmt)
    ("kernel-launch" . compile-kernel-launch-stmt) ("asm!" . compile-asm-stmt)
    ("let-values" . compile-let-values-stmt)))

(defun compile-stmt (form env)
  "Compile a single form as a statement, return list of C statement strings"
  (when (and (listp form) (symbolp (first form)))
    (multiple-value-bind (expanded was-expanded) (macroexpand-1-sysp form)
      (when was-expanded
        (return-from compile-stmt (compile-stmt (macroexpand-all expanded) env)))))
  (when (and (listp form) (symbolp (first form)))
    (let* ((name (symbol-name (first form)))
           (handler (cdr (assoc name *stmt-dispatch* :test #'string-equal))))
      (when handler (return-from compile-stmt (funcall handler form env)))
      (cond
        ((string-equal name "break") (return-from compile-stmt (list "  break;")))
        ((string-equal name "continue") (return-from compile-stmt (list "  continue;")))
        ((string-equal name "pragma")
         (return-from compile-stmt (list (format nil "#pragma ~a" (second form)))))
        )))
  ;; Default: compile as expression statement
  (let ((*pending-stmts* nil) (*pending-string-frees* nil))
    (multiple-value-bind (code tp) (compile-expr form env)
      (declare (ignore tp))
      (let ((frees (mapcar (lambda (tmp) (format nil "  free((char*)~a);" tmp)) *pending-string-frees*)))
        (append *pending-stmts* (list (format nil "  ~a;" code)) frees)))))

(defun compile-let-stmt (form env)
  "(let name expr) or (let name :type expr) or (let name (make-array :type size))
   (let-mut name expr) for mutable bindings"
  (let* ((is-mut (sym= (first form) "let-mut"))
         (name (string (second form)))
         (rest (cddr form))
         (type-ann (cond
                    ((keywordp (first rest))
                     (prog1 (parse-type-annotation (first rest))
                       (setf rest (cdr rest))))
                    ((and (listp (first rest)) (keywordp (car (first rest))))
                     (prog1 (parse-type-expr (first rest))
                       (setf rest (cdr rest))))
                    (t nil)))
         (init-form (first rest)))
    (let ((*pending-stmts* nil)
          (*pending-string-frees* nil)
          (*current-let-target* name))
      (multiple-value-bind (init-code init-type) (compile-expr init-form env)
        ;; Track non-capturing lambda names for C interop
        (when (and (listp init-form)
                   (symbolp (first init-form))
                   (string-equal (string (first init-form)) "lambda"))
          (let ((raw (gethash (format nil "_lambda_~d" *lambda-counter*) *raw-lambda-names*)))
            (when raw (setf (gethash name *raw-lambda-names*) raw))))
        (let* ((lifted-stmts *pending-stmts*)
               (str-frees *pending-string-frees*)
               (final-type (or type-ann init-type))
               (c-name (sanitize-name name))
               ;; Check if escape analysis says this is stack-allocatable
               (stack-rc-p (and (rc-type-p final-type)
                                (listp init-form) (sym= (first init-form) "new")
                                *current-fn-name*
                                (escape-local-p *current-fn-name* name)))
               ;; Retain if storing borrowed ref or shared variable (not fresh allocs)
               (needs-retain (and *uses-value-type*
                                 (value-type-p final-type)
                                 (needs-retain-for-storage-p init-form env))))
          ;; Downgrade RC to struct type for stack alloc
          (when stack-rc-p
            (setf final-type (rc-inner-type final-type)))
          (env-bind env name final-type)
          (when is-mut (env-mark-mutable env name))
          ;; Track Value-typed locals for release at scope exit
          (when (and *uses-value-type* (value-type-p final-type))
            (env-add-release env c-name))
          ;; Track RC-typed locals for release at scope exit (skip stack-allocated)
          (when (and (rc-type-p final-type) (not stack-rc-p))
            (env-add-rc-release env c-name (rc-inner-type final-type)))
          ;; Track vector/hashmap locals for data release at scope exit
          ;; Three cases:
          ;;   EA says :local  → register (non-escaping allocation, we own it)
          ;;   EA says :escapes → skip (ownership transfers to caller)
          ;;   Not in EA (macro results, copies) → fall back to init-form:
          ;;     list init (constructor/call) → register (likely new allocation)
          ;;     symbol init (variable ref) → skip (shallow copy, borrow)
          (let* ((ea-key (when *current-fn-name*
                          (format nil "~a.~a" *current-fn-name* name)))
                 (ea-result (when ea-key (gethash ea-key *escape-info*)))
                 (should-release (or (eq ea-result :local)
                                     (and (null ea-result)
                                          (not (symbolp init-form))))))
            (when (and (vector-type-p final-type) should-release)
              (env-add-data-release env c-name final-type))
            (when (and (hashmap-type-p final-type) should-release)
              (env-add-data-release env c-name final-type))
            ;; For strings: only register for scope-exit free when the init
            ;; actually produced string allocations (tracked via *pending-string-frees*).
            ;; This avoids false positives on borrows like (vector-ref v i).
            (when (and (str-type-p final-type) str-frees
                       (or (eq ea-result :local) (null ea-result)))
              (env-add-data-release env c-name '(:ptr :char))))
          ;; Determine if this is an RC copy (variable → variable, needs retain)
          (let* ((rc-copy-p (and (rc-type-p final-type)
                                 (symbolp init-form)
                                 (not (null init-form))))
                 ;; Don't emit C const — sysp enforces mutability via let vs let-mut
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
            ;; Free intermediate string temps (not the one assigned to this let)
            ;; If this let is tracking the string for scope-exit cleanup, the outermost
            ;; temp (init-code) is aliased by c-name — don't free it.
            (let* ((str-free-stmts
                     (when str-frees
                       (let ((exclude (when (member (cons c-name '(:ptr :char)) (env-data-releases env) :test #'equal)
                                        init-code)))
                         (mapcan (lambda (tmp)
                                   (unless (and exclude (string= tmp exclude))
                                     (list (format nil "  free((char*)~a);" tmp))))
                                 str-frees)))))
              (append lifted-stmts decl str-free-stmts))))))))

(defparameter *printf-formats*
  '((:char . "%c") (:short . "%hd") (:int . "%d") (:long . "%ld") (:long-long . "%lld")
    (:uchar . "%u") (:ushort . "%hu") (:uint . "%u") (:ulong . "%lu") (:ulong-long . "%llu")
    (:float . "%f") (:f32 . "%f") (:double . "%f") (:f64 . "%f")
    (:size . "%zu") (:ptrdiff . "%td")))

(defparameter *pri-formats*
  '((:i8 . "PRId8") (:i16 . "PRId16") (:i32 . "PRId32") (:i64 . "PRId64")
    (:u8 . "PRIu8") (:u16 . "PRIu16") (:u32 . "PRIu32") (:u64 . "PRIu64")
    (:intptr . "PRIdPTR") (:uintptr . "PRIuPTR")))

(defun format-print-arg (val-code val-type)
  "Return format string and arg for a typed value."
  (let* ((kind (type-kind val-type))
         (fmt (cdr (assoc kind *printf-formats*)))
         (pri (cdr (assoc kind *pri-formats*))))
    (cond
      ((str-type-p val-type) (values "%s" val-code))
      (fmt (values fmt val-code))
      (pri (values :pri pri val-code))
      ((eq kind :bool) (values "%s" (format nil "(~a ? \"true\" : \"false\")" val-code)))
      ((member kind '(:value :cons)) (values :value-print val-code))
      ((member kind '(:struct :generic))
       (ensure-show-helper val-type)
       (values :show (format nil "show_~a(~a)" (mangle-type-name val-type) val-code)))
      (t (values "%d" val-code)))))

(defun compile-print-impl (form env newline-p)
  "Shared impl for print/println. Emits printf with optional \\n suffix."
  (let ((*pending-stmts* nil) (*pending-string-frees* nil)
        (nl (if newline-p "\\n" "")))
    (multiple-value-bind (val-code val-type) (compile-expr (second form) env)
      (multiple-value-bind (fmt arg) (format-print-arg val-code val-type)
        (let ((frees (mapcar (lambda (tmp) (format nil "  free((char*)~a);" tmp)) *pending-string-frees*)))
          (append *pending-stmts*
                  (cond
                    ((eq fmt :value-print)
                     (if newline-p
                         (list (format nil "  sysp_print_value(~a); printf(\"\\n\");" arg))
                         (list (format nil "  sysp_print_value(~a);" arg))))
                    ((eq fmt :show)
                     (let ((tmp (fresh-tmp)))
                       (list (format nil "  const char* ~a = ~a;" tmp arg)
                             (format nil "  printf(\"%s~a\", ~a);" nl tmp)
                             (format nil "  free((char*)~a);" tmp))))
                    ((eq fmt :pri)
                     (list (format nil "  printf(\"%\" ~a \"~a\", ~a);" arg nl val-code)))
                    (t (list (format nil "  printf(\"~a~a\", ~a);" fmt nl arg))))
                  frees))))))

(defun compile-print-stmt (form env) (compile-print-impl form env nil))
(defun compile-println-stmt (form env)
  (if (null (rest form)) (list "  printf(\"\\n\");") (compile-print-impl form env t)))

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

(defun compile-when-unless-impl (form env negate-p)
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let ((body-env (make-env :parent env))
          (result (list (format nil (if negate-p "  if (!(~a)) {" "  if (~a) {") cond-code))))
      (dolist (s (compile-body (cddr form) body-env))
        (push (format nil "  ~a" s) result))
      (push "  }" result)
      (nreverse result))))

(defun compile-when-stmt (form env) (compile-when-unless-impl form env nil))
(defun compile-unless-stmt (form env) (compile-when-unless-impl form env t))

(defun compile-while-stmt (form env)
  "(while cond body...)"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let ((body-env (make-env :parent env))
          (result (list (format nil "  while (~a) {" cond-code))))
      (dolist (s (compile-body (cddr form) body-env))
        (push (format nil "  ~a" s) result))
      ;; Release locals at end of each iteration
      (when *uses-value-type*
        (dolist (r (emit-releases body-env))
          (push (format nil "  ~a" r) result)))
      (dolist (r (emit-data-releases body-env))
        (push (format nil "  ~a" r) result))
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
          ;; Release locals at end of each iteration
          (when *uses-value-type*
            (dolist (r (emit-releases body-env))
              (push (format nil "  ~a" r) result)))
          (dolist (r (emit-data-releases body-env))
            (push (format nil "  ~a" r) result))
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
  (let ((*pending-stmts* nil)
        (*pending-string-frees* nil))
    (multiple-value-bind (code tp) (compile-set-expr form env)
      ;; Free intermediate string temps (not the one being assigned to the target)
      (let ((str-free-stmts (mapcar (lambda (tmp) (format nil "  free((char*)~a);" tmp))
                                    (if (and (str-type-p tp) *pending-string-frees*)
                                        (rest *pending-string-frees*)
                                        *pending-string-frees*))))
        (append *pending-stmts*
                (list (format nil "  ~a;" code))
                str-free-stmts)))))

(defun compile-return-stmt (form env)
  "(return expr) or (return)"
  (if (rest form)
      (let ((*pending-string-frees* nil))
        (multiple-value-bind (code tp) (compile-expr (second form) env)
          (declare (ignore tp))
          ;; Free intermediate string temps (not the returned value itself)
          (let ((str-free-stmts (mapcar (lambda (tmp) (format nil "  free((char*)~a);" tmp))
                                        (if (and (str-type-p tp) *pending-string-frees*)
                                            (rest *pending-string-frees*)
                                            *pending-string-frees*))))
            (append str-free-stmts (list (format nil "  return ~a;" code))))))
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
    ;; Struct destructuring: (StructName f1 f2 ...)
    ((and (listp pattern) (symbolp (first pattern))
          (not (keywordp (first pattern)))
          (gethash (string (first pattern)) *structs*))
     (let* ((struct-name (string (first pattern)))
            (field-defs (gethash struct-name *structs*))  ; ((name . type) ...)
            (pat-vars (rest pattern))
            (new-env (make-env :parent env))
            (bindings nil))
       ;; Bind each pattern variable to corresponding struct field
       (loop for field-def in field-defs
             for pat-var in pat-vars
             when (and (symbolp pat-var) (not (string= (string pat-var) "_")))
             do (let* ((field-name (car field-def))
                       (field-type (cdr field-def))
                       (var-name (string pat-var))
                       (c-var (sanitize-name var-name))
                       ;; For union scrutinee: access via .as_StructName.field
                       ;; For direct struct: access via .field
                       (access (if (union-type-p scrutinee-type)
                                   (format nil "~a.as_~a.~a"
                                           scrutinee struct-name (sanitize-name field-name))
                                   (format nil "~a.~a"
                                           scrutinee (sanitize-name field-name)))))
                  (push (format nil "  ~a ~a = ~a;"
                                (type-to-c field-type) c-var access)
                        bindings)
                  (env-bind new-env var-name field-type)))
       ;; If scrutinee is union → tag check; if struct → no check (always matches)
       (let ((cond-code (when (union-type-p scrutinee-type)
                          (let ((union-c-name (ensure-union-type scrutinee-type)))
                            (format nil "~a.tag == ~a_TAG_~a"
                                    scrutinee union-c-name
                                    (string-upcase struct-name))))))
         (values cond-code (nreverse bindings) new-env))))
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
                                               ((and (numeric-type-p a) (numeric-type-p b))
                                                (sysp-arithmetic-type a b))
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
    ;; Release locals at scope exit
    (when *uses-value-type*
      (dolist (r (emit-releases body-env))
        (push (format nil "  ~a" r) result)))
    (dolist (r (emit-data-releases body-env))
      (push (format nil "  ~a" r) result))
    (push "  }" result)
    (nreverse result)))

;;; === Top-Level Form Compilation ===

(defun parse-type-from-list (lst)
  "Parse a type annotation from LST, consuming tokens. Returns (type . remaining-lst).
   Handles multi-token types like :fn (:int :int) :int, (:list :int), (:variadic :int), (:cons T1 T2)."
  (let ((sym (pop lst)))
    (cond
      ;; Parenthesized type: (:ptr :void), (:fn (...) :ret), (Vector :T), etc.
      ((listp sym)
       (cons (parse-type-expr sym) lst))
      ;; Function type: :fn (arg-types...) :ret-type
      ((and (keywordp sym)
            (string-equal (symbol-name sym) "fn")
            lst
            (listp (first lst)))
       (let* ((arg-syms (pop lst))
              (ret-sym (pop lst))
              (arg-types (mapcar (lambda (s) (if (listp s) (parse-type-expr s) (parse-type-annotation s))) arg-syms))
              (ret-type (if (listp ret-sym) (parse-type-expr ret-sym) (parse-type-annotation ret-sym))))
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
      ;; Vector type: (:Vector elem-type)
      ((and (keywordp sym)
            (string= (symbol-name sym) "Vector")
            lst)
       (let* ((elem-sym (pop lst))
              (elem-type (if (listp elem-sym) (parse-type-expr elem-sym) (parse-type-annotation elem-sym))))
         (cons (make-vector-type elem-type) lst)))
      ;; HashMap type: (:HashMap key-type val-type)
      ((and (keywordp sym)
            (string= (symbol-name sym) "HashMap")
            lst (cdr lst))
       (let* ((key-sym (pop lst))
              (val-sym (pop lst))
              (key-type (if (listp key-sym) (parse-type-expr key-sym) (parse-type-annotation key-sym)))
              (val-type (if (listp val-sym) (parse-type-expr val-sym) (parse-type-annotation val-sym))))
         (cons (make-hashmap-type key-type val-type) lst)))
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
                  (type (cond
                          ;; Keyword type annotation: name :type ...
                          ((and lst (keywordp (first lst)))
                           (let ((result (parse-type-from-list lst)))
                             (setf lst (cdr result))
                             (car result)))
                          ;; Parenthesized type annotation: name (:ptr :void) ... or name (Vector :T) ...
                          ((and lst (listp (first lst)))
                           (parse-type-expr (pop lst)))
                          ;; No annotation — use inferred or default to :int
                          ((and inferred-arg-types
                                (< inf-idx (length inferred-arg-types)))
                           (nth inf-idx inferred-arg-types))
                          (t :int))))
             (if in-rest
                 (setf rest (list name :value))
                 (push (list name type) fixed)))
           (incf inf-idx)))))
    (values (nreverse fixed) rest)))

(defun params-all (fixed rest)
  "Combine fixed and rest params for type registration."
  (if rest (append fixed (list rest)) fixed))

(defun compile-struct (form)
  "(struct Name [field :type, ...]) or (struct \"attr\" Name [field :type, ...])
   Generic: (struct (Name :T ...) [field :type, ...]) — stores template, no C emission"
  (let* ((has-attr (stringp (second form)))
         (attr (when has-attr (second form)))
         (name-form (if has-attr (third form) (second form)))
         (fields-raw (if has-attr (fourth form) (third form))))
    ;; Check for generic struct: name-form is a list like (Pair :T :U)
    (if (and (listp name-form) (> (length name-form) 1))
        ;; Generic struct — store template, skip C emission
        (let ((name (string (first name-form)))
              (type-params (rest name-form)))
          (setf (gethash name *generic-structs*)
                (list type-params (if (listp fields-raw) fields-raw nil))))
        ;; Concrete struct — original behavior
        (let* ((name (string name-form))
               (already-registered (let ((v (gethash name *structs*)))
                                     (and v (not (eq v :infer-placeholder))))))
          (unless already-registered
            (setf (gethash name *structs*) :forward-declared)
            (push (format nil "typedef struct ~a ~a;~%" name name) *struct-defs*))
          (let* ((fields (multiple-value-bind (fixed rest) (parse-params fields-raw)
                           (declare (ignore rest))
                           fixed)))
            (setf (gethash name *structs*)
                  (mapcar (lambda (f) (cons (first f) (second f))) fields))
            (push (format nil "struct ~a~a {~%~{  ~a ~a;~%~}};~%"
                          (if attr (format nil "~a " attr) "")
                          name
                          (loop for f in fields
                                append (list (type-to-c (second f)) (sanitize-name (first f)))))
                  *struct-defs*))))))

(defun compile-deftrait (form)
  "(deftrait TraitName [:T ...]
     (method-name [params] :ret-type)
     ...)
   Registers the trait and its method signatures. No C emission."
  (let* ((name (string (second form)))
         (type-params (third form))
         (methods (cdddr form))
         (sigs nil))
    ;; Parse method signatures
    (dolist (m methods)
      (when (listp m)
        (let ((mname (string (first m)))
              (mparams (second m))
              (mret (when (and (cddr m) (keywordp (third m))) (third m))))
          (push (list mname mparams mret) sigs)
          ;; Register method → trait reverse lookup
          (setf (gethash mname *method-to-trait*) name))))
    (setf (gethash name *traits*)
          (list type-params (nreverse sigs)))))

(defun compile-impl (form)
  "(impl TraitName (TypeName :T ...)
     (defn method-name [self (TypeName :T ...) ...] :ret-type body...)
     ...)
   Stores method implementations as templates for monomorphization."
  (let* ((trait-name (string (second form)))
         (type-form (third form))
         ;; type-form is a symbol (Point), keyword (:str), or list (Vector :T)
         (type-name (cond
                      ((listp type-form) (string (first type-form)))
                      ((keywordp type-form) (string-downcase (symbol-name type-form)))
                      (t (string type-form))))
         (impl-key (format nil "~a:~a" trait-name type-name))
         (method-table (or (gethash impl-key *trait-impls*)
                           (make-hash-table :test 'equal)))
         (defn-forms (cdddr form)))
    (dolist (defn-form defn-forms)
      (when (and (listp defn-form) (sym= (first defn-form) "defn"))
        (let ((method-name (string (second defn-form))))
          (setf (gethash method-name method-table) defn-form))))
    (setf (gethash impl-key *trait-impls*) method-table)))

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
  "Check if any form in the tree contains a (recur ...) call.
   Stops at lambda/fn boundaries — recur inside a nested lambda
   belongs to that lambda, not the enclosing defn."
  (cond
    ((null forms) nil)
    ((symbolp forms) (sym= forms "recur"))
    ((listp forms)
     (let ((head (first forms)))
       (cond
         ((and (symbolp head) (sym= head "recur")) t)
         ;; Don't descend into nested function forms
         ((and (symbolp head)
               (or (sym= head "lambda") (sym= head "fn")))
          nil)
         (t (some #'form-uses-recur-p forms)))))
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

(defun type-annotation-form-p (form)
  "Check if FORM is a type annotation: a keyword or a list starting with a keyword
   (e.g., :int, (:values :int :int), (:ptr :int))."
  (or (keywordp form)
      (and (listp form) (keywordp (first form))
           ;; Distinguish from body forms: type lists have only keywords/symbols/numbers
           (every (lambda (x) (or (keywordp x) (numberp x) (listp x))) (rest form)))))

(defun parse-ret-annotation (form)
  "Parse a return type annotation, handling both keyword and list forms."
  (if (keywordp form)
      (parse-type-annotation form)
      (parse-type-expr form)))

(defun form-has-poly-marker-p (form)
  "Check if a type annotation form contains :? or :poly anywhere."
  (cond
    ((eq form :poly) t)
    ((and (keywordp form) (string-equal (symbol-name form) "?")) t)
    ((listp form) (some #'form-has-poly-marker-p form))
    (t nil)))

(defun defn-is-poly-p (form)
  "Check if a defn form has any :? type annotations (polymorphic)."
  (let ((params-raw (third form))
        (rest-forms (cdddr form)))
    (or ;; Check params for :?
        (and (listp params-raw)
             (some (lambda (x) (and (keywordp x) (string-equal (symbol-name x) "?")))
                   params-raw))
        ;; Check return type annotation for :? (keyword or list form)
        (and (first rest-forms)
             (type-annotation-form-p (first rest-forms))
             (form-has-poly-marker-p (first rest-forms))))))

(defun subst-poly-type (type-form concrete-arg-types)
  "Substitute :poly (resolved from :?) in a compound type with concrete types.
   Each :poly gets replaced with the next concrete type."
  (let ((idx 0))
    (labels ((subst-rec (form)
               (cond
                 ((eq form :poly)
                  (prog1 (or (nth idx concrete-arg-types) :int)
                    (incf idx)))
                 ((listp form)
                  (cons (car form) (mapcar #'subst-rec (cdr form))))
                 (t form))))
      (subst-rec type-form))))

(defun mangle-poly-name (base-name concrete-types)
  "Generate a mangled name for a monomorphized instance."
  (format nil "~a_~{~a~^_~}" (sanitize-name base-name)
          (mapcar #'mangle-type-name concrete-types)))

(defun type-to-annotation-tokens (tp)
  "Convert an internal type to annotation tokens for synthetic defn param lists.
   Simple types become a single keyword; compound types become multiple tokens."
  (cond
    ;; Compound fn type: (:fn (arg-types) ret) -> :fn (:arg1 :arg2) :ret
    ((and (consp tp) (eq (car tp) :fn))
     (let ((arg-types (fn-type-args tp))
           (ret-type (fn-type-ret tp)))
       (list (intern "FN" :keyword)
             (mapcar (lambda (at)
                       (let ((tokens (type-to-annotation-tokens at)))
                         (if (= (length tokens) 1) (first tokens) tokens)))
                     arg-types)
             (let ((ret-tokens (type-to-annotation-tokens ret-type)))
               (if (= (length ret-tokens) 1) (first ret-tokens) ret-tokens)))))
    ;; Generic types: (:generic "Vector" :int) -> (:Vector :int), etc.
    ((and (consp tp) (eq (car tp) :generic))
     (let* ((name (second tp))
            (params (cddr tp))
            (param-tokens (mapcan #'type-to-annotation-tokens params)))
       (list (cons (intern name :keyword) param-tokens))))
    ;; Pointer type: (:ptr :int) -> (:PTR-INT)
    ((and (consp tp) (eq (car tp) :ptr))
     (let ((inner-tokens (type-to-annotation-tokens (second tp))))
       (if (= (length inner-tokens) 1)
           ;; Simple pointee: (:ptr :int) -> :PTR-INT
           (list (intern (format nil "PTR-~a" (symbol-name (first inner-tokens))) :keyword))
           ;; Compound pointee: wrap as (:ptr inner...)
           (cons (intern "PTR" :keyword) inner-tokens))))
    ;; Struct type: (:struct "Color") -> (:Color) — preserve case
    ((and (consp tp) (eq (car tp) :struct))
     (list (intern (second tp) :keyword)))
    ;; Array type: (:array :int 9) -> treat as pointer (arrays decay to ptr)
    ((and (consp tp) (eq (car tp) :array))
     (type-to-annotation-tokens (make-ptr-type (second tp))))
    ;; Generic struct type: (:generic "Pair" :int :str) -> ((:Pair :INT :STR))
    ((and (consp tp) (eq (car tp) :generic))
     (let ((name-kw (intern (second tp) :keyword))
           (arg-tokens (mapcan #'type-to-annotation-tokens (cddr tp))))
       (list (cons name-kw arg-tokens))))
    ;; Simple type: :int -> (:INT)
    (t (list (intern (string-upcase (mangle-type-name tp)) :keyword)))))

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
               ;; Push annotation tokens for the concrete type (may be multiple for compound types)
               (let* ((concrete (nth type-idx concrete-arg-types))
                      (tokens (type-to-annotation-tokens concrete)))
                 (dolist (tok tokens)
                   (push tok new-params)))
               (incf type-idx))
              ;; Other type annotation — skip it for counting
              ((keywordp item)
               (incf type-idx))
              ;; Symbol (param name) — for auto-poly, insert concrete type annotation
              (t
               (when (and (gethash name *auto-poly-fns*)
                          (not (and lst (keywordp (first lst)))))
                 (let* ((concrete (nth type-idx concrete-arg-types))
                        (tokens (type-to-annotation-tokens concrete)))
                   (dolist (tok tokens)
                     (push tok new-params)))
                 (incf type-idx))))))
        (setf new-params (nreverse new-params))
        ;; Determine concrete return type
        (let* ((concrete-ret (cond
                               ((eq ret-ann :poly)
                                ;; Return :poly → omit annotation, let body type inference handle it
                                nil)
                               ;; Compound return with :? (e.g., (:values :? :?))
                               ((and (listp ret-ann) (form-has-poly-marker-p ret-ann))
                                (subst-poly-type ret-ann concrete-arg-types))
                               (t ret-ann)))
               ;; Convert return type to form for synthetic defn
               (ret-form (cond
                           ((null concrete-ret) nil)
                           ;; Compound types: pass as list for parse-type-expr
                           ((consp concrete-ret) concrete-ret)
                           ;; Simple types: keyword for parse-type-annotation
                           (t (intern (string-upcase (mangle-type-name concrete-ret)) :keyword))))
               ;; Build the synthetic defn form
               (synthetic-form `(,(intern "defn" :sysp)
                                 ,(intern mangled :sysp)
                                 ,new-params
                                 ,@(when ret-form (list ret-form))
                                 ,@body-forms)))
          ;; Run inference so compile-defn can resolve local types (e.g. empty Vector)
          ;; Save/restore auto-poly table since infer-defn may incorrectly mark mono fns
          (let ((saved-auto-poly (make-hash-table :test 'equal)))
            (maphash (lambda (k v) (setf (gethash k saved-auto-poly) v)) *auto-poly-fns*)
            (infer-defn synthetic-form)
            (setf *auto-poly-fns* saved-auto-poly))
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
  (when (or (defn-is-poly-p form)
            (gethash (string (second form)) *auto-poly-fns*))
    (let* ((name (string (second form)))
           (params-raw (third form))
           (rest-forms (cdddr form))
           (ret-ann (when (type-annotation-form-p (first rest-forms))
                      (prog1 (parse-ret-annotation (first rest-forms))
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
         (ret-annotation (when (type-annotation-form-p (first rest-forms))
                           (prog1 (parse-ret-annotation (first rest-forms))
                             (setf rest-forms (cdr rest-forms)))))
         (body-forms rest-forms)
         ;; Also register for compile-time use by macros
         (raw-body (let ((rb (cdddr form)))
                     (if (keywordp (first rb)) (cdr rb) rb)))
         (env (make-env :parent *global-env*)))
    ;; Track if we need to infer return type from body
    (let ((no-ret-annotation-p (and (null ret-annotation) (null inferred-ret-type))))
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
      ;; If no return annotation and last form is inherently void (when/for/while/unless),
      ;; force void return type
      (when (and no-ret-annotation-p
                 (listp last-form)
                 (symbolp (first last-form))
                 (member (string (first last-form)) '("when" "unless" "while" "for") :test #'string-equal))
        (setf ret-type :void)
        ;; Update global env
        (let* ((arg-types (mapcar #'second params))
               (fn-type (make-fn-type arg-types :void)))
          (env-bind *global-env* name fn-type)))
      ;; Handle void return or expression return
      (let (return-stmt)
        (if (eq (type-kind ret-type) :void)
            ;; Void: last form is just another statement, no return
            (progn
              (setf stmts (append stmts (compile-stmt last-form env)))
              (let ((releases (append (when *uses-value-type* (emit-releases env))
                                      (emit-rc-releases env)
                                      (emit-data-releases env))))
                (when releases
                  (setf return-stmt (format nil "~{~a~%~}" releases)))))
            ;; Non-void: last form is return value
            ;; If the last form is statement-like (if/cond/do/let) and uses recur,
            ;; use compile-expr-returning to handle branches that recur (goto)
            ;; vs branches that produce values (assign to temp).
            (cond
              ;; Return unlifting: statement-like, no Value/RC cleanup needed
              ;; Branches emit "return expr;" directly, no temp variable
              ((and (statement-like-p last-form) (not *uses-value-type*) (null (env-rc-releases env)) (null (env-data-releases env)))
               (multiple-value-bind (type ret-stmts)
                   (compile-expr-returning last-form env ":return")
                 ;; Infer return type from body when no annotation was given
                 (when (and no-ret-annotation-p type (not (eq type :unknown)))
                   (setf ret-type type))
                 (setf stmts (append stmts ret-stmts))))
              ;; Statement-like with Value/RC cleanup: need temp for releases before return
              ((statement-like-p last-form)
               (let* ((tmp (fresh-tmp))
                      (tmp-decl (format nil "  ~a ~a;" (type-to-c ret-type) tmp)))
                 (multiple-value-bind (type ret-stmts)
                     (compile-expr-returning last-form env tmp)
                   ;; Infer return type from body when no annotation was given
                   (when (and no-ret-annotation-p type (not (eq type :unknown)))
                     (setf ret-type type)
                     (setf tmp-decl (format nil "  ~a ~a;" (type-to-c ret-type) tmp)))
                   (setf stmts (append stmts (list tmp-decl) ret-stmts))
                   (let ((releases (append (when *uses-value-type* (emit-releases env))
                                           (emit-rc-releases env)
                                           (emit-data-releases env))))
                     (setf return-stmt
                           (if releases
                               (format nil "~{~a~%~}  return ~a;~%" releases tmp)
                               (format nil "  return ~a;~%" tmp)))))))
              ;; Normal: compile last form as expression
              (t
               (let ((*pending-stmts* nil))
                 (multiple-value-bind (last-code lt) (compile-expr last-form env)
                   ;; Infer return type from body when no annotation was given
                   (when (and no-ret-annotation-p lt (not (eq lt :unknown)))
                     (setf ret-type lt))
                   (when *pending-stmts*
                     (setf stmts (append stmts *pending-stmts*)))
                   (let* ((releases (append (when *uses-value-type* (emit-releases env))
                                            (emit-rc-releases env)
                                            (emit-data-releases env)))
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
          ;; Update global env if return type was inferred from body
          (when no-ret-annotation-p
            (let* ((arg-types (mapcar #'second params))
                   (fn-type (make-fn-type arg-types ret-type)))
              (env-bind *global-env* name fn-type)))
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
                  *forward-decls*)))))))))


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
    (setf (gethash name *direct-fns*) t)
    (setf (gethash name *extern-fns*) t)))

(defun compile-extern-var (form)
  "(extern-var name :type) — declare external C variable (no codegen, just type registration)"
  (let* ((name (string (second form)))
         (tp (parse-type-annotation (third form))))
    (env-bind *global-env* name tp)))

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

(defun parse-asm-operands (rest env)
  "Parse :in/:out operand lists from asm! extended form.
   Returns (values out-constraints in-constraints clobbers).
   Each constraint is (c-var constraint-str type)."
  (let ((outs nil) (ins nil) (clobbers nil)
        (items rest))
    (loop while items do
      (let ((key (pop items)))
        (cond
          ((and (keywordp key) (string-equal (string key) "OUT"))
           (let ((spec (pop items)))
             ;; spec is [name :type] or just a sysp var name
             (if (listp spec)
                 (let* ((name (string (first spec)))
                        (tp (if (keywordp (second spec))
                                (parse-type-annotation (second spec))
                                :int)))
                   (push (list name "=r" tp) outs))
                 (multiple-value-bind (code tp) (compile-expr spec env)
                   (push (list code "=r" tp) outs)))))
          ((and (keywordp key) (string-equal (string key) "IN"))
           (let ((spec (pop items)))
             ;; spec can be [var1 var2 ...] or single var
             (if (and (listp spec) (not (keywordp (first spec))))
                 (dolist (v spec)
                   (multiple-value-bind (code tp) (compile-expr v env)
                     (declare (ignore tp))
                     (push code ins)))
                 (multiple-value-bind (code tp) (compile-expr spec env)
                   (declare (ignore tp))
                   (push code ins)))))
          ((and (keywordp key) (string-equal (string key) "CLOBBER"))
           (let ((spec (pop items)))
             (if (listp spec)
                 (dolist (c spec) (push (string c) clobbers))
                 (push (string spec) clobbers)))))))
    (values (nreverse outs) (nreverse ins) (nreverse clobbers))))

(defun compile-asm-stmt (form env)
  "(asm! \"instruction\") — simple form
   (asm! \"pattern\" :out [result :int] :in [a b] :clobber [\"memory\"]) — extended form"
  (let* ((template (second form))
         (rest (cddr form)))
    (if (null rest)
        ;; Simple form: bare asm
        (list (format nil "  __asm__ volatile(~s);" template))
        ;; Extended form: GCC extended asm
        (multiple-value-bind (outs ins clobbers) (parse-asm-operands rest env)
          (let ((out-str (format nil "~{~s (~a)~^, ~}"
                                (loop for (var constraint tp) in outs
                                      collect constraint collect var)))
                (in-str (format nil "~{~s (~a)~^, ~}"
                               (loop for v in ins
                                     collect "r" collect v)))
                (clob-str (format nil "~{~s~^, ~}" clobbers)))
            (list (format nil "  __asm__ volatile(~s : ~a : ~a~a);"
                          template out-str in-str
                          (if clobbers (format nil " : ~a" clob-str) ""))))))))

(defun compile-asm-expr (form env)
  "(asm! \"pattern\" :out [result :type] :in [vars...]) — expression form, returns :out value"
  (let* ((template (second form))
         (rest (cddr form)))
    (if (null rest)
        (values (format nil "({__asm__ volatile(~s); 0;})" template) :void)
        (multiple-value-bind (outs ins clobbers) (parse-asm-operands rest env)
          (if (null outs)
              ;; No output: void
              (values (format nil "({__asm__ volatile(~s :: ~{~s (~a)~^, ~}~a); 0;})"
                              template
                              (loop for v in ins collect "r" collect v)
                              (if clobbers
                                  (format nil " : ~{~s~^, ~}" clobbers)
                                  ""))
                      :void)
              ;; Has output: return the first output value
              (let* ((out-var (first (first outs)))
                     (out-type (third (first outs)))
                     (tmp (fresh-tmp))
                     (out-str (format nil "~s (~a)"
                                      "=r" tmp))
                     (in-str (format nil "~{~s (~a)~^, ~}"
                                    (loop for v in ins collect "r" collect v)))
                     (clob-str (format nil "~{~s~^, ~}" clobbers)))
                (declare (ignore out-var))
                (push (format nil "  ~a ~a;" (type-to-c out-type) tmp) *pending-stmts*)
                (push (format nil "  __asm__ volatile(~s : ~a : ~a~a);"
                              template out-str in-str
                              (if clobbers (format nil " : ~a" clob-str) ""))
                      *pending-stmts*)
                (values tmp out-type)))))))

(defun compile-c-expr (form env)
  "(c-expr \"raw C\" :type) — raw C expression with type annotation."
  (declare (ignore env))
  (let ((code (second form))
        (tp (parse-type-annotation (third form))))
    (values code tp)))

(defun c-tmpl-interpolate (template compiled-args)
  "Replace each ~ in TEMPLATE with the next element of COMPILED-ARGS.
   Returns the interpolated C string."
  (let ((result (make-array 0 :element-type 'character :adjustable t :fill-pointer 0))
        (arg-idx 0))
    (loop for i from 0 below (length template)
          for c = (char template i)
          do (if (char= c #\~)
                 (progn
                   (when (>= arg-idx (length compiled-args))
                     (error "sysp: c-tmpl: more ~ placeholders than arguments"))
                   (loop for ch across (nth arg-idx compiled-args)
                         do (vector-push-extend ch result))
                   (incf arg-idx))
                 (vector-push-extend c result)))
    (coerce result 'string)))

(defun compile-c-tmpl-stmt (form env)
  "(c-tmpl \"pattern with ~ holes\" expr1 expr2 ...) — C statement with sysp interpolation."
  (let* ((template (second form))
         (args (cddr form))
         (compiled (mapcar (lambda (a)
                            (multiple-value-bind (code tp) (compile-expr a env)
                              (declare (ignore tp))
                              code))
                          args))
         (code (c-tmpl-interpolate template compiled)))
    (list (format nil "  ~a" code))))

(defun compile-c-tmpl-expr (form env)
  "(c-tmpl \"pattern\" :type expr1 expr2 ...) — C expression with sysp interpolation and type."
  (let* ((template (second form))
         (rest (cddr form))
         (tp (if (keywordp (first rest))
                 (prog1 (parse-type-annotation (first rest))
                   (setf rest (cdr rest)))
                 :int))
         (compiled (mapcar (lambda (a)
                            (multiple-value-bind (code atp) (compile-expr a env)
                              (declare (ignore atp))
                              code))
                          rest))
         (code (c-tmpl-interpolate template compiled)))
    (values code tp)))

(defun compile-let-array-stmt (form env)
  "(let-array name :type dim...) or (let-array \"qualifier\" name :type dim...)
   Declares a local C array, registers name in env as :ptr-type.
   Examples:
     (let-array tiles :float 16 16) → float tiles[16][16];
     (let-array \"__shared__\" As :float 16 16) → __shared__ float As[16][16];"
  (let* ((rest (cdr form))
         ;; Optional string qualifier
         (qualifier (when (stringp (first rest))
                      (prog1 (first rest)
                        (setf rest (cdr rest)))))
         (name (string (first rest)))
         (type-ann (parse-type-annotation (second rest)))
         (dims (cddr rest))
         (c-type (type-to-c type-ann))
         (c-name (sanitize-name name))
         (dim-str (format nil "~{[~a]~}" dims)))
    ;; Register in env as pointer to element type (for array-ref/set!)
    (env-bind env name (make-ptr-type type-ann))
    (list (format nil "  ~a~a ~a~a~a;"
                  (if qualifier (format nil "~a " qualifier) "")
                  c-type c-name dim-str
                  (if qualifier "" " = {0}")))))

(defun compile-enum (form)
  "(enum Name Variant1 Variant2 ...) or (enum Name [Variant1 0] [Variant2 1] ...)
   Bare symbols auto-number from 0. Brackets required only for explicit values."
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
               (sysp-error form "unknown function in macro expansion: ~a" fn-name)))))))

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

(defun compile-export (form)
  "(export name1 name2 ...) — mark names as public. When present, only listed names are exported."
  (unless *exports*
    (setf *exports* (make-hash-table :test 'equal)))
  (dolist (name (rest form))
    (setf (gethash (string name) *exports*) t)))

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
            ((sym= (first form) "export") (compile-export form))
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
                        (let ((sname (if (listp (second expanded))
                                         (string (first (second expanded)))
                                         (string (second expanded)))))
                          (push (cons sname c-comments) *struct-comments*)))
                       ((or (sym= (first expanded) "let")
                            (sym= (first expanded) "let-mut")
                            (sym= (first expanded) "const"))
                        (push (cons (string (second expanded)) c-comments) *var-comments*)))))
                 (cond
                   ((sym= (first expanded) "struct") (compile-struct expanded))
                   ((sym= (first expanded) "deftrait") (compile-deftrait expanded))
                   ((sym= (first expanded) "impl") (compile-impl expanded))
                   ((sym= (first expanded) "foreign-struct") (compile-foreign-struct expanded))
                   ((sym= (first expanded) "deftype") (compile-deftype expanded))
                   ((sym= (first expanded) "enum") (compile-enum expanded))
                   ((sym= (first expanded) "defn") (compile-defn expanded))
                   ((sym= (first expanded) "extern") (compile-extern expanded))
                   ((sym= (first expanded) "extern-var") (compile-extern-var expanded))
                   ((sym= (first expanded) "include") (compile-include expanded))
                   ((sym= (first expanded) "c-decl") (compile-c-decl expanded))
                   ((sym= (first expanded) "let") (compile-toplevel-let expanded nil))
                   ((sym= (first expanded) "let-mut") (compile-toplevel-let expanded t))
                   ((sym= (first expanded) "const") (compile-toplevel-let expanded nil)) ; legacy alias
                   (t (warn "Unknown top-level form: ~a" (first expanded))))))))))
      (incf form-idx))))

(defun emit-condition-preamble (out)
  "Emit the condition system runtime via #include."
  (format out "#include \"runtime/conditions.h\"~%~%"))

(defun emit-value-preamble (out)
  "Emit the Value/Cons/Symbol type system. Static parts via runtime/value.h,
   dynamic parts (symbol table, gensym counter, SYM_* defines) inline."
  ;; Gensym counter
  (format out "static SYSP_TLS uint32_t _sysp_gensym = 0x80000000;~%~%")
  ;; Symbol table (must come before #include so sysp_print_value can reference _sym_names)
  (let ((max-id *symbol-counter*))
    (format out "static const char* _sym_names[~d] = {~%" (1+ max-id))
    (format out "    \"\"")
    (loop for i from 1 to max-id do
      (let ((name nil))
        (maphash (lambda (n id) (when (= id i) (setf name n))) *symbol-table*)
        (format out ",~%    \"~a\"" (or name ""))))
    (format out "~%};~%~%"))
  ;; Static runtime (types, constructors, RC, print, list ops)
  (format out "#include \"runtime/value.h\"~%~%")
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
      (if (eql 0 (search "runtime/" inc))
          (format out "#include \"~a\"~%" inc)
          (format out "#include <~a>~%" inc)))
    (format out "~%")
    (format out "#include \"runtime/threads.h\"~%~%")
    ;; Hash functions now in runtime/hashmap.h (included via *includes* when needed)
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
  ;; Reset all hash tables
  (dolist (ht '(*structs* *enums* *generated-types* *symbol-table* *macro-fns*
                *type-aliases* *name-overrides* *poly-fns* *mono-instances* *auto-poly-fns*
                *included-files* *direct-fns* *defn-wrappers* *raw-lambda-names* *extern-fns*
                *escape-info* *sysp-modules* *imports*
                *generic-structs* *generic-struct-instances*
                *traits* *trait-impls* *method-to-trait*))
    (setf (symbol-value ht) (make-hash-table :test 'equal)))
  ;; Reset lists
  (dolist (var '(*functions* *struct-defs* *type-decls* *forward-decls* *top-level-vars*
                *lambda-forward-decls* *includes* *string-literals* *function-comments*
                *struct-comments* *var-comments* *exports* *pending-string-frees*))
    (setf (symbol-value var) nil))
  ;; Reset counters
  (setf *lambda-counter* 0 *temp-counter* 0 *symbol-counter* 0 *interp-gensym-counter* 0
        *env-counter* 0 *spawn-counter* 0 *restart-counter* 0 *handler-counter* 0
        *handler-wrap-counter* 0 *sysp-gensym-counter* #x80000000)
  ;; Reset flags
  (setf *uses-value-type* nil *uses-threads* nil *uses-conditions* nil)
  ;; Reset env
  (setf *global-env* (make-env))
  (register-builtin-poly-fns))

(defun register-builtin-poly-fns ()
  "Register built-in generic structs for Vector and HashMap.
   These are defined here so the compiler knows their structure
   before any library files are loaded."
  ;; Vector: (struct (Vector :T) [data (:ptr :T) len :int cap :int])
  (setf (gethash "Vector" *generic-structs*)
        (list '(:T) '(data (:ptr :T) len :int cap :int)))
  ;; HashMap: (struct (HashMap :K :V) [keys (:ptr :K) vals (:ptr :V) occ (:ptr :char) len :int cap :int])
  (setf (gethash "HashMap" *generic-structs*)
        (list '(:K :V) '(keys (:ptr :K) vals (:ptr :V) occ (:ptr :char) len :int cap :int))))

;;; === Escape Analysis ===

(defun escape-find-alloc-bindings (forms)
  "Find all let/let-mut bindings where init is a heap allocation:
   (new ...), (vector ...), (hash-map ...).
   Returns list of var-name strings."
  (let ((bindings nil))
    (labels ((alloc-form-p (init)
               "Check if init form is a known allocation (struct, vector, hashmap, or string)"
               (and (listp init) (symbolp (first init))
                    (let ((h (string-downcase (string (first init)))))
                      (or (string= h "new") (string= h "Vector") (string= h "HashMap")
                          (member h '("str-concat" "str-slice" "str-upper" "str-lower"
                                      "str-trim" "str-replace" "str-from-int" "str-from-float"
                                      "str-join")
                                  :test #'equal)))))
             (walk (form)
               (when (listp form)
                 (let ((head (first form)))
                   (cond
                     ;; let/let-mut with allocating initializer
                     ((and (or (sym= head "let") (sym= head "let-mut"))
                           (>= (length form) 3))
                      (let* ((name (string (second form)))
                             (rest (cddr form))
                             (init (if (keywordp (first rest)) (second rest) (first rest))))
                        (when (alloc-form-p init)
                          (push name bindings))
                        ;; Walk body forms
                        (dolist (f (if (keywordp (first rest)) (cddr rest) (cdr rest)))
                          (walk f))))
                     ;; Recurse into all subforms for compound statements
                     (t (dolist (f (rest form)) (walk f))))))))
      (dolist (f forms) (walk f)))
    bindings))

(defun escape-check-var (var-name forms)
  "Check if var-name escapes in forms. Conservative: escapes if returned, passed to a call, stored, or captured."
  (labels ((escapes-p (form context)
             ;; context: :expr (in expression), :stmt (in statement)
             (cond
               ((null form) nil)
               ((symbolp form) nil)  ; bare reference is fine
               ((not (listp form)) nil)
               (t
                (let ((head (first form)))
                  (cond
                    ;; Return: variable escapes
                    ((and (sym= head "return")
                          (some (lambda (f) (mentions-var-p f var-name)) (rest form)))
                     t)
                    ;; Function call: if var is an argument, it escapes (conservative)
                    ;; Safe: builtins, macros (expand inline, don't capture refs)
                    ((and (symbolp head)
                          (let ((h (string-downcase (string head))))
                            (and (not (member h
                                       '("let" "let-mut" "if" "do" "when" "unless" "while" "for"
                                         "set!" "get" "println" "printf" "print"
                                         "cond" "match" "+" "-" "*" "/" "%" "=" "!=" "<" ">" "<=" ">="
                                         "and" "or" "not" "cast" "addr-of" "sizeof" "deref"
                                         "array-ref" "array-set!" "vector-ref" "vector-set!"
                                         "vector-push!" "vector-free" "len" "sizeof-val"
                                         "hash-get" "hash-set!" "hash-has?" "hash-del!"
                                         "hash-keys" "hash-vals" "hash-free"
                                         "inc" "dec" "bit-and" "bit-or" "bit-xor" "bit-not"
                                         "bit-shl" "bit-shr" "&" "|" "^" "~" "<<" ">>" "new" "recur" "break" "continue"
                                         "block" "runtype" "as" "Vector" "HashMap"
                                         "str-concat" "str-slice" "str-upper" "str-lower"
                                         "str-split" "str-from-int" "str-from-float"
                                         "str-join" "str-trim" "str-replace"
                                         "nth" "asm!" "values" "let-values")
                                       :test #'equal))
                                 ;; Also safe: any known macro (expands inline)
                                 (not (gethash h *macros*))))
                          (some (lambda (arg) (var-escapes-through-arg-p arg var-name)) (rest form)))
                     t)
                    ;; set! to pointer/struct field — escapes
                    ((and (sym= head "set!")
                          (listp (second form))  ; compound target like (get x field)
                          (some (lambda (f) (mentions-var-p f var-name)) (cddr form)))
                     t)
                    ;; ptr-set! — escapes
                    ((and (sym= head "ptr-set!")
                          (some (lambda (f) (mentions-var-p f var-name)) (rest form)))
                     t)
                    ;; spawn/lambda — capture escapes
                    ((and (or (sym= head "spawn") (sym= head "lambda") (sym= head "fn"))
                          (mentions-var-p (rest form) var-name))
                     t)
                    ;; Recurse into subforms
                    (t (some (lambda (f) (escapes-p f :expr)) (rest form)))))))))
    (some (lambda (f) (escapes-p f :stmt)) forms)))

(defun mentions-var-p (form var-name)
  "Does form mention var-name as a symbol?"
  (cond
    ((null form) nil)
    ((symbolp form) (string= (string form) var-name))
    ((listp form) (some (lambda (f) (mentions-var-p f var-name)) form))
    (t nil)))

(defun var-escapes-through-arg-p (arg var-name)
  "Does var-name escape through arg? Returns nil if var is only accessed inside
   extraction forms (vector-ref, vector-len, hash-get, etc.) that read FROM the
   container without leaking the container itself."
  (cond
    ((null arg) nil)
    ((symbolp arg) (string= (string arg) var-name))
    ((not (listp arg)) nil)
    (t (let* ((head (first arg))
              (h (and (symbolp head) (string-downcase (string head)))))
         (if (and h (member h '("vector-ref" "vector-set!"
                                 "vector-push!" "vector-free" "len"
                                 "hash-get" "hash-has?" "hash-del!"
                                 "hash-keys" "hash-vals" "hash-free"
                                 "hash-set!" "array-ref" "array-set!" "get"
                                 "str-concat" "str-slice" "str-upper" "str-lower"
                                 "str-split" "str-from-int" "str-from-float"
                                 "str-join" "str-trim" "str-replace")
                            :test #'equal))
             nil  ; extraction: var is accessed, not leaked
             (some (lambda (f) (var-escapes-through-arg-p f var-name))
                   arg))))))

(defun escape-analysis-fn (fn-name body-forms)
  "Analyze a function body for non-escaping heap allocations (new, vector, hash-map).
   Expands macros first so binding forms like [x v] in for-each aren't misread as calls."
  (let* ((expanded (mapcar #'macroexpand-all body-forms))
         (bindings (escape-find-alloc-bindings expanded)))
    (dolist (var-name bindings)
      (let ((key (format nil "~a.~a" fn-name var-name)))
        (if (escape-check-var var-name expanded)
            (setf (gethash key *escape-info*) :escapes)
            (setf (gethash key *escape-info*) :local))))))

(defun escape-analysis (forms)
  "Run escape analysis on all defn forms."
  (dolist (form forms)
    (when (and (listp form) (sym= (first form) "defn"))
      (let* ((has-attr (stringp (second form)))
             (form2 (if has-attr (cons (first form) (cddr form)) form))
             (name (string (second form2)))
             (rest-forms (cdddr form2))
             (body (if (keywordp (first rest-forms)) (cdr rest-forms) rest-forms)))
        (escape-analysis-fn name body)))))

(defun escape-local-p (fn-name var-name)
  "Check if (new ...) bound to var-name in fn-name is stack-allocatable."
  (eq (gethash (format nil "~a.~a" fn-name var-name) *escape-info*) :local))

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
    ;; Phase 1.5: Escape analysis (marks non-escaping allocations for stack placement)
    (escape-analysis forms)
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
