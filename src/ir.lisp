;;;; IR datatypes.
(in-package :sysp-ir)

(defstruct ir-fn   name params ret-type blocks (no-inline nil))

;; term ∈ (:ret v) | (:ret-unit) | (:br c then-blk else-blk join-blk t-deaths e-deaths)
;;      | (:jump blk args) | (:loop cond body-blk exit-blk)
(defstruct ir-block name params instrs term)

;; op ∈ :const :prim :copy :call :str-lit :release :retain :set
(defstruct ir-instr dst type op args)

;;; Struct registry: name (symbol) → list of (field-name field-type) pairs.
(defvar *struct-fields* (make-hash-table))

;;; Generic struct templates: name (symbol) → (params fields), where
;;; params is a list of type-param keywords like (:T :U) and fields is
;;; the raw template that may reference those keywords. Concrete instances
;;; are produced by mono and added to *struct-fields* under a mangled name.
(defvar *generic-structs* (make-hash-table))

;;; Concrete instantiations seen this compile: (name . concrete-args)
;;; → mangled-name keyword. Drives per-program emit of struct decls.
(defvar *generic-struct-instances* (make-hash-table :test 'equal))

;;; Top-level constants: name → (type literal-value).
(defvar *globals* (make-hash-table))

(defun ref-type-p (ty)
  ;; Types that participate in ARC: :string (sysp String), :Value (cons cells),
  ;; and structs whose fields transitively contain rc types. Pointers and
  ;; primitives stay non-rc — only the *content* of a struct matters here.
  (cond
    ((eq ty :string) t)
    ((and (keywordp ty) (string-equal (symbol-name ty) "Value")) t)
    ((and (keywordp ty) (gethash (intern (symbol-name ty) :sysp-ir) *struct-fields*))
     (struct-has-rc-fields-p (intern (symbol-name ty) :sysp-ir)))
    (t nil)))

(defun struct-has-rc-fields-p (struct-name)
  "True when any field's type is itself rc-tracked. Direct self-reference
   is impossible in C (would have infinite size), so this terminates;
   pointer fields are not rc-typed and short-circuit indirect cycles."
  (some (lambda (f) (ref-type-p (second f)))
        (gethash struct-name *struct-fields*)))

(defun struct-name-p (sym)
  (and (symbolp sym) (gethash sym *struct-fields*)))

(defun generic-struct-name-p (sym)
  (and (symbolp sym) (gethash sym *generic-structs*)))

(defun struct-type-keyword (sym)
  "Convert struct name symbol to its type keyword: CPU → :CPU."
  (intern (symbol-name sym) :keyword))

(defun struct-keyword-name (kw)
  "Inverse: :CPU → CPU symbol (interned in sysp-ir for *struct-fields* lookup)."
  (intern (symbol-name kw) :sysp-ir))

(defun struct-type-p (ty)
  (and (keywordp ty)
       (gethash (struct-keyword-name ty) *struct-fields*)))

(defun struct-field-type (struct-ty field-name)
  (let ((fields (gethash (struct-keyword-name struct-ty) *struct-fields*)))
    (or (second (assoc field-name fields))
        (error "struct ~A has no field ~A" struct-ty field-name))))

;;; --- mutability axis (SPEC §9) ---
;;; A normalized field is (name type) for an immutable field, or
;;; (name type :mut) for a `mut` field. The only source of mutability is
;;; a :mut field; everything else (primitives, pointers, String, Value,
;;; Cons, Fn) is immutable.

(defun field-mut-p (field)
  "True if a normalized struct field is declared `mut`."
  (eq (third field) :mut))

(defun deeply-immutable-p (ty &optional in-progress)
  "True iff TY is transitively immutable, i.e. shareable by reference
   (SPEC §9.2). A struct is deeply immutable when it has no `mut` field
   and every field type is deeply immutable. Recursion is treated as
   immutable: a recursive immutable type (Cons-shaped) is still immutable.
   Everything that is not a struct-with-a-reachable-mut-field is immutable
   (primitives, pointers, String, Value, Fn)."
  (cond
    ((struct-type-p ty)
     (let ((name (struct-keyword-name ty)))
       (or (member name in-progress)        ; recursion: assume immutable
           (let ((ip (cons name in-progress)))
             (every (lambda (f)
                      (and (not (field-mut-p f))
                           (deeply-immutable-p (second f) ip)))
                    (gethash name *struct-fields*))))))
    (t t)))

(defun mutable-type-p (ty)
  "TY obeys mutable value semantics (SPEC §9.1): a struct with a reachable
   `mut` field. The complement of deeply-immutable-p."
  (not (deeply-immutable-p ty)))

(defun struct-field-mut-p (struct-ty field-name)
  "True if FIELD-NAME of STRUCT-TY is declared `mut`."
  (let ((fields (gethash (struct-keyword-name struct-ty) *struct-fields*)))
    (field-mut-p (or (assoc field-name fields)
                     (error "struct ~A has no field ~A" struct-ty field-name)))))
