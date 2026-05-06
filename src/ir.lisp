;;;; IR datatypes.
(in-package :sysp-ir)

(defstruct ir-fn   name params ret-type blocks (no-inline nil))

;; term ∈ (:ret v) | (:ret-unit) | (:br c then-blk else-blk join-blk t-deaths e-deaths)
;;      | (:jump blk args) | (:loop cond body-blk exit-blk)
(defstruct ir-block name params instrs term)

;; op ∈ :const :prim :copy :call :str-lit :release :retain :set
(defstruct ir-instr dst type op args)

(defun ref-type-p (ty)
  ;; Types that participate in ARC: :string (sysp String) and :Value (cons cells).
  ;; Case-insensitive for :Value to bridge parser-preserved vs CL-upcased.
  (or (eq ty :string)
      (and (keywordp ty) (string-equal (symbol-name ty) "Value"))))

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
