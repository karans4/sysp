;;;; IR datatypes.
(in-package :sysp-ir)

(defstruct ir-fn   name params ret-type blocks)

;; term ∈ (:ret v) | (:ret-unit) | (:br c then-blk else-blk join-blk t-deaths e-deaths)
;;      | (:jump blk args) | (:loop cond body-blk exit-blk)
(defstruct ir-block name params instrs term)

;; op ∈ :const :prim :copy :call :str-lit :release :retain :set
(defstruct ir-instr dst type op args)

(defun ref-type-p (ty) (eq ty :string))   ; extend as more ref types arrive
