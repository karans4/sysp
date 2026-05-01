;;;; CFG dataflow over ref-typed bindings.
;;;; Returns live-in / live-out tables for each block.

(in-package :sysp-ir)

(defun instr-uses (i)
  "Variables this instruction reads."
  (case (ir-instr-op i)
    (:const     nil)
    (:str-lit   nil)
    (:cstr-lit  nil)
    (:copy      (list (first (ir-instr-args i))))
    (:prim      (rest (ir-instr-args i)))
    (:call      (rest (ir-instr-args i)))
    (:release   (ir-instr-args i))
    (:retain    (ir-instr-args i))
    (:set       (list (second (ir-instr-args i))))   ; src only; target is a write
    (:unary     (list (second (ir-instr-args i))))   ; (op-string val) → reads val
    (:addr-of   (ir-instr-args i))                    ; reads the named binding
    (:cast      (list (second (ir-instr-args i))))   ; (target-type val) → reads val
    (:deref     (ir-instr-args i))
    (:ptr-ref   (ir-instr-args i))
    (:ptr-set   (ir-instr-args i))
    (:ptr-set-at (ir-instr-args i))))

(defun term-uses (term)
  "Variables the terminator reads (including transferred-out)."
  (case (first term)
    (:ret  (list (second term)))
    (:br   (list (second term)))
    (:loop (list (second term)))
    (:jump (third term))))

(defun term-transfers (term)
  "Variables whose ownership leaves this block via the terminator."
  (case (first term)
    (:ret  (list (second term)))
    (:jump (third term))))

(defun term-successors (term)
  (case (first term)
    (:br   (list (third term) (fourth term)))
    (:loop (list (third term) (fourth term)))    ; body-blk exit-blk
    (:jump (list (second term)))))

(defun br-then-blk    (term) (third term))
(defun br-else-blk    (term) (fourth term))
(defun br-join-blk    (term) (fifth term))
(defun br-then-deaths (term) (sixth term))
(defun br-else-deaths (term) (seventh term))

(defun build-type-map (fn)
  "All ref-typed bindings of the fn → type."
  (let ((tm (make-hash-table)))
    (dolist (p (ir-fn-params fn))
      (when (ref-type-p (second p))
        (setf (gethash (first p) tm) (second p))))
    (dolist (b (ir-fn-blocks fn))
      (dolist (p (ir-block-params b))
        (when (ref-type-p (second p))
          (setf (gethash (first p) tm) (second p))))
      (dolist (i (ir-block-instrs b))
        (when (and (ir-instr-dst i) (ref-type-p (ir-instr-type i)))
          (setf (gethash (ir-instr-dst i) tm) (ir-instr-type i)))))
    tm))

(defun ref-filter (vars type-map)
  (remove-if-not (lambda (v) (gethash v type-map)) vars))

(defun block-gen-kill (blk fn-params type-map)
  "GEN: ref vars used before being defined in this block.
   KILL: ref vars defined in this block."
  (let ((gen nil) (kill nil) (defined nil))
    (when (eq (ir-block-name blk) 'entry)
      (dolist (p fn-params)
        (when (ref-type-p (second p))
          (push (first p) defined)
          (push (first p) kill))))
    (dolist (p (ir-block-params blk))
      (when (ref-type-p (second p))
        (push (first p) defined)
        (push (first p) kill)))
    (dolist (i (ir-block-instrs blk))
      (dolist (u (ref-filter (instr-uses i) type-map))
        (unless (or (member u defined) (member u gen))
          (push u gen)))
      (when (and (ir-instr-dst i) (ref-type-p (ir-instr-type i)))
        (push (ir-instr-dst i) defined)
        (pushnew (ir-instr-dst i) kill)))
    (dolist (u (ref-filter (term-uses (ir-block-term blk)) type-map))
      (unless (or (member u defined) (member u gen))
        (push u gen)))
    (values gen kill)))

(defun liveness (fn type-map)
  "Returns (values live-in live-out), each a hashtable block-name → list of syms."
  (let ((live-in (make-hash-table))
        (live-out (make-hash-table))
        (gen-tab (make-hash-table))
        (kill-tab (make-hash-table)))
    (dolist (b (ir-fn-blocks fn))
      (multiple-value-bind (g k) (block-gen-kill b (ir-fn-params fn) type-map)
        (setf (gethash (ir-block-name b) gen-tab) g
              (gethash (ir-block-name b) kill-tab) k
              (gethash (ir-block-name b) live-in) nil
              (gethash (ir-block-name b) live-out) nil)))
    (loop with changed = t
          while changed do
          (setf changed nil)
          (dolist (b (ir-fn-blocks fn))
            (let* ((name (ir-block-name b))
                   (succs (term-successors (ir-block-term b)))
                   (new-out (reduce (lambda (a sn) (union a (gethash sn live-in)))
                                    succs :initial-value nil))
                   (new-in (union (gethash name gen-tab)
                                  (set-difference new-out (gethash name kill-tab)))))
              (unless (and (null (set-exclusive-or new-out (gethash name live-out)))
                           (null (set-exclusive-or new-in (gethash name live-in))))
                (setf (gethash name live-out) new-out
                      (gethash name live-in) new-in
                      changed t)))))
    (values live-in live-out)))
