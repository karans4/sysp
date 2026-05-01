;;;; Cosmetic passes that produce hand-written-looking C from the IR.
;;;;   - rewrite-jump-to-ret: collapse ret-only joins
;;;;   - prune-unreachable: drop blocks no longer reachable from entry
;;;;   - count-uses + build-inlinable: fold single-use tmps into use sites

(in-package :sysp-ir)

;;; --- ret-only-join collapse ---

(defun ret-only-join-p (b)
  (let ((params (ir-block-params b))
        (term (ir-block-term b)))
    (and (= (length params) 1)
         (null (ir-block-instrs b))
         (eq (first term) :ret)
         (eq (second term) (first (first params))))))

(defun rewrite-jump-to-ret (fn)
  (let ((by-name (make-hash-table))
        (changed t))
    (loop while changed do
      (setf changed nil)
      (clrhash by-name)
      (dolist (b (ir-fn-blocks fn))
        (setf (gethash (ir-block-name b) by-name) b))
      (dolist (b (ir-fn-blocks fn))
        (let ((term (ir-block-term b)))
          (when (eq (first term) :jump)
            (let* ((tgt-name (second term))
                   (args (third term))
                   (tgt (gethash tgt-name by-name)))
              (when (and tgt (ret-only-join-p tgt))
                (setf (ir-block-term b) (list :ret (first args)))
                (setf changed t)))))))))

;;; --- dead block pruning ---

(defun reachable-block-names (fn)
  (let ((seen (make-hash-table))
        (by-name (make-hash-table))
        (q (list 'entry)))
    (dolist (b (ir-fn-blocks fn))
      (setf (gethash (ir-block-name b) by-name) b))
    (loop while q do
      (let ((n (pop q)))
        (unless (gethash n seen)
          (setf (gethash n seen) t)
          (let ((b (gethash n by-name)))
            (when b
              (dolist (s (term-successors (ir-block-term b)))
                (push s q)))))))
    seen))

(defun prune-unreachable (fn)
  (let ((reachable (reachable-block-names fn)))
    (setf (ir-fn-blocks fn)
          (remove-if-not (lambda (b) (gethash (ir-block-name b) reachable))
                         (ir-fn-blocks fn))))
  fn)

;;; --- inline single-use tmps ---
;;;
;;; For tmps with exactly one use, fold their definition into the use site.
;;; Safe for :const, :prim, non-ref :copy. Not for :call, :str-lit, or
;;; ref-type :copy (allocations / aliasing). Block-params and :set targets
;;; are never inlined.

(defvar *inlinable*)   ; sym → C-expression-string

(defun count-uses (fn)
  "Use counts. :release/:retain don't count — they consume by name for ARC,
   not as a value to substitute."
  (let ((uc (make-hash-table)))
    (dolist (b (ir-fn-blocks fn))
      (dolist (i (ir-block-instrs b))
        (unless (member (ir-instr-op i) '(:release :retain))
          (dolist (u (instr-uses i)) (incf (gethash u uc 0)))))
      (dolist (u (term-uses (ir-block-term b))) (incf (gethash u uc 0))))
    uc))

(defun nameref (sym)
  "Render sym as C, substituting from *inlinable* if available."
  (or (gethash sym *inlinable*) (c-name sym)))

(defun build-inlinable (fn)
  (let ((uc (count-uses fn))
        (m (make-hash-table))
        (block-param-syms (make-hash-table))
        (set-targets (make-hash-table)))
    (dolist (b (ir-fn-blocks fn))
      (dolist (p (ir-block-params b))
        (setf (gethash (first p) block-param-syms) t))
      (dolist (i (ir-block-instrs b))
        (when (eq (ir-instr-op i) :set)
          (setf (gethash (first (ir-instr-args i)) set-targets) t))))
    (let ((*inlinable* m))
      (dolist (b (ir-fn-blocks fn))
        (dolist (i (ir-block-instrs b))
          (let ((dst (ir-instr-dst i)))
            (when (and dst
                       (not (gethash dst block-param-syms))
                       (not (gethash dst set-targets))
                       (= (gethash dst uc 0) 1))
              (case (ir-instr-op i)
                (:const (setf (gethash dst m)
                              (format nil "~a" (first (ir-instr-args i)))))
                (:copy  (unless (ref-type-p (ir-instr-type i))
                          (setf (gethash dst m)
                                (nameref (first (ir-instr-args i))))))
                (:prim  (let ((a (ir-instr-args i)))
                          (setf (gethash dst m)
                                (format nil "(~a ~a ~a)"
                                        (nameref (second a))
                                        (first a)
                                        (nameref (third a))))))))))))
    m))
