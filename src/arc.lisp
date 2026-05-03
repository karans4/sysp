;;;; ARC: borrow-retain insertion + release insertion.
;;;;
;;;; Calling convention: borrow everywhere.
;;;;   - Caller retains ownership of args across :call (no rc change at boundary).
;;;;   - Callee receives borrowed view of params; does NOT auto-release.
;;;;   - To transfer out (:ret / :jump-args), callee retains the borrowed value.
;;;;   - Locals (let-bound, str-lit, call results) are owned and released at last use.

(in-package :sysp-ir)

(defun borrowed-params (fn)
  (loop for p in (ir-fn-params fn)
        when (ref-type-p (second p)) collect (first p)))

(defun insert-borrow-retains (fn)
  "Insert :retain before any :ret or :jump term that transfers a borrowed
   fn-param. Destination receives a fresh +1. The retain instr carries
   the param's actual type so emit can pick the right rc fn."
  (let* ((borrowed (borrowed-params fn))
         (param-types (loop for p in (ir-fn-params fn)
                            collect (cons (first p) (second p)))))
    (when borrowed
      (dolist (b (ir-fn-blocks fn))
        (let* ((term (ir-block-term b))
               (transferred (term-transfers term))
               (borrowed-transferred (intersection transferred borrowed))
               (new-instrs nil))
          (dolist (v borrowed-transferred)
            (let ((ty (cdr (assoc v param-types))))
              (push (make-ir-instr :dst nil :type ty :op :retain :args (list v))
                    new-instrs)))
          (when new-instrs
            (setf (ir-block-instrs b)
                  (append (ir-block-instrs b) (nreverse new-instrs)))))))))

(defun insert-releases (fn)
  (insert-borrow-retains fn)
  (let* ((type-map (build-type-map fn))
         (borrowed (borrowed-params fn)))
    (multiple-value-bind (live-in live-out) (liveness fn type-map)
      (dolist (b (ir-fn-blocks fn))
        (let ((bname (ir-block-name b)))
          (insert-releases-block b type-map
                                 (gethash bname live-in)
                                 (gethash bname live-out)
                                 borrowed)))
      ;; Edge-deaths for :br: vars in P's live-out not in successor's live-in.
      ;; Excludes borrowed (caller-managed).
      (dolist (b (ir-fn-blocks fn))
        (let ((term (ir-block-term b)))
          (when (eq (first term) :br)
            (let* ((c (second term)) (tblk (third term))
                   (eblk (fourth term)) (jblk (fifth term))
                   (lo (gethash (ir-block-name b) live-out))
                   (then-deaths (set-difference (set-difference lo (gethash tblk live-in)) borrowed))
                   (else-deaths (set-difference (set-difference lo (gethash eblk live-in)) borrowed)))
              (setf (ir-block-term b)
                    (list :br c tblk eblk jblk then-deaths else-deaths))))))))
  fn)

(defun insert-releases-block (blk type-map live-in live-out borrowed)
  "Owned vars in block = (live-in ∪ block-defs) - borrowed. Of those,
   anything in live-out or transferred is kept; everything else releases at
   last use (or block top if never used)."
  (let* ((instrs (ir-block-instrs blk))
         (term   (ir-block-term blk))
         (transferred (ref-filter (term-transfers term) type-map))
         (defined nil)
         (last-use (make-hash-table)))
    (dolist (p (ir-block-params blk))
      (when (ref-type-p (second p))
        (push (first p) defined)))
    (dolist (i instrs)
      (when (and (ir-instr-dst i) (ref-type-p (ir-instr-type i)))
        (push (ir-instr-dst i) defined)))
    (let ((tracking (set-difference (union live-in defined) live-out)))
      (setf tracking (set-difference tracking transferred))
      (setf tracking (set-difference tracking borrowed))
      (loop for idx from 0
            for i in instrs
            do (dolist (u (ref-filter (instr-uses i) type-map))
                 (when (member u tracking)
                   (setf (gethash u last-use) idx))))
      (dolist (u (ref-filter (term-uses term) type-map))
        (when (member u tracking)
          (setf (gethash u last-use) :term)))
      ;; Defined-but-never-used: release at def site (or block top).
      (dolist (v tracking)
        (unless (gethash v last-use)
          (let ((def-idx (loop for idx from 0
                               for i in instrs
                               when (eq (ir-instr-dst i) v) return idx)))
            (setf (gethash v last-use) (or def-idx :pre))))))
    ;; Build new instr list with releases inserted.
    (let ((new-instrs nil))
      (maphash (lambda (v k)
                 (when (eq k :pre)
                   (push (make-ir-instr :dst nil :type (gethash v type-map)
                                        :op :release :args (list v))
                         new-instrs)))
               last-use)
      (loop for idx from 0
            for i in instrs
            do (push i new-instrs)
               (maphash (lambda (v k)
                          (when (and (numberp k) (= k idx))
                            (push (make-ir-instr :dst nil :type (gethash v type-map)
                                                 :op :release :args (list v))
                                  new-instrs)))
                        last-use))
      (maphash (lambda (v k)
                 (when (eq k :term)
                   (push (make-ir-instr :dst nil :type (gethash v type-map)
                                        :op :release :args (list v))
                         new-instrs)))
               last-use)
      (setf (ir-block-instrs blk) (nreverse new-instrs)))))
