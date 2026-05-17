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

;;; --- copy coalescing (pre-ARC) ---
;;;
;;; Lowering emits `tN = <expr>; userVar = copy tN;` for every let-binding
;;; of a compound value. Collapse to `userVar = <expr>;` by renaming the
;;; producer's dst, when tN's only use is that copy. Runs BEFORE
;;; insert-releases so ARC sees the coalesced variable and tracks it
;;; normally — ownership is unchanged (one value, one name instead of
;;; two), so this is leak-neutral by construction.

(defun coalesce-copies (fn)
  (let ((uc (count-uses fn))
        (block-param-syms (make-hash-table))
        (set-targets (make-hash-table)))
    (dolist (b (ir-fn-blocks fn))
      (dolist (p (ir-block-params b))
        (setf (gethash (first p) block-param-syms) t))
      (dolist (i (ir-block-instrs b))
        (when (eq (ir-instr-op i) :set)
          (setf (gethash (first (ir-instr-args i)) set-targets) t))))
    (dolist (b (ir-fn-blocks fn))
      (let ((instrs (ir-block-instrs b)))
        (loop for cell on instrs
              for prev = (first cell)
              for next = (second cell)
              when (and next
                        (eq (ir-instr-op next) :copy)
                        (ir-instr-dst prev)
                        ;; copy reads exactly prev's freshly-defined dst...
                        (eq (first (ir-instr-args next)) (ir-instr-dst prev))
                        ;; ...and that temp is used nowhere else.
                        (= (gethash (ir-instr-dst prev) uc 0) 1)
                        (not (gethash (ir-instr-dst prev) block-param-syms))
                        (not (gethash (ir-instr-dst prev) set-targets))
                        ;; copy's own dst must be a real binding, not itself
                        ;; a temp feeding another copy (keep the rewrite local).
                        (not (gethash (ir-instr-dst next) set-targets))
                        ;; producer must be value-yielding (its dst is the
                        ;; value); don't fold across copy/release/retain.
                        (not (member (ir-instr-op prev)
                                     '(:copy :release :retain :set)))
                        ;; same C type, so dropping the copy can't change
                        ;; the variable's declared type (or lose the
                        ;; Value/Fn type that gates the value.h include).
                        (equal (c-type (ir-instr-type prev))
                               (c-type (ir-instr-type next))))
              do (setf (ir-instr-dst prev) (ir-instr-dst next)
                       (ir-instr-op next) :nop
                       (ir-instr-args next) nil
                       (ir-instr-dst next) nil))
        (setf (ir-block-instrs b)
              (remove :nop instrs :key #'ir-instr-op))))
    fn))

;;; --- inline single-use tmps ---
;;;
;;; For tmps with exactly one use, fold their definition into the use site.
;;; Safe for :const, :prim, non-ref :copy. Not for :call, :str-lit, or
;;; ref-type :copy (allocations / aliasing). Block-params and :set targets
;;; are never inlined.

(defvar *inlinable*)   ; sym → C-expression-string
(defvar *no-inline*)   ; symbol set: tmps that must remain real C vars

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

(defun strip-outer-parens (s)
  "Drop one balanced paren pair if it wholly encloses S. Safe only in
   controlling-expression contexts (if/while), where C's own parens
   already group the expression — avoids `if ((x == 0))`, which clang
   flags under -Wparentheses-equality. Inner parens that don't span the
   whole string (e.g. `(a) + (b)`) are left untouched for precedence."
  (let ((n (length s)))
    (if (and (> n 1) (char= (char s 0) #\() (char= (char s (1- n)) #\)))
        (let ((depth 0))
          (dotimes (k n (subseq s 1 (1- n)))
            (case (char s k) (#\( (incf depth)) (#\) (decf depth)))
            (when (and (zerop depth) (< k (1- n)))
              (return-from strip-outer-parens s))))
        s)))

(defun debool (s)
  "`(X != 0)` → `X` in a boolean context: drop the explicit truthiness
   test lowering inserts, so conditions read `if (p)` not `if ((p != 0))`.
   Only fires when the `!= 0` is the whole expression's top operator
   (outer parens enclose everything), so nested `!= 0` is untouched."
  (let ((n (length s)))
    (if (and (> n 6)
             (char= (char s 0) #\()
             (string= (subseq s (- n 6)) " != 0)"))
        (let ((depth 0))
          (dotimes (k n s)
            (case (char s k) (#\( (incf depth)) (#\) (decf depth)))
            (when (and (zerop depth) (< k (1- n)))
              (return-from debool s)))
          (subseq s 1 (- n 6)))
        s)))

(defun cond-ref (sym)
  "nameref for a value used directly as an if/while condition."
  (strip-outer-parens (debool (nameref sym))))

(defun rc-named-syms (fn)
  "Syms that ARC tracks by name (any :release/:retain operand). A call
   result among these must keep its C variable — it is ARC's anchor."
  (let ((s (make-hash-table)))
    (dolist (b (ir-fn-blocks fn))
      (dolist (i (ir-block-instrs b))
        (when (member (ir-instr-op i) '(:release :retain))
          (dolist (u (ir-instr-args i)) (setf (gethash u s) t)))))
    s))

(defun call-inlinable-p (i next term tmap pset rc-named uc)
  "A :call result is safe to fold into its use iff:
     - single use (uc=1) that is the very next instr or the block term;
     - result is non-rc and no :release/:retain names it (ARC-neutral);
     - every arg is non-rc or a borrowed fn-param (no release inserted
       around the call, so moving its evaluation to the use can't UAF).
   Adjacency is the proof: any ARC release would itself sit between the
   call and a non-adjacent use, so requiring adjacency excludes it."
  (let ((dst (ir-instr-dst i)))
    (and dst
         (eq (ir-instr-op i) :call)
         (= (gethash dst uc 0) 1)
         (not (ref-type-p (ir-instr-type i)))
         (not (gethash dst rc-named))
         (every (lambda (a)
                  (or (not (symbolp a))
                      (member a pset)
                      (not (ref-type-p (gethash a tmap)))))
                (rest (ir-instr-args i)))
         (if next
             (member dst (instr-uses next))
             (member dst (term-uses term))))))

(defun call-inline-str (i)
  (format nil "~a(~{~a~^, ~})"
          (c-name (first (ir-instr-args i)))
          (mapcar #'nameref (rest (ir-instr-args i)))))

(defun build-inlinable (fn)
  (let ((uc (count-uses fn))
        (m (make-hash-table))
        (block-param-syms (make-hash-table))
        (set-targets (make-hash-table))
        (no-inline (and (boundp '*no-inline*) *no-inline*))
        (tmap (build-type-map fn))
        (rc-named (rc-named-syms fn))
        (pset (mapcar #'first (ir-fn-params fn))))
    (dolist (b (ir-fn-blocks fn))
      (dolist (p (ir-block-params b))
        (setf (gethash (first p) block-param-syms) t))
      (dolist (i (ir-block-instrs b))
        (when (eq (ir-instr-op i) :set)
          (setf (gethash (first (ir-instr-args i)) set-targets) t))))
    (let ((*inlinable* m))
      (dolist (b (ir-fn-blocks fn))
        (let ((term (ir-block-term b)))
          (loop for cell on (ir-block-instrs b)
                for i = (first cell)
                for next = (second cell)
                do
            (let ((dst (ir-instr-dst i)))
              (when (and dst
                         (not (gethash dst block-param-syms))
                         (not (gethash dst set-targets))
                         (not (and no-inline (member dst no-inline)))
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
                                          (nameref (third a))))))
                  (:call  (when (call-inlinable-p i next term tmap pset
                                                  rc-named uc)
                            (setf (gethash dst m)
                                  (call-inline-str i)))))))))))
    m))
