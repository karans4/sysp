;;;; sysp-ir: surface s-exprs → ANF/basic-block IR → C
;;;; Stage 1: literals, vars, prim ops, let, if, defn. No ownership yet.

(defpackage :sysp-ir
  (:use :cl)
  (:export :compile-form :emit-c-fn :compile-and-emit))
(in-package :sysp-ir)

;;; ---------- IR datatypes ----------

(defstruct ir-fn   name params ret-type blocks)
(defstruct ir-block name params instrs term)  ; term = (:ret v) | (:ret-unit) | (:br c then-blk else-blk then-args else-args) | (:jump blk args)
(defstruct ir-instr dst type op args)         ; op ∈ :const :prim :copy :call :str-lit :release :retain

;; Reference-counted types. Extend as we add more.
(defun ref-type-p (ty) (eq ty :string))

;;; ---------- builder state ----------

(defvar *tmp-counter*)
(defvar *blocks*)              ; list of ir-block, reverse order
(defvar *cur-instrs*)          ; list, reverse order
(defvar *cur-block-name*)
(defvar *cur-block-params*)

(defun fresh-tmp ()
  (intern (format nil "T~D" (incf *tmp-counter*))))

(defun fresh-blk (base)
  (intern (format nil "~A~D" base (incf *tmp-counter*))))

(defun emit (instr) (push instr *cur-instrs*))

(defun finish-block (term)
  (push (make-ir-block :name *cur-block-name*
                       :params *cur-block-params*
                       :instrs (nreverse *cur-instrs*)
                       :term term)
        *blocks*)
  (setf *cur-instrs* nil
        *cur-block-name* nil
        *cur-block-params* nil))

(defun start-block (name params)
  (setf *cur-block-name* name
        *cur-block-params* params
        *cur-instrs* nil))

;;; ---------- lowering ----------
;;; lower : surface-expr × env → (values value-name type)
;;; env is alist of (sym . type)

(defun lower (e env)
  (cond
    ((integerp e)
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :int :op :const :args (list e)))
       (values d :int)))
    ((eq e t)   (let ((d (fresh-tmp)))
                  (emit (make-ir-instr :dst d :type :bool :op :const :args (list 1)))
                  (values d :bool)))
    ((null e)   (let ((d (fresh-tmp)))
                  (emit (make-ir-instr :dst d :type :bool :op :const :args (list 0)))
                  (values d :bool)))
    ((stringp e)
     (let ((d (fresh-tmp)))
       (emit (make-ir-instr :dst d :type :string :op :str-lit :args (list e)))
       (values d :string)))
    ((symbolp e)
     (let ((b (assoc e env)))
       (unless b (error "unbound symbol: ~A" e))
       (values e (cdr b))))
    ((consp e)
     (lower-form (car e) (cdr e) env))
    (t (error "cannot lower: ~A" e))))

(defgeneric lower-form (head args env))

(defmethod lower-form ((head (eql '+)) args env) (lower-binop '+ :int args env))
(defmethod lower-form ((head (eql '-)) args env) (lower-binop '- :int args env))
(defmethod lower-form ((head (eql '*)) args env) (lower-binop '* :int args env))
(defmethod lower-form ((head (eql '/)) args env) (lower-binop '/ :int args env))
(defmethod lower-form ((head (eql '<)) args env) (lower-binop '< :bool args env))
(defmethod lower-form ((head (eql '>)) args env) (lower-binop '> :bool args env))
(defmethod lower-form ((head (eql '=)) args env) (lower-binop '== :bool args env))

(defmethod lower-form ((head (eql 'string-concat)) args env)
  (lower-rt-call 'sysp_str_concat :string args env))
(defmethod lower-form ((head (eql 'string-len)) args env)
  (lower-rt-call 'sysp_str_len :int args env))
(defmethod lower-form ((head (eql 'string-print)) args env)
  (lower-rt-call 'sysp_str_print :unit args env))

(defun lower-rt-call (cfn rty args env)
  (let ((arg-names nil))
    (dolist (a args)
      (multiple-value-bind (n _) (lower a env) (declare (ignore _))
        (push n arg-names)))
    (let ((d (fresh-tmp)))
      (emit (make-ir-instr :dst d :type rty :op :call
                           :args (cons cfn (nreverse arg-names))))
      (values d rty))))

(defun lower-binop (op rty args env)
  (multiple-value-bind (a _at) (lower (first args) env) (declare (ignore _at))
    (multiple-value-bind (b _bt) (lower (second args) env) (declare (ignore _bt))
      (let ((d (fresh-tmp)))
        (emit (make-ir-instr :dst d :type rty :op :prim :args (list op a b)))
        (values d rty)))))

(defmethod lower-form ((head (eql 'let)) args env)
  ;; (let ((x v) ...) body...)
  (let ((bindings (first args))
        (body (rest args))
        (env2 env))
    (dolist (b bindings)
      (multiple-value-bind (n ty) (lower (second b) env2)
        (emit (make-ir-instr :dst (first b) :type ty :op :copy :args (list n)))
        (push (cons (first b) ty) env2)))
    (let (last-n last-ty)
      (dolist (s body)
        (multiple-value-bind (n ty) (lower s env2)
          (setf last-n n last-ty ty)))
      (values last-n last-ty))))

(defmethod lower-form ((head (eql 'if)) args env)
  ;; (if c then else) — :br carries the join block name so the structured
  ;; emitter can drive `if`/`else` directly without CFG analysis.
  ;; :br shape: (:br cond then-blk else-blk join-blk then-deaths else-deaths)
  (destructuring-bind (c-expr t-expr e-expr) args
    (multiple-value-bind (cn _ct) (lower c-expr env) (declare (ignore _ct))
      (let* ((then-blk (fresh-blk "THEN"))
             (else-blk (fresh-blk "ELSE"))
             (join-blk (fresh-blk "JOIN"))
             (result   (fresh-tmp)))
        (finish-block (list :br cn then-blk else-blk join-blk nil nil))
        (start-block then-blk nil)
        (multiple-value-bind (tn tty) (lower t-expr env)
          (finish-block (list :jump join-blk (list tn)))
          (start-block else-blk nil)
          (multiple-value-bind (en _ety) (lower e-expr env) (declare (ignore _ety))
            (finish-block (list :jump join-blk (list en)))
            (start-block join-blk (list (list result tty)))
            (values result tty)))))))

(defmethod lower-form (head args env)
  ;; default: function call to user-defined fn
  (let ((arg-names nil) (arg-types nil))
    (dolist (a args)
      (multiple-value-bind (n ty) (lower a env)
        (push n arg-names) (push ty arg-types)))
    (let ((d (fresh-tmp))
          (rty (or (get head 'ret-type) :int))) ; default :int for now
      (emit (make-ir-instr :dst d :type rty :op :call
                           :args (cons head (nreverse arg-names))))
      (values d rty))))

;;; ---------- top-level: defn ----------

(defun compile-defn (form)
  "(defn name (params...) ret-type body...) → ir-fn"
  (destructuring-bind (_defn name params ret-type &rest body) form
    (declare (ignore _defn))
    (let ((*tmp-counter* 0)
          (*blocks* nil)
          (*cur-instrs* nil)
          (*cur-block-name* 'entry)
          (*cur-block-params* nil)
          (env (mapcar (lambda (p) (cons (first p) (second p))) params)))
      (setf (get name 'ret-type) ret-type)
      (let (last-n)
        (dolist (s body)
          (multiple-value-bind (n ty) (lower s env)
            (declare (ignore ty))
            (setf last-n n)))
        (finish-block (list :ret last-n)))
      (let ((fn (insert-releases
                 (make-ir-fn :name name :params params :ret-type ret-type
                             :blocks (nreverse *blocks*)))))
        (rewrite-jump-to-ret fn)
        (prune-unreachable fn)
        fn))))

;;; ---------- ownership / release-insertion pass ----------
;;; Cross-block CFG liveness over ref-typed bindings.
;;;
;;; Calling convention: caller's :jump-args TRANSFER ownership to dest's
;;; block-params; :ret TRANSFERS to caller of the function. Function-params
;;; of entry block are owned (+1) on entry. Calls (:call) BORROW their
;;; args (no rc change at call boundary). Return value of a :call is owned (+1).

(defun instr-uses (i)
  "Variables this instruction reads."
  (case (ir-instr-op i)
    (:const   nil)
    (:str-lit nil)
    (:copy    (list (first (ir-instr-args i))))
    (:prim    (rest (ir-instr-args i)))
    (:call    (rest (ir-instr-args i)))
    (:release (ir-instr-args i))
    (:retain  (ir-instr-args i))))

(defun term-uses (term)
  "Variables the terminator reads (including transferred-out)."
  (case (first term)
    (:ret  (list (second term)))
    (:br   (list (second term)))
    (:jump (third term))
    (t     nil)))

(defun term-transfers (term)
  "Variables whose ownership leaves this block via the terminator
   (returned out of fn, or sent to a successor's block-param)."
  (case (first term)
    (:ret  (list (second term)))
    (:jump (third term))
    (t     nil)))

(defun term-successors (term)
  (case (first term)
    (:br   (list (third term) (fourth term)))   ; then-blk else-blk
    (:jump (list (second term)))
    (t     nil)))

(defun br-then-blk (term) (third term))
(defun br-else-blk (term) (fourth term))
(defun br-join-blk (term) (fifth term))
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
        (when (ref-type-p (ir-instr-type i))
          (setf (gethash (ir-instr-dst i) tm) (ir-instr-type i)))))
    tm))

(defun ref-filter (vars type-map)
  (remove-if-not (lambda (v) (gethash v type-map)) vars))

(defun block-gen-kill (blk fn-params type-map)
  "GEN: ref vars used before being defined in this block.
   KILL: ref vars defined in this block (block-params + ref-typed instr dsts)."
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
      (when (ref-type-p (ir-instr-type i))
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

(defun insert-releases (fn)
  (let* ((type-map (build-type-map fn)))
    (multiple-value-bind (live-in live-out) (liveness fn type-map)
      (dolist (b (ir-fn-blocks fn))
        (let ((bname (ir-block-name b)))
          (insert-releases-block b fn type-map
                                 (gethash bname live-in)
                                 (gethash bname live-out))))
      (dolist (b (ir-fn-blocks fn))
        (let ((term (ir-block-term b)))
          (when (eq (first term) :br)
            (let* ((c (second term)) (tblk (third term))
                   (eblk (fourth term)) (jblk (fifth term))
                   (lo (gethash (ir-block-name b) live-out))
                   (then-deaths (set-difference lo (gethash tblk live-in)))
                   (else-deaths (set-difference lo (gethash eblk live-in))))
              (setf (ir-block-term b)
                    (list :br c tblk eblk jblk then-deaths else-deaths))))))))
  fn)

(defun insert-releases-block (blk fn type-map live-in live-out)
  "Universe of owned vars in this block = live-in ∪ block-defs.
   Of those, anything in live-out or in :ret/:jump-arg transfers is kept.
   Everything else must be released after its last use in this block (or at
   block top if never used)."
  (let* ((instrs (ir-block-instrs blk))
         (term   (ir-block-term blk))
         (transferred (ref-filter (term-transfers term) type-map))
         (defined nil)
         (last-use (make-hash-table)))
    (when (eq (ir-block-name blk) 'entry)
      (dolist (p (ir-fn-params fn))
        (when (ref-type-p (second p))
          (push (first p) defined))))
    (dolist (p (ir-block-params blk))
      (when (ref-type-p (second p))
        (push (first p) defined)))
    (dolist (i instrs)
      (when (ref-type-p (ir-instr-type i))
        (push (ir-instr-dst i) defined)))
    (let ((tracking (set-difference (union live-in defined) live-out)))
      (setf tracking (set-difference tracking transferred))
      (loop for idx from 0
            for i in instrs
            do (dolist (u (ref-filter (instr-uses i) type-map))
                 (when (member u tracking)
                   (setf (gethash u last-use) idx))))
      (dolist (u (ref-filter (term-uses term) type-map))
        (when (member u tracking)
          ;; Release before term
          (setf (gethash u last-use) :term)))
      ;; Defined-but-never-used: release immediately after definition.
      ;; For block-params (no instr defines them), release at idx 0 (before any instr).
      ;; For instr defs, release after that instr.
      (dolist (v tracking)
        (unless (gethash v last-use)
          (let ((def-idx (loop for idx from 0
                               for i in instrs
                               when (eq (ir-instr-dst i) v) return idx)))
            (setf (gethash v last-use) (or def-idx :pre))))))
    ;; Build new instr list with releases inserted.
    (let ((new-instrs nil))
      ;; :pre releases (for unused block-params)
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

;;; ---------- IR pretty printer ----------

(defun pp-ir (fn &optional (s t))
  (format s "(fn ~(~a~) ~a ~(~a~)~%"
          (ir-fn-name fn) (ir-fn-params fn) (ir-fn-ret-type fn))
  (dolist (b (ir-fn-blocks fn))
    (format s "  (~(~a~) ~a~%" (ir-block-name b) (ir-block-params b))
    (dolist (i (ir-block-instrs b))
      (format s "    (= ~(~a~) ~(~a~) (~(~a~)~{ ~(~a~)~}))~%"
              (ir-instr-dst i) (ir-instr-type i)
              (ir-instr-op i) (ir-instr-args i)))
    (format s "    ~(~a~))~%" (ir-block-term b)))
  (format s ")~%"))

;;; ---------- C emit ----------

(defun c-type (ty)
  (case ty (:int "int") (:bool "int") (:unit "void") (:string "String") (t "int")))

(defun c-escape-string (s)
  (with-output-to-string (out)
    (loop for ch across s do
      (case ch
        (#\\ (write-string "\\\\" out))
        (#\" (write-string "\\\"" out))
        (#\Newline (write-string "\\n" out))
        (#\Tab (write-string "\\t" out))
        (t (write-char ch out))))))

(defun c-name (s)
  (let ((str (string-downcase (symbol-name s))))
    (substitute #\_ #\- str)))

(defvar *block-by-name*)
(defvar *indent*)
(defvar *inlinable*)   ; sym → C-expression-string (for fold-into-uses)

;;; ---------- peephole: collapse ret-only joins ----------
;;; If block J has 1 block-param p, no instrs, terminator (:ret p), then for
;;; each predecessor B with terminator (:jump J (a)), rewrite B's terminator
;;; to (:ret a). Iterate to fixpoint, then prune unreachable blocks.
;;; Net effect: each branch of an `if` returns directly instead of writing a
;;; phi-sink and then returning the sink.

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

;;; ---------- inline-on-emit (cosmetic peephole) ----------
;;; For tmps with exactly one use, fold their definition into the use site.
;;; Safe for :const, :prim, :copy. Not for :call or :str-lit (allocations
;;; or side-effects). Block-params and fn-params are never inlined.

(defun count-uses (fn)
  "Use counts. Excludes :release/:retain (they consume the binding by name
   for ARC purposes, not as a value)."
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
        (block-param-syms (make-hash-table)))
    (dolist (b (ir-fn-blocks fn))
      (dolist (p (ir-block-params b))
        (setf (gethash (first p) block-param-syms) t)))
    (let ((*inlinable* m))
      (dolist (b (ir-fn-blocks fn))
        (dolist (i (ir-block-instrs b))
          (let ((dst (ir-instr-dst i)))
            (when (and dst
                       (not (gethash dst block-param-syms))
                       (= (gethash dst uc 0) 1))
              (case (ir-instr-op i)
                (:const (setf (gethash dst m)
                              (format nil "~a" (first (ir-instr-args i)))))
                (:copy  (setf (gethash dst m)
                              (nameref (first (ir-instr-args i)))))
                (:prim  (let ((a (ir-instr-args i)))
                          (setf (gethash dst m)
                                (format nil "(~a ~a ~a)"
                                        (nameref (second a))
                                        (first a)
                                        (nameref (third a))))))))))))
    m))

(defun ind (out) (loop repeat *indent* do (write-string "  " out)))

(defun emit-c-fn (fn &optional (out t))
  (let ((*block-by-name* (make-hash-table))
        (*indent* 1)
        (*inlinable* (build-inlinable fn)))
    (dolist (b (ir-fn-blocks fn))
      (setf (gethash (ir-block-name b) *block-by-name*) b))
    (format out "~a ~a(" (c-type (ir-fn-ret-type fn)) (c-name (ir-fn-name fn)))
    (loop for p in (ir-fn-params fn) for first = t then nil
          do (unless first (format out ", "))
             (format out "~a ~a" (c-type (second p)) (c-name (first p))))
    (format out ") {~%")
    ;; Pre-declare all block-params (needed because block-params are assigned
    ;; from each :jump source — equivalent to phi sinks).
    (dolist (b (ir-fn-blocks fn))
      (dolist (p (ir-block-params b))
        (format out "  ~a ~a;~%" (c-type (second p)) (c-name (first p)))))
    ;; Structured emit starting at entry.
    (emit-structured (gethash 'entry *block-by-name*) nil out)
    (format out "}~%")))

(defun emit-structured (blk until out)
  "Emit blk's instrs then walk its terminator. Stop when blk == until.
   :br produces structured if/else recursing into both arms up to the join.
   :jump assigns block-params and recurses into the dest (unless dest == until)."
  (when (and blk (not (eq (ir-block-name blk) until)))
    (dolist (i (ir-block-instrs blk))
      ;; Skip instrs that have been folded into their use sites.
      (unless (and (ir-instr-dst i) (gethash (ir-instr-dst i) *inlinable*))
        (emit-c-instr-indented i out)))
    (emit-c-term-structured (ir-block-term blk) until out)))

(defun emit-c-term-structured (term until out)
  (case (first term)
    (:ret      (ind out)
               (format out "return ~a;~%" (nameref (second term))))
    (:ret-unit (ind out) (format out "return;~%"))
    (:jump     (let* ((dest-name (second term))
                      (args (third term))
                      (dest (gethash dest-name *block-by-name*)))
                 (loop for p in (ir-block-params dest)
                       for a in args do
                       (ind out)
                       (format out "~a = ~a;~%" (c-name (first p)) (nameref a)))
                 (unless (eq dest-name until)
                   (emit-structured dest until out))))
    (:br       (let ((c (second term))
                     (tblk (br-then-blk term))
                     (eblk (br-else-blk term))
                     (jblk (br-join-blk term))
                     (t-d  (br-then-deaths term))
                     (e-d  (br-else-deaths term)))
                 (ind out)
                 (format out "if (~a) {~%" (nameref c))
                 (let ((*indent* (1+ *indent*)))
                   (dolist (v t-d)
                     (ind out) (format out "sysp_str_release(~a);~%" (c-name v)))
                   (emit-structured (gethash tblk *block-by-name*) jblk out))
                 (ind out) (format out "} else {~%")
                 (let ((*indent* (1+ *indent*)))
                   (dolist (v e-d)
                     (ind out) (format out "sysp_str_release(~a);~%" (c-name v)))
                   (emit-structured (gethash eblk *block-by-name*) jblk out))
                 (ind out) (format out "}~%")
                 (emit-structured (gethash jblk *block-by-name*) until out)))))

(defun emit-c-instr-indented (i out)
  (ind out) (emit-c-instr-body i out))

(defun emit-c-instr-body (i out)
  (let ((dst (and (ir-instr-dst i) (c-name (ir-instr-dst i))))
        (ty (c-type (ir-instr-type i))))
    (case (ir-instr-op i)
      (:const (format out "~a ~a = ~a;~%" ty dst (first (ir-instr-args i))))
      (:copy  (format out "~a ~a = ~a;~%" ty dst (nameref (first (ir-instr-args i)))))
      (:prim  (let ((a (ir-instr-args i)))
                (format out "~a ~a = ~a ~a ~a;~%"
                        ty dst (nameref (second a)) (first a) (nameref (third a)))))
      (:call  (if (eq (ir-instr-type i) :unit)
                  (format out "~a(~{~a~^, ~});~%"
                          (c-name (first (ir-instr-args i)))
                          (mapcar #'nameref (rest (ir-instr-args i))))
                  (format out "~a ~a = ~a(~{~a~^, ~});~%"
                          ty dst (c-name (first (ir-instr-args i)))
                          (mapcar #'nameref (rest (ir-instr-args i))))))
      (:str-lit (let ((s (first (ir-instr-args i))))
                  (format out "String ~a = sysp_str_lit(\"~a\", ~d);~%"
                          dst (c-escape-string s) (length s))))
      (:release (format out "sysp_str_release(~a);~%"
                        (c-name (first (ir-instr-args i)))))
      (:retain  (format out "sysp_str_retain(~a);~%"
                        (c-name (first (ir-instr-args i))))))))

(defun compile-and-emit (form &optional (out t))
  (emit-c-fn (compile-defn form) out))
