;;;; C emission. Structured (no labels/gotos), driven by the CFG.

(in-package :sysp-ir)

;;; --- name / type formatting ---

(defun kw-name= (ty name)
  "Case-insensitive keyword-name compare. Bridges 'parser-preserved
   case' (Fn, Value) and 'CL-reader-upcased' (FN, VALUE)."
  (and (keywordp ty) (string-equal (symbol-name ty) name)))

(defun c-type (ty)
  (cond
    ((eq ty :int)    "int")
    ((eq ty :bool)   "int")
    ((eq ty :unit)   "void")
    ((eq ty :string) "String")
    ((eq ty :cstr)   "const char*")
    ((eq ty :u8)     "uint8_t")
    ((eq ty :u16)    "uint16_t")
    ((eq ty :u32)    "uint32_t")
    ((eq ty :u64)    "uint64_t")
    ((eq ty :i8)     "int8_t")
    ((eq ty :i16)    "int16_t")
    ((eq ty :i32)    "int32_t")
    ((eq ty :i64)    "int64_t")
    ((eq ty :size)   "size_t")
    ((eq ty :float)  "float")
    ((eq ty :double) "double")
    ((eq ty :ptr-void) "void*")
    ((kw-name= ty "Value")  "Value")
    ((kw-name= ty "symbol") "uint32_t")
    ((kw-name= ty "Fn")     "Fn*")
    ;; Structural (:fn (arg-tys) ret-ty) — same C representation as opaque :Fn.
    ((and (consp ty) (eq (first ty) :fn)) "Fn*")
    ;; :ptr-T → "T*"
    ((and (keywordp ty)
          (let ((s (symbol-name ty)))
            (and (> (length s) 4) (string= s "PTR-" :end1 4))))
     (let ((inner (intern (subseq (symbol-name ty) 4) :keyword)))
       (concatenate 'string (c-type inner) "*")))
    ;; (:ptr T)
    ((and (consp ty) (eq (first ty) :ptr))
     (concatenate 'string (c-type (second ty)) "*"))
    ;; struct types: keyword name like :CPU → "CPU"
    ((struct-type-p ty) (symbol-name (struct-keyword-name ty)))
    (t "int")))   ; fallback

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
  ;; Preserve case if the symbol name is mixed-case (CamelCase from parser
  ;; preservation). Otherwise downcase like CL convention.
  ;; Mangle Lisp-y chars to valid C: - → _, ? → _p, ! → _bang.
  (let* ((name (symbol-name s))
         (mixed (and (some #'upper-case-p name)
                     (some #'lower-case-p name)))
         (str (if mixed name (string-downcase name))))
    (with-output-to-string (out)
      (loop for ch across str do
        (case ch
          (#\- (write-char #\_ out))
          (#\? (write-string "_p" out))
          (#\! (write-string "_bang" out))
          (t   (write-char ch out)))))))

;;; --- emitter state ---

(defvar *block-by-name*)
(defvar *indent*)
(defvar *type-map*)   ; sym → type, for typing :br edge-death releases

(defun ind (out) (loop repeat *indent* do (write-string "  " out)))

(defun rc-fn-name (ty op-name)
  "Dispatch retain/release to the right runtime fn based on type.
   op-name is \"retain\" or \"release\". Case-insensitive on keyword.
   Auto-derived struct-level retain/release functions follow the convention
   <StructName>_retain / <StructName>_release."
  (let ((drop (and (string-equal op-name "release")
                    (keywordp ty)
                    (gethash (intern (symbol-name ty) :sysp-ir) *struct-fields*)
                    (trait-impl-fn "Drop" "drop" ty))))
    (cond
      ;; A Drop impl overrides the auto field-walk destructor.
      (drop (c-name drop))
      ((eq ty :string)        (format nil "sysp_str_~a" op-name))
      ((kw-name= ty "Value")  (format nil "val_~a" op-name))
      ((and (keywordp ty)
            (gethash (intern (symbol-name ty) :sysp-ir) *struct-fields*))
       (format nil "~a_~a"
               (symbol-name (intern (symbol-name ty) :sysp-ir))
               op-name))
      (t (error "rc-fn-name: no rc fn for type ~A" ty)))))

(defun struct-rc-type-p (ty)
  "True when ty is a struct keyword whose retain/release takes a pointer.
   String, Value and Fn are runtime-provided with by-value rc ABIs, so
   they pass by value even when an extern-struct declaration registers
   them in *struct-fields* (which would otherwise flip them to &address
   and emit val_retain(&x) against a by-value val_retain(Value))."
  (and (keywordp ty)
       (not (eq ty :string))
       (not (kw-name= ty "Value"))
       (not (kw-name= ty "Fn"))
       (gethash (intern (symbol-name ty) :sysp-ir) *struct-fields*)))

;; Track whether the current program uses Value/cons. If so, we need to
;; emit the runtime header and link runtime/value.c.
(defvar *uses-value*)

;;; --- top-level fn / proto emit ---

(defun normalize-one-field (p)
  "Normalize one field spec to (name type) or (name type :mut).
     (name :t)        — immutable field
     (mut name :t)    — mutable field (SPEC §9.2)"
  (cond
    ((and (= (length p) 3)
          (symbolp (first p))
          (string-equal (symbol-name (first p)) "mut"))
     (list (second p) (third p) :mut))
    (t (list (first p) (second p)))))

(defun normalize-struct-fields (raw)
  "Accept several shapes for fields:
     ((f :t) (g :t))                  — list of pairs (preferred)
     ((mut f :t) (g :t))              — `mut` marks a mutable field
     (f :t g :t)                      — flat (no mut in this form)
     (((f :t) (g :t)))                — wrapped list of pairs
   Normalize to list of (name type [:mut]) entries."
  (cond
    ((null raw) nil)
    ;; wrapped: a single list-of-pairs
    ((and (= (length raw) 1) (consp (car raw)) (consp (caar raw)))
     (mapcar #'normalize-one-field (car raw)))
    ;; list of pairs
    ((consp (car raw))
     (mapcar #'normalize-one-field raw))
    ;; flat name/type
    (t (loop for (n ty) on raw by #'cddr collect (list n ty)))))

(defun emit-struct-decl (form out)
  "(defstruct Name (f :t) (g :t) ...) → typedef struct { ... } Name;"
  (let* ((name (second form))
         (fields (normalize-struct-fields (cddr form))))
    (format out "typedef struct {~%")
    (dolist (f fields)
      (format out "  ~a ~a;~%"
              (c-type (second f))
              (string-downcase (symbol-name (first f)))))
    (format out "} ~a;~%" (symbol-name name))))

(defun emit-struct-rc-fns (struct-name out)
  "Emit auto-derived <Name>_retain(void*) and <Name>_release(void*) for a
   struct that has rc-tracked fields. Both walk the fields and dispatch
   per-field via rc-fn-name. Pointer-typed fields and primitives are no-ops.
   Used both by ARC for struct values and by make_fn's release_state for
   lambda env structs (single fn signature serves both call sites)."
  (let* ((fields (gethash struct-name *struct-fields*))
         (rc-fields (remove-if-not (lambda (f) (ref-type-p (second f))) fields))
         (cname (symbol-name struct-name)))
    (when rc-fields
      (dolist (op '("retain" "release"))
        (format out "static void ~a_~a(void* _p) {~%" cname op)
        (format out "  ~a* s = (~a*)_p;~%" cname cname)
        (dolist (f rc-fields)
          (let* ((fty (second f))
                 (rc-call (rc-fn-name fty op))
                 (field-c (string-downcase (symbol-name (first f)))))
            (cond
              ((struct-rc-type-p fty)
               (format out "  ~a(&s->~a);~%" rc-call field-c))
              (t
               (format out "  ~a(s->~a);~%" rc-call field-c)))))
        (format out "}~%~%")))))

(defun emit-struct-rc-fn-decls (struct-name out)
  "Forward declarations so retain/release bodies can call into each other
   regardless of the order they were defined in the program."
  (let* ((fields (gethash struct-name *struct-fields*))
         (rc-fields (remove-if-not (lambda (f) (ref-type-p (second f))) fields))
         (cname (symbol-name struct-name)))
    (when rc-fields
      (format out "static void ~a_retain(void* _p);~%" cname)
      (format out "static void ~a_release(void* _p);~%" cname))))

(defun emit-include (form out)
  "(include \"foo.h\") → #include \"foo.h\"
   (include \"<stdio.h>\") → #include <stdio.h>"
  (let ((path (second form)))
    (if (and (>= (length path) 2)
             (char= (char path 0) #\<)
             (char= (char path (1- (length path))) #\>))
        (format out "#include ~a~%" path)
        (format out "#include \"~a\"~%" path))))

(defun emit-extern-proto (form out)
  "(extern name params ret-type) → extern Type name(Type a, Type b);"
  (let* ((name (second form))
         (params (normalize-extern-params (third form)))
         (ret-type (fourth form)))
    (format out "extern ~a ~a(~{~a~^, ~});~%"
            (c-type ret-type)
            (c-name name)
            (or (loop for p in params
                      collect (format nil "~a ~a"
                                      (c-type (second p))
                                      (c-name (first p))))
                '("void")))))

(defun emit-c-proto (fn out)
  (format out "~a ~a(~{~a~^, ~});~%"
          (c-type (ir-fn-ret-type fn))
          (c-name (ir-fn-name fn))
          (loop for p in (ir-fn-params fn)
                collect (format nil "~a ~a" (c-type (second p)) (c-name (first p))))))

(defun mark-uses-value-if-needed (fn)
  "Set *uses-value* if the IR touches :Value or :Fn (both live in value.h)."
  (flet ((flag (ty)
           (when (or (kw-name= ty "Value") (kw-name= ty "Fn"))
             (setf *uses-value* t))))
    (when (boundp '*uses-value*)
      (dolist (p (ir-fn-params fn)) (flag (second p)))
      (flag (ir-fn-ret-type fn))
      (dolist (b (ir-fn-blocks fn))
        (dolist (p (ir-block-params b)) (flag (second p)))
        (dolist (i (ir-block-instrs b)) (flag (ir-instr-type i)))))))

(defun emit-c-fn (fn &optional (out t))
  (mark-uses-value-if-needed fn)
  (let* ((*block-by-name* (make-hash-table))
         (*indent* 1)
         (*no-inline* (ir-fn-no-inline fn))
         (*inlinable* (build-inlinable fn))
         (*type-map* (build-type-map fn)))
    (dolist (b (ir-fn-blocks fn))
      (setf (gethash (ir-block-name b) *block-by-name*) b))
    (format out "~a ~a(" (c-type (ir-fn-ret-type fn)) (c-name (ir-fn-name fn)))
    (loop for p in (ir-fn-params fn) for first = t then nil
          do (unless first (format out ", "))
             (format out "~a ~a" (c-type (second p)) (c-name (first p))))
    (format out ") {~%")
    (dolist (b (ir-fn-blocks fn))
      (dolist (p (ir-block-params b))
        (unless (eq (second p) :unit)
          (format out "  ~a ~a;~%" (c-type (second p)) (c-name (first p))))))
    ;; If any block ends in :recur, emit label so the goto target exists.
    (when (loop for b in (ir-fn-blocks fn)
                thereis (eq (first (ir-block-term b)) :recur))
      (format out "  _recur_top: ;~%"))
    (emit-structured (gethash 'entry *block-by-name*) nil out)
    (format out "}~%")))

;;; --- structured emit: walk CFG as if/else/while ---

(defun emit-structured (blk until out)
  "Emit blk's instrs then walk its terminator. Stop when blk == until.
   Special case for :loop: don't emit the header's instrs here — the loop
   re-emits them inside its body so the cond re-evaluates each iteration."
  (when (and blk (not (eq (ir-block-name blk) until)))
    (let ((term (ir-block-term blk)))
      (unless (eq (first term) :loop)
        (dolist (i (ir-block-instrs blk))
          (unless (and (ir-instr-dst i) (gethash (ir-instr-dst i) *inlinable*))
            (emit-c-instr-indented i out))))
      (emit-c-term-structured blk term until out))))

(defun emit-death-release (v out)
  "Release an edge-dying variable. Same dispatch as a :release instr —
   the var's type (via *type-map*) picks val_/sysp_str_/Struct_ and
   whether it passes by &address."
  (let ((ty (gethash v *type-map*)))
    (ind out)
    (format out "~a(~:[~;&~]~a);~%"
            (rc-fn-name ty "release")
            (struct-rc-type-p ty)
            (c-name v))))

(defun emit-c-term-structured (blk term until out)
  (case (first term)
    (:ret      (ind out)
               (format out "return ~a;~%" (nameref (second term))))
    (:ret-unit (ind out) (format out "return;~%"))
    (:recur    (ind out) (format out "goto _recur_top;~%"))
    (:loop     (let ((c (second term))
                     (body-blk (third term))
                     (exit-blk (fourth term))
                     (header-instrs (ir-block-instrs blk)))
                 (ind out)
                 (format out "for (;;) {~%")
                 (let ((*indent* (1+ *indent*)))
                   ;; Re-evaluate cond each iteration: emit the header's
                   ;; instrs INSIDE the loop, then check.
                   (dolist (i header-instrs)
                     (unless (and (ir-instr-dst i)
                                  (gethash (ir-instr-dst i) *inlinable*))
                       (emit-c-instr-indented i out)))
                   (ind out)
                   (format out "if (!(~a)) break;~%" (cond-ref c))
                   (emit-structured (gethash body-blk *block-by-name*)
                                    (ir-block-name blk) out))
                 (ind out) (format out "}~%")
                 (emit-structured (gethash exit-blk *block-by-name*) until out)))
    (:jump     (let* ((dest-name (second term))
                      (args (third term))
                      (dest (gethash dest-name *block-by-name*)))
                 (loop for p in (ir-block-params dest)
                       for a in args do
                       (unless (eq (second p) :unit)
                         (ind out)
                         (format out "~a = ~a;~%" (c-name (first p)) (nameref a))))
                 (unless (eq dest-name until)
                   (emit-structured dest until out))))
    (:br       (let ((c (second term))
                     (tblk (br-then-blk term))
                     (eblk (br-else-blk term))
                     (jblk (br-join-blk term))
                     (t-d  (br-then-deaths term))
                     (e-d  (br-else-deaths term)))
                 (ind out)
                 (format out "if (~a) {~%" (cond-ref c))
                 (let ((*indent* (1+ *indent*)))
                   (dolist (v t-d) (emit-death-release v out))
                   (emit-structured (gethash tblk *block-by-name*) jblk out))
                 (ind out) (format out "} else {~%")
                 (let ((*indent* (1+ *indent*)))
                   (dolist (v e-d) (emit-death-release v out))
                   (emit-structured (gethash eblk *block-by-name*) jblk out))
                 (ind out) (format out "}~%")
                 (emit-structured (gethash jblk *block-by-name*) until out)))))

;;; --- per-instr emit ---

(defun emit-c-instr-indented (i out)
  (ind out) (emit-c-instr-body i out))

(defun emit-c-instr-body (i out)
  (let ((dst (and (ir-instr-dst i) (c-name (ir-instr-dst i))))
        (ty (c-type (ir-instr-type i))))
    (case (ir-instr-op i)
      (:const (format out "~a ~a = ~a;~%" ty dst (first (ir-instr-args i))))
      (:copy  (format out "~a ~a = ~a;~%" ty dst (nameref (first (ir-instr-args i))))
              (when (ref-type-p (ir-instr-type i))
                (ind out)
                (format out "~a(~:[~;&~]~a);~%"
                        (rc-fn-name (ir-instr-type i) "retain")
                        (struct-rc-type-p (ir-instr-type i))
                        dst)))
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
      (:cstr-lit (let ((s (first (ir-instr-args i))))
                   (format out "const char* ~a = \"~a\";~%"
                           dst (c-escape-string s))))
      (:release (format out "~a(~:[~;&~]~a);~%"
                        (rc-fn-name (ir-instr-type i) "release")
                        (struct-rc-type-p (ir-instr-type i))
                        (c-name (first (ir-instr-args i)))))
      (:retain  (format out "~a(~:[~;&~]~a);~%"
                        (rc-fn-name (ir-instr-type i) "retain")
                        (struct-rc-type-p (ir-instr-type i))
                        (c-name (first (ir-instr-args i)))))
      (:set     (let* ((args (ir-instr-args i))
                       (tgt  (first args))
                       (src  (second args))
                       (ity  (ir-instr-type i)))
                  (cond
                    ((ref-type-p ity)
                     ;; release old; assign; retain new. Source's own ARC
                     ;; release at last-use covers its end-of-scope.
                     (format out "~a(~:[~;&~]~a);~%"
                             (rc-fn-name ity "release") (struct-rc-type-p ity)
                             (c-name tgt))
                     (ind out)
                     (format out "~a = ~a;~%" (c-name tgt) (nameref src))
                     (ind out)
                     (format out "~a(~:[~;&~]~a);~%"
                             (rc-fn-name ity "retain") (struct-rc-type-p ity)
                             (c-name tgt)))
                    (t
                     (format out "~a = ~a;~%" (c-name tgt) (nameref src))))))
      (:unary   (let ((args (ir-instr-args i)))
                  (format out "~a ~a = ~a~a;~%"
                          ty dst (first args) (nameref (second args)))))
      (:addr-of (format out "~a ~a = &~a;~%"
                        ty dst (c-name (first (ir-instr-args i)))))
      (:cast    (let ((args (ir-instr-args i)))
                  (format out "~a ~a = (~a)~a;~%"
                          ty dst (c-type (first args)) (nameref (second args)))))
      (:deref   (format out "~a ~a = *~a;~%" ty dst (nameref (first (ir-instr-args i)))))
      (:ptr-ref (let ((args (ir-instr-args i)))
                  (format out "~a ~a = ~a[~a];~%"
                          ty dst (nameref (first args)) (nameref (second args)))))
      (:ptr-set (let ((args (ir-instr-args i)))
                  (format out "*~a = ~a;~%"
                          (nameref (first args)) (nameref (second args)))))
      (:ptr-set-at (let ((args (ir-instr-args i)))
                     (format out "~a[~a] = ~a;~%"
                             (nameref (first args)) (nameref (second args))
                             (nameref (third args)))))
      (:struct-init (let* ((args (ir-instr-args i))
                           (struct-name (first args))
                           (vals (rest args)))
                      (format out "~a ~a = (~a){~{~a~^, ~}};~%"
                              (symbol-name struct-name) dst
                              (symbol-name struct-name)
                              (mapcar #'nameref vals))))
      (:field-get (let ((args (ir-instr-args i))
                        (fty (ir-instr-type i)))
                    (format out "~a ~a = ~a.~a;~%"
                            ty dst (nameref (first args))
                            (string-downcase (symbol-name (second args))))
                    ;; rc'd field: copy creates a second co-owner. The struct
                    ;; itself still holds its share; the new local needs +1 so
                    ;; both can be released independently.
                    (when (ref-type-p fty)
                      (ind out)
                      (format out "~a(~:[~;&~]~a);~%"
                              (rc-fn-name fty "retain")
                              (struct-rc-type-p fty)
                              dst))))
      (:field-set (let* ((args (ir-instr-args i))
                         (obj (nameref (first args)))
                         (fld (string-downcase (symbol-name (second args))))
                         (val (nameref (third args)))
                         (fty (ir-instr-type i)))
                    (cond
                      ;; rc'd field: release the overwritten value, store,
                      ;; retain the new one. (:unit-typed stores — e.g. lambda
                      ;; env construction into fresh memory — skip this.)
                      ((ref-type-p fty)
                       (format out "~a(~:[~;&~]~a.~a);~%"
                               (rc-fn-name fty "release") (struct-rc-type-p fty) obj fld)
                       (ind out)
                       (format out "~a.~a = ~a;~%" obj fld val)
                       (ind out)
                       (format out "~a(~:[~;&~]~a.~a);~%"
                               (rc-fn-name fty "retain") (struct-rc-type-p fty) obj fld))
                      (t (format out "~a.~a = ~a;~%" obj fld val)))))
      (:field-get-ptr (let ((args (ir-instr-args i))
                            (fty (ir-instr-type i)))
                        (format out "~a ~a = ~a->~a;~%"
                                ty dst (nameref (first args))
                                (string-downcase (symbol-name (second args))))
                        (when (ref-type-p fty)
                          (ind out)
                          (format out "~a(~:[~;&~]~a);~%"
                                  (rc-fn-name fty "retain")
                                  (struct-rc-type-p fty)
                                  dst))))
      (:field-set-ptr (let* ((args (ir-instr-args i))
                             (obj (nameref (first args)))
                             (fld (string-downcase (symbol-name (second args))))
                             (val (nameref (third args)))
                             (fty (ir-instr-type i)))
                        (cond
                          ((ref-type-p fty)
                           (format out "~a(~:[~;&~]~a->~a);~%"
                                   (rc-fn-name fty "release") (struct-rc-type-p fty) obj fld)
                           (ind out)
                           (format out "~a->~a = ~a;~%" obj fld val)
                           (ind out)
                           (format out "~a(~:[~;&~]~a->~a);~%"
                                   (rc-fn-name fty "retain") (struct-rc-type-p fty) obj fld))
                          (t (format out "~a->~a = ~a;~%" obj fld val)))))
      (:sizeof   (format out "~a ~a = sizeof(~a);~%"
                         ty dst (symbol-name (first (ir-instr-args i)))))
      (:fn-addr  (format out "~a ~a = (void*)&~a;~%"
                         ty dst (c-name (first (ir-instr-args i)))))
      (:fn-call  (let* ((args (ir-instr-args i))
                        (fn-ty (first args))
                        (arg-tys (second fn-ty))
                        (ret-ty  (third fn-ty))
                        (f (second args))
                        (call-args (cddr args))
                        (cast-type (with-output-to-string (s)
                                     (format s "~a(*)(void*" (c-type ret-ty))
                                     (dolist (at arg-tys)
                                       (format s ", ~a" (c-type at)))
                                     (write-char #\) s))))
                   (format out "~a ~a = ((~a)~a->invoke)(~a->state~{, ~a~});~%"
                           (c-type ret-ty) dst cast-type
                           (c-name f) (c-name f)
                           (mapcar #'nameref call-args)))))))
