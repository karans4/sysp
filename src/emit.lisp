;;;; C emission. Structured (no labels/gotos), driven by the CFG.

(in-package :sysp-ir)

;;; --- name / type formatting ---

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
    ((eq ty :ptr-void) "void*")
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
  (let ((str (string-downcase (symbol-name s))))
    (substitute #\_ #\- str)))

;;; --- emitter state ---

(defvar *block-by-name*)
(defvar *indent*)

(defun ind (out) (loop repeat *indent* do (write-string "  " out)))

;;; --- top-level fn / proto emit ---

(defun normalize-struct-fields (raw)
  "Accept several shapes for fields:
     ((f :t) (g :t))                  — list of pairs (preferred)
     (f :t g :t)                      — flat
     (((f :t) (g :t)))                — wrapped list of pairs
   Normalize to list of (name type) pairs."
  (cond
    ((null raw) nil)
    ;; wrapped: a single list-of-pairs
    ((and (= (length raw) 1) (consp (car raw)) (consp (caar raw)))
     (mapcar (lambda (p) (list (first p) (second p))) (car raw)))
    ;; list of pairs
    ((consp (car raw))
     (mapcar (lambda (p) (list (first p) (second p))) raw))
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
    ;; Pre-declare block-params (phi sinks; assigned from each :jump source).
    (dolist (b (ir-fn-blocks fn))
      (dolist (p (ir-block-params b))
        (format out "  ~a ~a;~%" (c-type (second p)) (c-name (first p)))))
    (emit-structured (gethash 'entry *block-by-name*) nil out)
    (format out "}~%")))

;;; --- structured emit: walk CFG as if/else/while ---

(defun emit-structured (blk until out)
  "Emit blk's instrs then walk its terminator. Stop when blk == until."
  (when (and blk (not (eq (ir-block-name blk) until)))
    (dolist (i (ir-block-instrs blk))
      (unless (and (ir-instr-dst i) (gethash (ir-instr-dst i) *inlinable*))
        (emit-c-instr-indented i out)))
    (emit-c-term-structured blk (ir-block-term blk) until out)))

(defun emit-c-term-structured (blk term until out)
  (case (first term)
    (:ret      (ind out)
               (format out "return ~a;~%" (nameref (second term))))
    (:ret-unit (ind out) (format out "return;~%"))
    (:loop     (let ((c (second term))
                     (body-blk (third term))
                     (exit-blk (fourth term)))
                 (ind out)
                 (format out "while (~a) {~%" (nameref c))
                 (let ((*indent* (1+ *indent*)))
                   (emit-structured (gethash body-blk *block-by-name*)
                                    (ir-block-name blk) out))
                 (ind out) (format out "}~%")
                 (emit-structured (gethash exit-blk *block-by-name*) until out)))
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
                (format out "sysp_str_retain(~a);~%" dst)))
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
      (:release (format out "sysp_str_release(~a);~%"
                        (c-name (first (ir-instr-args i)))))
      (:retain  (format out "sysp_str_retain(~a);~%"
                        (c-name (first (ir-instr-args i)))))
      (:set     (let ((args (ir-instr-args i)))
                  (format out "~a = ~a;~%"
                          (c-name (first args))
                          (nameref (second args)))))
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
      (:field-get (let ((args (ir-instr-args i)))
                    (format out "~a ~a = ~a.~a;~%"
                            ty dst (nameref (first args))
                            (string-downcase (symbol-name (second args))))))
      (:field-set (let ((args (ir-instr-args i)))
                    (format out "~a.~a = ~a;~%"
                            (nameref (first args))
                            (string-downcase (symbol-name (second args)))
                            (nameref (third args)))))
      (:field-get-ptr (let ((args (ir-instr-args i)))
                        (format out "~a ~a = ~a->~a;~%"
                                ty dst (nameref (first args))
                                (string-downcase (symbol-name (second args))))))
      (:field-set-ptr (let ((args (ir-instr-args i)))
                        (format out "~a->~a = ~a;~%"
                                (nameref (first args))
                                (string-downcase (symbol-name (second args)))
                                (nameref (third args))))))))
