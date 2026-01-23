;;;; sysp.lisp — Bootstrap compiler for Systems Lisp
;;;; Compiles .sysp files to C

(defpackage :sysp
  (:use :cl))
(in-package :sysp)

;;; === Types ===

(defstruct sysp-type
  (kind nil) ; :int :float :bool :void :str :char :struct :vector :tuple :fn :ptr :unknown
  (name nil)
  (params nil)) ; type params (element types for vector/tuple, arg+ret for fn, pointee for ptr)

(defun make-int-type () (make-sysp-type :kind :int))
(defun make-float-type () (make-sysp-type :kind :float))
(defun make-void-type () (make-sysp-type :kind :void))
(defun make-bool-type () (make-sysp-type :kind :bool))
(defun make-str-type () (make-sysp-type :kind :str))
(defun make-char-type () (make-sysp-type :kind :char))
(defun make-u8-type () (make-sysp-type :kind :u8))
(defun make-f32-type () (make-sysp-type :kind :f32))

(defun make-ptr-type (pointee)
  (make-sysp-type :kind :ptr :params (list pointee)))

(defun make-vector-type (elem-type)
  (make-sysp-type :kind :vector :params (list elem-type)))

(defun make-tuple-type (elem-types)
  (make-sysp-type :kind :tuple :params elem-types))

(defun make-fn-type (arg-types ret-type)
  (make-sysp-type :kind :fn :params (append arg-types (list ret-type))))

(defun make-array-type (elem-type size)
  (make-sysp-type :kind :array :params (list elem-type size)))

(defun make-enum-type (name)
  (make-sysp-type :kind :enum :name name))

(defun make-struct-type (name)
  (make-sysp-type :kind :struct :name name))

(defun fn-type-ret (ft)
  (car (last (sysp-type-params ft))))

(defun fn-type-args (ft)
  (butlast (sysp-type-params ft)))

(defun type-equal-p (a b)
  (and (eq (sysp-type-kind a) (sysp-type-kind b))
       (equal (sysp-type-name a) (sysp-type-name b))
       (= (length (sysp-type-params a)) (length (sysp-type-params b)))
       (every #'type-equal-p
              (sysp-type-params a) (sysp-type-params b))))

;;; === Environment ===

(defstruct env
  (bindings nil)  ; alist of (name . type)
  (parent nil))

(defun env-lookup (env name)
  (if (null env) nil
      (let ((found (assoc name (env-bindings env) :test #'equal)))
        (if found (cdr found)
            (env-lookup (env-parent env) name)))))

(defun env-bind (env name type)
  (push (cons name type) (env-bindings env))
  env)

;;; === Global State ===

(defvar *structs* (make-hash-table :test 'equal))
(defvar *enums* (make-hash-table :test 'equal))  ; name -> list of (variant-name . value)
(defvar *functions* nil)
(defvar *struct-defs* nil)
(defvar *lambda-counter* 0)
(defvar *temp-counter* 0)
(defvar *generated-types* (make-hash-table :test 'equal))
(defvar *type-decls* nil)
(defvar *forward-decls* nil)
(defvar *global-env* (make-env))
(defvar *string-literals* nil)  ; collected string constants
(defvar *includes* nil)         ; extra #includes

(defun lookup-enum-variant (name)
  "If name is an enum variant, return (enum-name . value). Else nil."
  (maphash (lambda (enum-name variants)
             (dolist (v variants)
               (when (string= (car v) name)
                 (return-from lookup-enum-variant (cons enum-name (cdr v))))))
           *enums*)
  nil)

;;; === Parsing ===

(defun make-sysp-readtable ()
  (let ((rt (copy-readtable nil)))
    (setf (readtable-case rt) :preserve)
    (set-syntax-from-char #\, #\Space rt)
    (set-macro-character #\[
      (lambda (stream char)
        (declare (ignore char))
        (read-delimited-list #\] stream t))
      nil rt)
    (set-syntax-from-char #\] #\) rt)
    rt))

(defvar *sysp-readtable* (make-sysp-readtable))

(defun read-sysp-file (path)
  (let ((*readtable* *sysp-readtable*))
    (with-open-file (in path :direction :input)
      (let ((forms nil)
            (eof (gensym)))
        (loop for form = (read in nil eof)
              until (eq form eof)
              do (push form forms))
        (nreverse forms)))))

;;; === Type Annotation Parsing ===

(defun parse-type-annotation (sym)
  (let ((name (string-downcase (symbol-name sym))))
    (cond
      ((string= name "int") (make-int-type))
      ((string= name "float") (make-float-type))
      ((string= name "bool") (make-bool-type))
      ((string= name "void") (make-void-type))
      ((string= name "str") (make-str-type))
      ((string= name "char") (make-char-type))
      ((string= name "u8") (make-u8-type))
      ((string= name "f32") (make-f32-type))
      ;; Pointer shorthand: :ptr-int, :ptr-float, etc.
      ((and (> (length name) 4) (string= (subseq name 0 4) "ptr-"))
       (make-ptr-type (parse-type-annotation
                       (intern (string-upcase (subseq name 4)) :keyword))))
      (t (let ((sname (symbol-name sym)))
           (cond
             ((gethash sname *structs*) (make-struct-type sname))
             ((gethash sname *enums*) (make-enum-type sname))
             (t (make-sysp-type :kind :unknown :name sname))))))))


;;; === C Type Emission ===

(defun type-to-c (tp)
  (case (sysp-type-kind tp)
    (:int "int")
    (:float "double")
    (:bool "int")
    (:void "void")
    (:str "const char*")
    (:char "char")
    (:u8 "unsigned char")
    (:f32 "float")
    (:ptr (format nil "~a*" (type-to-c (first (sysp-type-params tp)))))
    (:struct (sysp-type-name tp))
    (:enum (sysp-type-name tp))
    (:array (type-to-c (first (sysp-type-params tp))))  ; array decl handled specially
    (:vector (vector-type-c-name tp))
    (:tuple (tuple-type-c-name tp))
    (:fn (fn-type-c-name tp))
    (otherwise "int")))

(defun mangle-type-name (tp)
  (case (sysp-type-kind tp)
    (:int "int")
    (:float "float")
    (:bool "bool")
    (:str "str")
    (:char "char")
    (:u8 "u8")
    (:f32 "f32")
    (:ptr (format nil "ptr_~a" (mangle-type-name (first (sysp-type-params tp)))))
    (:struct (sysp-type-name tp))
    (:enum (sysp-type-name tp))
    (:array (format nil "arr_~a_~a" (mangle-type-name (first (sysp-type-params tp)))
                    (second (sysp-type-params tp))))
    (:vector (vector-type-c-name tp))
    (:tuple (tuple-type-c-name tp))
    (:fn (fn-type-c-name tp))
    (otherwise "unknown")))

(defun vector-type-c-name (tp)
  (let* ((elem (first (sysp-type-params tp)))
         (name (format nil "Vector_~a" (mangle-type-name elem))))
    (ensure-vector-type name elem)
    name))

(defun tuple-type-c-name (tp)
  (let* ((elems (sysp-type-params tp))
         (name (format nil "Tuple_~{~a~^_~}" (mapcar #'mangle-type-name elems))))
    (ensure-tuple-type name elems)
    name))

(defun fn-type-c-name (tp)
  (let* ((args (fn-type-args tp))
         (ret (fn-type-ret tp))
         (name (format nil "Fn_~{~a~^_~}_~a"
                       (or (mapcar #'mangle-type-name args) '("void"))
                       (mangle-type-name ret))))
    (ensure-fn-type name args ret)
    name))

;;; === Generated Type Structs ===

(defun ensure-vector-type (name elem-type)
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    (push (format nil "typedef struct { ~a* data; int len; int cap; } ~a;~%"
                  (type-to-c elem-type) name)
          *type-decls*)))

(defun ensure-tuple-type (name elem-types)
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    (let ((fields (loop for tp in elem-types
                        for i from 0
                        collect (format nil "  ~a _~d;" (type-to-c tp) i))))
      (push (format nil "typedef struct {~%~{~a~%~}} ~a;~%" fields name)
            *type-decls*))))

(defun ensure-fn-type (name arg-types ret-type)
  (unless (gethash name *generated-types*)
    (setf (gethash name *generated-types*) t)
    (let ((arg-str (if arg-types
                       (format nil "~{~a~^, ~}" (mapcar #'type-to-c arg-types))
                       "void")))
      (push (format nil "typedef ~a (*~a)(~a);~%"
                    (type-to-c ret-type) name arg-str)
            *type-decls*))))

;;; === Expression Compilation ===

(defun compile-expr (form env)
  "Compile an expression, return (values c-string type)"
  (cond
    ((null form) (values "0" (make-int-type)))
    ((integerp form) (values (format nil "~d" form) (make-int-type)))
    ((floatp form) (values (format nil "~f" form) (make-float-type)))
    ((stringp form) (values (format nil "~s" form) (make-str-type)))
    ((symbolp form)
     (let ((name (string form)))
       (cond
         ((string-equal name "true") (values "1" (make-bool-type)))
         ((string-equal name "false") (values "0" (make-bool-type)))
         ((string-equal name "null") (values "NULL" (make-ptr-type (make-void-type))))
         (t (let ((tp (env-lookup env name)))
              (if tp
                  (values (sanitize-name name) tp)
                  ;; Check if it's an enum variant
                  (let ((enum-info (lookup-enum-variant name)))
                    (if enum-info
                        (values (sanitize-name name)
                                (make-enum-type (car enum-info)))
                        (values (sanitize-name name)
                                (make-sysp-type :kind :unknown))))))))))
    ((listp form) (compile-list form env))
    (t (values (format nil "~a" form) (make-sysp-type :kind :unknown)))))

(defun sanitize-name (name)
  (let ((result (substitute #\_ #\- name)))
    ;; Handle names that are C keywords
    (if (member result '("int" "float" "double" "char" "void" "struct"
                         "if" "else" "while" "for" "return" "break"
                         "continue" "switch" "case" "default" "do"
                         "typedef" "static" "const" "sizeof" "union"
                         "enum" "extern" "register" "volatile" "goto")
               :test #'string-equal)
        (concatenate 'string result "_")
        result)))

(defun sym= (sym name)
  (and (symbolp sym) (string-equal (symbol-name sym) name)))

(defun compile-list (form env)
  (let ((head (first form)))
    (cond
      ;; Arithmetic
      ((sym= head "+") (compile-binop "+" form env))
      ((sym= head "-")
       (if (= (length form) 2)
           (compile-unary-minus form env)
           (compile-binop "-" form env)))
      ((sym= head "*") (compile-binop "*" form env))
      ((sym= head "/") (compile-binop "/" form env))
      ((sym= head "%") (compile-binop "%" form env))
      ((sym= head "mod") (compile-binop "%" form env))
      ;; Comparison
      ((sym= head "<") (compile-binop "<" form env))
      ((sym= head ">") (compile-binop ">" form env))
      ((sym= head "<=") (compile-binop "<=" form env))
      ((sym= head ">=") (compile-binop ">=" form env))
      ((sym= head "==") (compile-binop "==" form env))
      ((sym= head "!=") (compile-binop "!=" form env))
      ;; Logical (variadic)
      ((sym= head "and") (compile-logical "&&" form env))
      ((sym= head "or") (compile-logical "||" form env))
      ((sym= head "not") (compile-not form env))
      ;; Bitwise
      ((sym= head "bit-and") (compile-binop "&" form env))
      ((sym= head "bit-or") (compile-binop "|" form env))
      ((sym= head "bit-xor") (compile-binop "^" form env))
      ((sym= head "bit-not") (compile-bit-not form env))
      ((sym= head "shl") (compile-binop "<<" form env))
      ((sym= head "shr") (compile-binop ">>" form env))
      ;; Control flow (as expression)
      ((sym= head "if") (compile-if-expr form env))
      ((sym= head "do") (compile-do-expr form env))
      ((sym= head "cond") (compile-cond-expr form env))
      ;; Data structures
      ((sym= head "get") (compile-get form env))
      ((sym= head "vector") (compile-vector form env))
      ((sym= head "vector-ref") (compile-vector-ref form env))
      ((sym= head "vector-set!") (compile-vector-set form env))
      ((sym= head "vector-push!") (compile-vector-push form env))
      ((sym= head "vector-len") (compile-vector-len form env))
      ((sym= head "tuple") (compile-tuple form env))
      ((sym= head "tuple-ref") (compile-tuple-ref form env))
      ((sym= head "lambda") (compile-lambda form env))
      ;; Arrays
      ((sym= head "array-ref") (compile-array-ref form env))
      ((sym= head "array-set!") (compile-array-set form env))
      ((sym= head "make-array") (compile-make-array form env))
      ;; Assignment (as expression)
      ((sym= head "set!") (compile-set-expr form env))
      ;; Pointer ops
      ((sym= head "addr-of") (compile-addr-of form env))
      ((sym= head "deref") (compile-deref form env))
      ;; Type ops
      ((sym= head "cast") (compile-cast form env))
      ((sym= head "sizeof") (compile-sizeof form env))
      ;; Otherwise: function/constructor call
      (t (compile-call form env)))))

(defun compile-binop (op form env)
  (multiple-value-bind (lhs lt) (compile-expr (second form) env)
    (multiple-value-bind (rhs rt) (compile-expr (third form) env)
      (declare (ignore rt))
      (let ((result-type
              (cond
                ((member op '("<" ">" "<=" ">=" "==" "!=" "&&" "||") :test #'string=)
                 (make-bool-type))
                ((member op '("&" "|" "^" "<<" ">>") :test #'string=)
                 (make-int-type))
                (t lt))))
        (values (format nil "(~a ~a ~a)" lhs op rhs) result-type)))))

(defun compile-logical (op form env)
  "(and a b c ...) or (or a b c ...) — variadic logical"
  (let* ((args (rest form))
         (compiled (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args)))
    (if (= (length compiled) 1)
        (values (first compiled) (make-bool-type))
        (values (format nil "(~a)"
                        (reduce (lambda (acc x) (format nil "~a ~a ~a" acc op x))
                                compiled))
                (make-bool-type)))))

(defun compile-unary-minus (form env)
  (multiple-value-bind (val tp) (compile-expr (second form) env)
    (values (format nil "(-~a)" val) tp)))

(defun compile-not (form env)
  (multiple-value-bind (val tp) (compile-expr (second form) env)
    (declare (ignore tp))
    (values (format nil "(!~a)" val) (make-bool-type))))

(defun compile-bit-not (form env)
  (multiple-value-bind (val tp) (compile-expr (second form) env)
    (declare (ignore tp))
    (values (format nil "(~~~a)" val) (make-int-type))))

(defun compile-if-expr (form env)
  "(if cond then else) -> ternary"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (multiple-value-bind (then-code then-type) (compile-expr (third form) env)
      (if (fourth form)
          (multiple-value-bind (else-code et) (compile-expr (fourth form) env)
            (declare (ignore et))
            (values (format nil "(~a ? ~a : ~a)" cond-code then-code else-code)
                    then-type))
          (values (format nil "(~a ? ~a : 0)" cond-code then-code)
                  then-type)))))

(defun compile-do-expr (form env)
  "(do expr...) -> GNU statement expression, value is last"
  (let* ((exprs (rest form))
         (new-env (make-env :parent env)))
    (if (= (length exprs) 1)
        (compile-expr (first exprs) new-env)
        (let* ((stmts (compile-body (butlast exprs) new-env))
               (last-expr (car (last exprs))))
          (multiple-value-bind (last-code last-type) (compile-expr last-expr new-env)
            (values (format nil "({ ~{~a ~}~a; })"
                            (mapcar (lambda (s) (format nil "~a " (string-trim '(#\Space) s))) stmts)
                            last-code)
                    last-type))))))

(defun compile-cond-expr (form env)
  "(cond [test1 expr1] [test2 expr2] ... [else exprN]) -> nested ternary"
  (let ((clauses (rest form)))
    (compile-cond-clauses clauses env)))

(defun compile-cond-clauses (clauses env)
  (if (null clauses)
      (values "0" (make-int-type))
      (let ((clause (first clauses)))
        (if (and (symbolp (first clause)) (sym= (first clause) "else"))
            (compile-expr (second clause) env)
            (multiple-value-bind (test-code tt) (compile-expr (first clause) env)
              (declare (ignore tt))
              (multiple-value-bind (then-code then-type) (compile-expr (second clause) env)
                (multiple-value-bind (rest-code rt) (compile-cond-clauses (rest clauses) env)
                  (declare (ignore rt))
                  (values (format nil "(~a ? ~a : ~a)" test-code then-code rest-code)
                          then-type))))))))

(defun compile-get (form env)
  "(get struct field)"
  (multiple-value-bind (obj tp) (compile-expr (second form) env)
    (let* ((field-name (string (third form)))
           (field-type (if (and (eq (sysp-type-kind tp) :struct)
                                (gethash (sysp-type-name tp) *structs*))
                           (let ((fields (gethash (sysp-type-name tp) *structs*)))
                             (cdr (assoc field-name fields :test #'equal)))
                           (make-int-type))))
      (values (format nil "~a.~a" obj (sanitize-name field-name))
              (or field-type (make-int-type))))))

(defun compile-vector (form env)
  "(vector elem ...)"
  (let* ((elems (rest form))
         (compiled (mapcar (lambda (e) (multiple-value-list (compile-expr e env))) elems))
         (elem-type (second (first compiled)))
         (vec-type (make-vector-type elem-type))
         (c-name (type-to-c vec-type))
         (n (length elems)))
    (values (format nil "({ ~a* _tmp = malloc(sizeof(~a) * ~d); ~{_tmp[~d] = ~a; ~}~a _v = {_tmp, ~d, ~d}; _v; })"
                    (type-to-c elem-type) (type-to-c elem-type) n
                    (loop for i from 0
                          for c in compiled
                          append (list i (first c)))
                    c-name n n)
            vec-type)))

(defun compile-vector-ref (form env)
  "(vector-ref vec idx)"
  (multiple-value-bind (vec vt) (compile-expr (second form) env)
    (multiple-value-bind (idx it) (compile-expr (third form) env)
      (declare (ignore it))
      (let ((elem-type (if (eq (sysp-type-kind vt) :vector)
                           (first (sysp-type-params vt))
                           (make-int-type))))
        (values (format nil "~a.data[~a]" vec idx) elem-type)))))

(defun compile-vector-set (form env)
  "(vector-set! vec idx val)"
  (multiple-value-bind (vec vt) (compile-expr (second form) env)
    (multiple-value-bind (idx it) (compile-expr (third form) env)
      (declare (ignore it))
      (multiple-value-bind (val val-type) (compile-expr (fourth form) env)
        (declare (ignore val-type))
        (let ((elem-type (if (eq (sysp-type-kind vt) :vector)
                             (first (sysp-type-params vt))
                             (make-int-type))))
          (values (format nil "(~a.data[~a] = ~a)" vec idx val) elem-type))))))

(defun compile-vector-push (form env)
  "(vector-push! vec val) — push to dynamic vector"
  (multiple-value-bind (vec vt) (compile-expr (second form) env)
    (multiple-value-bind (val val-type) (compile-expr (third form) env)
      (declare (ignore val-type))
      (let ((elem-type (if (eq (sysp-type-kind vt) :vector)
                           (first (sysp-type-params vt))
                           (make-int-type))))
        (pushnew "string.h" *includes* :test #'string=)
        (values (format nil "({ if (~a.len >= ~a.cap) { ~a.cap = ~a.cap ? ~a.cap * 2 : 4; ~a.data = realloc(~a.data, sizeof(~a) * ~a.cap); } ~a.data[~a.len++] = ~a; })"
                        vec vec vec vec vec vec vec
                        (type-to-c elem-type) vec vec vec val)
                (make-void-type))))))

(defun compile-vector-len (form env)
  "(vector-len vec)"
  (multiple-value-bind (vec vt) (compile-expr (second form) env)
    (declare (ignore vt))
    (values (format nil "~a.len" vec) (make-int-type))))

(defun compile-tuple (form env)
  "(tuple elem ...)"
  (let* ((elems (rest form))
         (compiled (mapcar (lambda (e) (multiple-value-list (compile-expr e env))) elems))
         (elem-types (mapcar #'second compiled))
         (tup-type (make-tuple-type elem-types))
         (c-name (type-to-c tup-type)))
    (values (format nil "(~a){~{~a~^, ~}}"
                    c-name (mapcar #'first compiled))
            tup-type)))

(defun compile-tuple-ref (form env)
  "(tuple-ref tup idx)"
  (multiple-value-bind (tup tt) (compile-expr (second form) env)
    (let* ((idx (third form))
           (elem-type (if (eq (sysp-type-kind tt) :tuple)
                          (nth idx (sysp-type-params tt))
                          (make-int-type))))
      (values (format nil "~a._~d" tup idx) elem-type))))

(defun compile-array-ref (form env)
  "(array-ref arr idx)"
  (multiple-value-bind (arr at) (compile-expr (second form) env)
    (multiple-value-bind (idx it) (compile-expr (third form) env)
      (declare (ignore it))
      (let ((elem-type (if (eq (sysp-type-kind at) :array)
                           (first (sysp-type-params at))
                           (make-int-type))))
        (values (format nil "~a[~a]" arr idx) elem-type)))))

(defun compile-array-set (form env)
  "(array-set! arr idx val)"
  (multiple-value-bind (arr at) (compile-expr (second form) env)
    (multiple-value-bind (idx it) (compile-expr (third form) env)
      (declare (ignore it))
      (multiple-value-bind (val vt) (compile-expr (fourth form) env)
        (declare (ignore vt))
        (let ((elem-type (if (eq (sysp-type-kind at) :array)
                             (first (sysp-type-params at))
                             (make-int-type))))
          (values (format nil "(~a[~a] = ~a)" arr idx val) elem-type))))))

(defun compile-make-array (form env)
  "(make-array :type size) — stack-allocated zero-init array"
  (declare (ignore env))
  (let* ((elem-type (parse-type-annotation (second form)))
         (size (third form))
         (arr-type (make-array-type elem-type size)))
    (values (format nil "{0}" ) arr-type)))

(defun compile-lambda (form env)
  "(lambda [params...] :ret-type body...)"
  (let* ((params-raw (second form))
         (rest-forms (cddr form))
         (params (parse-params params-raw))
         (ret-annotation (when (keywordp (first rest-forms))
                           (prog1 (parse-type-annotation (first rest-forms))
                             (setf rest-forms (cdr rest-forms)))))
         (body-forms rest-forms)
         (lambda-name (format nil "_lambda_~d" (incf *lambda-counter*)))
         (fn-env (make-env :parent env)))
    (dolist (p params)
      (env-bind fn-env (first p) (second p)))
    ;; Multi-expression body: all but last are statements, last is return value
    (let* ((all-but-last (butlast body-forms))
           (last-form (car (last body-forms))))
      (multiple-value-bind (last-code last-type) (compile-expr last-form fn-env)
        (let* ((ret-type (or ret-annotation last-type))
               (arg-types (mapcar #'second params))
               (fn-type (make-fn-type arg-types ret-type))
               (param-str (format nil "~{~a~^, ~}"
                                 (mapcar (lambda (p)
                                           (format nil "~a ~a"
                                                   (type-to-c (second p))
                                                   (sanitize-name (first p))))
                                         params)))
               (body-stmts (when all-but-last (compile-body all-but-last fn-env))))
          (push (format nil "static ~a ~a(~a) {~%~{~a~%~}  return ~a;~%}~%"
                        (type-to-c ret-type) lambda-name
                        (if params param-str "void")
                        (or body-stmts nil)
                        last-code)
                *functions*)
          (values lambda-name fn-type))))))

(defun compile-set-expr (form env)
  "(set! name expr) as expression"
  (let ((target (second form)))
    (cond
      ;; (set! (get struct field) val) -> struct.field = val
      ((and (listp target) (sym= (first target) "get"))
       (multiple-value-bind (obj tp) (compile-expr (second target) env)
         (declare (ignore tp))
         (let ((field (string (third target))))
           (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
             (values (format nil "(~a.~a = ~a)" obj (sanitize-name field) val-code)
                     val-type)))))
      ;; (set! (deref ptr) val) -> *ptr = val
      ((and (listp target) (sym= (first target) "deref"))
       (multiple-value-bind (ptr-code pt) (compile-expr (second target) env)
         (declare (ignore pt))
         (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
           (values (format nil "(*~a = ~a)" ptr-code val-code) val-type))))
      ;; (set! (vector-ref vec idx) val) -> vec.data[idx] = val
      ((and (listp target) (sym= (first target) "vector-ref"))
       (multiple-value-bind (vec-code vt) (compile-expr (second target) env)
         (declare (ignore vt))
         (multiple-value-bind (idx-code it) (compile-expr (third target) env)
           (declare (ignore it))
           (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
             (values (format nil "(~a.data[~a] = ~a)" vec-code idx-code val-code)
                     val-type)))))
      ;; simple variable
      (t (let ((name (string target)))
           (multiple-value-bind (val-code val-type) (compile-expr (third form) env)
             (values (format nil "(~a = ~a)" (sanitize-name name) val-code)
                     val-type)))))))

(defun compile-addr-of (form env)
  "(addr-of expr)"
  (multiple-value-bind (code tp) (compile-expr (second form) env)
    (values (format nil "(&~a)" code) (make-ptr-type tp))))

(defun compile-deref (form env)
  "(deref ptr)"
  (multiple-value-bind (code tp) (compile-expr (second form) env)
    (let ((pointee (if (eq (sysp-type-kind tp) :ptr)
                       (first (sysp-type-params tp))
                       (make-int-type))))
      (values (format nil "(*~a)" code) pointee))))

(defun compile-cast (form env)
  "(cast :type expr)"
  (let ((target-type (parse-type-annotation (second form))))
    (multiple-value-bind (code tp) (compile-expr (third form) env)
      (declare (ignore tp))
      (values (format nil "((~a)~a)" (type-to-c target-type) code) target-type))))

(defun compile-sizeof (form env)
  "(sizeof :type) or (sizeof expr)"
  (declare (ignore env))
  (let ((arg (second form)))
    (if (keywordp arg)
        (values (format nil "sizeof(~a)" (type-to-c (parse-type-annotation arg)))
                (make-int-type))
        (values (format nil "sizeof(~a)" (sanitize-name (string arg)))
                (make-int-type)))))

(defun compile-call (form env)
  (let* ((fn-name (string (first form)))
         (args (rest form)))
    (if (gethash fn-name *structs*)
        (compile-struct-construct fn-name args env)
        (let* ((compiled-args (mapcar (lambda (a) (multiple-value-list (compile-expr a env))) args))
               (fn-type (env-lookup env fn-name))
               (ret-type (if (and fn-type (eq (sysp-type-kind fn-type) :fn))
                             (fn-type-ret fn-type)
                             (make-int-type))))
          (values (format nil "~a(~{~a~^, ~})"
                          (sanitize-name fn-name)
                          (mapcar #'first compiled-args))
                  ret-type)))))

(defun compile-struct-construct (name args env)
  (let ((compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args)))
    (values (format nil "(~a){~{~a~^, ~}}" name compiled-args)
            (make-struct-type name))))

;;; === Statement Compilation ===

(defun compile-body (forms env)
  "Compile a sequence of body forms, return list of C statement strings"
  (let ((stmts nil))
    (dolist (form forms)
      (let ((new-stmts (compile-stmt form env)))
        (setf stmts (append stmts new-stmts))))
    stmts))

(defun compile-stmt (form env)
  "Compile a single form as a statement, return list of C statement strings"
  (cond
    ((and (listp form) (sym= (first form) "let"))
     (compile-let-stmt form env))
    ((and (listp form) (sym= (first form) "let-mut"))
     (compile-let-stmt form env))  ; same as let for now, mut is future annotation
    ((and (listp form) (sym= (first form) "print"))
     (compile-print-stmt form env))
    ((and (listp form) (sym= (first form) "println"))
     (compile-println-stmt form env))
    ((and (listp form) (sym= (first form) "if"))
     (compile-if-stmt form env))
    ((and (listp form) (sym= (first form) "when"))
     (compile-when-stmt form env))
    ((and (listp form) (sym= (first form) "unless"))
     (compile-unless-stmt form env))
    ((and (listp form) (sym= (first form) "while"))
     (compile-while-stmt form env))
    ((and (listp form) (sym= (first form) "for"))
     (compile-for-stmt form env))
    ((and (listp form) (sym= (first form) "set!"))
     (compile-set-stmt form env))
    ((and (listp form) (sym= (first form) "return"))
     (compile-return-stmt form env))
    ((and (listp form) (sym= (first form) "break"))
     (list "  break;"))
    ((and (listp form) (sym= (first form) "continue"))
     (list "  continue;"))
    ((and (listp form) (sym= (first form) "cond"))
     (compile-cond-stmt form env))
    ((and (listp form) (sym= (first form) "block"))
     (compile-block-stmt form env))
    (t (multiple-value-bind (code tp) (compile-expr form env)
         (declare (ignore tp))
         (list (format nil "  ~a;" code))))))

(defun compile-let-stmt (form env)
  "(let name expr) or (let name :type expr) or (let name (make-array :type size))"
  (let* ((name (string (second form)))
         (rest (cddr form))
         (type-ann (when (keywordp (first rest))
                     (prog1 (parse-type-annotation (first rest))
                       (setf rest (cdr rest)))))
         (init-form (first rest)))
    (multiple-value-bind (init-code init-type) (compile-expr init-form env)
      (let ((final-type (or type-ann init-type)))
        (env-bind env name final-type)
        (if (eq (sysp-type-kind final-type) :array)
            ;; Array declaration: int name[size] = {0};
            (list (format nil "  ~a ~a[~a] = ~a;"
                          (type-to-c (first (sysp-type-params final-type)))
                          (sanitize-name name)
                          (second (sysp-type-params final-type))
                          init-code))
            (list (format nil "  ~a ~a = ~a;"
                          (type-to-c final-type) (sanitize-name name) init-code)))))))

(defun format-print-arg (val-code val-type)
  "Return format string and arg for a typed value"
  (case (sysp-type-kind val-type)
    (:float (values "%f" val-code))
    (:f32 (values "%f" val-code))
    (:str (values "%s" val-code))
    (:char (values "%c" val-code))
    (:u8 (values "%u" val-code))
    (:bool (values "%s" (format nil "(~a ? \"true\" : \"false\")" val-code)))
    (otherwise (values "%d" val-code))))

(defun compile-print-stmt (form env)
  "(print expr) — print without newline"
  (multiple-value-bind (val-code val-type) (compile-expr (second form) env)
    (multiple-value-bind (fmt arg) (format-print-arg val-code val-type)
      (list (format nil "  printf(\"~a\", ~a);" fmt arg)))))

(defun compile-println-stmt (form env)
  "(println expr) or (println) — print with newline"
  (if (null (rest form))
      (list "  printf(\"\\n\");")
      (multiple-value-bind (val-code val-type) (compile-expr (second form) env)
        (multiple-value-bind (fmt arg) (format-print-arg val-code val-type)
          (list (format nil "  printf(\"~a\\n\", ~a);" fmt arg))))))

(defun compile-if-stmt (form env)
  "(if cond then-body...) or (if cond then-body... else else-body...)"
  ;; Find the else keyword position
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let* ((rest (cddr form))
           (else-pos (position-if (lambda (x) (and (symbolp x) (sym= x "else"))) rest))
           (then-forms (if else-pos (subseq rest 0 else-pos) rest))
           (else-forms (when else-pos (subseq rest (1+ else-pos)))))
      (let ((then-env (make-env :parent env))
            (else-env (make-env :parent env)))
        (let ((result (list (format nil "  if (~a) {" cond-code))))
          (dolist (s (compile-body then-forms then-env))
            (push (format nil "  ~a" s) result))
          (push "  }" result)
          (when else-forms
            (setf (car result) "  } else {")
            (dolist (s (compile-body else-forms else-env))
              (push (format nil "  ~a" s) result))
            (push "  }" result))
          (nreverse result))))))

(defun compile-when-stmt (form env)
  "(when cond body...)"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let ((body-env (make-env :parent env))
          (result (list (format nil "  if (~a) {" cond-code))))
      (dolist (s (compile-body (cddr form) body-env))
        (push (format nil "  ~a" s) result))
      (push "  }" result)
      (nreverse result))))

(defun compile-unless-stmt (form env)
  "(unless cond body...)"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let ((body-env (make-env :parent env))
          (result (list (format nil "  if (!(~a)) {" cond-code))))
      (dolist (s (compile-body (cddr form) body-env))
        (push (format nil "  ~a" s) result))
      (push "  }" result)
      (nreverse result))))

(defun compile-while-stmt (form env)
  "(while cond body...)"
  (multiple-value-bind (cond-code ct) (compile-expr (second form) env)
    (declare (ignore ct))
    (let ((body-env (make-env :parent env))
          (result (list (format nil "  while (~a) {" cond-code))))
      (dolist (s (compile-body (cddr form) body-env))
        (push (format nil "  ~a" s) result))
      (push "  }" result)
      (nreverse result))))

(defun compile-for-stmt (form env)
  "(for [var start end] body...) or (for [var start end step] body...)"
  (let* ((spec (second form))
         (var-name (string (first spec)))
         (body-forms (cddr form))
         (body-env (make-env :parent env)))
    (env-bind body-env var-name (make-int-type))
    (multiple-value-bind (start-code st) (compile-expr (second spec) body-env)
      (declare (ignore st))
      (multiple-value-bind (end-code et) (compile-expr (third spec) body-env)
        (declare (ignore et))
        (let* ((step (fourth spec))
               (step-code (if step
                              (first (multiple-value-list (compile-expr step body-env)))
                              "1"))
               (c-var (sanitize-name var-name))
               (result (list (format nil "  for (int ~a = ~a; ~a < ~a; ~a += ~a) {"
                                     c-var start-code c-var end-code c-var step-code))))
          (dolist (s (compile-body body-forms body-env))
            (push (format nil "  ~a" s) result))
          (push "  }" result)
          (nreverse result))))))

(defun compile-set-stmt (form env)
  "(set! target val)"
  (multiple-value-bind (code tp) (compile-set-expr form env)
    (declare (ignore tp))
    (list (format nil "  ~a;" code))))

(defun compile-return-stmt (form env)
  "(return expr) or (return)"
  (if (rest form)
      (multiple-value-bind (code tp) (compile-expr (second form) env)
        (declare (ignore tp))
        (list (format nil "  return ~a;" code)))
      (list "  return;")))

(defun compile-cond-stmt (form env)
  "(cond [test1 body1...] [test2 body2...] [else bodyN...])"
  (let ((clauses (rest form))
        (result nil)
        (first-clause t))
    (dolist (clause clauses)
      (let ((test (first clause))
            (body (rest clause)))
        (cond
          ((and (symbolp test) (sym= test "else"))
           (push "  } else {" result)
           (dolist (s (compile-body body (make-env :parent env)))
             (push (format nil "  ~a" s) result)))
          (first-clause
           (multiple-value-bind (test-code tt) (compile-expr test env)
             (declare (ignore tt))
             (push (format nil "  if (~a) {" test-code) result)
             (dolist (s (compile-body body (make-env :parent env)))
               (push (format nil "  ~a" s) result))
             (setf first-clause nil)))
          (t
           (multiple-value-bind (test-code tt) (compile-expr test env)
             (declare (ignore tt))
             (push (format nil "  } else if (~a) {" test-code) result)
             (dolist (s (compile-body body (make-env :parent env)))
               (push (format nil "  ~a" s) result)))))))
    (push "  }" result)
    (nreverse result)))

(defun compile-block-stmt (form env)
  "(block body...) — new scope"
  (let ((body-env (make-env :parent env))
        (result (list "  {")))
    (dolist (s (compile-body (rest form) body-env))
      (push (format nil "  ~a" s) result))
    (push "  }" result)
    (nreverse result)))

;;; === Top-Level Form Compilation ===

(defun parse-params (param-list)
  (let ((params nil)
        (lst (if (listp param-list) param-list nil)))
    (loop while lst do
      (let ((name (string (pop lst)))
            (type (if (and lst (keywordp (first lst)))
                      (parse-type-annotation (pop lst))
                      (make-int-type))))
        (push (list name type) params)))
    (nreverse params)))

(defun compile-struct (form)
  "(struct Name [field :type, ...])"
  (let* ((name (string (second form)))
         (fields-raw (third form))
         (fields (parse-params fields-raw)))
    (setf (gethash name *structs*)
          (mapcar (lambda (f) (cons (first f) (second f))) fields))
    (push (format nil "typedef struct {~%~{  ~a ~a;~%~}} ~a;~%"
                  (loop for f in fields
                        append (list (type-to-c (second f)) (sanitize-name (first f))))
                  name)
          *struct-defs*)))

(defun compile-foreign-struct (form)
  "(foreign-struct Name [field :type, ...]) — register struct from C header, no typedef emitted"
  (let* ((name (string (second form)))
         (fields-raw (third form))
         (fields (parse-params fields-raw)))
    (setf (gethash name *structs*)
          (mapcar (lambda (f) (cons (first f) (second f))) fields))))

(defun compile-defn (form)
  "(defn name [params] :ret-type body...)"
  (let* ((name (string (second form)))
         (params-raw (third form))
         (rest-forms (cdddr form))
         (params (parse-params params-raw))
         (ret-annotation (when (keywordp (first rest-forms))
                           (prog1 (parse-type-annotation (first rest-forms))
                             (setf rest-forms (cdr rest-forms)))))
         (body-forms rest-forms)
         (env (make-env :parent *global-env*)))
    ;; Register function in global env
    (let* ((arg-types (mapcar #'second params))
           (ret-type (or ret-annotation (make-int-type)))
           (fn-type (make-fn-type arg-types ret-type)))
      (env-bind *global-env* name fn-type))
    ;; Bind params
    (dolist (p params)
      (env-bind env (first p) (second p)))
    ;; Compile body: all but last are statements, last is return value
    (let* ((all-but-last (butlast body-forms))
           (last-form (car (last body-forms)))
           (stmts (when all-but-last (compile-body all-but-last env)))
           (ret-type (or ret-annotation (make-int-type)))
           (param-str (format nil "~{~a~^, ~}"
                             (mapcar (lambda (p)
                                       (format nil "~a ~a"
                                               (type-to-c (second p))
                                               (sanitize-name (first p))))
                                     params)))
           (c-name (if (or (string-equal name "main")
                            (string-equal name "sysp_main")
                            (string-equal name "sysp-main"))
                       "main"
                       (sanitize-name name))))
      ;; Handle void return or expression return
      (multiple-value-bind (last-code lt) (compile-expr last-form env)
        (declare (ignore lt))
        (let ((return-stmt (if (eq (sysp-type-kind ret-type) :void)
                               (progn
                                 ;; For void, compile last form as statement too
                                 (setf stmts (compile-body body-forms env))
                                 nil)
                               (format nil "  return ~a;~%" last-code))))
          (push (format nil "~a ~a(~a) {~%~{~a~%~}~@[~a~]}~%"
                        (type-to-c ret-type)
                        c-name
                        (if params param-str "void")
                        (or stmts nil)
                        return-stmt)
                *functions*)
          ;; Forward declaration (skip for main)
          (unless (string= c-name "main")
            (push (format nil "~a ~a(~a);"
                          (type-to-c ret-type) c-name
                          (if params param-str "void"))
                  *forward-decls*)))))))

(defun compile-extern (form)
  "(extern name [params] :ret-type) — declare external C function"
  (let* ((name (string (second form)))
         (params-raw (third form))
         (rest-forms (cdddr form))
         (params (parse-params params-raw))
         (ret-annotation (when (keywordp (first rest-forms))
                           (parse-type-annotation (first rest-forms))))
         (ret-type (or ret-annotation (make-int-type)))
         (arg-types (mapcar #'second params))
         (fn-type (make-fn-type arg-types ret-type)))
    (env-bind *global-env* name fn-type)))

(defun compile-include (form)
  "(include \"header.h\")"
  (let ((header (second form)))
    (pushnew (if (stringp header) header (string header))
             *includes* :test #'string=)))

(defun compile-enum (form)
  "(enum Name [Variant1] [Variant2] ...) or (enum Name [Variant1 0] [Variant2 1] ...)"
  (let* ((name (string (second form)))
         (variants-raw (cddr form))
         (variants nil)
         (counter 0))
    (dolist (v variants-raw)
      (let* ((vspec (if (listp v) v (list v)))
             (vname (string (first vspec)))
             (vval (if (second vspec) (second vspec) counter)))
        (push (cons vname vval) variants)
        (setf counter (1+ (if (integerp vval) vval counter)))))
    (setf variants (nreverse variants))
    (setf (gethash name *enums*) variants)
    ;; Register each variant in global env as the enum type
    (dolist (v variants)
      (env-bind *global-env* (car v) (make-enum-type name)))
    ;; Emit C enum
    (push (format nil "typedef enum {~%~{  ~a = ~a~^,~%~}~%} ~a;~%"
                  (loop for v in variants
                        append (list (sanitize-name (car v)) (cdr v)))
                  name)
          *struct-defs*)))

(defun compile-const (form)
  "(const name :type expr) — top-level constant"
  (let* ((name (string (second form)))
         (rest (cddr form))
         (type-ann (when (keywordp (first rest))
                     (prog1 (parse-type-annotation (first rest))
                       (setf rest (cdr rest)))))
         (init-form (first rest)))
    (multiple-value-bind (init-code init-type) (compile-expr init-form (make-env))
      (let ((final-type (or type-ann init-type)))
        (env-bind *global-env* name final-type)
        (push (format nil "static const ~a ~a = ~a;~%"
                      (type-to-c final-type) (sanitize-name name) init-code)
              *struct-defs*)))))  ; reuse struct-defs for ordering (before functions)

;;; === Main Compiler Driver ===

(defun compile-toplevel (forms)
  (dolist (form forms)
    (when (listp form)
      (cond
        ((sym= (first form) "struct") (compile-struct form))
        ((sym= (first form) "foreign-struct") (compile-foreign-struct form))
        ((sym= (first form) "enum") (compile-enum form))
        ((sym= (first form) "defn") (compile-defn form))
        ((sym= (first form) "extern") (compile-extern form))
        ((sym= (first form) "include") (compile-include form))
        ((sym= (first form) "const") (compile-const form))
        (t (warn "Unknown top-level form: ~a" (first form)))))))

(defun emit-c (out-path)
  (with-open-file (out out-path :direction :output :if-exists :supersede)
    (format out "#include <stdio.h>~%")
    (format out "#include <stdlib.h>~%")
    (dolist (inc *includes*)
      (format out "#include <~a>~%" inc))
    (format out "~%")
    ;; struct definitions & constants
    (dolist (s (nreverse *struct-defs*))
      (write-string s out)
      (terpri out))
    ;; generated type declarations
    (dolist (d (nreverse *type-decls*))
      (write-string d out)
      (terpri out))
    ;; forward declarations
    (dolist (fwd (nreverse *forward-decls*))
      (format out "~a~%" fwd))
    (when *forward-decls* (terpri out))
    ;; functions
    (dolist (f (nreverse *functions*))
      (write-string f out)
      (terpri out))))

(defun reset-state ()
  (setf *structs* (make-hash-table :test 'equal))
  (setf *enums* (make-hash-table :test 'equal))
  (setf *functions* nil)
  (setf *struct-defs* nil)
  (setf *lambda-counter* 0)
  (setf *temp-counter* 0)
  (setf *generated-types* (make-hash-table :test 'equal))
  (setf *type-decls* nil)
  (setf *forward-decls* nil)
  (setf *global-env* (make-env))
  (setf *includes* nil)
  (setf *string-literals* nil))

(defun compile-file-to-c (in-path out-path)
  (reset-state)
  (let ((forms (read-sysp-file in-path)))
    (compile-toplevel forms)
    (emit-c out-path)
    (format t "Compiled ~a -> ~a~%" in-path out-path)))

;;; === CLI Entry Point ===

(defun main ()
  (let ((args (cdr sb-ext:*posix-argv*)))
    (when (< (length args) 1)
      (format *error-output* "Usage: sysp <input.sysp> [output.c]~%")
      (sb-ext:exit :code 1))
    (let* ((input (first args))
           (output (or (second args)
                       (concatenate 'string
                                    (subseq input 0 (position #\. input :from-end t))
                                    ".c"))))
      (compile-file-to-c input output))))

(main)
