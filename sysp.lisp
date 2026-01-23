;;;; sysp.lisp — Bootstrap compiler for Systems Lisp
;;;; Compiles .sysp files to C

(defpackage :sysp
  (:use :cl))
(in-package :sysp)

;;; === Types ===

(defstruct sysp-type
  (kind nil) ; :int :float :bool :void :struct :vector :tuple :fn :unknown
  (name nil)
  (params nil)) ; type params (element types for vector/tuple, arg+ret for fn)

(defun make-int-type () (make-sysp-type :kind :int))
(defun make-float-type () (make-sysp-type :kind :float))
(defun make-void-type () (make-sysp-type :kind :void))
(defun make-bool-type () (make-sysp-type :kind :bool))

(defun make-vector-type (elem-type)
  (make-sysp-type :kind :vector :params (list elem-type)))

(defun make-tuple-type (elem-types)
  (make-sysp-type :kind :tuple :params elem-types))

(defun make-fn-type (arg-types ret-type)
  (make-sysp-type :kind :fn :params (append arg-types (list ret-type))))

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

(defvar *structs* (make-hash-table :test 'equal))   ; name -> field list
(defvar *functions* nil)                              ; collected C function strings
(defvar *struct-defs* nil)                            ; collected C struct definitions
(defvar *lambda-counter* 0)
(defvar *generated-types* (make-hash-table :test 'equal)) ; track generated vector/tuple types
(defvar *type-decls* nil)                             ; forward declarations for generated types

;;; === Parsing ===
;;; Custom readtable: commas are whitespace, [] are list delimiters.

(defun make-sysp-readtable ()
  (let ((rt (copy-readtable nil)))
    ;; Preserve case
    (setf (readtable-case rt) :preserve)
    ;; Treat comma as whitespace
    (set-syntax-from-char #\, #\Space rt)
    ;; Treat [ as ( and ] as )
    (set-macro-character #\[
      (lambda (stream char)
        (declare (ignore char))
        (read-delimited-list #\] stream t))
      nil rt)
    (set-syntax-from-char #\] #\) rt)
    rt))

(defvar *sysp-readtable* (make-sysp-readtable))

(defun read-sysp-file (path)
  "Read all forms from a .sysp file"
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
  "Convert a type keyword like :int, :float to a sysp-type"
  (let ((name (string-downcase (symbol-name sym))))
    (cond
      ((string= name "int") (make-int-type))
      ((string= name "float") (make-float-type))
      ((string= name "bool") (make-bool-type))
      ((string= name "void") (make-void-type))
      (t (let ((sname (symbol-name sym)))
           (if (gethash sname *structs*)
               (make-struct-type sname)
               (make-sysp-type :kind :unknown :name sname)))))))

;;; === C Type Emission ===

(defun type-to-c (tp)
  "Convert a sysp-type to its C type string"
  (case (sysp-type-kind tp)
    (:int "int")
    (:float "double")
    (:bool "int")
    (:void "void")
    (:struct (sysp-type-name tp))
    (:vector (vector-type-c-name tp))
    (:tuple (tuple-type-c-name tp))
    (:fn (fn-type-c-name tp))
    (otherwise "int")))

(defun mangle-type-name (tp)
  "Create a mangled name for a type"
  (case (sysp-type-kind tp)
    (:int "int")
    (:float "float")
    (:bool "bool")
    (:struct (sysp-type-name tp))
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
                       (mapcar #'mangle-type-name args)
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
;;; Each compile-* returns (values c-code inferred-type)

(defun compile-expr (form env)
  "Compile an expression, return (values c-string type)"
  (cond
    ((integerp form) (values (format nil "~d" form) (make-int-type)))
    ((floatp form) (values (format nil "~f" form) (make-float-type)))
    ((symbolp form)
     (let ((tp (env-lookup env (string form))))
       (values (sanitize-name (string form))
               (or tp (make-sysp-type :kind :unknown)))))
    ((listp form) (compile-list form env))
    (t (values (format nil "~a" form) (make-sysp-type :kind :unknown)))))

(defun sanitize-name (name)
  "Make a name safe for C identifiers"
  (substitute #\_ #\- name))

(defun sym= (sym name)
  (and (symbolp sym) (string-equal (symbol-name sym) name)))

(defun compile-list (form env)
  "Compile a list form (function call or special form)"
  (let ((head (first form)))
    (cond
      ((sym= head "+") (compile-binop "+" form env))
      ((sym= head "-") (compile-binop "-" form env))
      ((sym= head "*") (compile-binop "*" form env))
      ((sym= head "/") (compile-binop "/" form env))
      ((sym= head "get") (compile-get form env))
      ((sym= head "vector") (compile-vector form env))
      ((sym= head "vector-ref") (compile-vector-ref form env))
      ((sym= head "tuple") (compile-tuple form env))
      ((sym= head "tuple-ref") (compile-tuple-ref form env))
      ((sym= head "lambda") (compile-lambda form env))
      (t (compile-call form env)))))

(defun compile-binop (op form env)
  (multiple-value-bind (lhs lt) (compile-expr (second form) env)
    (multiple-value-bind (rhs rt) (compile-expr (third form) env)
      (declare (ignore rt))
      (values (format nil "(~a ~a ~a)" lhs op rhs) lt))))

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

(defun compile-lambda (form env)
  "(lambda [params...] :ret-type body)"
  (let* ((params-raw (second form))
         (rest-forms (cddr form))
         ;; parse params: [name :type name :type ...]
         (params (parse-params params-raw))
         ;; check for return type annotation
         (ret-annotation (when (keywordp (first rest-forms))
                           (prog1 (parse-type-annotation (first rest-forms))
                             (setf rest-forms (cdr rest-forms)))))
         (body (first rest-forms))
         (lambda-name (format nil "_lambda_~d" (incf *lambda-counter*)))
         (fn-env (make-env :parent env)))
    ;; bind params
    (dolist (p params)
      (env-bind fn-env (first p) (second p)))
    ;; compile body
    (multiple-value-bind (body-code body-type) (compile-expr body fn-env)
      (let* ((ret-type (or ret-annotation body-type))
             (arg-types (mapcar #'second params))
             (fn-type (make-fn-type arg-types ret-type))
             (param-str (format nil "~{~a~^, ~}"
                               (mapcar (lambda (p)
                                         (format nil "~a ~a"
                                                 (type-to-c (second p))
                                                 (sanitize-name (first p))))
                                       params))))
        ;; emit the lambda as a static function
        (push (format nil "static ~a ~a(~a) { return ~a; }~%"
                      (type-to-c ret-type) lambda-name
                      (if params param-str "void")
                      body-code)
              *functions*)
        (values lambda-name fn-type)))))

(defun compile-call (form env)
  "Compile a function/constructor call"
  (let* ((fn-name (string (first form)))
         (args (rest form)))
    ;; Check if it's a struct constructor
    (if (gethash fn-name *structs*)
        (compile-struct-construct fn-name args env)
        ;; Regular function call
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
  "(StructName val ...)"
  (let ((compiled-args (mapcar (lambda (a) (first (multiple-value-list (compile-expr a env)))) args)))
    (values (format nil "(~a){~{~a~^, ~}}" name compiled-args)
            (make-struct-type name))))

;;; === Statement Compilation ===

(defun compile-body (forms env)
  "Compile a sequence of body forms, return list of C statement strings"
  (let ((stmts nil))
    (dolist (form forms)
      (cond
        ((and (listp form) (sym= (first form) "let"))
         (let* ((name (string (second form)))
                (init-form (third form)))
           (multiple-value-bind (init-code init-type) (compile-expr init-form env)
             (env-bind env name init-type)
             (push (format nil "  ~a ~a = ~a;"
                           (type-to-c init-type) (sanitize-name name) init-code)
                   stmts))))
        ((and (listp form) (sym= (first form) "print"))
         (multiple-value-bind (val-code val-type) (compile-expr (second form) env)
           (let ((fmt (case (sysp-type-kind val-type)
                        (:float "%f")
                        (otherwise "%d"))))
             (push (format nil "  printf(\"~a\\n\", ~a);" fmt val-code) stmts))))
        (t
         (multiple-value-bind (code tp) (compile-expr form env)
           (declare (ignore tp))
           (push (format nil "  ~a;" code) stmts)))))
    (nreverse stmts)))

;;; === Top-Level Form Compilation ===

(defun parse-params (param-list)
  "Parse (name :type name :type ...) -> ((name type) ...)"
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
    ;; register struct
    (setf (gethash name *structs*)
          (mapcar (lambda (f) (cons (first f) (second f))) fields))
    ;; emit C struct
    (push (format nil "typedef struct {~%~{  ~a ~a;~%~}} ~a;~%"
                  (loop for f in fields
                        append (list (type-to-c (second f)) (sanitize-name (first f))))
                  name)
          *struct-defs*)))

(defun compile-defn (form)
  "(defn name [params] :ret-type body...)"
  (let* ((name (string (second form)))
         (params-raw (third form))
         (rest-forms (cdddr form))
         (params (parse-params params-raw))
         ;; check for return type
         (ret-annotation (when (keywordp (first rest-forms))
                           (prog1 (parse-type-annotation (first rest-forms))
                             (setf rest-forms (cdr rest-forms)))))
         (body-forms rest-forms)
         (env (make-env)))
    ;; bind params
    (dolist (p params)
      (env-bind env (first p) (second p)))
    ;; compile body
    (let* ((stmts (compile-body body-forms env))
           (ret-type (or ret-annotation (make-int-type)))
           (param-str (format nil "~{~a~^, ~}"
                             (mapcar (lambda (p)
                                       (format nil "~a ~a"
                                               (type-to-c (second p))
                                               (sanitize-name (first p))))
                                     params)))
           ;; rename main
           (c-name (if (string-equal name "sysp_main") "main" (sanitize-name name))))
      (push (format nil "~a ~a(~a) {~%~{~a~%~}  return ~a;~%}~%"
                    (type-to-c ret-type)
                    c-name
                    (if params param-str "void")
                    stmts
                    (first (multiple-value-list (compile-expr (car (last body-forms)) env))))
            *functions*))))

;;; === Main Compiler Driver ===

(defun compile-toplevel (forms)
  "Compile all top-level forms"
  (dolist (form forms)
    (when (listp form)
      (cond
        ((sym= (first form) "struct") (compile-struct form))
        ((sym= (first form) "defn") (compile-defn form))
        (t (warn "Unknown top-level form: ~a" (first form)))))))

(defun emit-c (out-path)
  "Write the compiled C to a file"
  (with-open-file (out out-path :direction :output :if-exists :supersede)
    (format out "#include <stdio.h>~%")
    (format out "#include <stdlib.h>~%~%")
    ;; struct definitions
    (dolist (s (nreverse *struct-defs*))
      (write-string s out)
      (terpri out))
    ;; generated type declarations
    (dolist (d (nreverse *type-decls*))
      (write-string d out)
      (terpri out))
    ;; functions (lambdas first, then defns)
    (dolist (f (nreverse *functions*))
      (write-string f out)
      (terpri out))))

(defun reset-state ()
  (setf *structs* (make-hash-table :test 'equal))
  (setf *functions* nil)
  (setf *struct-defs* nil)
  (setf *lambda-counter* 0)
  (setf *generated-types* (make-hash-table :test 'equal))
  (setf *type-decls* nil))

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
