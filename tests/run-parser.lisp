(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun check (label src expected)
  (handler-case
      (let ((got (parse-string src)))
        (if (equal got expected)
            (progn (incf *ok*) (format t "~a: ok~%" label))
            (progn (incf *fail*)
                   (format t "~a: FAIL~%  got:  ~s~%  want: ~s~%" label got expected))))
    (error (e)
      (incf *fail*)
      (format t "~a: ERR ~a~%" label e))))

(defun check-error (label src expected-substr)
  (handler-case
      (progn (parse-string src)
             (incf *fail*)
             (format t "~a: FAIL — expected error~%" label))
    (error (e)
      (let ((msg (format nil "~a" e)))
        (if (search expected-substr msg)
            (progn (incf *ok*) (format t "~a: ok (err: ~a)~%" label expected-substr))
            (progn (incf *fail*)
                   (format t "~a: FAIL — error didn't match~%  got: ~a~%  want substr: ~a~%"
                           label msg expected-substr)))))))

;; --- atoms ---
(check "empty"      ""        nil)
(check "int"        "42"      '(42))
(check "neg-int"    "-42"     '(-42))
(check "zero"       "0"       '(0))
(check "hex"        "0xff"    '(255))
(check "neg-hex"    "-0x10"   '(-16))
(check "binary"     "0b1010"  '(10))
(check "octal"      "0o17"    '(15))
(check "float"      "3.14"    '(3.14))
(check "neg-float"  "-2.5"    '(-2.5))
(check "symbol"     "foo"     (list (intern "FOO" :sysp-ir)))
(check "kebab-sym"  "my-fn"   (list (intern "MY-FN" :sysp-ir)))
(check "keyword"    ":int"    '(:int))
(check "kw-multi"   ":int :string" '(:int :string))
(check "true"       "t"       (list cl:t))
(check "false"      "nil"     (list cl:nil))

;; --- strings + escapes ---
(check "string-simple" "\"hello\"" '("hello"))
(check "string-empty"  "\"\""      '(""))
(check "string-escape" "\"a\\nb\"" (list (format nil "a~%b")))
(check "string-tab"    "\"a\\tb\"" (list (format nil "a~Cb" #\Tab)))
(check "string-quote"  "\"a\\\"b\"" (list "a\"b"))
(check "string-bs"     "\"a\\\\b\"" (list "a\\b"))

;; --- char literals ---
(check "char-c"       "#\\a"        '(#\a))
(check "char-newline" "#\\newline"  (list #\Newline))
(check "char-space"   "#\\space"    (list #\Space))
(check "char-tab"     "#\\tab"      (list #\Tab))

;; --- lists, brackets, comments, commas ---
(check "list"      "(+ 1 2)"     `((,(intern "+" :sysp-ir) 1 2)))
(check "nested"    "(a (b c))"   '((a (b c))))
(check "brackets"  "[1 2 3]"     '((1 2 3)))
(check "commas"    "(1, 2, 3)"   '((1 2 3)))
(check "comment"   "; hi
foo"
  (list (intern "FOO" :sysp-ir)))
(check "ws-leading" "   42"      '(42))
(check "multi-form" "1 2 3"      '(1 2 3))

;; --- quotes ---
(check "quote"      "'foo"  `((quote ,(intern "FOO" :sysp-ir))))
(check "qq-uq"      "`(a ~b)"   '((quasiquote (a (unquote b)))))
(check "splice"     "`(a ~@b)"  '((quasiquote (a (splice b)))))

;; --- error cases ---
(check-error "unclosed-paren"    "(a b c"   "unclosed (")
(check-error "mismatched-close"  "(a b ]"   "mismatched")
(check-error "unterminated-str"  "\"hi"     "unterminated string")

;; --- end-to-end: parse then compile ---
(format t "~%--- Round-trip ---~%")
(let* ((src "(defn add ((x :int) (y :int)) :int (+ x y))")
       (forms (parse-string src))
       (form (first forms)))
  (format t "surface: ~s~%C:~%" form)
  (compile-and-emit form))

(format t "~%--- Source location ---~%")
(let* ((src "

  (defn foo () :int 42)
")
       (forms (parse-string src "demo.sysp"))
       (form (first forms)))
  (format t "form: ~s~%" form)
  (format t "loc:  ~s~%" (loc-of form)))

(format t "~%--- End-to-end: parse .sysp file, compile, run, valgrind ---~%")
(let* ((forms (parse-file "examples/hello.sysp"))
       (program-c (with-output-to-string (s) (compile-program forms s)))
       (driver "int main(){
  String n=sysp_str_lit(\"karan\",5);
  String r=loud(n); sysp_str_print(r);
  sysp_str_release(r); sysp_str_release(n); return 0;}")
       (full (with-output-to-string (s)
               (write-string "#include \"runtime.h\"" s) (terpri s)
               (write-string program-c s) (terpri s)
               (write-string driver s)))
       (c-file "/tmp/sysp-ir-pf.c") (exe "/tmp/sysp-ir-pf"))
  (with-open-file (s c-file :direction :output :if-exists :supersede)
    (write-string full s))
  (let ((cc (sb-ext:run-program "/usr/bin/cc" (list "-O0" "-Isrc" "-o" exe c-file)
                                :output t :error t)))
    (cond
      ((not (zerop (sb-ext:process-exit-code cc)))
       (incf *fail*) (format t "e2e-parse-file: CC FAIL~%"))
      (t
       (let* ((p (sb-ext:run-program exe nil :output :stream))
              (out (with-output-to-string (s)
                     (loop for line = (read-line (sb-ext:process-output p) nil nil)
                           while line do (write-line line s)))))
         (sb-ext:process-wait p)
         (let ((got (string-trim '(#\Newline #\Space) out)))
           (cond
             ((string= got "hello karan!")
              (let* ((vp (sb-ext:run-program "/usr/bin/valgrind"
                          (list "--error-exitcode=2" "--leak-check=full" "-q" exe)
                          :output nil :error :stream)))
                (sb-ext:process-wait vp)
                (if (zerop (sb-ext:process-exit-code vp))
                    (progn (incf *ok*) (format t "e2e-parse-file: ok (valgrind clean)~%"))
                    (progn (incf *fail*) (format t "e2e-parse-file: VG FAIL~%")))))
             (t (incf *fail*)
                (format t "e2e-parse-file: FAIL got ~s~%" got))))))))
  (format t "C output:~%~a~%" full))

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
