(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (program-c expected-stdout)
  (let ((c-file "/tmp/sysp-ir-cond.c") (exe "/tmp/sysp-ir-cond"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string program-c s) (terpri s))
    (let ((cc (sb-ext:run-program "/usr/bin/cc"
                  (list "-O0" "-Iruntime" "-o" exe c-file
                        "runtime/value.c" "runtime/conditions.c")
                  :output t :error t)))
      (unless (zerop (sb-ext:process-exit-code cc))
        (incf *fail*) (format t " [CC FAIL]~%") (return-from cc-and-run nil)))
    (let* ((p (sb-ext:run-program exe nil :output :stream))
           (out (with-output-to-string (s)
                  (loop for l = (read-line (sb-ext:process-output p) nil nil)
                        while l do (write-line l s)))))
      (sb-ext:process-wait p)
      (let ((got (string-trim '(#\Newline #\Space) out)))
        (if (string= got expected-stdout)
            (progn (incf *ok*) (format t " ok (~a)~%" got))
            (progn (incf *fail*) (format t " FAIL got ~s want ~s~%" got expected-stdout)))))))

(defun program-c (forms) (with-output-to-string (s) (compile-program forms s)))
(defun check (label forms expected)
  (format t "~a:" label)
  (cc-and-run (program-c forms) expected))

;; The full CL flow from examples/conditions.sysp
(check "signal-handler-restart"
       (parse-file "examples/conditions.sysp")
       "result: 99")

;; Restart invoked directly (no handler)
(check "restart-direct"
       '((include "<stdio.h>")
         (include "value.h")
         (include "conditions.h")
         (extern with_restart    ((name :u32) (body :Fn) (fb :Fn)) :Value)
         (extern invoke_restart  ((name :u32) (arg :Value)) :unit)
         (extern intern_sym      ((name :cstr)) :u32)
         (extern val_int         ((i :int)) :Value)
         (extern val_int_of      ((v :Value)) :int)
         (extern printf          ((fmt :cstr) (n :int)) :int)
         (defn main () :int
           (let ((r (with_restart (intern_sym (cstr "abort"))
                      (lambda () :Value
                        (invoke_restart (intern_sym (cstr "abort")) (val_int 42))
                        (val-nil))
                      (lambda ((v :Value)) :Value v))))
             (printf (cstr "got %d
") (val_int_of r))
             0)))
       "got 42")

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
