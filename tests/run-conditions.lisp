(load "tests/common.lisp")
(in-package :sysp-ir)

;; The full CL flow from examples/conditions.sysp.
;; This file pulls its own driver in via (defn main ...) producing the
;; complete C program — no external driver, no preamble injection.
(check-prog "signal-handler-restart"
            (parse-file "examples/conditions.sysp")
            ""
            "result: 99"
            :runtime :conditions :preamble "")

;; Restart invoked directly (no handler)
(check-prog "restart-direct"
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
            ""
            "got 42"
            :runtime :conditions :preamble "")

(report-and-exit)
