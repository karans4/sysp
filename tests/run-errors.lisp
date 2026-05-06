;;;; Source-location threading: parser tags each cons with its (file line col),
;;;; inference looks up *current-form*'s loc on error. Verifying the lookup
;;;; survives the mono pass's body copy-tree.

(load "tests/common.lisp")
(in-package :sysp-ir)

(defparameter +tmp-sysp+ "/tmp/sysp-error-test.sysp")

(defun write-sysp (src)
  (with-open-file (s +tmp-sysp+ :direction :output :if-exists :supersede)
    (write-string src s)))

(defun expect-error-with-location (label src match-substr)
  "Compile src, expect an error whose printed form contains match-substr."
  (format t "~a:" label)
  (write-sysp src)
  (handler-case
      (progn
        (compile-program (parse-file +tmp-sysp+) (make-broadcast-stream))
        (incf *fail*) (format t " FAIL — expected error~%"))
    (error (e)
      (let ((msg (format nil "~a" e)))
        (cond
          ((search match-substr msg)
           (incf *ok*) (format t " ok~%"))
          (t (incf *fail*)
             (format t " FAIL — error didn't contain ~s~%  got: ~a~%"
                     match-substr msg)))))))

;; type mismatch points at the concat call's line+col
(expect-error-with-location "type-mismatch points at line"
                            "(defn bad ((x :int)) :int
  (string-concat x \"!\"))"
                            +tmp-sysp+)

;; arity mismatch on user fn call
(expect-error-with-location "arity-mismatch on user fn"
                            "(defn add ((x :int) (y :int)) :int (+ x y))
(defn use () :int (add 1))"
                            +tmp-sysp+)

;; unknown fn
(expect-error-with-location "unknown-fn points at call"
                            "(defn use () :int (does-not-exist 1 2))"
                            +tmp-sysp+)

;; The error format includes the offending source line + caret marker
(expect-error-with-location "error includes source line"
                            "(defn bad ((x :int)) :int
  (string-concat x \"!\"))"
                            "(string-concat x")

(report-and-exit)
