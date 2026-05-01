;;;; IR pretty-printer (debug aid).
(in-package :sysp-ir)

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
