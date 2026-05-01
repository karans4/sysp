;;;; sysp-ir package.

(defpackage :sysp-ir
  (:use :cl)
  (:export :compile-defn :compile-program :compile-and-emit
           :emit-c-fn :emit-c-proto :pp-ir))
(in-package :sysp-ir)
