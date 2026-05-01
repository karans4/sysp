(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun cc-and-run (program-c driver expected)
  (let ((c-file "/tmp/sysp-ir-st.c") (exe "/tmp/sysp-ir-st"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string "#include <stdint.h>" s) (terpri s)
      (write-string "#include <stdio.h>" s) (terpri s)
      (write-string program-c s) (terpri s)
      (write-string driver s))
    (let ((cc (sb-ext:run-program "/usr/bin/cc" (list "-O0" "-o" exe c-file)
                                  :output t :error t)))
      (unless (zerop (sb-ext:process-exit-code cc))
        (incf *fail*) (format t " [CC FAIL]~%") (return-from cc-and-run nil)))
    (let* ((p (sb-ext:run-program exe nil :output :stream))
           (out (with-output-to-string (s)
                  (loop for l = (read-line (sb-ext:process-output p) nil nil)
                        while l do (write-line l s)))))
      (sb-ext:process-wait p)
      (let ((got (string-trim '(#\Newline #\Space) out)))
        (if (string= got expected)
            (progn (incf *ok*) (format t " ok (~a)~%" got))
            (progn (incf *fail*) (format t " FAIL got ~s want ~s~%" got expected)))))))
(defun program-c (forms) (with-output-to-string (s) (compile-program forms s)))
(defun check (label forms driver expected)
  (format t "~a:" label)
  (cc-and-run (program-c forms) driver expected))

;; Basic struct: construct, read field
(check "make-and-read"
       '((defstruct POINT ((x :int) (y :int)))
         (defn px ((p :POINT)) :int (get-field p x))
         (defn py ((p :POINT)) :int (get-field p y))
         (defn make-pt () :POINT (POINT 3 7)))
       "int main(){
  POINT p = make_pt();
  printf(\"%d %d\\n\", px(p), py(p)); return 0; }"
       "3 7")

;; Mutate via set-field! through a pointer
(check "mutate-via-ptr"
       '((defstruct CELL ((v :int)))
         (defn bump ((c :ptr-CELL)) :unit
            (set-field! c v (+ (get-field c v) 1))))
       "int main(){
  CELL c = (CELL){10};
  bump(&c); bump(&c); bump(&c);
  printf(\"%d\\n\", c.v); return 0; }"
       "13")

;; The 6502-flavored test: build a register file struct, read fields
(check "cpu-style"
       '((defstruct CPU ((a :u8) (x :u8) (y :u8) (sp :u8) (pc :int) (status :u8)))
         (defn make-cpu () :CPU (CPU 0 0 0 253 0 36))
         (defn cpu-a ((c :CPU)) :int (get-field c a))
         (defn cpu-pc ((c :CPU)) :int (get-field c pc)))
       "int main(){
  CPU c = make_cpu();
  printf(\"%d %d %d\\n\", cpu_a(c), c.sp, cpu_pc(c)); return 0; }"
       "0 253 0")

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
