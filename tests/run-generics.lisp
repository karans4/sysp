;;;; Stage 17: generic structs.
;;;; (defstruct (Name :T1 :T2 ...) fields) → template; each concrete
;;;; instantiation materializes a per-T struct with substituted field types.

(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0) (defvar *fail* 0)

(defun program-c (defns)
  (with-output-to-string (s) (compile-program defns s)))

(defun cc-and-run (preamble program-c driver expected)
  (let ((c-file "/tmp/sysp-gen.c") (exe "/tmp/sysp-gen"))
    (with-open-file (s c-file :direction :output :if-exists :supersede)
      (write-string preamble s) (terpri s)
      (write-string program-c s) (terpri s)
      (write-string driver s))
    (let ((cc (sb-ext:run-program "/usr/bin/cc"
                                  (list "-O0" "-Isrc" "-Iruntime" "-o" exe c-file
                                        "runtime/value.c")
                                  :output t :error t)))
      (unless (zerop (sb-ext:process-exit-code cc))
        (incf *fail*) (format t " [CC FAIL]~%") (return-from cc-and-run nil)))
    (let* ((p (sb-ext:run-program exe nil :output :stream))
           (out (with-output-to-string (s)
                  (loop for line = (read-line (sb-ext:process-output p) nil nil)
                        while line do (write-line line s)))))
      (sb-ext:process-wait p)
      (let ((got (string-trim '(#\Newline #\Space) out)))
        (if (string= got expected)
            (progn (incf *ok*) (format t " ok~%"))
            (progn (incf *fail*) (format t " FAIL got ~s want ~s~%" got expected)))))))

(defun check-prog (label defns driver expected)
  (format t "~a:" label)
  (cc-and-run "#include \"runtime.h\"" (program-c defns) driver expected))

;; --- Box<int>: simplest case, value-typed field ---
(check-prog "box-int"
            '((defstruct (Box :T) ((value :T)))
              (defn use () :int (get-field (Box 5) value)))
            "#include <stdio.h>
int main(){ printf(\"%d\\n\", use()); return 0; }"
            "5")

;; --- Two materializations of Box at different int widths ---
(check-prog "box-int-and-u8"
            '((defstruct (Box :T) ((value :T)))
              (defn use-int () :int (get-field (Box 42) value))
              (defn use-u8  () :u8  (cast :u8 (get-field (Box 7) value))))
            "#include <stdio.h>
int main(){ printf(\"%d %d\\n\", use_int(), use_u8()); return 0; }"
            "42 7")

;; --- Two type params: Pair<int, int> with both fields read ---
(check-prog "pair-int-int"
            '((defstruct (Pair :A :B) ((fst :A) (snd :B)))
              (defn use-fst () :int (get-field (Pair 7 99) fst))
              (defn use-snd () :int (get-field (Pair 7 99) snd)))
            "#include <stdio.h>
int main(){ printf(\"%d %d\\n\", use_fst(), use_snd()); return 0; }"
            "7 99")

;; --- Vec<int> with a (:ptr :T) field — exercises struct templates that
;; reference the type param inside another type form. This is the real
;; Stage-17 milestone: a generic data structure as library code.
(check-prog "vec-int-push-get"
            '((extern malloc ((sz :size)) :ptr-void)

              (defstruct (Vec :T) ((data (:ptr :T)) (len :int) (cap :int)))

              (defn vec-empty () (Vec :int)
                (Vec (cast (:ptr :int) (cast :ptr-void 0)) 0 0))

              (defn vec-push-i ((v (Vec :int)) (x :int)) (Vec :int)
                ;; This sample reserves 8 ints up front on first push, then
                ;; appends. Real growable push needs realloc — out of scope for
                ;; the milestone; this proves struct fields + (:ptr :T) work.
                (let ((newcap 8))
                  (let ((newdata (cast (:ptr :int) (malloc (cast :size 32)))))
                    (ptr-set-at! newdata 0 x)
                    (Vec newdata 1 newcap))))

              (defn use () :int
                (let ((v (vec-empty)))
                  (let ((v2 (vec-push-i v 99)))
                    (ptr-ref (get-field v2 data) 0)))))
            "#include <stdio.h>
int main(){ printf(\"%d\\n\", use()); return 0; }"
            "99")

(format t "~%~a passed, ~a failed~%" *ok* *fail*)
(unless (zerop *fail*) (sb-ext:exit :code 1))
