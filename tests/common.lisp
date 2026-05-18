;;;; Shared test harness for sysp-ir runners.
;;;;
;;;; Each runner loads this, calls (check-prog ...) per case, then
;;;; (report-and-exit) at the bottom. Common defaults:
;;;;   - prepends `#include "runtime.h"` and `#include <stdio.h>`
;;;;   - links runtime/value.c
;;;;   - compiles with -Isrc -Iruntime
;;;;
;;;; Knobs (keyword args to check-prog):
;;;;   :mode    :stdout (default) | :exit
;;;;   :runtime :value (default) | :conditions | :none
;;;;   :preamble override the default include block
;;;;   :valgrind t to additionally run under valgrind (skipped if missing)

(load "src/load.lisp")
(in-package :sysp-ir)

(defvar *ok* 0)
(defvar *fail* 0)
(defvar *mem-skipped* 0)   ; memory-safety checks with no usable tool

(defparameter *test-c-file* "/tmp/sysp-test.c")
(defparameter *test-exe*    "/tmp/sysp-test")

(defparameter *default-preamble*
  (concatenate 'string
               "#include \"runtime.h\"" (string #\Newline)
               "#include <stdio.h>"     (string #\Newline)))

(defun program-c (defns)
  "Run compile-program on a list of top-level forms; return the C source."
  (with-output-to-string (s) (compile-program defns s)))

(defun runtime-srcs (key)
  (case key
    (:none       nil)
    (:value      (list "runtime/value.c"))
    (:conditions (list "runtime/value.c" "runtime/conditions.c"))
    (t (error "runtime-srcs: unknown ~A" key))))

(defun cc-build (c-path exe-path runtime-key)
  "Compile c-path to exe-path. Return t on success, nil + count fail on cc error."
  (let* ((args (append (list "-O0" "-Isrc" "-Iruntime" "-o" exe-path c-path)
                       (runtime-srcs runtime-key)))
         (cc (sb-ext:run-program "/usr/bin/cc" args :output t :error t)))
    (cond ((zerop (sb-ext:process-exit-code cc)) t)
          (t (incf *fail*) (format t " [CC FAIL]~%") nil))))

(defun run-and-capture (exe)
  "Run exe, return (values trimmed-stdout exit-code)."
  (let* ((p (sb-ext:run-program exe nil :output :stream))
         (out (with-output-to-string (s)
                (loop for l = (read-line (sb-ext:process-output p) nil nil)
                      while l do (write-line l s)))))
    (sb-ext:process-wait p)
    (values (string-trim '(#\Newline #\Space) out)
            (sb-ext:process-exit-code p))))

(defun proc-stream-string (stream)
  (with-output-to-string (s)
    (loop for l = (read-line stream nil nil) while l do (write-line l s))))

(defun valgrind-check (exe)
  (let ((p (sb-ext:run-program "/usr/bin/valgrind"
                               (list "--error-exitcode=2"
                                     "--leak-check=full" "-q" exe)
                               :output nil :error nil)))
    (sb-ext:process-wait p)
    (zerop (sb-ext:process-exit-code p))))

(defun asan-check (c-path runtime-key)
  "Rebuild c-path with ASan+UBSan and run it. t = clean, nil = sanitizer
   diagnostic, :skip = toolchain can't build sanitized. Exit code is
   ignored (programs legitimately exit non-zero in :exit mode); only a
   sanitizer report on stderr counts as failure."
  (let* ((exe (concatenate 'string *test-exe* ".asan"))
         (args (append (list "-fsanitize=address,undefined"
                             "-fno-sanitize-recover=undefined"
                             "-DSYSP_ALLOC_AUDIT"
                             "-g" "-O1" "-Isrc" "-Iruntime" "-o" exe c-path)
                       (runtime-srcs runtime-key)))
         (cc (sb-ext:run-program "/usr/bin/cc" args :output nil :error nil)))
    (if (not (zerop (sb-ext:process-exit-code cc)))
        :skip
        (let ((p (sb-ext:run-program
                  exe nil
                  :environment (cons "ASAN_OPTIONS=detect_leaks=0:abort_on_error=1"
                                     (sb-ext:posix-environ))
                  :output nil :error :stream)))
          (let ((err (proc-stream-string (sb-ext:process-error p))))
            (sb-ext:process-wait p)
            (not (or (search "Sanitizer" err)
                     (search "runtime error:" err)
                     (search "SYSP_LEAK" err))))))))

(defun leaks-check (exe)
  "macOS `leaks`. t = no leaks, nil = leaks, :skip = tool couldn't run
   (SIP/attach failure — surfaced, not silently passed)."
  (let* ((p (sb-ext:run-program "/usr/bin/leaks"
                                (list "--atExit" "--" exe)
                                :output :stream :error nil))
         (out (proc-stream-string (sb-ext:process-output p))))
    (sb-ext:process-wait p)
    (cond ((search "0 leaks for 0 total leaked bytes" out) t)
          ((search " leaks for " out) nil)
          (t :skip))))

(defun run-valgrind (c-path exe runtime-key)
  "Memory-safety gate. valgrind when present (Linux/CI); otherwise the
   macOS substitute: ASan+UBSan (use-after-free / overflow / UB) plus
   `leaks` (leak detection). Together these cover valgrind memcheck +
   leak-check. Returns t (clean), nil (real failure), or :skip ONLY when
   no usable tool exists — and a :skip is reported loudly, never swallowed."
  (cond
    ((probe-file "/usr/bin/valgrind") (valgrind-check exe))
    ((probe-file "/usr/bin/leaks")
     (let ((a (asan-check c-path runtime-key))
           (l (leaks-check exe)))
       (cond ((or (eq a :skip) (eq l :skip)) :skip)
             ((and a l) t)
             (t nil))))
    (t :skip)))

(defun write-c-source (preamble program-src driver path)
  (with-open-file (s path :direction :output :if-exists :supersede)
    (write-string preamble s)
    (write-string program-src s) (terpri s)
    (write-string driver s)))

(defun check-prog (label defns driver expected
                   &key (mode :stdout) (runtime :value)
                        (preamble *default-preamble*)
                        valgrind)
  "Compile defns + driver, run, compare against expected.
   mode :stdout — compare trimmed stdout (expected is a string).
   mode :exit   — compare process exit code (expected is an int)."
  (format t "~a:" label)
  (write-c-source preamble (program-c defns) driver *test-c-file*)
  (when (cc-build *test-c-file* *test-exe* runtime)
    (multiple-value-bind (got code) (run-and-capture *test-exe*)
      (case mode
        (:stdout
         (cond ((string= got expected)
                (incf *ok*) (format t " ok (~a)~%" got))
               (t (incf *fail*)
                  (format t " FAIL got ~s want ~s~%" got expected))))
        (:exit
         (cond ((= code expected)
                (incf *ok*) (format t " ok (exit ~a)~%" code))
               (t (incf *fail*)
                  (format t " FAIL exit ~a want ~a~%" code expected)))))
      (when valgrind
        (case (run-valgrind *test-c-file* *test-exe* runtime)
          (:skip (incf *mem-skipped*)
                 (format t "  MEM SKIP (no valgrind/leaks)~%"))
          ((nil) (incf *fail*) (format t "  MEM FAIL~%")))))))

(defun report-and-exit ()
  (format t "~%~a passed, ~a failed~%" *ok* *fail*)
  (unless (zerop *mem-skipped*)
    (format t "WARNING: ~a memory-safety check(s) skipped — no valgrind or leaks~%"
            *mem-skipped*))
  (unless (zerop *fail*) (sb-ext:exit :code 1)))
