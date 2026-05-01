#!/usr/bin/env bash
# Compile the interpreter (interp.sysp) using sysp-ir.
set -e
cd "$(dirname "$0")/.."

cat > /tmp/compile-interp.lisp <<'EOF'
(load "src/load.lisp")
(in-package :sysp-ir)
(with-open-file (out "runtime/interp.c"
                     :direction :output :if-exists :supersede)
  (compile-program (parse-file "runtime/interp.sysp") out))
EOF
sbcl --script /tmp/compile-interp.lisp

cc -O2 -o runtime/interp \
   -Iruntime \
   runtime/value.c runtime/interp.c

echo "built runtime/interp"
