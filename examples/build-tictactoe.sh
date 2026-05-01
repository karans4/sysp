#!/usr/bin/env bash
# Build script for the tictactoe demo.
set -e
cd "$(dirname "$0")/.."

cat > /tmp/build-tt.lisp <<'EOF'
(load "src/load.lisp")
(in-package :sysp-ir)
(with-open-file (out "examples/tictactoe.c"
                     :direction :output :if-exists :supersede)
  (format out "#include <stdint.h>~%")
  (format out "#include <stdlib.h>~%")
  (compile-program (parse-file "examples/tictactoe.sysp") out))
EOF
sbcl --script /tmp/build-tt.lisp

# 2. Compile generated C, link against raylib (no shim).
cc -O2 -o examples/tictactoe examples/tictactoe.c \
   -I/usr/local/include -L/usr/local/lib -lraylib -lm

echo "built examples/tictactoe"
