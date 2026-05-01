;;;; Load all sysp-ir source files in dependency order.

(load "src/package.lisp")
(load "src/ir.lisp")
(load "src/lower.lisp")
(load "src/liveness.lisp")
(load "src/arc.lisp")
(load "src/peephole.lisp")
(load "src/emit.lisp")
(load "src/pp.lisp")
(load "src/compiler.lisp")
