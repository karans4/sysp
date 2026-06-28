(load "tests/common.lisp")
(in-package :sysp-ir)

;; Basic struct: construct, read field
(check-prog "make-and-read"
            '((defstruct POINT ((x :int) (y :int)))
              (defn px ((p :POINT)) :int (get-field p x))
              (defn py ((p :POINT)) :int (get-field p y))
              (defn make-pt () :POINT (POINT 3 7)))
            "int main(){
  POINT p = make_pt();
  printf(\"%d %d\\n\", px(p), py(p)); return 0; }"
            "3 7")

;; Mutate via set-field! through a pointer
(check-prog "mutate-via-ptr"
            '((defstruct CELL ((v :int)))
              (defn bump ((c :ptr-CELL)) :unit
                (set-field! c v (+ (get-field c v) 1))))
            "int main(){
  CELL c = (CELL){10};
  bump(&c); bump(&c); bump(&c);
  printf(\"%d\\n\", c.v); return 0; }"
            "13")

;; The 6502-flavored test: build a register file struct, read fields
(check-prog "cpu-style"
            '((defstruct CPU ((a :u8) (x :u8) (y :u8) (sp :u8) (pc :int) (status :u8)))
              (defn make-cpu () :CPU (CPU 0 0 0 253 0 36))
              (defn cpu-a ((c :CPU)) :int (get-field c a))
              (defn cpu-pc ((c :CPU)) :int (get-field c pc)))
            "int main(){
  CPU c = make_cpu();
  printf(\"%d %d %d\\n\", cpu_a(c), c.sp, cpu_pc(c)); return 0; }"
            "0 253 0")

;; set-field! over an rc'd (String) field must release the overwritten
;; value, not just store over it. Before the fix the old "aaa" leaked; the
;; memory gate (alloc audit) catches it.
(check-prog "set-field-rc-releases-old"
            '((defstruct HOLDER ((s :string)))
              (defn run () :int
                (let ((a "aaa") (b "bbb"))
                  (let ((h (HOLDER a)))
                    (do (set-field! h s b)
                        (string-len (get h s)))))))
            "int main(){ printf(\"%d\\n\", run()); return 0; }"
            "3" :valgrind t)

(report-and-exit)
