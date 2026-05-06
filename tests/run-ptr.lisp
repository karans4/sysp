(load "tests/common.lisp")
(in-package :sysp-ir)

;; addr-of + deref via a helper that reads through a pointer
(check-prog "addr-deref"
            '((defn read-via-ptr ((p :ptr-int)) :int (deref p)))
            "int main(){ int x = 42; printf(\"%d\\n\", read_via_ptr(&x)); return 0; }"
            "42")

;; ptr-ref (array indexing)
(check-prog "ptr-ref"
            '((extern malloc ((n :size)) :ptr-void)
              (extern free ((p :ptr-void)) :unit)
              (defn array-third () :int
                (let ((arr (cast :ptr-int (malloc (cast :size 32)))))
                  (ptr-set-at! arr 0 10)
                  (ptr-set-at! arr 1 20)
                  (ptr-set-at! arr 2 30)
                  (ptr-set-at! arr 3 40)
                  (let ((v (ptr-ref arr 2)))
                    (free (cast :ptr-void arr))
                    v))))
            "int main(){ printf(\"%d\\n\", array_third()); return 0; }"
            "30")

;; cast int to u8 on assign to u8 storage (via ptr)
(check-prog "cast-narrow"
            '((extern malloc ((n :size)) :ptr-void)
              (extern free ((p :ptr-void)) :unit)
              (defn store-byte () :int
                (let ((mem (cast :ptr-u8 (malloc (cast :size 16)))))
                  (ptr-set-at! mem 0 (cast :u8 (band #xff #xab)))
                  (let ((b (ptr-ref mem 0)))
                    (free (cast :ptr-void mem))
                    b))))
            "int main(){ printf(\"%d\\n\", store_byte()); return 0; }"
            "171")

(report-and-exit)
