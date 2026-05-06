;;;; Stage 17: generic structs.
;;;; (defstruct (Name :T1 :T2 ...) fields) → template; each concrete
;;;; instantiation materializes a per-T struct with substituted field types.

(load "tests/common.lisp")
(in-package :sysp-ir)

;; --- Box<int>: simplest case, value-typed field ---
(check-prog "box-int"
            '((defstruct (Box :T) ((value :T)))
              (defn use () :int (get-field (Box 5) value)))
            "int main(){ printf(\"%d\\n\", use()); return 0; }"
            "5")

;; --- Two materializations of Box at different int widths ---
(check-prog "box-int-and-u8"
            '((defstruct (Box :T) ((value :T)))
              (defn use-int () :int (get-field (Box 42) value))
              (defn use-u8  () :u8  (cast :u8 (get-field (Box 7) value))))
            "int main(){ printf(\"%d %d\\n\", use_int(), use_u8()); return 0; }"
            "42 7")

;; --- Box<String>: rc'd field. Without retain at struct-init + auto
;; <Box_string>_release, the field's buf would be freed at the local's
;; ARC release before main reads it (UAF). Result is the captured string.
(check-prog "box-string"
            '((defstruct (Box :T) ((value :T)))
              (defn make-box ((s :string)) (Box :string) (Box s))
              (defn use () :string
                (let ((b (make-box (string-concat "hello" "_world"))))
                  (get-field b value))))
            "int main(){ String s = use(); sysp_str_print(s); sysp_str_release(s); return 0; }"
            "hello_world")

;; --- Pair<String, int>: mixed rc/non-rc fields. The retain/release walk
;; should only fire on the rc'd one; the int field is left alone.
(check-prog "pair-string-int"
            '((defstruct (Pair :A :B) ((fst :A) (snd :B)))
              (defn name-and-len () :int
                (let ((p (Pair (string-concat "ab" "cd") 99)))
                  (+ (string-len (get-field p fst)) (get-field p snd)))))
            "int main(){ printf(\"%d\\n\", name_and_len()); return 0; }"
            "103")

;; --- Two type params: Pair<int, int> with both fields read ---
(check-prog "pair-int-int"
            '((defstruct (Pair :A :B) ((fst :A) (snd :B)))
              (defn use-fst () :int (get-field (Pair 7 99) fst))
              (defn use-snd () :int (get-field (Pair 7 99) snd)))
            "int main(){ printf(\"%d %d\\n\", use_fst(), use_snd()); return 0; }"
            "7 99")

;; --- Vec<int> with a (:ptr :T) field — generic data structure as
;; library code, with realloc-based growth. Exercises pointer-in-struct,
;; multiple instantiations through poly fns, and realistic memory mgmt.
(check-prog "vec-int-push-realloc"
            '((extern malloc  ((sz :size)) :ptr-void)
              (extern realloc ((p :ptr-void) (sz :size)) :ptr-void)
              (extern free    ((p :ptr-void)) :unit)

              (defstruct (Vec :T) ((data (:ptr :T)) (len :int) (cap :int)))

              (defn vec-empty-i () (Vec :int)
                (Vec (cast (:ptr :int) (cast :ptr-void 0)) 0 0))

              (defn vec-push-i ((v (Vec :int)) (x :int)) (Vec :int)
                (let ((cap (get-field v cap))
                      (len (get-field v len)))
                  (let ((new-cap (if (= len cap)
                                     (if (= cap 0) 4 (* cap 2))
                                   cap)))
                    (let ((data (if (= len cap)
                                    (cast (:ptr :int)
                                          (realloc (cast :ptr-void (get-field v data))
                                                   (cast :size (* new-cap 4))))
                                  (get-field v data))))
                      (ptr-set-at! data len x)
                      (Vec data (+ len 1) new-cap)))))

              (defn use () :int
                (let ((v (vec-empty-i)))
                  (let ((v1 (vec-push-i v  10)))
                    (let ((v2 (vec-push-i v1 20)))
                      (let ((v3 (vec-push-i v2 30)))
                        (+ (ptr-ref (get-field v3 data) 0)
                           (+ (ptr-ref (get-field v3 data) 1)
                              (ptr-ref (get-field v3 data) 2)))))))))
            "int main(){ printf(\"%d\\n\", use()); return 0; }"
            "60")

(report-and-exit)
