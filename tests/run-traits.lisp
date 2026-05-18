(load "tests/common.lisp")
(in-package :sysp-ir)

;; Static dispatch over a struct impl and a primitive impl.
(check-prog "dispatch-struct-and-prim"
            '((defstruct POINT ((x :int) (y :int)))
              (deftrait Show () (show ((self :int)) :int))
              (impl Show (POINT)
                (defn show ((self :POINT)) :int
                  (+ (get-field self x) (get-field self y))))
              (impl Show (int)
                (defn show ((self :int)) :int (* self self)))
              (defn main () :int
                (+ (show (POINT 3 4)) (show 5))))
            "" 32 :mode :exit)

;; Trait call through a function parameter (exercises the type env in
;; both infer and mono-walk).
(check-prog "dispatch-via-param"
            '((defstruct BOX ((v :int)))
              (deftrait Val () (val ((self :int)) :int))
              (impl Val (BOX) (defn val ((self :BOX)) :int (get-field self v)))
              (defn twice ((b :BOX)) :int (+ (val b) (val b)))
              (defn main () :int (twice (BOX 21))))
            "" 42 :mode :exit)

;; Two traits, two methods, dispatch independent per method+type.
(check-prog "two-traits"
            '((defstruct P ((x :int)))
              (deftrait Show () (show ((self :int)) :int))
              (deftrait Neg  () (neg  ((self :int)) :int))
              (impl Show (P)   (defn show ((self :P)) :int (get-field self x)))
              (impl Neg  (P)   (defn neg  ((self :P)) :int (- 0 (get-field self x))))
              (defn main () :int
                (+ (show (P 10)) (neg (P 3)))))
            "" 7 :mode :exit)

;; Trait method whose body itself calls another trait method.
(check-prog "trait-calls-trait"
            '((defstruct Q ((n :int)))
              (deftrait A () (a ((self :int)) :int))
              (deftrait B () (b ((self :int)) :int))
              (impl A (Q) (defn a ((self :Q)) :int (* (get-field self n) 2)))
              (impl B (Q) (defn b ((self :Q)) :int (+ (a self) 1)))
              (defn main () :int (b (Q 20))))
            "" 41 :mode :exit)

;; --- Gettable/Settable: built-in struct-field default ---

(check-prog "get-default-field"
            '((defstruct PT ((x :int) (y :int)))
              (defn main () :int (get (PT 11 31) y)))
            "" 31 :mode :exit)

(check-prog "set-default-field"
            '((defstruct CELL ((v :int)))
              (defn bump ((c :ptr-CELL)) :unit (set! (get c v) 99))
              (defn main () :int
                (let ((c (CELL 1)))
                  (bump (addr-of c))
                  (get c v))))
            "" 99 :mode :exit)

;; --- Gettable/Settable: trait override wins over the default ---

(check-prog "gettable-override"
            '((defstruct BOX ((v :int)))
              (impl Gettable (BOX)
                (defn get ((self :BOX) (i :int)) :int
                  (+ (get-field self v) i)))
              (defn main () :int (get (BOX 40) 2)))
            "" 42 :mode :exit)

(check-prog "settable-override"
            '((defstruct ACC ((v :int)))
              (impl Settable (ptr-ACC)
                (defn set ((self :ptr-ACC) (k :int) (val :int)) :unit
                  (set-field! self v (+ val k))))
              (defn main () :int
                (let ((a (ACC 0)))
                  (set! (get (addr-of a) 1) 9)
                  (get a v))))
            "" 10 :mode :exit)

;; --- Drop: default auto field-walk release of an rc'd field ---
;; The memory gate (alloc audit) fails if the String leaks.

(check-prog "drop-default-rc-field"
            '((defstruct WRAP ((s :string)))
              (defn mk () :WRAP (WRAP (string-concat "ab" "cd")))
              (defn main () :int
                (let ((w (mk))) (string-len (get w s)))))
            "" 4 :mode :exit :valgrind t)

;; --- Drop: a Drop impl overrides the auto destructor. If the override
;; is not invoked at scope exit, the String leaks -> MEM FAIL. ---

(check-prog "drop-impl-override"
            '((extern sysp_str_release ((s :string)) :unit)
              (defstruct WRAP ((s :string)))
              (impl Drop (WRAP)
                (defn drop ((self :ptr-WRAP)) :unit
                  (sysp_str_release (get-field self s))))
              (defn mk () :WRAP (WRAP (string-concat "xy" "zw")))
              (defn main () :int
                (let ((w (mk))) (string-len (get w s)))))
            "" 4 :mode :exit :valgrind t)

;; --- String as a pure library type, pulled in via (use ...) ---
;; Proves "no type is special": Str is a plain struct + trait impls,
;; loaded from lib/string.sysp, with zero compiler special-casing.

(check-prog "string-as-library"
            '((use "lib/string.sysp")
              (defn main () :int
                (+ (show (str-new (cstr "hello")))
                   (slen (str-new (cstr "worldXX"))))))
            "" 12 :mode :exit)

;; --- A collection as a pure library type (Seq + Gettable override) ---

(check-prog "collection-as-library"
            '((use "lib/collections.sysp")
              (defn main () :int
                (let ((v (ivec3 10 20 12)))
                  (+ (seq-len v) (+ (get v 0) (get v 2))))))
            "" 25 :mode :exit)

(report-and-exit)
