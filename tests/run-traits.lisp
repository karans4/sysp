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

(report-and-exit)
