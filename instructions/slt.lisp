(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)
;; idk why the following two books are necessary
(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "../ltu")
(include-book "../eq")
(include-book "../eq-abs")
(include-book "../lt-abs")
(include-book "../left-msb")
(include-book "../right-msb")

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(define slt-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low  0 :width 8))
       (x8-2 (part-select x :low  8 :width 8))
       (x8-1 (part-select x :low 16 :width 8))
       (x8-0 (part-select x :low 24 :width 8))
       (y8-3 (part-select y :low  0 :width 8))
       (y8-2 (part-select y :low  8 :width 8))
       (y8-1 (part-select y :low 16 :width 8))
       (y8-0 (part-select y :low 24 :width 8))
       ;; LOOKUP SEMANTICS
       (L    (logbit 7 x8-0))
       (R    (logbit 7 y8-0))
       (Z0   (if (< (loghead 7 x8-0) (loghead 7 y8-0)) 1 0))
       (z1   (if (< x8-1 y8-1) 1 0))
       (z2   (if (< x8-2 y8-2) 1 0))
       (z3   (if (< x8-3 y8-3) 1 0))
       (w0   (if (= (loghead 7 x8-0) (loghead 7 y8-0)) 1 0))
       (w1   (if (= x8-1 y8-1) 1 0))
       (w2   (if (= x8-2 y8-2) 1 0))
       (?w3  (if (= x8-3 y8-3) 1 0))) ;; ignore w3
      ;; COMBINE
      (b-xor (b-and L (b-xor R 1))
	     (b-and (b-xor (b-and (b-xor L 1) (b-xor R 1)) (b-and L R))
                    (+    z0
                       (* z1 w0)
                       (* z2 w0 w1)
	               (* z3 w0 w1 w2))))))

(define slt-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low  0 :width 8))
       (x8-2 (part-select x :low  8 :width 8))
       (x8-1 (part-select x :low 16 :width 8))
       (x8-0 (part-select x :low 24 :width 8))
       (y8-3 (part-select y :low  0 :width 8))
       (y8-2 (part-select y :low  8 :width 8))
       (y8-1 (part-select y :low 16 :width 8))
       (y8-0 (part-select y :low 24 :width 8))
       ;; MATERIALIZE SUBTABLES 
       (indices            (create-x-indices (expt 2 8) (expt 2 8)))
       (eq-subtable        (materialize-eq-subtable          indices))
       (ltu-subtable       (materialize-ltu-subtable         indices))
       (eq-abs-subtable    (materialize-eq-abs-8-subtable    indices))
       (lt-abs-subtable    (materialize-lt-abs-8-subtable    indices))
       (left-msb-subtable  (materialize-left-msb-8-subtable  indices))
       (right-msb-subtable (materialize-right-msb-8-subtable indices))
       ;; LOOKUPS
       (L    (lookup x8-0 y8-0 left-msb-subtable))
       (R    (lookup x8-0 y8-0 right-msb-subtable))

       (Z0   (lookup x8-0 y8-0 lt-abs-subtable))

       (z1   (lookup x8-1 y8-1 ltu-subtable))
       (z2   (lookup x8-2 y8-2 ltu-subtable))
       (z3   (lookup x8-3 y8-3 ltu-subtable))

       (W0   (lookup x8-0 y8-0 eq-abs-subtable))

       (w1   (lookup x8-1 y8-1 eq-subtable))
       (w2   (lookup x8-2 y8-2 eq-subtable))
       (?w3  (lookup x8-3 y8-3 eq-subtable))) ;; ignore w3
      ;; COMBINE
      (b-xor (b-and L (b-xor R 1))
	     (b-and (b-xor (b-and (b-xor L 1) (b-xor R 1)) (b-and L R))
                    (+    z0
                       (* z1 w0)
                       (* z2 w0 w1)
	               (* z3 w0 w1 w2))))))

(defthm slt-32-slt-semantics-32-equiv
 (equal (slt-32 x y)
	(slt-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (slt-32 slt-semantics-32) ((:e expt) (:e create-x-indices))))))

;; SEMANTIC CORRECTNESS OF SLT
(gl::def-gl-thm slt-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (slt-semantics-32 x y)
	       (if (< (logext 32 x) (logext 32 y)) 1 0))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm slt-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (slt-32 x y)
		 (if (< (logext 32 x) (logext 32 y)) 1 0))))
