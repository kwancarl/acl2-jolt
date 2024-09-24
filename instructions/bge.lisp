(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)
;; idk why the following two books are necessary
(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "slt")

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

;; 32-BIT VERSION

(define bge-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
      ;; (- 1 (slt-32-semantics x y))
      (- 1 (b-xor (b-and L (b-xor R 1))
	     (b-and (b-xor (b-and (b-xor L 1) (b-xor R 1)) (b-and L R))
                    (+    z0
                       (* z1 w0)
                       (* z2 w0 w1)
	               (* z3 w0 w1 w2)))))))

(define bge-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
      ;; (- 1 (slt-32 x y))
      (- 1 (b-xor (b-and L (b-xor R 1))
	     (b-and (b-xor (b-and (b-xor L 1) (b-xor R 1)) (b-and L R))
                    (+    z0
                       (* z1 w0)
                       (* z2 w0 w1)
	               (* z3 w0 w1 w2)))))))

(defthm bge-32-bge-semantics-32-equiv
 (equal (bge-32 x y)
	(bge-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (bge-32 bge-semantics-32) ((:e expt) (:e create-x-indices))))))

;; SEMANTIC CORRECTNESS OF BGE
(gl::def-gl-thm bge-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (bge-semantics-32 x y)
	       (if (>= (logext 32 x) (logext 32 y)) 1 0))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm bge-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (bge-32 x y)
		 (if (>= (logext 32 x) (logext 32 y)) 1 0))))


;; 64-BIT VERSION

(define bge-semantics-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; CHUNK
       (x8-7 (part-select x :low  0 :width 8))
       (x8-6 (part-select x :low  8 :width 8))
       (x8-5 (part-select x :low 16 :width 8))
       (x8-4 (part-select x :low 24 :width 8))
       (x8-3 (part-select x :low 32 :width 8))
       (x8-2 (part-select x :low 40 :width 8))
       (x8-1 (part-select x :low 48 :width 8))
       (x8-0 (part-select x :low 56 :width 8))
       (y8-7 (part-select y :low  0 :width 8))
       (y8-6 (part-select y :low  8 :width 8))
       (y8-5 (part-select y :low 16 :width 8))
       (y8-4 (part-select y :low 24 :width 8))
       (y8-3 (part-select y :low 32 :width 8))
       (y8-2 (part-select y :low 40 :width 8))
       (y8-1 (part-select y :low 48 :width 8))
       (y8-0 (part-select y :low 56 :width 8))
       ;; LOOKUP SEMANTICS
       (L    (logbit 7 x8-0))
       (R    (logbit 7 y8-0))

       (z0   (if (< (loghead 7 x8-0) (loghead 7 y8-0)) 1 0))
       (z1   (if (< x8-1 y8-1) 1 0))
       (z2   (if (< x8-2 y8-2) 1 0))
       (z3   (if (< x8-3 y8-3) 1 0))
       (z4   (if (< x8-4 y8-4) 1 0))
       (z5   (if (< x8-5 y8-5) 1 0))
       (z6   (if (< x8-6 y8-6) 1 0))
       (z7   (if (< x8-7 y8-7) 1 0))

       (w0   (if (= (loghead 7 x8-0) (loghead 7 y8-0)) 1 0))
       (w1   (if (= x8-1 y8-1) 1 0))
       (w2   (if (= x8-2 y8-2) 1 0))
       (w3   (if (= x8-3 y8-3) 1 0))
       (w4   (if (= x8-4 y8-4) 1 0))
       (w5   (if (= x8-5 y8-5) 1 0))
       (w6   (if (= x8-6 y8-6) 1 0))
       (?w7  (if (= x8-7 y8-7) 1 0))) ;; ignore w7
      ;; COMBINE
      ;; (- 1 (slt-64-semantics x y))
      (- 1 (b-xor (b-and L (b-xor R 1))
	     (b-and (b-xor (b-and (b-xor L 1) (b-xor R 1)) (b-and L R))
        (+   z0
          (* z1 w0)
          (* z2 w0 w1)
          (* z3 w0 w1 w2)
          (* z4 w0 w1 w2 w3)
          (* z5 w0 w1 w2 w3 w4)
          (* z6 w0 w1 w2 w3 w4 w5)
          (* z7 w0 w1 w2 w3 w4 w5 w6)))))))

(define bge-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; CHUNK
       (x8-7 (part-select x :low  0 :width 8))
       (x8-6 (part-select x :low  8 :width 8))
       (x8-5 (part-select x :low 16 :width 8))
       (x8-4 (part-select x :low 24 :width 8))
       (x8-3 (part-select x :low 32 :width 8))
       (x8-2 (part-select x :low 40 :width 8))
       (x8-1 (part-select x :low 48 :width 8))
       (x8-0 (part-select x :low 56 :width 8))
       (y8-7 (part-select y :low  0 :width 8))
       (y8-6 (part-select y :low  8 :width 8))
       (y8-5 (part-select y :low 16 :width 8))
       (y8-4 (part-select y :low 24 :width 8))
       (y8-3 (part-select y :low 32 :width 8))
       (y8-2 (part-select y :low 40 :width 8))
       (y8-1 (part-select y :low 48 :width 8))
       (y8-0 (part-select y :low 56 :width 8))
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
       (z4   (lookup x8-4 y8-4 ltu-subtable))
       (z5   (lookup x8-5 y8-5 ltu-subtable))
       (z6   (lookup x8-6 y8-6 ltu-subtable))
       (z7   (lookup x8-7 y8-7 ltu-subtable))

       (W0   (lookup x8-0 y8-0 eq-abs-subtable))

       (w1   (lookup x8-1 y8-1 eq-subtable))
       (w2   (lookup x8-2 y8-2 eq-subtable))
       (w3   (lookup x8-3 y8-3 eq-subtable))
       (w4   (lookup x8-4 y8-4 eq-subtable))
       (w5   (lookup x8-5 y8-5 eq-subtable))
       (w6   (lookup x8-6 y8-6 eq-subtable))
       (?w7  (lookup x8-7 y8-7 eq-subtable))) ;; ignore w7
      ;; COMBINE
      ;; (- 1 (slt-64 x y))
      (- 1 (b-xor (b-and L (b-xor R 1))
	     (b-and (b-xor (b-and (b-xor L 1) (b-xor R 1)) (b-and L R))
        (+   z0
          (* z1 w0)
          (* z2 w0 w1)
          (* z3 w0 w1 w2)
          (* z4 w0 w1 w2 w3)
          (* z5 w0 w1 w2 w3 w4)
          (* z6 w0 w1 w2 w3 w4 w5)
          (* z7 w0 w1 w2 w3 w4 w5 w6)))))))

(defthm bge-64-bge-semantics-64-equiv
 (equal (bge-64 x y)
	(bge-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (bge-64 bge-semantics-64) ((:e expt) (:e create-x-indices))))))

;; SEMANTIC CORRECTNESS OF BGE
(gl::def-gl-thm bge-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (bge-semantics-64 x y)
	       (if (>= (logext 64 x) (logext 64 y)) 1 0))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))

(defthm bge-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (bge-64 x y)
		 (if (>= (logext 64 x) (logext 64 y)) 1 0))))