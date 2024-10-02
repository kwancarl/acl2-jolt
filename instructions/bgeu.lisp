(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "sltu")

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

;; 32-BIT VERSION

(define bgeu-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
       (z0   (if (< x8-0 y8-0) 1 0))
       (z1   (if (< x8-1 y8-1) 1 0))
       (z2   (if (< x8-2 y8-2) 1 0))
       (z3   (if (< x8-3 y8-3) 1 0))
       (w0   (if (= x8-0 y8-0) 1 0))
       (w1   (if (= x8-1 y8-1) 1 0))
       (w2   (if (= x8-2 y8-2) 1 0))
       (?w3  (if (= x8-3 y8-3) 1 0))) ;; ignore w3
      ;; COMBINE
      (- 1 (+ z0
        (* z1 w0)
        (* z2 w0 w1)
        (* z3 w0 w1 w2)))))

;; Define bgeu with lookups to subtables
(define bgeu-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
       (indices      (create-tuple-indices (expt 2 8) (expt 2 8)))
       (ltu-subtable (materialize-ltu-subtable indices))
       (eq-subtable  (materialize-eq-subtable indices))
       ;; LOOKUPS
       (z0   (tuple-lookup x8-0 y8-0 ltu-subtable))
       (z1   (tuple-lookup x8-1 y8-1 ltu-subtable))
       (z2   (tuple-lookup x8-2 y8-2 ltu-subtable))
       (z3   (tuple-lookup x8-3 y8-3 ltu-subtable))
       (w0   (tuple-lookup x8-0 y8-0  eq-subtable))
       (w1   (tuple-lookup x8-1 y8-1  eq-subtable))
       (w2   (tuple-lookup x8-2 y8-2  eq-subtable))
       (?w3  (tuple-lookup x8-3 y8-3  eq-subtable))) ;; ignore w3
      ;; COMBINE
      (- 1 (+ z0
        (* z1 w0)
        (* z2 w0 w1)
	      (* z3 w0 w1 w2)))))

(in-theory (disable (:EXECUTABLE-COUNTERPART EXPT)))

(defthm bgeu-32-bgeu-semantics-32-equiv
 (equal (bgeu-32 x y)
	(bgeu-semantics-32 x y))
 :hints (("goal" :in-theory (e/d (bgeu-32 bgeu-semantics-32) ((:e create-tuple-indices))))))
	         
;; SEMANTIC CORRECTNESS OF BGEU
(gl::def-gl-thm bgeu-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (bgeu-semantics-32 x y)
	       (if (>= x y) 1 0))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

;; CORRECTNESS OF BGEU
(defthm bgeu-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (bgeu-semantics-32 x y) (if (>= x y) 1 0))))


;; 64-BIT VERSION

(define bgeu-semantics-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
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
       (z0   (if (< x8-0 y8-0) 1 0))
       (z1   (if (< x8-1 y8-1) 1 0))
       (z2   (if (< x8-2 y8-2) 1 0))
       (z3   (if (< x8-3 y8-3) 1 0))
       (z4   (if (< x8-4 y8-4) 1 0))
       (z5   (if (< x8-5 y8-5) 1 0))
       (z6   (if (< x8-6 y8-6) 1 0))
       (z7   (if (< x8-7 y8-7) 1 0))
       (w0   (if (= x8-0 y8-0) 1 0))
       (w1   (if (= x8-1 y8-1) 1 0))
       (w2   (if (= x8-2 y8-2) 1 0))
       (w3   (if (= x8-3 y8-3) 1 0))
       (w4   (if (= x8-4 y8-4) 1 0))
       (w5   (if (= x8-5 y8-5) 1 0))
       (w6   (if (= x8-6 y8-6) 1 0))
       (?w7  (if (= x8-7 y8-7) 1 0))) ;; ignore w7
       ;; COMBINE
       (- 1 (+ z0
        (* z1 w0)
        (* z2 w0 w1)
        (* z3 w0 w1 w2)
        (* z4 w0 w1 w2 w3)
        (* z5 w0 w1 w2 w3 w4)
        (* z6 w0 w1 w2 w3 w4 w5)
        (* z7 w0 w1 w2 w3 w4 w5 w6)))))

;; Define bgeu with lookups to subtables
(define bgeu-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
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
       (indices      (create-tuple-indices (expt 2 8) (expt 2 8)))
       (ltu-subtable (materialize-ltu-subtable indices))
       (eq-subtable  (materialize-eq-subtable indices))
       ;; LOOKUPS
       (z0   (tuple-lookup x8-0 y8-0 ltu-subtable))
       (z1   (tuple-lookup x8-1 y8-1 ltu-subtable))
       (z2   (tuple-lookup x8-2 y8-2 ltu-subtable))
       (z3   (tuple-lookup x8-3 y8-3 ltu-subtable))
       (z4   (tuple-lookup x8-4 y8-4 ltu-subtable))
       (z5   (tuple-lookup x8-5 y8-5 ltu-subtable))
       (z6   (tuple-lookup x8-6 y8-6 ltu-subtable))
       (z7   (tuple-lookup x8-7 y8-7 ltu-subtable))
       (w0   (tuple-lookup x8-0 y8-0  eq-subtable))
       (w1   (tuple-lookup x8-1 y8-1  eq-subtable))
       (w2   (tuple-lookup x8-2 y8-2  eq-subtable))
       (w3   (tuple-lookup x8-3 y8-3  eq-subtable))
       (w4   (tuple-lookup x8-4 y8-4  eq-subtable))
       (w5   (tuple-lookup x8-5 y8-5  eq-subtable))
       (w6   (tuple-lookup x8-6 y8-6  eq-subtable))
       (?w7  (tuple-lookup x8-7 y8-7  eq-subtable))) ;; ignore w7
      ;; COMBINE
      (- 1 (+ z0
        (* z1 w0)
        (* z2 w0 w1)
        (* z3 w0 w1 w2)
        (* z4 w0 w1 w2 w3)
        (* z5 w0 w1 w2 w3 w4)
        (* z6 w0 w1 w2 w3 w4 w5)
        (* z7 w0 w1 w2 w3 w4 w5 w6)))))

(in-theory (disable (:EXECUTABLE-COUNTERPART EXPT)))

(defthm bgeu-64-bgeu-semantics-64-equiv
 (equal (bgeu-64 x y)
	(bgeu-semantics-64 x y))
 :hints (("goal" :in-theory (e/d (bgeu-64 bgeu-semantics-64) ((:e create-tuple-indices))))))

;; SEMANTIC CORRECTNESS OF SLTU
(gl::def-gl-thm bgeu-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (bgeu-semantics-64 x y)
	       (if (>= x y) 1 0))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))

;; CORRECTNESS OF SLTU
(defthm bgeu-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (bgeu-semantics-64 x y) (if (>= x y) 1 0))))