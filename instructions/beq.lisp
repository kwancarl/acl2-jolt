(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)
;; idk why the following two books are necessary
(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "../eq")

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

;; 32-BIT VERSION

(define beq-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
       (w0   (if (= x8-0 y8-0) 1 0))
       (w1   (if (= x8-1 y8-1) 1 0))
       (w2   (if (= x8-2 y8-2) 1 0))
       (w3   (if (= x8-3 y8-3) 1 0)))
      ;; COMBINE
      (* w0 w1 w2 w3)))

(define beq-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
       (eq-subtable  (materialize-eq-subtable  indices))
       ;; LOOKUPS
       (w0   (tuple-lookup x8-0 y8-0 eq-subtable))
       (w1   (tuple-lookup x8-1 y8-1 eq-subtable))
       (w2   (tuple-lookup x8-2 y8-2 eq-subtable))
       (w3   (tuple-lookup x8-3 y8-3 eq-subtable)))
      ;; COMBINE
      (* w0 w1 w2 w3)))

(defthm beq-32-beq-semantics-32-equiv
 (equal (beq-32 x y) (beq-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (beq-32 beq-semantics-32) ((:e expt))))))

;; SEMANTIC CORRECTNESS OF BEQ
(gl::def-gl-thm beq-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (beq-semantics-32 x y) (if (= x y) 1 0))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm beq-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (beq-32 x y) (if (= x y) 1 0))))


;; 64-BIT VERSION

(define beq-semantics-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
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
       (w0   (if (= x8-0 y8-0) 1 0))
       (w1   (if (= x8-1 y8-1) 1 0))
       (w2   (if (= x8-2 y8-2) 1 0))
       (w3   (if (= x8-3 y8-3) 1 0))
       (w4   (if (= x8-4 y8-4) 1 0))
       (w5   (if (= x8-5 y8-5) 1 0))
       (w6   (if (= x8-6 y8-6) 1 0))
       (w7   (if (= x8-7 y8-7) 1 0)))
      ;; COMBINE
      (* w0 w1 w2 w3 w4 w5 w6 w7)))

(define beq-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
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
       (eq-subtable  (materialize-eq-subtable  indices))
       ;; LOOKUPS
       (w0   (tuple-lookup x8-0 y8-0 eq-subtable))
       (w1   (tuple-lookup x8-1 y8-1 eq-subtable))
       (w2   (tuple-lookup x8-2 y8-2 eq-subtable))
       (w3   (tuple-lookup x8-3 y8-3 eq-subtable))
       (w4   (tuple-lookup x8-4 y8-4 eq-subtable))
       (w5   (tuple-lookup x8-5 y8-5 eq-subtable))
       (w6   (tuple-lookup x8-6 y8-6 eq-subtable))
       (w7   (tuple-lookup x8-7 y8-7 eq-subtable)))
      ;; COMBINE
      (* w0 w1 w2 w3 w4 w5 w6 w7)))

(defthm beq-64-beq-semantics-64-equiv
 (equal (beq-64 x y) (beq-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (beq-64 beq-semantics-64) ((:e expt))))))

;; SEMANTIC CORRECTNESS OF BEQ
(gl::def-gl-thm beq-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (beq-semantics-64 x y) (if (= x y) 1 0))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))

(defthm beq-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (beq-64 x y) (if (= x y) 1 0))))