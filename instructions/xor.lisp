(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)
;; idk why the following two books are necessary
(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "../subtables/xor")

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

;; 32-BIT VERSION

(define xor-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
       (w0   (logxor x8-0 y8-0))
       (w1   (logxor x8-1 y8-1))
       (w2   (logxor x8-2 y8-2))
       (w3   (logxor x8-3 y8-3)))
      ;; COMBINE
      (merge-4-u8s w0 w1 w2 w3)))

(define xor-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
       (xor-subtable  (materialize-xor-subtable  indices))
       ;; LOOKUPS
       (w0   (tuple-lookup x8-0 y8-0 xor-subtable))
       (w1   (tuple-lookup x8-1 y8-1 xor-subtable))
       (w2   (tuple-lookup x8-2 y8-2 xor-subtable))
       (w3   (tuple-lookup x8-3 y8-3 xor-subtable)))
      ;; COMBINE
      (merge-4-u8s w0 w1 w2 w3)))

(defthm xor-32-xor-semantics-32-equiv
 (equal (xor-32 x y) (xor-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (xor-32 xor-semantics-32) ((:e expt))))))

;; SEMANTIC CORRECTNESS OF XOR
(gl::def-gl-thm xor-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (xor-semantics-32 x y) (logxor x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm xor-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (xor-32 x y) (logxor x y))))


;; 64-BIT VERSION

(define xor-semantics-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
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
       (w0   (logxor x8-0 y8-0))
       (w1   (logxor x8-1 y8-1))
       (w2   (logxor x8-2 y8-2))
       (w3   (logxor x8-3 y8-3))
       (w4   (logxor x8-4 y8-4))
       (w5   (logxor x8-5 y8-5))
       (w6   (logxor x8-6 y8-6))
       (w7   (logxor x8-7 y8-7)))
      ;; COMBINE
      (merge-8-u8s w0 w1 w2 w3 w4 w5 w6 w7)))

(define xor-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
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
       (indices            (create-tuple-indices (expt 2 8) (expt 2 8)))
       (xor-subtable        (materialize-xor-subtable  indices))
       ;; LOOKUPS
       (w0   (tuple-lookup x8-0 y8-0 xor-subtable))
       (w1   (tuple-lookup x8-1 y8-1 xor-subtable))
       (w2   (tuple-lookup x8-2 y8-2 xor-subtable))
       (w3   (tuple-lookup x8-3 y8-3 xor-subtable))
       (w4   (tuple-lookup x8-4 y8-4 xor-subtable))
       (w5   (tuple-lookup x8-5 y8-5 xor-subtable))
       (w6   (tuple-lookup x8-6 y8-6 xor-subtable))
       (w7   (tuple-lookup x8-7 y8-7 xor-subtable)))
      ;; COMBINE
      (merge-8-u8s w0 w1 w2 w3 w4 w5 w6 w7)))

(defthm xor-64-xor-semantics-64-equiv
 (equal (xor-64 x y)
	(xor-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (xor-64 xor-semantics-64) ((:e expt))))))

;; SEMANTIC CORRECTNESS OF XOR
(gl::def-gl-thm xor-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (xor-semantics-64 x y) (logxor x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))

(defthm xor-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (xor-64 x y) (logxor x y))))