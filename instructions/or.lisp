(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "../subtables/or")

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

;; 32-BIT VERSION

(define or-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 8))
       (x8-2 (part-select x :low  8 :width 8))
       (x8-1 (part-select x :low 16 :width 8))
       (x8-0 (part-select x :low 24 :width 8))
       (y8-3 (part-select y :low  0 :width 8))
       (y8-2 (part-select y :low  8 :width 8))
       (y8-1 (part-select y :low 16 :width 8))
       (y8-0 (part-select y :low 24 :width 8))
       ;; Lookup semantics
       (w0   (logior x8-0 y8-0))
       (w1   (logior x8-1 y8-1))
       (w2   (logior x8-2 y8-2))
       (w3   (logior x8-3 y8-3)))
      ;; Combine
      (merge-4-u8s w0 w1 w2 w3)))

(define or-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 8))
       (x8-2 (part-select x :low  8 :width 8))
       (x8-1 (part-select x :low 16 :width 8))
       (x8-0 (part-select x :low 24 :width 8))
       (y8-3 (part-select y :low  0 :width 8))
       (y8-2 (part-select y :low  8 :width 8))
       (y8-1 (part-select y :low 16 :width 8))
       (y8-0 (part-select y :low 24 :width 8))
       ;; Materialize subtables 
       (indices      (create-tuple-indices (expt 2 8) (expt 2 8)))
       (or-subtable  (materialize-or-subtable  indices))
       ;; Perform lookups
       (w0   (tuple-lookup x8-0 y8-0 or-subtable))
       (w1   (tuple-lookup x8-1 y8-1 or-subtable))
       (w2   (tuple-lookup x8-2 y8-2 or-subtable))
       (w3   (tuple-lookup x8-3 y8-3 or-subtable)))
      ;; Combine
      (merge-4-u8s w0 w1 w2 w3)))

(defthm or-32-or-semantics-32-equiv
 (equal (or-32 x y) (or-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (or-32 or-semantics-32) ((:e expt))))))

;; Semantic correctness of or
(gl::def-gl-thm or-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (or-semantics-32 x y) (logior x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm or-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (or-32 x y) (logior x y))))


;; 64-BIT VERSION

(define or-semantics-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Chunk
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
       ;; Lookup semantics
       (w0   (logior x8-0 y8-0))
       (w1   (logior x8-1 y8-1))
       (w2   (logior x8-2 y8-2))
       (w3   (logior x8-3 y8-3))
       (w4   (logior x8-4 y8-4))
       (w5   (logior x8-5 y8-5))
       (w6   (logior x8-6 y8-6))
       (w7   (logior x8-7 y8-7)))
      ;; COMBINE
      (merge-8-u8s w0 w1 w2 w3 w4 w5 w6 w7)))

(define or-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Chunk
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
       ;; Materialize subtables 
       (indices            (create-tuple-indices (expt 2 8) (expt 2 8)))
       (or-subtable        (materialize-or-subtable  indices))
       ;; Perform lookups
       (w0   (tuple-lookup x8-0 y8-0 or-subtable))
       (w1   (tuple-lookup x8-1 y8-1 or-subtable))
       (w2   (tuple-lookup x8-2 y8-2 or-subtable))
       (w3   (tuple-lookup x8-3 y8-3 or-subtable))
       (w4   (tuple-lookup x8-4 y8-4 or-subtable))
       (w5   (tuple-lookup x8-5 y8-5 or-subtable))
       (w6   (tuple-lookup x8-6 y8-6 or-subtable))
       (w7   (tuple-lookup x8-7 y8-7 or-subtable)))
      ;; Combine
      (merge-8-u8s w0 w1 w2 w3 w4 w5 w6 w7)))

(defthm or-64-or-semantics-64-equiv
 (equal (or-64 x y)
	(or-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (or-64 or-semantics-64) ((:e expt))))))

;; Semantic correctness of or
(gl::def-gl-thm or-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (or-semantics-64 x y) (logior x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))

(defthm or-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (or-64 x y) (logior x y))))
