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

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(define sltu-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
      (+    z0
         (* z1 w0)
         (* z2 w0 w1)
	 (* z3 w0 w1 w2))))

;; Define sltu with lookups to subtables
(define sltu-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
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
       (indices      (create-x-indices (expt 2 8) (expt 2 8)))
       (ltu-subtable (materialize-ltu-subtable indices))
       (eq-subtable  (materialize-eq-subtable indices))
       ;; LOOKUPS
       (z0   (lookup x8-0 y8-0 ltu-subtable))
       (z1   (lookup x8-1 y8-1 ltu-subtable))
       (z2   (lookup x8-2 y8-2 ltu-subtable))
       (z3   (lookup x8-3 y8-3 ltu-subtable))
       (w0   (lookup x8-0 y8-0  eq-subtable))
       (w1   (lookup x8-1 y8-1  eq-subtable))
       (w2   (lookup x8-2 y8-2  eq-subtable))
       (?w3  (lookup x8-3 y8-3  eq-subtable))) ;; ignore w3
      ;; COMBINE
      (+    z0
         (* z1 w0)
         (* z2 w0 w1)
	 (* z3 w0 w1 w2))))

(in-theory (disable (:EXECUTABLE-COUNTERPART EXPT)))

(defthm sltu-semantics-when-0
 (implies (or (not (unsigned-byte-p 32 x)) (not (unsigned-byte-p 32 y)))
	  (equal (sltu-semantics-32 x y) 0))
 :hints (("Goal" :use ((:instance sltu-semantics-32)))))

(defthm sltu-32-sltu-semantics-32-equiv
 (equal (sltu-32 x y)
	(sltu-semantics-32 x y))
 :hints (("goal" :in-theory (e/d (sltu-32 sltu-semantics-32) ((:e create-x-indices))))))
	         
;; SEMANTIC CORRECTNESS OF SLTU
(gl::def-gl-thm sltu-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (sltu-semantics-32 x y)
	       (if (< x y) 1 0))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

;; CORRECTNESS OF SLTU
(defthm sltu-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (sltu-semantics-32 x y) (if (< x y) 1 0))))
