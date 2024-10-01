(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../subtables/srl")

(include-book "centaur/fgl/top" :dir :system)
(value-triple (acl2::tshell-ensure))

;; SRL-semantics-32
(define srl-semantics-32 (x y)
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p  5 y)) 0)
       ;; chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       ;; shift chunks
       (u8-0 (ash      u8-0     (- y)))
       (u8-1 (ash (ash u8-1  8) (- y)))
       (u8-2 (ash (ash u8-2 16) (- y)))
       (u8-3 (ash (ash u8-3 24) (- y))))
       ;; add chunks
      (+ u8-3 u8-2 u8-1 u8-0)))

;; SRL-32 (with lookups)
(define srl-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p  5 y)) 0)
       ;; setup subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 5)))
       (subtable-0 (materialize-srli-subtable indices  0))
       (subtable-1 (materialize-srli-subtable indices  8))
       (subtable-2 (materialize-srli-subtable indices 16))
       (subtable-3 (materialize-srli-subtable indices 24))
       ;; chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       ;; shift chunks
       (u8-0 (tuple-lookup u8-0 y subtable-0))
       (u8-1 (tuple-lookup u8-1 y subtable-1))
       (u8-2 (tuple-lookup u8-2 y subtable-2))
       (u8-3 (tuple-lookup u8-3 y subtable-3)))
       ;; add chunks
      (+ u8-3 u8-2 u8-1 u8-0)))

;; This lemma must be proven with GL and not FGL
(local
 (gl::def-gl-thm aux-lemma
  :hyp  (and (integerp x) (<= 0 x) (< x 4294967296))
  :concl (not (< 256 (logtail 24 x)))
  :g-bindings (gl::auto-bindings (:nat x 32))))

(defthm srl-32-srl-semantics-32-equiv
 (equal (srl-32 x y) (srl-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (srl-semantics-32 srl-32) ((:e create-tuple-indices))))))

(fgl::def-fgl-thm srl-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
 :concl (equal (srl-semantics-32 x y) (ash x (- y))))

(defthm srl-chunk-lookup-combine-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
          (equal (srl-32 x y) (ash x (- y))))
 :hints (("Goal" :use ((:instance srl-semantics-32-correctness) 
		       (:instance srl-32-srl-semantics-32-equiv)))))
