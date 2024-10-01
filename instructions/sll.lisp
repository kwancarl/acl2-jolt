(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../subtables/sll")

(include-book "centaur/fgl/top" :dir :system)
(value-triple (acl2::tshell-ensure))

;; 32-BIT

;; SLL-semantics-32
(define sll-semantics-32 (x y)
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (shift-amount (part-select y :low 0 :width 5))
       ;; shift chunks
       (u8-0 (ash u8-0 (+ shift-amount  0) ))
       (u8-1 (ash u8-1 (+ shift-amount  8)))
       (u8-2 (ash u8-2 (+ shift-amount 16)))
       (u8-3 (ash u8-3 (+ shift-amount 24))))
       ;; add chunks
      (+ u8-3 u8-2 u8-1 u8-0)))


;; SLL-32 (with lookups)
(define sll-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; setup subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 5)))
       (subtable-0 (materialize-slli-subtable indices  0))
       (subtable-1 (materialize-slli-subtable indices  8))
       (subtable-2 (materialize-slli-subtable indices 16))
       (subtable-3 (materialize-slli-subtable indices 24))
       ;; chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (shift-amount (part-select y :low 0 :width 5))
       ;; shift chunks
       (u8-0 (tuple-lookup u8-0 shift-amount subtable-0))
       (u8-1 (tuple-lookup u8-1 shift-amount subtable-1))
       (u8-2 (tuple-lookup u8-2 shift-amount subtable-2))
       (u8-3 (tuple-lookup u8-3 shift-amount subtable-3)))
       ;; add chunks
      (+ u8-3 u8-2 u8-1 u8-0)))

;; This lemma must be proven with GL and not FGL
;; It should be named something else though
(local 
 (gl::def-gl-thm aux-lemma-32
  :hyp  (and (integerp x) (<= 0 x) (< x 4294967296))
  :concl (not (< 256 (logtail 24 x)))
  :g-bindings (gl::auto-bindings (:nat x 32))))


(defthm sll-32-sll-semantics-32-equiv
 (equal (sll-32 x y) (sll-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (sll-semantics-32 sll-32) ((:e create-tuple-indices))))))

(fgl::def-fgl-thm sll-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (sll-semantics-32 x y) (ash x (part-select y :low 0 :width 5))))

(defthm sll-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (sll-32 x y) (ash x (part-select y :low 0 :width 5))))
 :hints (("Goal" :use ((:instance sll-semantics-32-correctness) 
		       (:instance sll-32-sll-semantics-32-equiv)))))

;; 64-BIT

;; SLL-semantics-64
(define sll-semantics-64 (x y)
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; chunk
       (u8-7 (part-select x :low  0 :width 8))
       (u8-6 (part-select x :low  8 :width 8))
       (u8-5 (part-select x :low 16 :width 8))
       (u8-4 (part-select x :low 24 :width 8))
       (u8-3 (part-select x :low 32 :width 8))
       (u8-2 (part-select x :low 40 :width 8))
       (u8-1 (part-select x :low 48 :width 8))
       (u8-0 (part-select x :low 56 :width 8))
       (shift-amount (part-select y :low 0 :width 6))
       ;; shift chunks
       (u8-7 (ash u8-7 (+ shift-amount  0)))
       (u8-6 (ash u8-6 (+ shift-amount  8)))
       (u8-5 (ash u8-5 (+ shift-amount 16)))
       (u8-4 (ash u8-4 (+ shift-amount 24)))
       (u8-3 (ash u8-3 (+ shift-amount 32)))
       (u8-2 (ash u8-2 (+ shift-amount 40)))
       (u8-1 (ash u8-1 (+ shift-amount 48)))
       (u8-0 (ash u8-0 (+ shift-amount 56))))
       ;; add chunks
      (+ u8-7 u8-6 u8-5 u8-4 u8-3 u8-2 u8-1 u8-0)))

;; SLL-64 (with lookups)
(define sll-64 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; setup subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 6)))
       (subtable-0 (materialize-slli-subtable indices  0))
       (subtable-1 (materialize-slli-subtable indices  8))
       (subtable-2 (materialize-slli-subtable indices 16))
       (subtable-3 (materialize-slli-subtable indices 24))
       (subtable-4 (materialize-slli-subtable indices 32))
       (subtable-5 (materialize-slli-subtable indices 40))
       (subtable-6 (materialize-slli-subtable indices 48))
       (subtable-7 (materialize-slli-subtable indices 56))
       ;; chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (u8-4 (part-select x :low 32 :width 8))
       (u8-5 (part-select x :low 40 :width 8))
       (u8-6 (part-select x :low 48 :width 8))
       (u8-7 (part-select x :low 56 :width 8))
       (shift-amount (part-select y :low 0 :width 6))
       ;; shift chunks
       (u8-0 (tuple-lookup u8-0 shift-amount subtable-0))
       (u8-1 (tuple-lookup u8-1 shift-amount subtable-1))
       (u8-2 (tuple-lookup u8-2 shift-amount subtable-2))
       (u8-3 (tuple-lookup u8-3 shift-amount subtable-3))
       (u8-4 (tuple-lookup u8-4 shift-amount subtable-4))
       (u8-5 (tuple-lookup u8-5 shift-amount subtable-5))
       (u8-6 (tuple-lookup u8-6 shift-amount subtable-6))
       (u8-7 (tuple-lookup u8-7 shift-amount subtable-7)))
       ;; add chunks
      (+ u8-7 u8-6 u8-5 u8-4 u8-3 u8-2 u8-1 u8-0)))

;; This lemma must be proven with GL and not FGL
(local
 (gl::def-gl-thm aux-lemma-64
  :hyp  (and (integerp x) (<= 0 x) (< x 18446744073709551616))
  :concl (not (< 256 (logtail 56 x)))
  :g-bindings (gl::auto-bindings (:nat x 64))))

(defthm sll-64-sll-semantics-64-equiv
 (equal (sll-64 x y) (sll-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (sll-semantics-64 sll-64) ((:e create-tuple-indices))))))

(fgl::def-fgl-thm sll-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 6 y))
 :concl (equal (sll-semantics-64 x y) (ash x (part-select y :low 0 :width 6))))

(defthm sll-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 6 y))
          (equal (sll-64 x y) (ash x (part-select y :low 0 :width 6))))
 :hints (("Goal" :use ((:instance sll-semantics-64-correctness) 
		       (:instance sll-64-sll-semantics-64-equiv)))))
