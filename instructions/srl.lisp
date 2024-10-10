(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../subtables/srl")

;; 32-BIT

;; SRL-32-Prime semantics (with truncation)
(define srl-semantics-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (shift-amount (part-select y :low 0 :width 5))
       ;; Lookup semantics
       (u8-0 (srli-rust u8-0 shift-amount  0 32))
       (u8-1 (srli-rust u8-1 shift-amount  8 32))
       (u8-2 (srli-rust u8-2 shift-amount 16 32))
       (u8-3 (srli-rust u8-3 shift-amount 24 32)))
      ;; Combine
      (+ u8-3 u8-2 u8-1 u8-0)))

(gl::def-gl-thm srl-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (srl-semantics-32 x y) (ash x (- (part-select y :low 0 :width 5))))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

;; Alternate SRL definition with truncation
(define srl-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (shift-amount (part-select y :low 0 :width 5))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (srli-subtable-0 (materialize-srli-subtable indices  0 32))
       (srli-subtable-1 (materialize-srli-subtable indices  8 32))
       (srli-subtable-2 (materialize-srli-subtable indices 16 32))
       (srli-subtable-3 (materialize-srli-subtable indices 24 32))
       ;; Perform lookups
       (u8-0 (tuple-lookup u8-0 shift-amount srli-subtable-0))
       (u8-1 (tuple-lookup u8-1 shift-amount srli-subtable-1))
       (u8-2 (tuple-lookup u8-2 shift-amount srli-subtable-2))
       (u8-3 (tuple-lookup u8-3 shift-amount srli-subtable-3)))
      ;; Combine
      (+ u8-3 u8-2 u8-1 u8-0)))

(defthm srl-32-srl-semantics-32-equiv
 (equal (srl-32 x y) (srl-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (srl-semantics-32 srl-32) (srli-rust (:e create-tuple-indices) (:e expt))))))

(defthm srl-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (srl-32 x y) (ash x (- (part-select y :low 0 :width 5))))))
