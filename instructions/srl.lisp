(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../subtables/srl")

;; 32-BIT VERSION

;; SRL-32 semantics
(define srl-semantics-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 8))
       (x8-2 (part-select x :low  8 :width 8))
       (x8-1 (part-select x :low 16 :width 8))
       (x8-0 (part-select x :low 24 :width 8))
       (y8-3 (part-select y :low 0 :width 8))
       ;; Lookup semantics
       (u8-3 (srli-rust x8-3 y8-3  0 32))
       (u8-2 (srli-rust x8-2 y8-3  8 32))
       (u8-1 (srli-rust x8-1 y8-3 16 32))
       (u8-0 (srli-rust x8-0 y8-3 24 32)))
      ;; Combine
      (+ u8-3 u8-2 u8-1 u8-0)))

(gl::def-gl-thm srl-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (srl-semantics-32 x y) (ash x (- (mod y 32))))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

;; SRL-32
(define srl-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 8))
       (x8-2 (part-select x :low  8 :width 8))
       (x8-1 (part-select x :low 16 :width 8))
       (x8-0 (part-select x :low 24 :width 8))
       (y8-3 (part-select y :low 0 :width 8))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (srli-subtable-3 (materialize-srli-subtable indices  0 32))
       (srli-subtable-2 (materialize-srli-subtable indices  8 32))
       (srli-subtable-1 (materialize-srli-subtable indices 16 32))
       (srli-subtable-0 (materialize-srli-subtable indices 24 32))
       ;; Perform lookups
       (u8-3 (tuple-lookup x8-3 y8-3 srli-subtable-3))
       (u8-2 (tuple-lookup x8-2 y8-3 srli-subtable-2))
       (u8-1 (tuple-lookup x8-1 y8-3 srli-subtable-1))
       (u8-0 (tuple-lookup x8-0 y8-3 srli-subtable-0)))
      ;; Combine
      (+ u8-3 u8-2 u8-1 u8-0)))

(defthm srl-32-srl-semantics-32-equiv
 (equal (srl-32 x y) (srl-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (srl-semantics-32 srl-32) (srli-rust (:e create-tuple-indices) (:e expt))))))

(defthm srl-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (srl-32 x y) (ash x (- (mod y 32))))))


;; 64-BIT VERSION

;; SRL-64 semantics
(define srl-semantics-64 (x y)
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
       (y8-7 (part-select y :low 0 :width 8))
       ;; Lookup semantics
       (u8-7 (srli-rust x8-7 y8-7  0 64))
       (u8-6 (srli-rust x8-6 y8-7  8 64))
       (u8-5 (srli-rust x8-5 y8-7 16 64))
       (u8-4 (srli-rust x8-4 y8-7 24 64))
       (u8-3 (srli-rust x8-3 y8-7 32 64))
       (u8-2 (srli-rust x8-2 y8-7 40 64))
       (u8-1 (srli-rust x8-1 y8-7 48 64))
       (u8-0 (srli-rust x8-0 y8-7 56 64)))
      ;; Combine
      (+ u8-7 u8-6 u8-5 u8-4 u8-3 u8-2 u8-1 u8-0)))

(gl::def-gl-thm srl-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (srl-semantics-64 x y) (ash x (- (mod y 64))))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))

;; SRL-64
(define srl-64 (x y)
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
       (y8-7 (part-select y :low 0 :width 8))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (srli-subtable-7 (materialize-srli-subtable indices  0 64))
       (srli-subtable-6 (materialize-srli-subtable indices  8 64))
       (srli-subtable-5 (materialize-srli-subtable indices 16 64))
       (srli-subtable-4 (materialize-srli-subtable indices 24 64))
       (srli-subtable-3 (materialize-srli-subtable indices 32 64))
       (srli-subtable-2 (materialize-srli-subtable indices 40 64))
       (srli-subtable-1 (materialize-srli-subtable indices 48 64))
       (srli-subtable-0 (materialize-srli-subtable indices 56 64))
       ;; Perform lookups
       (u8-7 (tuple-lookup x8-7 y8-7 srli-subtable-7))
       (u8-6 (tuple-lookup x8-6 y8-7 srli-subtable-6))
       (u8-5 (tuple-lookup x8-5 y8-7 srli-subtable-5))
       (u8-4 (tuple-lookup x8-4 y8-7 srli-subtable-4))
       (u8-3 (tuple-lookup x8-3 y8-7 srli-subtable-3))
       (u8-2 (tuple-lookup x8-2 y8-7 srli-subtable-2))
       (u8-1 (tuple-lookup x8-1 y8-7 srli-subtable-1))
       (u8-0 (tuple-lookup x8-0 y8-7 srli-subtable-0)))
      ;; Combine
      (+ u8-7 u8-6 u8-5 u8-4 u8-3 u8-2 u8-1 u8-0)))

(defthm srl-64-srl-semantics-64-equiv
 (equal (srl-64 x y) (srl-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (srl-semantics-64 srl-64) (srli-rust (:e create-tuple-indices) (:e expt))))))

(defthm srl-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (srl-64 x y) (ash x (- (mod y 64))))))
