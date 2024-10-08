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

;; 32-BIT

;; SRL-32-Prime semantics (with truncation)
(define srl-semantics-32-prime (x y)
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

(gl::def-gl-thm srl-semantics-32-prime-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (srl-semantics-32-prime x y) (ash x (- (part-select y :low 0 :width 5))))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

;; Alternate SRL definition with truncation
(define srl-32-prime (x y)
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
       (srli-subtable-0 (materialize-srli-subtable-prime indices  0 32))
       (srli-subtable-1 (materialize-srli-subtable-prime indices  8 32))
       (srli-subtable-2 (materialize-srli-subtable-prime indices 16 32))
       (srli-subtable-3 (materialize-srli-subtable-prime indices 24 32))
       ;; Perform lookups
       (u8-0 (tuple-lookup u8-0 shift-amount srli-subtable-0))
       (u8-1 (tuple-lookup u8-1 shift-amount srli-subtable-1))
       (u8-2 (tuple-lookup u8-2 shift-amount srli-subtable-2))
       (u8-3 (tuple-lookup u8-3 shift-amount srli-subtable-3)))
      ;; Combine
      (+ u8-3 u8-2 u8-1 u8-0)))

(defthm srl-32-prime-srl-semantics-32-prime-equiv
 (equal (srl-32-prime x y) (srl-semantics-32-prime x y))
 :hints (("Goal" :in-theory (e/d (srl-semantics-32-prime srl-32-prime) (srli-rust (:e create-tuple-indices) (:e expt))))))

(defthm srl-32-prime-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (srl-32-prime x y) (ash x (- (part-select y :low 0 :width 5))))))

;; SRL-32 intermediary lookup semantics (no truncation)
(define srl-semantics-32 (x y)
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (shift-amount (part-select y :low 0 :width 5))
       ;; Lookup semantics
       (u8-0 (ash      u8-0     (- shift-amount)))
       (u8-1 (ash (ash u8-1  8) (- shift-amount)))
       (u8-2 (ash (ash u8-2 16) (- shift-amount)))
       (u8-3 (ash (ash u8-3 24) (- shift-amount))))
      ;; Combine
      (+ u8-3 u8-2 u8-1 u8-0)))

;; SRL-32 (no truncation)
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
       (indices (create-tuple-indices (expt 2 8) (expt 2 5)))
       (srli-subtable-0 (materialize-srli-subtable indices  0))
       (srli-subtable-1 (materialize-srli-subtable indices  8))
       (srli-subtable-2 (materialize-srli-subtable indices 16))
       (srli-subtable-3 (materialize-srli-subtable indices 24))
       ;; Perform lookups
       (u8-0 (tuple-lookup u8-0 shift-amount srli-subtable-0))
       (u8-1 (tuple-lookup u8-1 shift-amount srli-subtable-1))
       (u8-2 (tuple-lookup u8-2 shift-amount srli-subtable-2))
       (u8-3 (tuple-lookup u8-3 shift-amount srli-subtable-3)))
      ;; Combine
      (+ u8-3 u8-2 u8-1 u8-0)))

;; This lemma must be proven with GL and not FGL
;; Making this non-local because SRA depends on it for some reason
;; It should be named something else though
(gl::def-gl-thm aux-lemma-32
 :hyp  (and (integerp x) (<= 0 x) (< x 4294967296))
 :concl (not (< 256 (logtail 24 x)))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(defthm srl-32-srl-semantics-32-equiv
 (equal (srl-32 x y) (srl-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (srl-semantics-32 srl-32) ((:e create-tuple-indices))))))

(fgl::def-fgl-thm srl-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (srl-semantics-32 x y) (ash x (- (part-select y :low 0 :width 5)))))

(defthm srl-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (srl-32 x y) (ash x (- (part-select y :low 0 :width 5)))))
 :hints (("Goal" :use ((:instance srl-semantics-32-correctness) 
		       (:instance srl-32-srl-semantics-32-equiv)))))

;; 64-BIT

;; SRL-semantics-64
(define srl-semantics-64 (x y)
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Chunk
       (u8-7 (part-select x :low  0 :width 8))
       (u8-6 (part-select x :low  8 :width 8))
       (u8-5 (part-select x :low 16 :width 8))
       (u8-4 (part-select x :low 24 :width 8))
       (u8-3 (part-select x :low 32 :width 8))
       (u8-2 (part-select x :low 40 :width 8))
       (u8-1 (part-select x :low 48 :width 8))
       (u8-0 (part-select x :low 56 :width 8))
       (shift-amount (part-select y :low 0 :width 6))
       ;; Lookup semantics
       (u8-7 (ash      u8-7     (- shift-amount)))
       (u8-6 (ash (ash u8-6  8) (- shift-amount)))
       (u8-5 (ash (ash u8-5 16) (- shift-amount)))
       (u8-4 (ash (ash u8-4 24) (- shift-amount)))
       (u8-3 (ash (ash u8-3 32) (- shift-amount)))
       (u8-2 (ash (ash u8-2 40) (- shift-amount)))
       (u8-1 (ash (ash u8-1 48) (- shift-amount)))
       (u8-0 (ash (ash u8-0 56) (- shift-amount))))
      ;; Combine
      (+ u8-7 u8-6 u8-5 u8-4 u8-3 u8-2 u8-1 u8-0)))

;; SRL-64 (with lookups)
(define srl-64 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (u8-4 (part-select x :low 32 :width 8))
       (u8-5 (part-select x :low 40 :width 8))
       (u8-6 (part-select x :low 48 :width 8))
       (u8-7 (part-select x :low 56 :width 8))
       (shift-amount (part-select y :low 0 :width 6))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 6)))
       (subtable-0 (materialize-srli-subtable indices  0))
       (subtable-1 (materialize-srli-subtable indices  8))
       (subtable-2 (materialize-srli-subtable indices 16))
       (subtable-3 (materialize-srli-subtable indices 24))
       (subtable-4 (materialize-srli-subtable indices 32))
       (subtable-5 (materialize-srli-subtable indices 40))
       (subtable-6 (materialize-srli-subtable indices 48))
       (subtable-7 (materialize-srli-subtable indices 56))
       ;; Perform lookups
       (u8-0 (tuple-lookup u8-0 shift-amount subtable-0))
       (u8-1 (tuple-lookup u8-1 shift-amount subtable-1))
       (u8-2 (tuple-lookup u8-2 shift-amount subtable-2))
       (u8-3 (tuple-lookup u8-3 shift-amount subtable-3))
       (u8-4 (tuple-lookup u8-4 shift-amount subtable-4))
       (u8-5 (tuple-lookup u8-5 shift-amount subtable-5))
       (u8-6 (tuple-lookup u8-6 shift-amount subtable-6))
       (u8-7 (tuple-lookup u8-7 shift-amount subtable-7)))
      ;; Combine
      (+ u8-7 u8-6 u8-5 u8-4 u8-3 u8-2 u8-1 u8-0)))

;; This lemma must be proven with GL and not FGL
(local
 (gl::def-gl-thm aux-lemma-64
  :hyp  (and (integerp x) (<= 0 x) (< x 18446744073709551616))
  :concl (not (< 256 (logtail 56 x)))
  :g-bindings (gl::auto-bindings (:nat x 64))))

(defthm srl-64-srl-semantics-64-equiv
 (equal (srl-64 x y) (srl-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (srl-semantics-64 srl-64) ((:e create-tuple-indices))))))

(fgl::def-fgl-thm srl-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 6 y))
 :concl (equal (srl-semantics-64 x y) (ash x (- (part-select y :low 0 :width 6)))))

(defthm srl-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 6 y))
          (equal (srl-64 x y) (ash x (- (part-select y :low 0 :width 6)))))
 :hints (("Goal" :use ((:instance srl-semantics-64-correctness) 
		       (:instance srl-64-srl-semantics-64-equiv)))))
