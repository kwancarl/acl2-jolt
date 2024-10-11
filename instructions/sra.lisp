(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "srl")
(include-book "../subtables/sra-sign")

;; 32-BIT

(gl::def-gl-thm sra-sign-32-chunk-correctness
  :hyp (unsigned-byte-p 32 x)
  :concl (equal (logbit 7 (part-select x :low 24 :width 8))
                (logbit 31 x))
  :g-bindings (gl::auto-bindings (:nat x 32)))

(local 
 (gl::def-gl-thm sra-aux-lemma
  :hyp (unsigned-byte-p 32 x)
  :concl (< (logtail 24 x) 256)
  :g-bindings (gl::auto-bindings (:nat x 32))))

;; SRA-32 with lookup semantics
(define sra-semantics-32 (x y)
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
       (sign (sra-sign x8-0 y8-3 32))
       (u8-3 (srli-rust x8-3 y8-3  0 32))
       (u8-2 (srli-rust x8-2 y8-3  8 32))
       (u8-1 (srli-rust x8-1 y8-3 16 32))
       (u8-0 (srli-rust x8-0 y8-3 24 32)))
      ;; Combine
      (+ sign u8-3 u8-2 u8-1 u8-0)))

;; (ashu size i cnt) first coerces i to a size-bit signed integer by sign-extension, then shifts it with ash by cnt, and finally converts the result back to a size-bit unsigned integer.
(gl::def-gl-thm sra-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (sra-semantics-32 x y)
              (ashu 32 x (- (mod y 32))))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

;; SRA-32
(define sra-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (x8-3 (part-select x :low 0 :width 8))
       (x8-2 (part-select x :low 8 :width 8))
       (x8-1 (part-select x :low 16 :width 8))
       (x8-0 (part-select x :low 24 :width 8))
       (y8-3 (part-select y :low 0 :width 8))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (srli-subtable-3 (materialize-srli-subtable indices 0 32))
       (srli-subtable-2 (materialize-srli-subtable indices 8 32))
       (srli-subtable-1 (materialize-srli-subtable indices 16 32))
       (srli-subtable-0 (materialize-srli-subtable indices 24 32))
       (sra-sign-subtable (materialize-sra-sign-subtable indices 32))
       ;; Perform lookups
       (sign (tuple-lookup x8-0 y8-3 sra-sign-subtable))
       (u8-3 (tuple-lookup x8-3 y8-3 srli-subtable-3))
       (u8-2 (tuple-lookup x8-2 y8-3 srli-subtable-2))
       (u8-1 (tuple-lookup x8-1 y8-3 srli-subtable-1))
       (u8-0 (tuple-lookup x8-0 y8-3 srli-subtable-0)))
      ;; Combine
      (+ sign u8-3 u8-2 u8-1 u8-0)))

(defthm sra-32-sra-semantics-32-equiv
 (equal (sra-32 x y) (sra-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (sra-semantics-32 sra-32)
                                 (srli-rust sra-sign (:e create-tuple-indices) (:e expt))))))

(defthm sra-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (sra-32 x y) (ashu 32 x (- (mod y 32))))))


;; 64-BIT

#|
;; SRA with lookup semantics & truncation
(define sra-semantics-64 (x y)
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
       (sign (sra-sign x8-0 y8-7 64))
       (u8-7 (srli-rust x8-7 y8-7  0 64))
       (u8-6 (srli-rust x8-6 y8-7  8 64))
       (u8-5 (srli-rust x8-5 y8-7 16 64))
       (u8-4 (srli-rust x8-4 y8-7 24 64))
       (u8-3 (srli-rust x8-3 y8-7 32 64))
       (u8-2 (srli-rust x8-2 y8-7 40 64))
       (u8-1 (srli-rust x8-1 y8-7 48 64))
       (u8-0 (srli-rust x8-0 y8-7 56 64)))
      ;; Combine
      (+ sign u8-7 u8-6 u8-5 u8-4 u8-3 u8-2 u8-1 u8-0)))

;; SRA with truncation
(define sra-64 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Chunk
       (x8-7 (part-select x :low 56 :width 8))
       (x8-6 (part-select x :low 48 :width 8))
       (x8-5 (part-select x :low 40 :width 8))
       (x8-4 (part-select x :low 32 :width 8))
       (x8-3 (part-select x :low 24 :width 8))
       (x8-2 (part-select x :low 16 :width 8))
       (x8-1 (part-select x :low  8 :width 8))
       (x8-0 (part-select x :low  0 :width 8))
       (shift-amount (part-select y :low 0 :width 6))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (srli-subtable-7 (materialize-srli-subtable indices 56 64))
       (srli-subtable-6 (materialize-srli-subtable indices 48 64))
       (srli-subtable-5 (materialize-srli-subtable indices 40 64))
       (srli-subtable-4 (materialize-srli-subtable indices 32 64))
       (srli-subtable-3 (materialize-srli-subtable indices 24 64))
       (srli-subtable-2 (materialize-srli-subtable indices 16 64))
       (srli-subtable-1 (materialize-srli-subtable indices  8 64))
       (srli-subtable-0 (materialize-srli-subtable indices  0 64))
       (sra-sign-subtable (materialize-sra-sign-subtable indices 64))
       ;; Perform lookups
       (sign (tuple-lookup x8-7 shift-amount sra-sign-subtable))
       (u8-0 (tuple-lookup x8-0 shift-amount srli-subtable-0))
       (u8-1 (tuple-lookup x8-1 shift-amount srli-subtable-1))
       (u8-2 (tuple-lookup x8-2 shift-amount srli-subtable-2))
       (u8-3 (tuple-lookup x8-3 shift-amount srli-subtable-3))
       (u8-4 (tuple-lookup x8-4 shift-amount srli-subtable-4))
       (u8-5 (tuple-lookup x8-5 shift-amount srli-subtable-5))
       (u8-6 (tuple-lookup x8-6 shift-amount srli-subtable-6))
       (u8-7 (tuple-lookup x8-7 shift-amount srli-subtable-7)))
      ;; Combine
      (+ sign u8-7 u8-6 u8-5 u8-4 u8-3 u8-2 u8-1 u8-0)))

(defthm sra-64-sra-semantics-64-equiv
 (equal (sra-64 x y) (sra-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (sra-semantics-64 sra-64)
                                 (srli-rust sra-sign (:e create-tuple-indices) (:e expt))))))


(defthm sra-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
	  (equal (sra-64 x y)
		 (logextu 64 (- 64 (part-select y :low 0 :width 6)) (ash x (- (part-select y :low 0 :width 6))))))
 :hints (("Goal" :use ((:instance sign-lemma)
                       (:instance sra-64-correctness-lemma))
	         :in-theory (e/d ()
				 ((:e create-tuple-indices)
				  (:e materialize-srli-subtable))))))
|#
