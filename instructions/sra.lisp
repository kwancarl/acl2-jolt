(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
;(include-book "arithmetic/top" :dir :system)
;
;(include-book "centaur/bitops/ihsext-basics" :dir :system)
;(include-book "centaur/bitops/fast-logext" :dir :system)
;
;(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "srl")
(include-book "../subtables/sra-sign")

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

(define sra-semantics-32 (x y)
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
      ;;  (sign (sra-sign-8 u8-3 shift-amount))
       (sign (sra-sign u8-3 shift-amount 32))
       (u8-0 (srli-rust u8-0 shift-amount  0 32))
       (u8-1 (srli-rust u8-1 shift-amount  8 32))
       (u8-2 (srli-rust u8-2 shift-amount 16 32))
       (u8-3 (srli-rust u8-3 shift-amount 24 32)))
      ;; Combine
      (+ sign u8-3 u8-2 u8-1 u8-0)))

;; SRA with truncation
(define sra-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (x8-3 (part-select x :low 24 :width 8))
       (x8-2 (part-select x :low 16 :width 8))
       (x8-1 (part-select x :low  8 :width 8))
       (x8-0 (part-select x :low  0 :width 8))
       (shift-amount (part-select y :low 0 :width 5))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (srli-subtable-3 (materialize-srli-subtable indices 24 32))
       (srli-subtable-2 (materialize-srli-subtable indices 16 32))
       (srli-subtable-1 (materialize-srli-subtable indices  8 32))
       (srli-subtable-0 (materialize-srli-subtable indices  0 32))
       (sra-sign-subtable (materialize-sra-sign-subtable indices 32))
       ;; Perform lookups
       (sign (tuple-lookup x8-3 shift-amount sra-sign-subtable))
       (u8-0 (tuple-lookup x8-0 shift-amount srli-subtable-0))
       (u8-1 (tuple-lookup x8-1 shift-amount srli-subtable-1))
       (u8-2 (tuple-lookup x8-2 shift-amount srli-subtable-2))
       (u8-3 (tuple-lookup x8-3 shift-amount srli-subtable-3)))
      ;; Combine
      (+ sign u8-3 u8-2 u8-1 u8-0)))

(local (in-theory (disable srl-32-srl-semantics-32-equiv)))

(defthm sra-32-=-sign-+-srl-32
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
	  (equal (sra-32 x y)
	         (+ (sra-sign (part-select x :low 24 :width 8) (part-select y :low 0 :width 5) 32)
	            (srl-32 x y))))
 :hints (("Goal" :use ((:instance lookup-materialize-sra-sign-subtable-correctness 
				  (word-size 32)
				  (x-hi (expt 2 8))
				  (y-hi (expt 2 8))
				  (i (logtail 24 x))
				  (j (loghead 5 y)))
		       (:instance sra-aux-lemma))

	         :in-theory (e/d (srl-32 sra-32)
				 ((:e create-tuple-indices)
				  (:e materialize-srli-subtable))))))

(defthm sra-32-correctness-lemma
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
	  (equal (sra-32 x y)
	         (+ (sra-sign (part-select x :low 24 :width 8) (part-select y :low 0 :width 5) 32)
	            (ash x (- (part-select y :low 0 :width 5))))))
 :hints (("Goal" :use ((:instance srl-32-correctness)
		       (:instance sra-32-=-sign-+-srl-32))
	         :in-theory (disable (:e create-tuple-indices) (:e materialize-srli-subtable)))))

(gl::def-gl-thm sign-lemma
 :hyp (and (unsigned-byte-p 32 y) (unsigned-byte-p 32 x))
 :concl (equal (+ (sra-sign (part-select x :low 24 :width 8) (part-select y :low 0 :width 5) 32)
	          (ash x (- (part-select y :low 0 :width 5))))
	       (logextu 32 (- 32 (part-select y :low 0 :width 5)) (ash x (- (part-select y :low 0 :width 5)))))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm sra-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
	  (equal (sra-32 x y)
		 (logextu 32 (- 32 (part-select y :low 0 :width 5)) (ash x (- (part-select y :low 0 :width 5))))))
 :hints (("Goal" :use ((:instance sign-lemma)
                       (:instance sra-32-correctness-lemma))
	         :in-theory (e/d ()
				 ((:e create-tuple-indices)
				  (:e materialize-srli-subtable))))))
