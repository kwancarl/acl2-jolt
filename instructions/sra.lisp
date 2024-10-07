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

;;;;;;;;;;;;;
;;
;; Chunking and append
;;
;;;;;;;;;;;;;

;; 32-BIT VERSION

(gl::def-gl-thm sra-sign-32-chunk-correctness
  :hyp (unsigned-byte-p 32 x)
  :concl (equal (logbit 7 (part-select x :low 24 :width 8))
                (logbit 31 x))
  :g-bindings (gl::auto-bindings (:nat x 32)))

(define sra-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; CHUNK
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (shift-amount (part-select y :low 0 :width 5))
       ;; MATERIALIZE SUBTABLES
       (indices (create-tuple-indices (expt 2 8) (expt 2 5)))
       (srli-subtable-0 (materialize-srli-subtable indices  0))
       (srli-subtable-1 (materialize-srli-subtable indices  8))
       (srli-subtable-2 (materialize-srli-subtable indices 16))
       (srli-subtable-3 (materialize-srli-subtable indices 24))
       (sra-sign-subtable (materialize-sra-sign-subtable-8 indices))
       ;; LOOKUPS
       (sign (tuple-lookup u8-3 shift-amount sra-sign-subtable))
       (u8-0 (tuple-lookup u8-0 shift-amount srli-subtable-0))
       (u8-1 (tuple-lookup u8-1 shift-amount srli-subtable-1))
       (u8-2 (tuple-lookup u8-2 shift-amount srli-subtable-2))
       (u8-3 (tuple-lookup u8-3 shift-amount srli-subtable-3)))
      ;; COMBINE
      (+ sign u8-3 u8-2 u8-1 u8-0)))

(local (in-theory (disable srl-32-srl-semantics-32-equiv)))

(defthm sra-32-=-sign-+-srl-32
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
	  (equal (sra-32 x y)
	         (+ (sra-sign-8 (part-select x :low 24 :width 8) y)
	            (srl-32 x y))))
 :hints (("Goal" :in-theory (e/d (srl-32 sra-32)
				 ((:e create-tuple-indices)
				  (:e materialize-srli-subtable))))))

(defthm sra-correctness-32-lemma
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
	  (equal (sra-32 x y)
	         (+ (sra-sign-8 (part-select x :low 24 :width 8) y)
	            (ash x (- y)))))
 :hints (("Goal" :use ((:instance srl-32-correctness))
	         :in-theory (disable (:e create-tuple-indices) (:e materialize-srli-subtable)))))

;(defthm sra-correctness-32
; (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
;	  (equal (sra-32 x y)
;		 (logextu 32 (- 32 (logtail 5 y)) (ash x (- (logtail 5 y))))))
; :hints (("Goal" :use ((:instance sra-sign-8-correctness)
;		       (:instance sra-correctness-32-lemma))
;	         :in-theory (e/d ()
;				 ((:e create-tuple-indices)
;				  (:e materialize-srli-subtable))))))



(define sra-32-prime (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low 24 :width 8))
       (x8-2 (part-select x :low 16 :width 8))
       (x8-1 (part-select x :low  8 :width 8))
       (x8-0 (part-select x :low  0 :width 8))
       (shift-amount (part-select y :low 0 :width 5))
       ;; MATERIALIZE SUBTABLES
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (srli-subtable-3 (materialize-srli-subtable-prime indices 24 32))
       (srli-subtable-2 (materialize-srli-subtable-prime indices 16 32))
       (srli-subtable-1 (materialize-srli-subtable-prime indices  8 32))
       (srli-subtable-0 (materialize-srli-subtable-prime indices  0 32))
       (sra-sign-subtable (materialize-sra-sign-subtable-8 indices))
       ;; LOOKUPS
       (sign (tuple-lookup x8-3 shift-amount sra-sign-subtable))
       (u8-0 (tuple-lookup x8-0 shift-amount srli-subtable-0))
       (u8-1 (tuple-lookup x8-1 shift-amount srli-subtable-1))
       (u8-2 (tuple-lookup x8-2 shift-amount srli-subtable-2))
       (u8-3 (tuple-lookup x8-3 shift-amount srli-subtable-3)))
      ;; COMBINE
      (+ sign u8-3 u8-2 u8-1 u8-0)))

(local (in-theory (disable srl-32-prime-srl-semantics-32-prime-equiv)))

(defthm sra-32-prime-=-sign-+-srl-32-prime
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
	  (equal (sra-32-prime x y)
	         (+ (sra-sign-8 (part-select x :low 24 :width 8) (part-select y :low 0 :width 5))
	            (srl-32-prime x y))))
 :hints (("Goal" :in-theory (e/d (srl-32-prime sra-32-prime)
				 ((:e create-tuple-indices)
				  (:e materialize-srli-subtable))))))

(defthm sra-32-prime-correctness-lemma
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
	  (equal (sra-32-prime x y)
	         (+ (sra-sign-8 (part-select x :low 24 :width 8) (part-select y :low 0 :width 5))
	            (ash x (- (part-select y :low 0 :width 5))))))
 :hints (("Goal" :use ((:instance srl-32-prime-correctness)
		       (:instance sra-32-prime-=-sign-+-srl-32-prime))
	         :in-theory (disable (:e create-tuple-indices) (:e materialize-srli-subtable)))))

(gl::def-gl-thm sign-lemma
 :hyp (and (unsigned-byte-p 32 y) (unsigned-byte-p 32 x))
 :concl (equal (+ (sra-sign-8 (part-select x :low 24 :width 8) (part-select y :low 0 :width 5))
	          (ash x (- (part-select y :low 0 :width 5))))
	       (logextu 32 (- 32 (part-select y :low 0 :width 5)) (ash x (- (part-select y :low 0 :width 5)))))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm sra-32-prime-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
	  (equal (sra-32-prime x y)
		 (logextu 32 (- 32 (part-select y :low 0 :width 5)) (ash x (- (part-select y :low 0 :width 5))))))
 :hints (("Goal" :use ((:instance sign-lemma)
                       (:instance sra-32-prime-correctness-lemma))
	         :in-theory (e/d ()
				 ((:e create-tuple-indices)
				  (:e materialize-srli-subtable))))))


;; 64-BIT VERSION (TODO: Fix some lemmas)

;; (gl::def-gl-thm sra-sign-64-chunk-correctness
;;   :hyp (unsigned-byte-p 64 x)
;;   :concl (equal (logbit 7 (part-select x :low 56 :width 8))
;;                 (logbit 63 x))
;;   :g-bindings (gl::auto-bindings (:nat x 64)))

;; (define sra-64 (x y)
;;   :verify-guards nil
;;   (b* (((unless (unsigned-byte-p 64 x)) 0)
;;        ((unless (unsigned-byte-p 64 y)) 0)
;;        ;; CHUNK
;;        (u8-0 (part-select x :low  0 :width 8))
;;        (u8-1 (part-select x :low  8 :width 8))
;;        (u8-2 (part-select x :low 16 :width 8))
;;        (u8-3 (part-select x :low 24 :width 8))
;;        (u8-4 (part-select x :low 32 :width 8))
;;        (u8-5 (part-select x :low 40 :width 8))
;;        (u8-6 (part-select x :low 48 :width 8))
;;        (u8-7 (part-select x :low 56 :width 8))
;;        (shift-amount (part-select y :low 0 :width 6))
;;        ;; MATERIALIZE SUBTABLES
;;        (indices (create-tuple-indices (expt 2 8) (expt 2 6)))
;;        (srli-subtable-0 (materialize-srli-subtable indices  0))
;;        (srli-subtable-1 (materialize-srli-subtable indices  8))
;;        (srli-subtable-2 (materialize-srli-subtable indices 16))
;;        (srli-subtable-3 (materialize-srli-subtable indices 24))
;;        (srli-subtable-4 (materialize-srli-subtable indices 32))
;;        (srli-subtable-5 (materialize-srli-subtable indices 40))
;;        (srli-subtable-6 (materialize-srli-subtable indices 48))
;;        (srli-subtable-7 (materialize-srli-subtable indices 56))
;;        (sra-sign-subtable (materialize-sra-sign-subtable-8 indices))
;;        ;; LOOKUPS
;;        (sign (tuple-lookup u8-7 y sra-sign-subtable))
;;        (u8-0 (tuple-lookup u8-0 y srli-subtable-0))
;;        (u8-1 (tuple-lookup u8-1 y srli-subtable-1))
;;        (u8-2 (tuple-lookup u8-2 y srli-subtable-2))
;;        (u8-3 (tuple-lookup u8-3 y srli-subtable-3))
;;        (u8-4 (tuple-lookup u8-4 y srli-subtable-4))
;;        (u8-5 (tuple-lookup u8-5 y srli-subtable-5))
;;        (u8-6 (tuple-lookup u8-6 y srli-subtable-6))
;;        (u8-7 (tuple-lookup u8-7 y srli-subtable-7)))
;;       ;; COMBINE
;;       (+ sign u8-7 u8-6 u8-5 u8-4 u8-3 u8-2 u8-1 u8-0)))

;; (local (in-theory (disable srl-64-srl-semantics-64-equiv)))

;; (defthm sra-64-=-sign-+-srl-64
;;  (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 6 y))
;; 	  (equal (sra-64 x y)
;; 	         (+ (sra-sign-8 (part-select x :low 56 :width 8) y)
;; 	            (srl-64 x y))))
;;  :hints (("Goal" :in-theory (e/d (srl-64 sra-64)
;; 				 ((:e create-tuple-indices)
;; 				  (:e materialize-srli-subtable))))))

;; (defthm sra-correctness-64-lemma
;;  (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 6 y))
;; 	  (equal (sra-64 x y)
;; 	         (+ (sra-sign-8 (part-select x :low 24 :width 8) y)
;; 	            (ash x (- y)))))
;;  :hints (("Goal" :use ((:instance srl-64-correctness))
;; 	         :in-theory (disable (:e create-tuple-indices) (:e materialize-srli-subtable)))))

;; (defthm sra-correctness-64
;;  (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 6 y))
;; 	  (equal (sra-64 x y)
;; 		 (logextu 64 (- 64 y) (ash x (- y)))))
;;  :hints (("Goal" :use ((:instance sra-sign-8-correctness)
;; 		       (:instance sra-correctness-lemma))
;; 	         :in-theory (e/d ()
;; 				 ((:e create-tuple-indices)
;; 				  (:e materialize-srli-subtable))))))
