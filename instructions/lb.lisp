(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "../subtables/identity")
(include-book "../subtables/truncate-overflow")
(include-book "../subtables/sign-extend")

(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

;; LB returns the lower 8 bits of the input, sign-extended to word size (32 or 64)
;; Note: semantics for loads and stores are handled in different parts of Jolt,
;; and not the scope of this formalization

;; 32-BIT VERSION

(define lb-semantics-32 ((x (unsigned-byte-p 32 x)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; Chunk
       (x8 (part-select x :low  0 :width 16))
       ;; LOOKUP SEMANTICS
       (z (truncate-overflow x8 8))
       (s (sign-extend x8 8)))
      ;; COMBINE
      (+ z (ash s 8) (ash s 16) (ash s 24))))

(define lb-32 ((x (unsigned-byte-p 32 x)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16))
       ;; Materialize subtables
       (id-subtable          (materialize-identity-subtable (expt 2 16)))
       (sign-extend-subtable (materialize-sign-extend-subtable (expt 2 16) 8))
       (truncate-subtable    (materialize-truncate-subtable (expt 2 16) #xff))
       ;; Perform lookups
       ;; Note that the `id` lookups are present in the Jolt codebase for reasons not related to
       ;; the immediate semantics of LB. Instead they are used as range checks for the input value,
       ;; which is necessary for other parts of the Jolt's constraint system.
       ;; We include them here for completeness.
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (s     (single-lookup x8-3 sign-extend-subtable))
       (z     (single-lookup x8-3 truncate-subtable)))
      ;; Combine
      (+ z (ash s 8) (ash s 16) (ash s 24))))

(local 
 (def-gl-thm loghead-lemma
  :hyp (AND (INTEGERP X) (<= 0 X) (< X 65536))
  :concl (EQUAL (LOGHEAD 8 X) (MOD X 256))
  :g-bindings (gl::auto-bindings (:nat x 16))))

(defthm lb-32-lb-semantics-32-equiv
 (equal (lb-32 x) (lb-semantics-32 x))
 :hints (("Goal" :in-theory (e/d (lb-semantics-32) ((:e materialize-sign-extend-subtable) (:e materialize-truncate-subtable))))))

;; Semantic correctness of lb
;; `logextu 32 8 y` views `y` as an 8-bit int, then sign-extends to 32 bits,
;; and interprets the result as an unsigned 32-bit number.
(gl::def-gl-thm lb-semantics-32-correctness
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (lb-semantics-32 x)
	       (logextu 32 8 (logand x #xff)))
 :g-bindings (gl::auto-bindings (:nat x 32)))

;; Equivalence of lb-32 with its semantics
(defthm lb-32-correctness
 (implies (unsigned-byte-p 32 x)
          (equal (lb-32 x) (logextu 32 8 (logand x #xff))))) 

;; 64-BIT VERSION

(define lb-semantics-64 ((x (unsigned-byte-p 64 x)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ;; Chunk
       (x8 (part-select x :low  0 :width 16))
       ;; Lookup semantics
       (z (truncate-overflow x8 8))
       (s (sign-extend x8 8)))
     ;; Combine
     (+ z (ash s 8) (ash s 16) (ash s 24) (ash s 32) (ash s 40) (ash s 48) (ash s 56))))

(define lb-64 ((x (unsigned-byte-p 64 x)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ;; Chunk
       (x8-7 (part-select x :low  0 :width 16))
       (x8-6 (part-select x :low 16 :width 16))
       (x8-5 (part-select x :low 32 :width 16))
       (x8-4 (part-select x :low 48 :width 16))
       (x8-3 (part-select x :low 64 :width 16))
       (x8-2 (part-select x :low 80 :width 16))
       (x8-1 (part-select x :low 96 :width 16))
       (x8-0 (part-select x :low 112 :width 16))
       ;; Materialize subtables
       (id-subtable          (materialize-identity-subtable (expt 2 16)))
       (sign-extend-subtable (materialize-sign-extend-subtable (expt 2 16) 8))
       (truncate-subtable    (materialize-truncate-subtable (expt 2 16) #xff))
       ;; Perform lookups
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (?x8-3 (single-lookup x8-3 id-subtable))
       (?x8-4 (single-lookup x8-4 id-subtable))
       (?x8-5 (single-lookup x8-5 id-subtable))
       (?x8-6 (single-lookup x8-6 id-subtable))
       (s     (single-lookup x8-7 sign-extend-subtable))
       (z     (single-lookup x8-7 truncate-subtable)))
      ;; Combine
      (+ z (ash s 8) (ash s 16) (ash s 24) (ash s 32) (ash s 40) (ash s 48) (ash s 56))))

(defthm lb-64-lb-semantics-64-equiv
 (equal (lb-64 x) (lb-semantics-64 x))
 :hints (("Goal" :in-theory (e/d (lb-semantics-64) ((:e materialize-sign-extend-subtable) (:e materialize-truncate-subtable))))))

;; SEMANTIC CORRECTNESS OF LB
(gl::def-gl-thm lb-semantics-64-correctness
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (lb-semantics-64 x)
	       (logextu 64 8 (logand x #xff)))
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Equivalence of lb-64 with its semantics
(defthm lb-64-correctness
 (implies (unsigned-byte-p 64 x)
          (equal (lb-64 x) (logextu 64 8 (logand x #xff))))) 
