(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)

(include-book "../subtables/identity")

;; SH returns the lowest 16 bits of the input, zero-extended to word size

;; 32-BIT VERSION

(define sh-semantics-32 ((x (unsigned-byte-p 32 x)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16))
       ;; Lookup semantics
       (?x8-0 x8-0)
       (?x8-1 x8-1)
       (?x8-2 x8-2)
       (x8-3 x8-3))
      ;; Combine
      x8-3))

(define sh-32 ((x (unsigned-byte-p 32 x)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16))
       ;; Materialize subtables 
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       ;; Perform lookups
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (x8-3 (single-lookup x8-3 id-subtable)))
      ;; Combine
      x8-3))

(defthm sh-32-sh-semantics-32-equiv
 (equal (sh-32 x) (sh-semantics-32 x))
 :hints (("Goal" :in-theory (e/d (sh-semantics-32) ((:e materialize-identity-subtable))))))

;; Semantic correctness of sh
(gl::def-gl-thm sh-semantics-32-correctness
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (sh-semantics-32 x)
	       (logand x #xffff))
 :g-bindings (gl::auto-bindings (:nat x 32)))

;; Equivalence of sh-32 with its semantics
(defthm sh-32-correctness
 (implies (unsigned-byte-p 32 x)
          (equal (sh-32 x) (logand x #xffff)))) 


;; 64-BIT VERSION

(define sh-semantics-64 ((x (unsigned-byte-p 64 x)))
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
       ;; Lookup semantics
       (?x8-0 x8-0)
       (?x8-1 x8-1)
       (?x8-2 x8-2)
       (?x8-3 x8-3)
       (?x8-4 x8-4)
       (?x8-5 x8-5)
       (?x8-6 x8-6)
       (x8-7 x8-7))
      ;; Combine
      x8-7))

(define sh-64 ((x (unsigned-byte-p 64 x)))
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
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       ;; Perform lookups
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (?x8-3 (single-lookup x8-3 id-subtable))
       (?x8-4 (single-lookup x8-4 id-subtable))
       (?x8-5 (single-lookup x8-5 id-subtable))
       (?x8-6 (single-lookup x8-6 id-subtable))
       (x8-7 (single-lookup x8-7 id-subtable)))
      ;; Combine
      x8-7))

(defthm sh-64-sh-semantics-64-equiv
 (equal (sh-64 x) (sh-semantics-64 x))
 :hints (("Goal" :in-theory (e/d (sh-semantics-64) ((:e materialize-identity-subtable))))))

;; Semantic correctness of sh
(gl::def-gl-thm sh-semantics-64-correctness
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (sh-semantics-64 x)
	       (logand x #xffff))
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Equivalence of sh-64 with its semantics
(defthm sh-64-correctness
 (implies (unsigned-byte-p 64 x)
          (equal (sh-64 x) (logand x #xffff))))
