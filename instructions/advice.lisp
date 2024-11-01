(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../subtables/truncate-overflow")
(include-book "../subtables/identity")

;; 32-BIT VERSION

(define advice-semantics-32 ((x (unsigned-byte-p 32 x)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (?x8-1 (part-select x :low 32 :width 16))
       (?x8-0 (part-select x :low 48 :width 16))
       ;; Lookup semantics
       (x8-0 (truncate-overflow x8-0 0))
       (x8-1 (truncate-overflow x8-1 0))
       (x8-2 x8-2)
       (x8-3 x8-3))
      ;; Combine
      (merge-4-u16s x8-0 x8-1 x8-2 x8-3)))

(define advice-32 ((x (unsigned-byte-p 32 x)))
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
       (truncate-subtable (materialize-truncate-subtable (expt 2 16) 0))
       ;; Perform lookups
       (x8-0 (single-lookup x8-0 truncate-subtable))
       (x8-1 (single-lookup x8-1 truncate-subtable))
       (x8-2 (single-lookup x8-2 id-subtable))
       (x8-3 (single-lookup x8-3 id-subtable)))
      ;; Combine
      (merge-4-u16s x8-0 x8-1 x8-2 x8-3)))

(defthm advice-32-advice-semantics-32-equiv
 (equal (advice-32 x) (advice-semantics-32 x))
 :hints (("Goal" :in-theory (e/d (advice-semantics-32)
                                 ((:e materialize-identity-subtable) 
                                  (:e materialize-truncate-subtable)))
                  :use ((:instance lookup-identity-subtable-correctness)))))

;; Semantic correctness of ADVICE
(gl::def-gl-thm advice-semantics-32-correctness
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (advice-semantics-32 x) x)
 :g-bindings (gl::auto-bindings (:nat x 32)))

;; Equivalence of ADVICE with its semantics
(defthm advice-32-correctness
 (implies (unsigned-byte-p 32 x)
          (equal (advice-32 x) x))) 


;; 64-BIT VERSION

(define advice-semantics-64 ((x (unsigned-byte-p 64 x)))
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
       (x8-0 (truncate-overflow x8-0 0))
       (x8-1 (truncate-overflow x8-1 0))
       (x8-2 (truncate-overflow x8-2 0))
       (x8-3 (truncate-overflow x8-3 0))
       (x8-4 x8-4)
       (x8-5 x8-5)
       (x8-6 x8-6)
       (x8-7 x8-7))
      ;; Combine
      (merge-8-u16s x8-0 x8-1 x8-2 x8-3 x8-4 x8-5 x8-6 x8-7)))

(define advice-64 ((x (unsigned-byte-p 64 x)))
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
       (truncate-subtable (materialize-truncate-subtable (expt 2 16) 0))
       ;; Perform lookups
       (x8-0 (single-lookup x8-0 truncate-subtable))
       (x8-1 (single-lookup x8-1 truncate-subtable))
       (x8-2 (single-lookup x8-2 truncate-subtable))
       (x8-3 (single-lookup x8-3 truncate-subtable))
       (x8-4 (single-lookup x8-4 id-subtable))
       (x8-5 (single-lookup x8-5 id-subtable))
       (x8-6 (single-lookup x8-6 id-subtable))
       (x8-7 (single-lookup x8-7 id-subtable)))
      ;; Combine
      (merge-8-u16s x8-0 x8-1 x8-2 x8-3 x8-4 x8-5 x8-6 x8-7)))

(defthm advice-64-advice-semantics-64-equiv
 (equal (advice-64 x) (advice-semantics-64 x))
 :hints (("Goal" :in-theory (e/d (advice-semantics-64 advice-64)
                                 ((:e materialize-identity-subtable) 
                                  (:e materialize-truncate-subtable))))))

;; Semantic correctness of ADVICE
(gl::def-gl-thm advice-semantics-64-correctness
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (advice-semantics-64 x) x)
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Equivalence of ADVICE-64 with its semantics
(defthm advice-64-correctness
 (implies (unsigned-byte-p 64 x)
          (equal (advice-64 x) x)))
