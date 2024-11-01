(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../subtables/identity")

;; 32-BIT VERSION

(define move-semantics-32 ((x (unsigned-byte-p 32 x)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16)))
       ;; All lookups are identity
      ;; Combine
      (merge-4-u16s x8-0 x8-1 x8-2 x8-3)))

(define move-32 ((x (unsigned-byte-p 32 x)))
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
       (x8-0 (single-lookup x8-0 id-subtable))
       (x8-1 (single-lookup x8-1 id-subtable))
       (x8-2 (single-lookup x8-2 id-subtable))
       (x8-3 (single-lookup x8-3 id-subtable)))
      ;; Combine
      (merge-4-u16s x8-0 x8-1 x8-2 x8-3)))

;; Auxiliary lemmas for proof of equivalence
 
 (local
  (gl::def-gl-thm auxiliary-lemma-1
   :hyp (unsigned-byte-p 32 x)
   :concl (< (logtail 16 x) (expt 2 16))
   :g-bindings (gl::auto-bindings (:nat x 32))))

(defthm move-32-move-semantics-32-equiv
 (equal (move-32 x) (move-semantics-32 x))
 :hints (("Goal" :in-theory (e/d (move-semantics-32)
                                 ((:e materialize-identity-subtable)))
                  :use ((:instance lookup-identity-subtable-correctness
                                   (x-hi (expt 2 16))
                                   (i (logtail 16 x)))
		                    (:instance auxiliary-lemma-1)))))

;; Semantic correctness of MOVE
(gl::def-gl-thm move-semantics-32-correctness
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (move-semantics-32 x) x)
 :g-bindings (gl::auto-bindings (:nat x 32)))

;; Equivalence of MOVE with its semantics
(defthm move-32-correctness
 (implies (unsigned-byte-p 32 x)
          (equal (move-32 x) x))) 


;; 64-BIT VERSION

(define move-semantics-64 ((x (unsigned-byte-p 64 x)))
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ;; Chunk
       (x8-7 (part-select x :low  0 :width 16))
       (x8-6 (part-select x :low 16 :width 16))
       (x8-5 (part-select x :low 32 :width 16))
       (x8-4 (part-select x :low 48 :width 16))
       (x8-3 (part-select x :low 64 :width 16))
       (x8-2 (part-select x :low 80 :width 16))
       (x8-1 (part-select x :low 96 :width 16))
       (x8-0 (part-select x :low 112 :width 16)))
      ;; All lookups are identity
      ;; Combine
      (merge-8-u16s x8-0 x8-1 x8-2 x8-3 x8-4 x8-5 x8-6 x8-7)))

(define move-64 ((x (unsigned-byte-p 64 x)))
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
       (x8-0 (single-lookup x8-0 id-subtable))
       (x8-1 (single-lookup x8-1 id-subtable))
       (x8-2 (single-lookup x8-2 id-subtable))
       (x8-3 (single-lookup x8-3 id-subtable))
       (x8-4 (single-lookup x8-4 id-subtable))
       (x8-5 (single-lookup x8-5 id-subtable))
       (x8-6 (single-lookup x8-6 id-subtable))
       (x8-7 (single-lookup x8-7 id-subtable)))
      ;; Combine
      (merge-8-u16s x8-0 x8-1 x8-2 x8-3 x8-4 x8-5 x8-6 x8-7)))

 (local
  (gl::def-gl-thm auxiliary-lemma-2
   :hyp (unsigned-byte-p 64 x)
   :concl (< (logtail 48 x) (expt 2 16))
   :g-bindings (gl::auto-bindings (:nat x 64))))

(defthm move-64-move-semantics-64-equiv
 (equal (move-64 x) (move-semantics-64 x))
 :hints (("Goal" :in-theory (e/d (move-semantics-64)
                                 ((:e materialize-identity-subtable)))
                  :use ((:instance lookup-identity-subtable-correctness
                                   (x-hi (expt 2 16))
                                   (i (logtail 48 x)))
		                    (:instance auxiliary-lemma-2)))))

;; Semantic correctness of MOVE
(gl::def-gl-thm move-semantics-64-correctness
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (move-semantics-64 x) x)
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Equivalence of MOVE-64 with its semantics
(defthm move-64-correctness
 (implies (unsigned-byte-p 64 x)
          (equal (move-64 x) x)))
