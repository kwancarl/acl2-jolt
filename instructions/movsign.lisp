(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../subtables/sign-extend")
(include-book "../subtables/identity")

;; 32-BIT VERSION

(define movsign-semantics-32 ((x (unsigned-byte-p 32 x)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; Chunk
       (?x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (?x8-1 (part-select x :low 32 :width 16))
       (?x8-0 (part-select x :low 48 :width 16))
       ;; Lookup semantics
       (s (sign-extend x8-2 16)))
      ;; Combine
      (merge-2-u16s s s)))

(define movsign-32 ((x (unsigned-byte-p 32 x)))
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
       (sign-extend-subtable (materialize-sign-extend-subtable (expt 2 16) 16))
       ;; Perform lookups (identity lookups are present in Jolt for range-checking purposes)
       (s (single-lookup x8-2 sign-extend-subtable))
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (?x8-3 (single-lookup x8-3 id-subtable)))
      ;; Combine
      (merge-2-u16s s s)))

;; Semantic correctness of MOVSIGN
(gl::def-gl-thm movsign-semantics-32-correctness
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (movsign-semantics-32 x) (* (logtail 31 x) (1- (expt 2 32))))
 :g-bindings (gl::auto-bindings (:nat x 32)))

;; Auxiliary lemmas for proof of equivalence
 
 (local
  (gl::def-gl-thm auxiliary-lemma-1
   :hyp (unsigned-byte-p 32 x)
   :concl (< (logtail 16 x) (expt 2 16))
   :g-bindings (gl::auto-bindings (:nat x 32))))

(defthm movsign-32-movsign-semantics-32-equiv
 (equal (movsign-32 x) (movsign-semantics-32 x))
 :hints (("Goal" :in-theory (e/d (movsign-semantics-32)
                                 ((:e expt) (:e sign-extend) (:e materialize-identity-subtable)
                                 (:e materialize-sign-extend-subtable)))
                  :use ((:instance lookup-materialize-sign-extend-subtable-correctness
                                   (x-hi (expt 2 16))
                                   (width 16)
                                   (i (logtail 16 x)))
		                         (:instance auxiliary-lemma-1)))))

;; Equivalence of MOVSIGN with its semantics
(defthm movsign-32-correctness
 (implies (unsigned-byte-p 32 x)
          (equal (movsign-32 x) (* (logtail 31 x) (1- (expt 2 32)))))) 


;; 64-BIT VERSION

(define movsign-semantics-64 ((x (unsigned-byte-p 64 x)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ;; Chunk
       (?x8-7 (part-select x :low  0 :width 16))
       (?x8-6 (part-select x :low 16 :width 16))
       (?x8-5 (part-select x :low 32 :width 16))
       (x8-4 (part-select x :low 48 :width 16))
       (?x8-3 (part-select x :low 64 :width 16))
       (?x8-2 (part-select x :low 80 :width 16))
       (?x8-1 (part-select x :low 96 :width 16))
       (?x8-0 (part-select x :low 112 :width 16))
       ;; Lookup semantics
       (s (sign-extend x8-4 16)))
      ;; Combine
      (merge-4-u16s s s s s)))

(define movsign-64 ((x (unsigned-byte-p 64 x)))
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
       (sign-extend-subtable (materialize-sign-extend-subtable (expt 2 16) 16))
       ;; Perform lookups (identity lookups are present in Jolt for range-checking purposes)
       (s (single-lookup x8-4 sign-extend-subtable))
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (?x8-3 (single-lookup x8-3 id-subtable))
       (?x8-4 (single-lookup x8-4 id-subtable))
       (?x8-5 (single-lookup x8-5 id-subtable))
       (?x8-6 (single-lookup x8-6 id-subtable))
       (?x8-7 (single-lookup x8-7 id-subtable)))
      ;; Combine
      (merge-4-u16s s s s s)))

 (local
  (gl::def-gl-thm auxiliary-lemma-2
   :hyp (unsigned-byte-p 64 x)
   :concl (< (logtail 48 x) (expt 2 16))
   :g-bindings (gl::auto-bindings (:nat x 64))))

(defthm movsign-64-movsign-semantics-64-equiv
 (equal (movsign-64 x) (movsign-semantics-64 x))
 :hints (("Goal" :in-theory (e/d (movsign-semantics-64)
                                 ((:e expt) (:e materialize-identity-subtable)
                                  (:e materialize-sign-extend-subtable)))
                  :use ((:instance lookup-materialize-sign-extend-subtable-correctness
                                   (x-hi (expt 2 16))
                                   (width 16)
                                   (i (logtail 48 x)))
		                    (:instance auxiliary-lemma-2)))))

;; Semantic correctness of MOVSIGN
(gl::def-gl-thm movsign-semantics-64-correctness
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (movsign-semantics-64 x) (* (logtail 63 x) (1- (expt 2 64))))
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Equivalence of MOVSIGN-64 with its semantics
(defthm movsign-64-correctness
 (implies (unsigned-byte-p 64 x)
          (equal (movsign-64 x) (* (logtail 63 x) (1- (expt 2 64))))))
