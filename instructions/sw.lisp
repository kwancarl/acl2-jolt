(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../identity")

;; SH returns the lowest 16 bits of the input, zero-extended to word size

;; 32-BIT VERSION

(define sw-semantics-32 ((x (unsigned-byte-p 32 x)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16))
       ;; LOOKUP SEMANTICS
       (?x8-0 x8-0)
       (?x8-1 x8-1)
       (x8-2 x8-2)
       (x8-3 x8-3))
      ;; COMBINE
      (merge-2-u16s x8-2 x8-3)))

(define sw-32 ((x (unsigned-byte-p 32 x)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16))
       ;; MATERIALIZE SUBTABLES 
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       ;; LOOKUP SEMANTICS
       (?x8-0 (id-lookup x8-0 id-subtable))
       (?x8-1 (id-lookup x8-1 id-subtable))
       (x8-2 (id-lookup x8-2 id-subtable))
       (x8-3 (id-lookup x8-3 id-subtable)))
      ;; COMBINE
      (merge-2-u16s x8-2 x8-3)))


;; Proof of sw-32 and sw-semantics-32 equivalence
(encapsulate
 nil
 ;; ACL2 rewrites some chunk to "logtail" which could explain why the following
 ;; two lemmas are necessary, but sw-64 doesn't require these lemmas so perhaps
 ;; it has something to do with 16 being exactly half of 32

 (local (defthm silly-lemma-1 (natp (expt 2 16))))
 
 (local
  (gl::def-gl-thm silly-lemma-2
   :hyp (unsigned-byte-p 32 x)
   :concl (< (logtail 16 x) (expt 2 16))
   :g-bindings (gl::auto-bindings (:nat x 32))))
 
 (local (in-theory (disable id-lookup (:e expt))))
 
 (defthm sw-32-sw-semantics-32-equiv
  (equal (sw-32 x) (sw-semantics-32 x))
  :hints (("Goal" :in-theory (e/d (sw-semantics-32) ((:e materialize-identity-subtable)))
                  :use ((:instance lookup-identity-subtable-correctness
                                   (x-hi (expt 2 16))
                                   (i (logtail 16 x)))
 		       (:instance silly-lemma-2))))))
;; end encapsulate

;; SEMANTIC CORRECTNESS OF SW
(gl::def-gl-thm sw-semantics-32-correctness
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (sw-semantics-32 x)
	       (logand x #xffffffff))
 :g-bindings (gl::auto-bindings (:nat x 32)))

;; Equivalence of sw-32 with its semantics
(defthm sw-32-correctness
 (implies (unsigned-byte-p 32 x)
          (equal (sw-32 x) (logand x #xffffffff)))) 



;; 64-BIT VERSION

(define sw-semantics-64 ((x (unsigned-byte-p 64 x)))
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ;; CHUNK
       (x8-7 (part-select x :low  0 :width 16))
       (x8-6 (part-select x :low 16 :width 16))
       (x8-5 (part-select x :low 32 :width 16))
       (x8-4 (part-select x :low 48 :width 16))
       (x8-3 (part-select x :low 64 :width 16))
       (x8-2 (part-select x :low 80 :width 16))
       (x8-1 (part-select x :low 96 :width 16))
       (x8-0 (part-select x :low 112 :width 16))
       ;; LOOKUP SEMANTICS
       (?x8-0 x8-0)
       (?x8-1 x8-1)
       (?x8-2 x8-2)
       (?x8-3 x8-3)
       (?x8-4 x8-4)
       (?x8-5 x8-5)
       (x8-6 x8-6)
       (x8-7 x8-7))
      ;; COMBINE
      (merge-2-u16s x8-6 x8-7)))

(define sw-64 ((x (unsigned-byte-p 64 x)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ;; CHUNK
       (x8-7 (part-select x :low  0 :width 16))
       (x8-6 (part-select x :low 16 :width 16))
       (x8-5 (part-select x :low 32 :width 16))
       (x8-4 (part-select x :low 48 :width 16))
       (x8-3 (part-select x :low 64 :width 16))
       (x8-2 (part-select x :low 80 :width 16))
       (x8-1 (part-select x :low 96 :width 16))
       (x8-0 (part-select x :low 112 :width 16))
       ;; MATERIALIZE SUBTABLES 
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       ;; LOOKUP SEMANTICS
       (?x8-0 (id-lookup x8-0 id-subtable))
       (?x8-1 (id-lookup x8-1 id-subtable))
       (?x8-2 (id-lookup x8-2 id-subtable))
       (?x8-3 (id-lookup x8-3 id-subtable))
       (?x8-4 (id-lookup x8-4 id-subtable))
       (?x8-5 (id-lookup x8-5 id-subtable))
       (x8-6 (id-lookup x8-6 id-subtable))
       (x8-7 (id-lookup x8-7 id-subtable)))
      ;; COMBINE
      (merge-2-u16s x8-6 x8-7)))

(defthm sw-64-sw-semantics-64-equiv
 (equal (sw-64 x) (sw-semantics-64 x))
 :hints (("Goal" :in-theory (e/d (sw-semantics-64) ((:e materialize-identity-subtable))))))

;; SEMANTIC CORRECTNESS OF SW
(gl::def-gl-thm sw-semantics-64-correctness
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (sw-semantics-64 x)
	       (logand x #xffffffff))
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Equivalence of sw-64 with its semantics
(defthm sw-64-correctness
 (implies (unsigned-byte-p 64 x)
          (equal (sw-64 x) (logand x #xffffffff))))
