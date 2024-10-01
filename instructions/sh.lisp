(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)

(include-book "../identity")

;; SH returns the lowest 16 bits of the input, zero-extended to word size

;; 32-BIT VERSION

(define sh-semantics-32 ((x (unsigned-byte-p 32 x)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16))
       ;; LOOKUP SEMANTICS
       (?x8-0 x8-0)
       (?x8-1 x8-1)
       (?x8-2 x8-2)
       (x8-3 x8-3))
      ;; COMBINE
      x8-3))

(define sh-32 ((x (unsigned-byte-p 32 x)))
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
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (x8-3 (single-lookup x8-3 id-subtable)))
      ;; COMBINE
      x8-3))

(defthm sh-32-sh-semantics-32-equiv
 (equal (sh-32 x) (sh-semantics-32 x))
 :hints (("Goal" :in-theory (e/d (sh-semantics-32) ((:e materialize-identity-subtable))))))

;; SEMANTIC CORRECTNESS OF SH
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
       (?x8-6 x8-6)
       (x8-7 x8-7))
      ;; COMBINE
      x8-7))

(define sh-64 ((x (unsigned-byte-p 64 x)))
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
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (?x8-3 (single-lookup x8-3 id-subtable))
       (?x8-4 (single-lookup x8-4 id-subtable))
       (?x8-5 (single-lookup x8-5 id-subtable))
       (?x8-6 (single-lookup x8-6 id-subtable))
       (x8-7 (single-lookup x8-7 id-subtable)))
      ;; COMBINE
      x8-7))

(defthm sh-64-sh-semantics-64-equiv
 (equal (sh-64 x) (sh-semantics-64 x))
 :hints (("Goal" :in-theory (e/d (sh-semantics-64) ((:e materialize-identity-subtable))))))

;; SEMANTIC CORRECTNESS OF SH
(gl::def-gl-thm sh-semantics-64-correctness
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (sh-semantics-64 x)
	       (logand x #xffff))
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Equivalence of sh-64 with its semantics
(defthm sh-64-correctness
 (implies (unsigned-byte-p 64 x)
          (equal (sh-64 x) (logand x #xffff)))) 



;; A prior approach that separates chunking, lookup, and combining
;; May revisit later

;; Lemmas
(local
 (gl::def-gl-thm mask-of-mask-32-16
  :hyp   (and (unsigned-byte-p 64 x))
  :concl (equal (logand (logand x #xffff) #xff)
                (logand x #xff))
  :g-bindings (gl::auto-bindings (:nat x 64))))

(local 
 (gl::def-gl-thm mask-lower-16-bound
  :hyp   (unsigned-byte-p 64 x)
  :concl (<= (logand x #xffff) (expt 2 16))
  :g-bindings (gl::auto-bindings (:nat x 64))))

;; This lemma should not be local
(local 
 (defthm natp-of-logand
  (implies (and (natp x) (natp y))
           (natp (logand x y)))))

;; "CHUNK"
(define sh-chunk ((x :type unsigned-byte) y) 
 :enabled t 
 :ignore-ok t
 :irrelevant-formals-ok t
 (logand x #xffff))

;; "LOOKUP"
(defun sh-lookup (chunk subtable) 
 (single-lookup chunk subtable))

;; "COMBINE"
(defun sh-combine (lookup) lookup)

;; This is the same theorem for both 32-bit and 64-bit?
;; (defthm sh-correctness
;;  (implies (unsigned-byte-p 64 x)
;;           (b* ((indices  (expt 2 16))
;;                (id-subtable (materialize-identity-subtable indices)))
;;               (equal (sh-lookup (sh-chunk x 0) id-subtable)
;;                      (logand x #xffff))))
;;  :hints (("Goal" :use ((:instance lookup-identity-subtable-correctness
;;                                   (x-hi (expt 2 16))
;;                                   (i (logand x #xffff)))
;;                        (:instance mask-lower-16-bound)))))

