(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)

(include-book "../subtables/truncate-overflow")
(include-book "../subtables/identity")

;; SB returns the lower 8 bits of the input, zero-extended to word size

(local
 (gl::def-gl-thm loghead-8-16-32
  :hyp   (and (unsigned-byte-p 32 x))
  :concl (equal (loghead 8 x)
                (mod (loghead 16 x) (expt 2 8)))
  :g-bindings (gl::auto-bindings (:nat x 32))))

;; 32-BIT VERSION

(define sb-semantics-32 ((x (unsigned-byte-p 32 x)))
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
       (z8-3 (truncate-overflow x8-3 8)))
      ;; COMBINE
      z8-3))

(define sb-32 ((x (unsigned-byte-p 32 x)))
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
       (truncate-idx      (truncate-indices (expt 2 16) #xff))
       (truncate-subtable (materialize-truncate-subtable truncate-idx))
       ;; LOOKUP SEMANTICS
       ;; Note that the `id` lookups are present in the Jolt codebase for reasons not related to the immediate semantics of SB
       ;; Instead they are used as range checks for the input value, which is necessary for other parts of the Jolt's constraint system
       ;; We include them here for completeness
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (x8-3 (tuple-lookup x8-3 #xff truncate-subtable)))
      ;; COMBINE
      x8-3))

(defthm sb-32-sb-semantics-32-equiv
 (equal (sb-32 x) (sb-semantics-32 x))
 :hints (("Goal" :in-theory (e/d (sb-semantics-32) ((:e materialize-identity-subtable) (:e truncate-indices))))))

;; SEMANTIC CORRECTNESS OF SB
(gl::def-gl-thm sb-semantics-32-correctness
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (sb-semantics-32 x)
	       (logand x #xff))
 :g-bindings (gl::auto-bindings (:nat x 32)))

;; Equivalence of sb-32 with its semantics
(defthm sb-32-correctness
 (implies (unsigned-byte-p 32 x)
          (equal (sb-32 x) (logand x #xff)))) 

;; 64-BIT VERSION

(define sb-semantics-64 ((x (unsigned-byte-p 64 x)))
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
       (x8-7 (truncate-overflow x8-7 8)))
      ;; COMBINE
      x8-7))

(define sb-64 ((x (unsigned-byte-p 64 x)))
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
       (truncate-idx      (truncate-indices (expt 2 16) #xff))
       (truncate-subtable (materialize-truncate-subtable truncate-idx))
       ;; LOOKUP SEMANTICS
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (?x8-3 (single-lookup x8-3 id-subtable))
       (?x8-4 (single-lookup x8-4 id-subtable))
       (?x8-5 (single-lookup x8-5 id-subtable))
       (?x8-6 (single-lookup x8-6 id-subtable))
       (x8-7 (tuple-lookup x8-7 #xff truncate-subtable)))
      ;; COMBINE
      x8-7))

(defthm sb-64-sb-semantics-64-equiv
 (equal (sb-64 x) (sb-semantics-64 x))
 :hints (("Goal" :in-theory (e/d (sb-semantics-64) ((:e materialize-identity-subtable) (:e truncate-indices))))))

;; SEMANTIC CORRECTNESS OF SB
(gl::def-gl-thm sb-semantics-64-correctness
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (sb-semantics-64 x)
	       (logand x #xff))
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Equivalence of sb-64 with its semantics
(defthm sb-64-correctness
 (implies (unsigned-byte-p 64 x)
          (equal (sb-64 x) (logand x #xff)))) 


;; Lemmas
;; (local
;;  (gl::def-gl-thm mask-of-mask-32-16
;;   :hyp   (and (unsigned-byte-p 64 x))
;;   :concl (equal (logand (logand x #xffff) #xff)
;;                 (logand x #xff))
;;   :g-bindings (gl::auto-bindings (:nat x 64))))

;; (local 
;;  (gl::def-gl-thm mask-lower-16-bound
;;   :hyp   (unsigned-byte-p 64 x)
;;   :concl (<= (logand x #xffff) (expt 2 16))
;;   :g-bindings (gl::auto-bindings (:nat x 64))))

;; ;; This lemma should not be local
;; (local 
;;  (defthm natp-of-logand
;;   (implies (and (natp x) (natp y))
;;            (natp (logand x y)))))

;; ;; "CHUNK"
;; (define sb-chunk ((x :type unsigned-byte) y) 
;;  :enabled t 
;;  :ignore-ok t
;;  :irrelevant-formals-ok t
;;  (logand x #xffff))

;; ;; "LOOKUP"
;; (defun sb-lookup (chunk subtable) 
;;  (tuple-lookup chunk #xff subtable))

;; ;; "COMBINE"
;; (defun sb-combine (tuple-lookup) lookup)

;; ;; This is the same theorem for both 32-bit and 64-bit?
;; (defthm sb-correctness
;;  (implies (unsigned-byte-p 64 x)
;;           (b* ((indices  (truncate-indices (expt 2 16) #xff))
;;                (subtable (materialize-truncate-subtable indices)))
;;               (equal (sb-lookup (sb-chunk x 0) subtable)
;;                      (logand x #xff))))
;;  :hints (("Goal" :use ((:instance lookup-truncate-subtable-correctness
;;                                   (mask #xff)
;;                                   (x-hi (expt 2 16))
;;                                   (i (logand x #xffff)))
;;                        (:instance mask-lower-16-bound)))))

