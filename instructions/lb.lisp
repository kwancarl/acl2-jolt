(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "../subtables/identity")
(include-book "../subtables/truncate")
(include-book "../subtables/sign-extend")

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

;; LB returns the lower 8 bits of the input, sign-extended to word size
;; Note: semantics for loads and stores are handled in different parts of Jolt,
;; and not the scope of this formalization


;; (not quite working yet but committing anyway)

;; 32-BIT VERSION

(defun sign-extend-m-w (z m w)
  (if (= (logbit (1- w) z) 0)
      0
      (1- (ash 1 m))))

(defun sign-extend (z w)
  (sign-extend-m-w z 32 w))

(define lb-semantics-32 ((x (unsigned-byte-p 32 x)))
  :verify-guards nil
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
       (z (truncate-overflow x8-3 8))
       (s (sign-extend x8-3 8)))
      ;; COMBINE
      (merge-4-u8s s s s z)))

(define lb-32 ((x (unsigned-byte-p 32 x)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16))
       ;; MATERIALIZE SUBTABLES
       (indices            (create-tuple-indices (expt 2 8) (expt 2 8)))
       (id-subtable        (materialize-identity-subtable (expt 2 16)))
       (sign-extend-subtable (materialize-sign-extend-subtable-32 indices))
       (truncate-indices      (truncate-indices (expt 2 16) #xff))
       (truncate-subtable (materialize-truncate-subtable truncate-indices))
       ;; LOOKUP SEMANTICS
       ;; Note that the `id` lookups are present in the Jolt codebase for reasons not related to the immediate semantics of SB
       ;; Instead they are used as range checks for the input value, which is necessary for other parts of the Jolt's constraint system
       ;; We include them here for completeness
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (s (tuple-lookup x8-3 8 sign-extend-subtable))
       (z (tuple-lookup x8-3 #xff truncate-subtable)))
      ;; COMBINE
      (merge-4-u8s s s s z)))

(defthm lb-32-lb-semantics-32-equiv
 (equal (lb-32 x) (lb-semantics-32 x))
 :hints (("Goal" :in-theory (e/d (lb-semantics-32) ((:e materialize-sign-extend-subtable-32) (:e truncate-indices))))))

;; SEMANTIC CORRECTNESS OF LB
(gl::def-gl-thm lb-semantics-32-correctness
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (lb-semantics-32 x)
	       (logext 32 (logand x #xff)))
 :g-bindings (gl::auto-bindings (:nat x 32)))

;; Equivalence of lb-32 with its semantics
(defthm lb-32-correctness
 (implies (unsigned-byte-p 32 x)
          (equal (lb-32 x) (logext 32 (logand x #xff))))) 









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


(local
 (gl::def-gl-thm mask-lower-8-bound
  :hyp (unsigned-byte-p 64 x)
  :concl (<= (logand x #xff) (expt 2 8))
  :g-bindings (gl::auto-bindings (:nat x 64))))

(local
 (gl::def-gl-thm logextu-32-8-of-logand-#xff
  :hyp (unsigned-byte-p 64 x)
  :concl (equal (logextu 32 8 (logand x #xff))
                (logextu 32 8 x))
  :g-bindings (gl::auto-bindings (:nat x 64))))
  
;; This lemma should not be local
(local 
 (defthm natp-of-logand
  (implies (and (natp x) (natp y))
           (natp (logand x y)))))

;; "CHUNK"
(define lb-chunk ((x :type unsigned-byte) y) 
 :enabled t 
 :ignore-ok t
 :irrelevant-formals-ok t
 (logand x #xffff))

;; "LOOKUP"
(defun lb-lookup (chunk truncate-subtable sign-extend-subtable) 
 (b* ((trunc (tuple-lookup chunk #xff truncate-subtable))
      (ext   (tuple-lookup trunc 8    sign-extend-subtable)))
     (cons trunc ext)))

(defthm lb-lookup-correctness-32
 (implies (and (unsigned-byte-p 64 x))
          (b* ((chunk (lb-chunk x 0))
               (truncate-idx  (truncate-indices (expt 2 16) #xff))
               (truncate-subtable (materialize-truncate-subtable truncate-idx))
               (sgn-ext-idx (sign-extend-idx (expt 2 16) 8))
               (sgn-ext-subtable (materialize-sign-extend-subtable-32 sgn-ext-idx))
               ((cons trunc ext) (lb-lookup chunk truncate-subtable sgn-ext-subtable)))
              (and (equal trunc (logand x #xff))
                   (equal ext (logtail 8 (logextu 32 8 (logand x #xff)))))))
 :hints (("Goal" :use ((:instance lookup-truncate-subtable-correctness
                                  (mask #xff)
                                  (x-hi (expt 2 16))
                                  (i (logand x #xffff)))
                       (:instance lookup-materialize-sign-extend-subtable-32-correctness
                                  (width 8)
                                  (z-hi (expt 2 16))
                                  (i (logand x #xff)))
                       (:instance mask-lower-16-bound)
                       (:instance mask-lower-8-bound)))))
;; "COMBINE"
(defun lb-combine (trunc ext) (logapp 8 trunc ext))

;; 

(gl::def-gl-thm foo
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (logapp 8 (logand x #xff) (logtail 8 (logextu 32 8 (logand x #xff))))
               (logextu 32 8 (logand x #xff)))
 :g-bindings (gl::auto-bindings (:nat x 64)))

(defthm lb-correctness-32
 (implies (and (unsigned-byte-p 64 x))
          (b* ((chunk (lb-chunk x 0))
               (truncate-idx  (truncate-indices (expt 2 16) #xff))
               (truncate-subtable (materialize-truncate-subtable truncate-idx))
               (sgn-ext-idx (sign-extend-idx (expt 2 16) 8))
               (sgn-ext-subtable (materialize-sign-extend-subtable-32 sgn-ext-idx))
               ((cons trunc ext) (lb-lookup chunk truncate-subtable sgn-ext-subtable)))
              (equal (lb-combine trunc ext)
                     (logextu 32 8 (logand x #xff)))))
 :hints (("Goal" :use ((:instance lb-lookup-correctness-32)
                       (:instance foo)))))
         

