(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "../truncate")
(include-book "../sign-extend")

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
 (b* ((trunc (lookup chunk #xff truncate-subtable))
      (ext   (lookup trunc 8    sign-extend-subtable)))
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
         

