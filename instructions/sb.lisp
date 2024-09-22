(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "../truncate")

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
(define sb-chunk ((x :type unsigned-byte) y) 
 :enabled t 
 :ignore-ok t
 :irrelevant-formals-ok t
 (logand x #xffff))

;; "LOOKUP"
(defun sb-lookup (chunk subtable) 
 (lookup chunk #xff subtable))

;; "COMBINE"
(defun sb-combine (lookup) lookup)

(defthm sb-correctness
 (implies (unsigned-byte-p 64 x)
          (b* ((indices  (truncate-indices (expt 2 16) #xff))
               (subtable (materialize-truncate-subtable indices)))
              (equal (sb-lookup (sb-chunk x 0) subtable)
                     (logand x #xff))))
 :hints (("Goal" :use ((:instance lookup-truncate-subtable-correctness
                                  (mask #xff)
                                  (x-hi (expt 2 16))
                                  (i (logand x #xffff)))
                       (:instance mask-lower-16-bound)))))

