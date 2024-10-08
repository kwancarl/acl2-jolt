(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/logops-lemmas" :dir :system)

(include-book "subtable")

;; Materialize subtables for "truncate-overflow"

(define materialize-truncate-subtable (x-hi mask)
 :enabled t
 :returns (lst alistp)
 :measure (acl2-count x-hi)
 :verify-guards nil
 (if (or (not (natp x-hi)) (not (natp mask)))
     nil
     (if (zerop x-hi)
         (cons (cons x-hi (logand x-hi mask)) nil)
         (cons (cons x-hi (logand x-hi mask))
               (materialize-truncate-subtable (1- x-hi) mask)))))

(defthm truncate-subtable-correctness
 (implies (and (natp x-hi) 
               (natp i) 
               (natp mask) 
               (<= i x-hi))
          (b* ((subtable (materialize-truncate-subtable x-hi mask)))
              (equal (assoc-equal i subtable)
                     (cons i (logand i mask))))))

(defthm lookup-truncate-subtable-correctness
 (implies (and (natp x-hi) 
               (natp i) 
               (natp mask) 
               (<= i x-hi))
          (b* ((subtable (materialize-truncate-subtable x-hi mask)))
              (equal (single-lookup i subtable)
                     (logand i mask))))
 :hints (("Goal" :in-theory (e/d (single-lookup) (materialize-truncate-subtable))
	         :use ((:instance truncate-subtable-correctness)))))


;; Evaluate mle and correctness of lookup

;; Truncates `x` to `size` least significant bits
(define truncate-overflow ((x :type unsigned-byte) (size natp))
 :verify-guards nil
 :returns (smaller acl2-numberp)
 :measure (acl2-count size)
 (if (not (and (natp x) (posp size)))
     0
     (+ (logcar x)
        (* 2 (truncate-overflow (logcdr x) (1- size))))))
(verify-guards truncate-overflow)

;; Equivalence theorems for truncate-overflow

;; Equivalance to logand
(gl::def-gl-thm truncate-overflow-0-logand-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 x))
 :concl (equal (truncate-overflow x 0) 0)
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm truncate-overflow-8-logand-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 x))
 :concl (equal (truncate-overflow x 8) (logand x #xff))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm truncate-overflow-8-logand-equiv-64-bit-gl
 :hyp   (and (unsigned-byte-p 64 x))
 :concl (equal (truncate-overflow x 8) (logand x #xff))
 :g-bindings (gl::auto-bindings (:nat x 64)))

(gl::def-gl-thm truncate-overflow-16-logand-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 x))
 :concl (equal (truncate-overflow x 16) (logand x #xffff))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm truncate-overflow-16-logand-equiv-64-bit-gl
 :hyp   (and (unsigned-byte-p 64 x))
 :concl (equal (truncate-overflow x 16) (logand x #xffff))
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Equivalance to mod
(gl::def-gl-thm truncate-overflow-8-mod-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 x))
 :concl (equal (truncate-overflow x 8) (mod x (expt 2 8)))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm truncate-overflow-8-mod-equiv-64-bit-gl
 :hyp   (and (unsigned-byte-p 64 x))
 :concl (equal (truncate-overflow x 8) (mod x (expt 2 8)))
 :g-bindings (gl::auto-bindings (:nat x 64)))

(gl::def-gl-thm truncate-overflow-16-mod-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 x))
 :concl (equal (truncate-overflow x 16) (mod x (expt 2 16)))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm truncate-overflow-16-mod-equiv-64-bit-gl
 :hyp   (and (unsigned-byte-p 64 x))
 :concl (equal (truncate-overflow x 16) (mod x (expt 2 16)))
 :g-bindings (gl::auto-bindings (:nat x 64)))
