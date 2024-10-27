(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(include-book "subtable")

;;;;;;;;;;;;;;;;;;;;
;;	          ;;
;;    zero lsb    ;;
;;	          ;;
;;;;;;;;;;;;;;;;;;;;

;; (define zero-lsb ((x :type unsigned-byte))
;;  (logcons 0 (logcdr x)))

(define zero-lsb ((x :type unsigned-byte))
 (- x (mod x 2)))

(gl::def-gl-thm zero-lsb-correctness-32-gl
 :hyp (unsigned-byte-p 32 x)
 :concl (evenp (zero-lsb x))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm zero-lsb-correctness-32-gl-1
 :hyp (and (unsigned-byte-p 32 x) (oddp x))
 :concl (equal (zero-lsb x) (1- x))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm zero-lsb-correctness-32-gl-2
 :hyp (and (unsigned-byte-p 32 x) (evenp x))
 :concl (equal (zero-lsb x) x)
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm zero-lsb-correctness-64-gl
 :hyp (unsigned-byte-p 64 x)
 :concl (evenp (zero-lsb x))
 :g-bindings (gl::auto-bindings (:nat x 64)))

(gl::def-gl-thm zero-lsb-correctness-64-gl-1
 :hyp (and (unsigned-byte-p 64 x) (oddp x))
 :concl (equal (zero-lsb x) (1- x))
 :g-bindings (gl::auto-bindings (:nat x 64)))

(gl::def-gl-thm zero-lsb-correctness-64-gl-2
 :hyp (and (unsigned-byte-p 64 x) (evenp x))
 :concl (equal (zero-lsb x) x)
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; Materialize the zero-lsb subtable
;; ZeroLsb(z) = z - (z mod 2)
(define materialize-zero-lsb-subtable (z-hi)
 :enabled t
 :returns (lst alistp)
 :measure (acl2-count z-hi)
 :verify-guards nil
 (if (or (not (natp z-hi)))
     nil
     (if (zerop z-hi)
         (cons (cons z-hi (- z-hi (mod z-hi 2))) nil)
         (cons (cons z-hi (- z-hi (mod z-hi 2)))
               (materialize-zero-lsb-subtable (1- z-hi))))))

(defthm zero-lsb-subtable-correctness
 (implies (and (natp z-hi) 
               (natp i) 
               (<= i z-hi))
          (b* ((subtable (materialize-zero-lsb-subtable z-hi)))
              (equal (assoc-equal i subtable)
                     (cons i (- i (mod i 2)))))))

(defthm lookup-zero-lsb-subtable-correctness
 (implies (and (natp z-hi)
               (natp i)
               (<= i z-hi))
          (b* ((subtable (materialize-zero-lsb-subtable z-hi)))
              (equal (single-lookup i subtable)
                     (- i (mod i 2)))))
 :hints (("Goal" :in-theory (e/d (single-lookup) (materialize-zero-lsb-subtable))
	         :use ((:instance zero-lsb-subtable-correctness)))))