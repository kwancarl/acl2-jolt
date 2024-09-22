(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
;(include-book "eq")


;;;;;;;;;;;;;;
;;	    ;;
;;    zero lsb
;;	    ;;
;;;;;;;;;;;;;;
(define zero-lsb ((x :type unsigned-byte))
 (logcons 0 (logcdr x)))

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


