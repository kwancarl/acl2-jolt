(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(include-book "eq")


;;;;;;;;;;;;;;
;;	    ;;
;;    left is zero
;;	    ;;
;;;;;;;;;;;;;;
(define left-is-zero-w ((x :type unsigned-byte) y)
  :irrelevant-formals-ok t
  :returns (eq? bitp)
  (b* (((unless (and (natp x))) 0)
       (x-car  (logcar x))
       (x-cdr  (logcdr x)))
      (if (bitp x) 
          (b-xor 1 x-car)
          (b-and (logxor 1 x-car) (left-is-zero-w x-cdr y))))
 ///
 (defthm left-is-zero-correctness
   (implies (natp x)
            (equal (left-is-zero-w x y)
                   (if (zerop x) 1 0))))
 (defthm left-is-zero-32-correctness
   (implies (unsigned-byte-p 32 x)
            (equal (left-is-zero-w x y)
                   (if (zerop x) 1 0)))))
;; end define
