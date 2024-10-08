(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(include-book "eq")

;;;;;;;;;;;;;;;;;;;;;;;;;
;;	               ;;
;;    right is zero    ;;
;;	               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;

(define right-is-zero-w (x (y :type unsigned-byte))
  :irrelevant-formals-ok t
  :returns (zero bitp)
  (b* (((unless (and (natp y))) 0)
       (y-car  (logcar y))
       (y-cdr  (logcdr y)))
      (if (bitp y) 
          (b-xor 1 y-car)
          (b-and (logxor 1 y-car) (right-is-zero-w x y-cdr))))
 ///
 (defthm right-is-zero-correctness
   (implies (natp y)
            (equal (right-is-zero-w x y)
                   (if (zerop y) 1 0))))
 (defthm left-is-zero-32-correctness
   (implies (unsigned-byte-p 32 y)
            (equal (right-is-zero-w x y)
                   (if (zerop y) 1 0)))))
;; end define
