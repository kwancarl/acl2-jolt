(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(include-book "subtable")


;;;;;;;;;;;;;;
;;	    ;;
;;    left msb
;;	    ;;
;;;;;;;;;;;;;;

(define left-msb-8 ((x :type unsigned-byte) y)
  :irrelevant-formals-ok t
  :ignore-ok t
  :enabled t
  :returns (msb bitp)
 (logbit 7 x))

(gl::def-gl-thm left-msb-8-correctness
 :hyp (unsigned-byte-p 8 x)
 :concl (equal (left-msb-8 x y)
               (if (<= (expt 2 7) x) 1 0))
 :g-bindings (gl::auto-bindings (:nat x 8)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                      ;;
;;    MATERIALIZE LEFT-MSB SUBTABLE   ;;
;;                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun materialize-left-msb-8-subtable (idx-lst)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons x y)                    idx))
     (cons (cons idx (left-msb-8 x y))
           (materialize-left-msb-8-subtable rst))))

(defthm alistp-of-materialize-left-msb-8-subtable
 (alistp (materialize-left-msb-8-subtable idx-lst)))

(defthm member-idx-lst-assoc-materialize-left-msb-8-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-left-msb-8-subtable idx-lst))))

(defthm assoc-member-materialize-left-msb-8-subtable
 (implies (assoc (cons x y) (materialize-left-msb-8-subtable idx-lst))
          (member (cons x y) idx-lst)))

(defthm assoc-materialize-left-msb-8-subtable
 (implies (assoc (cons i j) (materialize-left-msb-8-subtable idx-lst))
          (equal (assoc (cons i j) (materialize-left-msb-8-subtable idx-lst))
                 (cons (cons i j) (left-msb-8 i j)))))

(defthm materialize-left-msb-8-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-left-msb-8-subtable indices)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j)
                           (left-msb-8 i j))))))

(defthm lookup-materialize-left-msb-8-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-left-msb-8-subtable indices)))
              (equal (tuple-lookup i j subtable)
                     (logbit 7 i))))
 :hints (("Goal" :in-theory (e/d (tuple-lookup left-msb-8) ()))))

(in-theory (disable left-msb-8))











