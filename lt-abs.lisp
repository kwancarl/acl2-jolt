(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(include-book "eq")
(include-book "subtable")

;;;;;;;;;;;;;;
;;	    ;;
;;    LT-ABS    ;;
;;	    ;;
;;;;;;;;;;;;;;
(define lt-abs-8 ((x (unsigned-byte-p 8 x)) (y (unsigned-byte-p 8 y)))
  :enabled t
  :returns (lt? bitp)
  (mbe 
    :logic
     (b* (((unless (and (natp x) (natp y))) 0)
          (x-abs  (loghead 7 x))
          (y-abs  (loghead 7 y)))
         (if (< x-abs y-abs) 1 0))
    :exec
     (b* ((x-abs  (loghead 7 x))
          (y-abs  (loghead 7 y)))
         (if (< x-abs y-abs) 1 0))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                      ;;
;;    MATERIALIZE LT-ABS SUBTABLE   ;;
;;                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun materialize-lt-abs-8-subtable (idx-lst)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons x y)                    idx))
     (cons (cons idx (lt-abs-8 x y))
           (materialize-lt-abs-8-subtable rst))))

(defthm alistp-of-materialize-lt-abs-8-subtable
 (alistp (materialize-lt-abs-8-subtable idx-lst)))

(defthm member-idx-lst-assoc-materialize-lt-abs-8-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-lt-abs-8-subtable idx-lst))))

(defthm assoc-member-materialize-lt-abs-8-subtable
 (implies (assoc (cons x y) (materialize-lt-abs-8-subtable idx-lst))
          (member (cons x y) idx-lst)))

(defthm assoc-materialize-lt-abs-8-subtable
 (implies (assoc (cons i j) (materialize-lt-abs-8-subtable idx-lst))
          (equal (assoc (cons i j) (materialize-lt-abs-8-subtable idx-lst))
                 (cons (cons i j) (lt-abs-8 i j)))))

(defthm materialize-lt-abs-8-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-x-indices x-hi y-hi))
               (subtable (materialize-lt-abs-8-subtable indices)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j)
                           (lt-abs-8 i j))))))

(defthm lookup-materialize-lt-abs-8-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-x-indices x-hi y-hi))
               (subtable (materialize-lt-abs-8-subtable indices)))
              (equal (lookup i j subtable)
                     (lt-abs-8 i j))))
 :hints (("Goal" :in-theory (e/d (lookup) ()))))

