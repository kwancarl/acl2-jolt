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

;; Materialize the right-is-zero subtable
;; RightIsZero(x, y) = 1 only when y = 00..0
(defun materialize-right-is-zero-subtable (idx-lst)
 (b* (;; Edge case
      ((unless (alistp idx-lst))     nil)
      ;; Base case
      ((if (atom idx-lst))           nil)
      ;; Bind head & tail in the index list
      ((cons hd tl)              idx-lst)
      ;; Edge case
      ((unless (consp hd))           nil)
      ;; Bind x & y operands in the head
      ((cons ?x y)                     hd))
     ;; Construct a key-value pair
     ;;   key:    (x y)
     ;;   value:  1 if y = 00..0, 0 otherwise
     (cons (cons hd (if (= y 0) 1 0))
           (materialize-right-is-zero-subtable tl))))

(defthm alistp-of-materialize-right-is-zero-subtable
 (alistp (materialize-right-is-zero-subtable idx-lst)))

(defthm member-idx-lst-assoc-materialize-right-is-zero-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-right-is-zero-subtable idx-lst))))

(defthm assoc-member-right-is-zero-subtable
 (implies (assoc (cons i j) (materialize-right-is-zero-subtable idx-lst))
          (member (cons i j) idx-lst)))

(defthm assoc-right-is-zero-subtable
 (implies (assoc (cons i j) (materialize-right-is-zero-subtable idx-lst))
          (equal (assoc (cons i j) (materialize-right-is-zero-subtable idx-lst))
                 (cons (cons i j) (if (equal j 0) 1 0)))))

(defthm right-is-zero-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi) )
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-right-is-zero-subtable indices)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j) (if (= j 0) 1 0))))))

;; Lookup values within the bounds of the subtable are equivalent to "x = 0"
(defthm lookup-right-is-zero-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-right-is-zero-subtable indices)))
              (equal (tuple-lookup i j subtable)
                     (if (= j 0) 1 0))))
 :hints (("Goal" :in-theory (enable tuple-lookup))))