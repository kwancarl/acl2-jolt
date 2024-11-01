(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(include-book "subtable")

;;;;;;;;;;;;;;;;;;;;;;;
;;	             ;;
;;    DIV_BY_ZERO    ;;
;;	             ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; Check if x_i = 0 and y_i = 1
;;   (1 - x0)y0
(define b-div-by-zero  ((x0 bitp) (y0 bitp))
  (b-and (b-xor 1 x0) y0)
  ///
  (defthm b-div-by-zero-correctness
    (implies (and (bitp x0) (bitp y0))
             (equal (b-div-by-zero x0 y0)
               	    (if (and (equal y0 1) 
                             (equal x0 0)) 
                        1 
                        0)))
    :hints (("Goal" :cases ((equal x0 0))))))


(local (defthm natp-of-integer-length
  (natp (integer-length x))))

(local (defthm natp-when-not-bitp
  (implies (and (natp x) (not (bitp x)))
	   (<= 2 x))
  :hints (("Goal" :in-theory (enable bitp))))) 

(local (defthm integer-length->-0
  (implies (and (natp x) (not (bitp x)))
	   (< 0 (integer-length x)))
  :hints (("Goal" :in-theory (enable integer-length)))))

(local
 (defthm non-zero-nat
  (implies (and (natp w) (not (equal w 0)))
           (<= 1 w))))

(defthm bitp-of-loghead-1
 (bitp (loghead 1 x)))

;; Equality of a chunk of size w/c
;; (x_0*y_0 + (1-x_0)*(1-y_0)) * recurse
(define div-by-zero-w ((x :type unsigned-byte) (y :type unsigned-byte) (w posp))
  :measure (nfix (1+ w))
  :returns (eq? bitp)
  (b* (((unless (and (natp x) (natp y) (natp w))) 0)
       ((if (and (equal w 1) (bitp x) (bitp y))) (b-div-by-zero x y))
       ((if (equal w 1)) 0)
       (x0  	(loghead 1 x))
       (y0  	(loghead 1 y))
       (div0 	(b-div-by-zero x0 y0))
       (x-rest  (ash x -1))
       (y-rest  (ash y -1)))
      (b-and div0 (div-by-zero-w x-rest y-rest (1- w)))))

;; DivByZero(x, y) = 1 only when x = 00..0 and y = 11..1
(defun div-by-zero (x y m)
  (declare (xargs :guard (and (natp x) (natp y) (natp m))))
  (if (and (equal x 0) (equal y (1- (expt 2 m))))
      1 0))

;; Materialize the div-by-zero subtable
(defun materialize-div-by-zero-subtable (idx-lst m)
 (b* (;; Edge case
      ((unless (alistp idx-lst))     nil)
      ;; Base case
      ((if (atom idx-lst))           nil)
      ;; Bind head & tail in the index list
      ((cons hd tl)              idx-lst)
      ;; Edge case
      ((unless (consp hd))           nil)
      ;; Bind x & y operands in the head
      ((cons x y)                     hd))
     ;; Construct a key-value pair
     ;;   key:    (x y)
     ;;   value:  1 if x = 00..0 and y = 11..1, 0 otherwise
     (cons (cons hd (div-by-zero x y m))
           (materialize-div-by-zero-subtable tl m))))

(defthm alistp-of-materialize-div-by-zero-subtable
 (alistp (materialize-div-by-zero-subtable idx-lst m)))

(defthm member-idx-lst-assoc-materialize-div-by-zero-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst) (natp m))
          (assoc idx (materialize-div-by-zero-subtable idx-lst m))))

(defthm assoc-member-div-by-zero-subtable
 (implies (assoc (cons i j) (materialize-div-by-zero-subtable idx-lst m))
          (member (cons i j) idx-lst)))

(defthm assoc-div-by-zero-subtable
 (implies (assoc (cons i j) (materialize-div-by-zero-subtable idx-lst m))
          (equal (assoc (cons i j) (materialize-div-by-zero-subtable idx-lst m))
                 (cons (cons i j) (div-by-zero i j m)))))

(defthm div-by-zero-subtable-correctness
 (implies (and (natp m)
               (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi) )
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-div-by-zero-subtable indices m)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j) (div-by-zero i j m))))))

;; Lookup values within the bounds of the subtable are
;; equivalent to "equal"
(defthm lookup-div-by-zero-subtable-correctness
 (implies (and (natp m)
               (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-div-by-zero-subtable indices m)))
              (equal (tuple-lookup i j subtable)
                     (div-by-zero i j m))))
 :hints (("Goal" :in-theory (enable tuple-lookup))))
