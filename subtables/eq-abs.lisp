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

;;;;;;;;;;;;;;;;;;
;;	        ;;
;;    Eq-abs    ;;
;;	        ;;
;;;;;;;;;;;;;;;;;;
(define eq-abs-w ((x :type unsigned-byte) (y :type unsigned-byte) (w posp))
  :returns (eq? bitp)
  (b* (((unless (and (natp x) (natp y) (posp w))) 0)
       (x-abs  (loghead (1- w) x))
       (y-abs  (loghead (1- w) y)))
      (eqw x-abs y-abs)))

(gl::def-gl-thm logbitp-when-<=-2^32
  :hyp   (and (unsigned-byte-p 32 x))
  :concl (equal (logbitp 31 x)
              (<= (expt 2 31) x))
  :g-bindings (gl::auto-bindings (:nat x 32)))

(define eq-abs-8 ((x (unsigned-byte-p 8 x)) (y (unsigned-byte-p 8 y)))
  :enabled t
  :returns (eq? bitp)
  (mbe 
    :logic
     (b* (((unless (and (natp x) (natp y))) 0)
          (x-abs  (loghead 7 x))
          (y-abs  (loghead 7 y)))
         (if (= x-abs y-abs) 1 0))
    :exec
     (b* ((x-abs  (loghead 7 x))
          (y-abs  (loghead 7 y)))
         (if (= x-abs y-abs) 1 0))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                      ;;
;;    Materialize eq-abs subtable       ;;
;;                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun materialize-eq-abs-subtable-8 (idx-lst)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons x y)                    idx))
     (cons (cons idx (eq-abs-8 x y))
           (materialize-eq-abs-subtable-8 rst))))

(defthm alistp-of-materialize-eq-abs-subtable-8
 (alistp (materialize-eq-abs-subtable-8 idx-lst)))

(defthm member-idx-lst-assoc-materialize-eq-abs-subtable-8
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-eq-abs-subtable-8 idx-lst))))

(defthm assoc-member-materialize-eq-abs-subtable-8
 (implies (assoc (cons x y) (materialize-eq-abs-subtable-8 idx-lst))
          (member (cons x y) idx-lst)))

(defthm assoc-materialize-eq-abs-subtable-8
 (implies (assoc (cons i j) (materialize-eq-abs-subtable-8 idx-lst))
          (equal (assoc (cons i j) (materialize-eq-abs-subtable-8 idx-lst))
                 (cons (cons i j) (eq-abs-8 i j)))))

(defthm materialize-eq-abs-subtable-8-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-eq-abs-subtable-8 indices)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j)
                           (eq-abs-8 i j))))))

(defthm lookup-materialize-eq-abs-subtable-8-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-eq-abs-subtable-8 indices)))
              (equal (tuple-lookup i j subtable)
                     (eq-abs-8 i j))))
 :hints (("Goal" :in-theory (e/d (tuple-lookup) ()))))
