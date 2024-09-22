(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "eq")
(include-book "subtable")
;; TODO: refactor and clean

;;
;;
;;    Materialize subtables for SRL
;;
;;
;; (ash (ash u8-1  8)

(encapsulate 
 nil

 (defun create-srli-subtable (idx-lst i)
  (b* (((unless (alistp idx-lst))     nil)
       ((if (atom idx-lst))           nil)
       ((cons idx rst)            idx-lst)
       ((unless (consp idx))          nil)
       ((cons x y)                    idx))
      (cons (cons idx (ash (ash x i) (- y)))
            (create-srli-subtable rst i))))
 
 (defthm alistp-of-create-srli-subtable
  (alistp (create-srli-subtable idx-lst i)))
 
 (defthm member-idx-lst-assoc-create-srli-subtable
  (implies (and (alistp idx-lst) (member idx idx-lst))
           (assoc idx (create-srli-subtable idx-lst i))))
 
 (defthm assoc-member-srli-subtable
  (implies (assoc (cons i j) (create-srli-subtable idx-lst k))
           (member (cons i j) idx-lst)))
 
 (defthm assoc-srli-subtable
  (implies (assoc (cons i j) (create-srli-subtable idx-lst k))
           (equal (assoc (cons i j) (create-srli-subtable idx-lst k))
                  (cons (cons i j) (ash (ash i k) (- j))))))
 
 (defthm srli-subtable-correctness
  (implies (and (natp x-hi)
                (natp y-hi)
                (natp i)
                (natp j)
                (<= i x-hi)
                (<= j y-hi) )
           (b* ((indices  (create-x-indices x-hi y-hi))
                (subtable (create-srli-subtable indices k)))
               (equal (assoc-equal (cons i j) subtable)
                      (cons (cons i j) (ash (ash i k) (- j)))))))
 (defthm lookup-srli-subtable-correctness
  (implies (and (natp x-hi) 
                (natp y-hi)
                (natp i) 
                (natp j) 
                (<= i x-hi)
                (<= j y-hi))
           (b* ((indices  (create-x-indices x-hi y-hi))
                (subtable (create-srli-subtable  indices k)))
               (equal (lookup i j subtable)
                      (ash (ash i k) (- j)))))
  :hints (("Goal" :in-theory (enable lookup))))
 
 (local (in-theory (disable ash)))
 (local (include-book "ihs/logops-lemmas" :dir :system))
 (local (defthm lemma-1 (implies (integerp i) (equal (ash i 0) i)) :hints (("Goal" :use ((:instance ash* (count 0)))))))

 (defthm lookup-srl-0-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2  8))
                (<= j (expt 2  5)))
           (b* ((indices  (create-x-indices (expt 2 8) (expt 2 5)))
                (subtable (create-srli-subtable indices 0)))
               (equal (lookup i j subtable)
                      (ash i (- j)))))
  :hints (("Goal" :in-theory (disable (:e create-srli-subtable) (:e create-x-indices))
	          :use ((:instance lookup-srli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 5)))))))

 (defthm lookup-srl-8-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2  8))
                (<= j (expt 2  5)))
           (b* ((indices  (create-x-indices (expt 2  8) (expt 2 5)))
                (subtable (create-srli-subtable indices 8)))
               (equal (lookup i j subtable)
                      (ash (ash i 8) (- j)))))
  :hints (("Goal" :in-theory (disable (:e create-srli-subtable) (:e create-x-indices))
	          :use ((:instance lookup-srli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 5)))))))

 (defthm lookup-srl-16-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2  5)))
           (b* ((indices  (create-x-indices (expt 2 8) (expt 2 5)))
                (subtable (create-srli-subtable indices 16)))
               (equal (lookup i j subtable)
                      (ash (ash i 16) (- j)))))
  :hints (("Goal" :in-theory (disable (:e create-srli-subtable) (:e create-x-indices))
	          :use ((:instance lookup-srli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 5)))))))

 (defthm lookup-srl-24-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2  5)))
           (b* ((indices  (create-x-indices (expt 2 8) (expt 2 5)))
                (subtable (create-srli-subtable indices 24)))
               (equal (lookup i j subtable)
                      (ash (ash i 24) (- j)))))
  :hints (("Goal" :in-theory (disable (:e create-srli-subtable) (:e create-x-indices))
	          :use ((:instance lookup-srli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 5))))))))
                 
(include-book "centaur/gl/gl" :dir :system)

(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;
;;	     ;;
;;    SRL    ;;
;;	     ;;
;;;;;;;;;;;;;;;

(define SRLi-helper ((x natp) (y natp) (k natp))
 (if (zp k)
     (* (eqw k y) (ash x (- y)))
     (+ (* (eqw k y) (ash x (- y)))
        (srli-helper x y (1- k))))
 ///

 (local (in-theory (enable eqw-equal-equiv)))
 
 (local (defthm srli-helper-subterm
  (implies (and (natp y) (natp k) (< k y))
 	   (equal (* (eqw k y) (ash x (- y))) 0))))

 (local (defthm srli-helper-when-k-<-y
  (implies (and (natp y) (natp k) (< k y))
	   (equal (srli-helper x y k) 0))))

 (local (defthm srli-helper-when-k-=-y
  (implies (and (natp y) (natp k) (= k y))
	   (equal (srli-helper x y k) (ash x (- y))))))

 (local (defthm srli-helper-when-y-<-k
  (implies (and (natp y) (natp k) (< y k))
	   (equal (srli-helper x y k) (ash x (- y))))))

 (defthm srli-helper-ash
  (implies (and (natp y) (natp k))
	   (equal (srli-helper x y k)
		  (if (< k y) 
                      0
		      (ash x (- y)))))
  :hints (("Goal" :cases ((= k y) (< y k) (< k y))))))


