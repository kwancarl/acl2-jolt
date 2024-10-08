(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "eq")

;; The following two encapsulates prove the table decomposition of SLL
;; lemmas about ash
(encapsulate
 nil
 ;; show (ash (+ x y) n) = (+ (ash x n) (ash y n))
 (local (include-book "arithmetic-5/top" :dir :system))
 (local (defthm mod-x-1
  (implies (integerp x) (equal (mod x 1) 0))))
 (defthm +-of-left-ash
  (implies (and (integerp x) (integerp y) (natp n))
	   (equal (ash (+ x y) n) (+ (ash x n) (ash y n))))
  :hints (("Goal" :in-theory (enable ash)))))
;; end encapsulate

(encapsulate
 nil
 (define sum-list ((lst nat-listp))
  :returns (sum integerp)
  (if (or (atom lst) (not (nat-listp lst)))
      0
      (+ (car lst) (sum-list (cdr lst))))
  ///
 (define sum-list-ash ((lst nat-listp) (n natp))
  :returns (sum integerp)
  (if (or (atom lst) (not (nat-listp lst)))
      0
      (+ (ash (car lst) n) (sum-list-ash (cdr lst) n)))
  ///
  (local (defthm ash-0-lemma (equal (ash 0 n) 0)))
  (local (in-theory (disable ash)))
  (defthm sum-list-ash-sum-list
    (implies (and (nat-listp chunks) (natp n))
	     (equal (sum-list-ash chunks n)
		    (ash (sum-list chunks) n)))
    :hints (("Subgoal *1/3" :use ((:instance +-of-left-ash (x (car chunks)) (y (sum-list (cdr chunks)))))))))))
;; end encapsulate

(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;	                    ;;
;;    SHIFT LEFT LOGICAL    ;;
;;	                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sllk ((x natp) (k natp) )
 (ash x k)
 ///
 (defthm sllk-of-zero
  (equal (sllk x 0) (ifix x))))

(define sll-helper ((x natp) (y natp) (k natp))
 (if (zp k)
     (* (eqw k y) (sllk x k))
     (+ (* (eqw k y) (sllk x k))
	(sll-helper x y (1- k))))
 ///
 (defthm eqw-when-not-equal
  (implies (and (natp k) (natp y) (not (equal k y)))
           (equal (eqw k y) 0))
  :hints (("Goal" :use ((:instance eqw-equal-equiv (x k))))))

 (defthm eqw-when-equal
  (implies (and (natp k) (natp y) (equal k y))
           (equal (eqw k y) 1))
  :hints (("Goal" :use ((:instance eqw-equal-equiv (x k))))))

 (local (defthm sll-helper-when-k-<-y
  (implies (and (natp k) (natp y) (< k y))
           (equal (sll-helper x y k) 0))))

 (local (defthm sll-helper-when-y-=-k
  (implies (and (natp k) (natp y) (= k y))
           (equal (sll-helper x y k) 
		  (sllk x y)))))

 (local (defthm sll-helper-subterm-when-y-<-k
  (implies (and (natp k) (natp y) (< k y))
           (equal (* (eqw k y) (sllk x k)) 0))))

 (local (defthm sll-helper-when-y-<-k
  (implies (and (natp k) (natp y) (< y k))
           (equal (sll-helper x y k) 
		  (sllk x y)))))

 (local (defthm sll-helper-sllk
  (implies (and (natp k) (natp y) (<= y k))
           (equal (sll-helper x y k) 
		  (sllk x y)))
  :hints (("Goal" :cases ((= y k) (< y k))))))

 (local (defthm sll-helper-ash
  (implies (and (natp k) (natp y) (<= y k))
           (equal (sll-helper x y k) 
		  (ash x y)))
  :hints (("Goal" :in-theory (enable sllk)))))

 (local (defthm expt-lemma
  (implies (posp y) (<= y (expt 2 y)))
  :hints (("Goal" :in-theory (enable expt)))))

 (define sll ((x natp) (y natp))
  :guard-hints (("Goal" :cases ((zp y) (posp y))))
  (mbe :logic (if (not (natp y))
                  (ifix x)
		  (sll-helper x y (expt 2 y)))
       :exec  (ash x y))
  ///
  (defthm sll-ash
   (implies (and (natp y))
            (equal (sll x y) (ash x y)))
   :hints (("Goal" :cases ((zp y) (posp y)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                ;;
;;    MATERIALIZE SLL SUBTABLE    ;;
;;                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 nil

 (defun materialize-slli-subtable (idx-lst i)
  (b* (((unless (alistp idx-lst))     nil)
       ((if (atom idx-lst))           nil)
       ((cons idx rst)            idx-lst)
       ((unless (consp idx))          nil)
       ((cons x y)                    idx))
      (cons (cons idx (ash x (+ y i)))
            (materialize-slli-subtable rst i))))

 (defthm alistp-of-materialize-slli-subtable
  (alistp (materialize-slli-subtable idx-lst i)))

 (defthm member-idx-lst-assoc-materialize-slli-subtable
  (implies (and (alistp idx-lst) (member idx idx-lst))
           (assoc idx (materialize-slli-subtable idx-lst i))))

 (defthm assoc-member-slli-subtable
  (implies (assoc (cons i j) (materialize-slli-subtable idx-lst k))
           (member (cons i j) idx-lst)))

 (defthm assoc-slli-subtable
  (implies (assoc (cons i j) (materialize-slli-subtable idx-lst k))
           (equal (assoc (cons i j) (materialize-slli-subtable idx-lst k))
                  (cons (cons i j) (ash i (+ j k))))))

 (defthm slli-subtable-correctness
  (implies (and (natp x-hi)
                (natp y-hi)
                (natp i)
                (natp j)
                (<= i x-hi)
                (<= j y-hi) )
           (b* ((indices  (create-tuple-indices x-hi y-hi))
                (subtable (materialize-slli-subtable indices k)))
               (equal (assoc-equal (cons i j) subtable)
                      (cons (cons i j) (ash i (+ j k)))))))

 (defthm lookup-slli-subtable-correctness
  (implies (and (natp x-hi)
                (natp y-hi)
                (natp i)
                (natp j)
                (<= i x-hi)
                (<= j y-hi))
           (b* ((indices  (create-tuple-indices x-hi y-hi))
                (subtable (materialize-slli-subtable  indices k)))
               (equal (tuple-lookup i j subtable)
                      (ash i (+ j k)))))
   :hints (("Goal" :in-theory (enable tuple-lookup))))
 
 (local (in-theory (disable ash)))
 (local (include-book "ihs/logops-lemmas" :dir :system))
 (local (defthm lemma-1 (implies (integerp i) (equal (ash i 0) i)) :hints (("Goal" :use ((:instance ash* (count 0)))))))

 (defthm lookup-sll-0-32-subtable-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2  8))
                (<= j (expt 2  5)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 5)))
                (subtable (materialize-slli-subtable indices 0)))
               (equal (tuple-lookup i j subtable)
                      (ash i j))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable) (:e create-tuple-indices))
	          :use ((:instance lookup-slli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 5)))))))

 (defthm lookup-sll-8-32-subtable-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2  8))
                (<= j (expt 2  5)))
           (b* ((indices  (create-tuple-indices (expt 2  8) (expt 2 5)))
                (subtable (materialize-slli-subtable indices 8)))
               (equal (tuple-lookup i j subtable)
                      (ash i (+ j 8)))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable) (:e create-tuple-indices))
	          :use ((:instance lookup-slli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 5)))))))

 (defthm lookup-sll-16-32-subtable-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2 8))
                (<= j (expt 2  5)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 5)))
                (subtable (materialize-slli-subtable indices 16)))
               (equal (tuple-lookup i j subtable)
                      (ash i (+ j 16)))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable) (:e create-tuple-indices))
	          :use ((:instance lookup-slli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 5)))))))

 (defthm lookup-sll-24-32-subtable-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2 8))
                (<= j (expt 2  5)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 5)))
                (subtable (materialize-slli-subtable indices 24)))
               (equal (tuple-lookup i j subtable)
                      (ash i (+ j 24)))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable) (:e create-tuple-indices))
	          :use ((:instance lookup-slli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 5))))))))

 (defthm lookup-sll-0-64-subtable-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2 8))
                (<= j (expt 2 6)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 6)))
                (subtable (materialize-slli-subtable indices 0)))
               (equal (tuple-lookup i j subtable)
                      (ash i j))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable) (:e create-tuple-indices))
	          :use ((:instance lookup-slli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 6)))))))

 (defthm lookup-sll-8-64-subtable-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2 8))
                (<= j (expt 2 6)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 6)))
                (subtable (materialize-slli-subtable indices 8)))
               (equal (tuple-lookup i j subtable)
                      (ash i (+ j 8)))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable) (:e create-tuple-indices))
	          :use ((:instance lookup-slli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 6)))))))

 (defthm lookup-sll-16-64-subtable-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2 8))
                (<= j (expt 2 6)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 6)))
                (subtable (materialize-slli-subtable indices 16)))
               (equal (tuple-lookup i j subtable)
                      (ash i (+ j 16)))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable) (:e create-tuple-indices))
	          :use ((:instance lookup-slli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 6)))))))

 (defthm lookup-sll-24-64-subtable-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2 8))
                (<= j (expt 2 6)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 6)))
                (subtable (materialize-slli-subtable indices 24)))
               (equal (tuple-lookup i j subtable)
                      (ash i (+ j 24)))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable) (:e create-tuple-indices))
	          :use ((:instance lookup-slli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 6)))))))

 (defthm lookup-sll-32-64-subtable-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2 8))
                (<= j (expt 2 6)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 6)))
                (subtable (materialize-slli-subtable indices 32)))
               (equal (tuple-lookup i j subtable)
                      (ash i (+ j 32)))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable) (:e create-tuple-indices))
	          :use ((:instance lookup-slli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 6)))))))


;; SLL subtable with trunctation

;; Semantics from the spec: (x << (y mod word-size)) mod (expt 2 (word-size - m * i))
(defun slli-rust (x y i word-size)
  (mod (ash x (mod y word-size))
       (expt 2 (- word-size i))))
          
(defun materialize-slli-subtable-prime (idx-lst i word-size)
  (b* (((unless (alistp idx-lst))     nil)
       ((if (atom idx-lst))           nil)
       ((cons idx rst)            idx-lst)
       ((unless (consp idx))          nil)
       ((cons x y)                    idx))
     (cons (cons idx (slli-rust x y i word-size))
	   (materialize-slli-subtable-prime rst i word-size))))

 (defthm alistp-of-materialize-slli-subtable-prime
  (alistp (materialize-slli-subtable-prime idx-lst i log-word-size)))

 (defthm member-idx-lst-assoc-materialize-slli-subtable-prime
  (implies (and (alistp idx-lst) (member idx idx-lst))
           (assoc idx (materialize-slli-subtable-prime idx-lst i word-size))))

 (defthm assoc-member-slli-subtable-prime
  (implies (assoc (cons i j) (materialize-slli-subtable-prime idx-lst k word-size))
           (member (cons i j) idx-lst)))

 (defthm assoc-slli-subtable-prime
  (implies (assoc (cons i j) (materialize-slli-subtable-prime idx-lst k word-size))
           (equal (assoc (cons i j) (materialize-slli-subtable-prime idx-lst k word-size))
                  (cons (cons i j) (slli-rust i j k word-size)))))

 (defthm slli-subtable-prime-correctness
  (implies (and (natp x-hi)
                (natp y-hi)
                (natp i)
                (natp j)
                (<= i x-hi)
                (<= j y-hi) )
           (b* ((indices  (create-tuple-indices x-hi y-hi))
                (subtable (materialize-slli-subtable-prime indices k word-size)))
               (equal (assoc-equal (cons i j) subtable)
                      (cons (cons i j) (slli-rust i j k word-size))))))

 (defthm lookup-slli-subtable-prime-correctness
  (implies (and (natp x-hi)
                (natp y-hi)
                (natp i)
                (natp j)
                (<= i x-hi)
                (<= j y-hi))
           (b* ((indices  (create-tuple-indices x-hi y-hi))
                (subtable (materialize-slli-subtable-prime  indices k word-size)))
               (equal (tuple-lookup i j subtable)
                      (slli-rust i j k word-size))))
   :hints (("Goal" :in-theory (enable tuple-lookup))))
 
 (local (in-theory (disable ash)))
 (local (include-book "ihs/logops-lemmas" :dir :system))
 (local (defthm lemma-1 (implies (integerp i) (equal (ash i 0) i)) :hints (("Goal" :use ((:instance ash* (count 0)))))))

 (defthm lookup-sll-0-32-subtable-prime-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2  8))
                (<= j (expt 2  8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-slli-subtable-prime indices 0 32)))
               (equal (tuple-lookup i j subtable)
                      (slli-rust i j 0 32))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable-prime) (:e create-tuple-indices)))))

 (defthm lookup-sll-8-32-subtable-prime-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2  8))
                (<= j (expt 2  8)))
           (b* ((indices  (create-tuple-indices (expt 2  8) (expt 2 8)))
                (subtable (materialize-slli-subtable-prime indices 8 32)))
               (equal (tuple-lookup i j subtable)
		      (slli-rust i j 8 32))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable-prime) (:e create-tuple-indices)))))

 (defthm lookup-sll-16-32-subtable-prime-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-slli-subtable-prime indices 16 32)))
               (equal (tuple-lookup i j subtable)
		      (slli-rust i j 16 32))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable-prime) (:e create-tuple-indices)))))

 (defthm lookup-sll-24-32-subtable-prime-correctness
  (implies (and (natp i)
                (natp j)
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-slli-subtable-prime indices 24 32)))
               (equal (tuple-lookup i j subtable)
                      (slli-rust i j 24 32))))
  :hints (("Goal" :in-theory (disable (:e materialize-slli-subtable-prime) (:e create-tuple-indices)))))
