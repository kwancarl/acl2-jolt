(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "eq")
(include-book "subtable")

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

(define srli-helper ((x natp) (y natp) (k natp))
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




;;
;;
;;   Materialize SRLi subtables with trucation
;;
;;

(defund srli-rust (x y i word-size)
 (ash (ash x i) (- (mod y word-size))))

(defun materialize-srli-subtable (idx-lst i word-size)
  (b* (((unless (alistp idx-lst))     nil)
       ((if (atom idx-lst))           nil)
       ((cons idx rst)            idx-lst)
       ((unless (consp idx))          nil)
       ((cons x y)                    idx))
     (cons (cons idx (srli-rust x y i word-size))
           (materialize-srli-subtable rst i word-size))))

 (defthm alistp-of-materialize-srli-subtable
  (alistp (materialize-srli-subtable idx-lst i word-size)))
 
 (defthm member-idx-lst-assoc-materialize-srli-subtable
  (implies (and (alistp idx-lst) (member idx idx-lst))
           (assoc idx (materialize-srli-subtable idx-lst i word-size))))
 
 (defthm assoc-member-srli-subtable
  (implies (assoc (cons i j) (materialize-srli-subtable idx-lst k word-size))
           (member (cons i j) idx-lst)))
 
 (defthm assoc-srli-subtable
  (implies (assoc (cons i j) (materialize-srli-subtable idx-lst k word-size))
           (equal (assoc (cons i j) (materialize-srli-subtable idx-lst k word-size))
                  (cons (cons i j) (srli-rust i j k word-size)))))
 
 (defthm srli-subtable-correctness
  (implies (and (natp x-hi)
                (natp y-hi)
                (natp i)
                (natp j)
                (<= i x-hi)
                (<= j y-hi) )
           (b* ((indices  (create-tuple-indices x-hi y-hi))
                (subtable (materialize-srli-subtable indices k word-size)))
               (equal (assoc-equal (cons i j) subtable)
                      (cons (cons i j) (srli-rust i j k word-size))))))

 (defthm lookup-srli-subtable-correctness
  (implies (and (natp x-hi) 
                (natp y-hi)
                (natp i) 
                (natp j) 
                (<= i x-hi)
                (<= j y-hi))
           (b* ((indices  (create-tuple-indices x-hi y-hi))
                (subtable (materialize-srli-subtable indices k word-size)))
               (equal (tuple-lookup i j subtable) (srli-rust i j k word-size))))
  :hints (("Goal" :in-theory (enable tuple-lookup))))

 (local (in-theory (disable ash)))
 (local (include-book "ihs/logops-lemmas" :dir :system))
 (local (defthm lemma-1 (implies (integerp i) (equal (ash i 0) i)) :hints (("Goal" :use ((:instance ash* (count 0)))))))

 (defthm lookup-srl-0-32-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 0 32)))
               (equal (tuple-lookup i j subtable)
                      (srli-rust i j 0 32))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-8-32-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2  8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 8 32)))
               (equal (tuple-lookup i j subtable) (srli-rust i j 8 32))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-16-32-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 16 32)))
               (equal (tuple-lookup i j subtable) (srli-rust i j 16 32))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-24-32-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 24 32)))
               (equal (tuple-lookup i j subtable) (srli-rust i j 24 32))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-0-64-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 0 64)))
               (equal (tuple-lookup i j subtable)
                      (srli-rust i j 0 64))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-8-64-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 8 64)))
               (equal (tuple-lookup i j subtable)
                      (srli-rust i j 8 64))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-16-64-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 16 64)))
               (equal (tuple-lookup i j subtable)
                      (srli-rust i j 16 64))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-24-64-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 24 64)))
               (equal (tuple-lookup i j subtable)
                      (srli-rust i j 24 64))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-32-64-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 32 64)))
               (equal (tuple-lookup i j subtable)
                      (srli-rust i j 32 64))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-40-64-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 40 64)))
               (equal (tuple-lookup i j subtable)
                      (srli-rust i j 40 64))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-48-64-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 48 64)))
               (equal (tuple-lookup i j subtable)
                      (srli-rust i j 48 64))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))

 (defthm lookup-srl-56-64-subtable-correctness
  (implies (and (natp i) 
                (natp j) 
                (<= i (expt 2 8))
                (<= j (expt 2 8)))
           (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
                (subtable (materialize-srli-subtable indices 56 64)))
               (equal (tuple-lookup i j subtable)
                      (srli-rust i j 56 64))))
  :hints (("Goal" :in-theory (disable (:e materialize-srli-subtable) (:e create-tuple-indices)))))