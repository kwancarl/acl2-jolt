(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;(local (include-book "centaur/bitops/fast-logext" :dir :system))
;(local (include-book "arithmetic/top" :dir :system))

(include-book "eq")
(include-book "subtable")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;		         	;;
;;    Set Less Than Unsigned    ;;
;;			        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(define ltu-i ((x :type unsigned-byte)
;	       (y :type unsigned-byte)
;               (i natp))
;  :returns (lti bitp)
;  (b-and (b-ltu (logbit i x) (logbit i y))
;	 (eqw (logtail i x) (logtail i y))))
;
;(define ltu-0 ((x :type unsigned-byte) (y :type unsigned-byte))
;  :enabled t
;  (b-and (b-ltu (logbit 1 x) (logbit 1 y))
;	 (eqw (logtail 1 x) (logtail 1 y))))

(local
  (defthm loghead-logcar-equiv
   (implies (natp x)
	    (equal (logcar x) (loghead 1 x)))
   :hints (("Goal" :in-theory (enable loghead logcar)))))

(local
  (defthm logcdr-logtail-equiv
   (implies (natp x)
	    (equal (logcdr x) (logtail 1 x)))
   :hints (("Goal" :in-theory (enable logcdr logtail)))))


(define b-ltu-w ((x0 bitp) (y0 bitp))
  :returns (lt bitp)
  (b-and (b-xor 1 x0) y0)
  ///
  (defthm b-ltu-w-<-equiv
    (implies (and (bitp x) (bitp y))
	     (equal (b-ltu-w x y)
		    (if (< x y) 1 0)))))





;(local
;  (defthm integer-length-lemma
;   (implies (equal x 0)
;	    (equal (integer-length x) 0))
;   :hints (("Goal" :in-theory (enable bitp integer-length)))))


;; Compute the MLE for LTU
(define ltu-w ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (max (integer-length x) (integer-length y))
  (b* (;; Edge case
       ((unless (and (natp x) (natp y)))      0)
       ;; Base case
       ((if (and (zerop (integer-length x)) 
		 (zerop (integer-length y)))) 0)
       ;; Bindings for x and y
       (x-0    (logcar x))
       (y-0    (logcar y))
       (x-rest (logcdr x))
       (y-rest (logcdr y))
       ;; Current summand
       (ltu-0  (b-and (b-and (b-xor 1 x-0) y-0)
	 	      (eq-w x-rest y-rest))))
      ;; Recursive case
      (b-xor ltu-0 (ltu-w x-rest y-rest))))

;; Theorem which states LTU is equivalent to < for 32-bit case
(gl::def-gl-thm ltu-w-<-equiv-gl-32
  :hyp   (and (unsigned-byte-p 32 x)
              (unsigned-byte-p 32 y))
  :concl (equal (ltu-w x y) (if (< x y) 1 0))
  :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))



(define ltuwc ((x :type unsigned-byte) (y :type unsigned-byte) (wc posp))
  :returns (ltu? bitp) ; :hyp :guard)
  :measure (max (integer-length x) (integer-length y))
  (mbe :logic
       (b* (((unless (and (natp x) (natp y))) 0)
            ((unless (posp wc)) 0)
            ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
            (car-chunk-x    (loghead wc x))
            (car-chunk-y    (loghead wc y))
            (cdr-chunk-x    (logtail wc x))
            (cdr-chunk-y    (logtail wc y))
            (cdr-chunk-eq   (eqw cdr-chunk-x cdr-chunk-y))
            (car-chunk-ltuw (ltu-w car-chunk-x car-chunk-y)))
           (b-xor (b-and car-chunk-ltuw cdr-chunk-eq)
     	     (ltuwc cdr-chunk-x cdr-chunk-y wc)))
       :exec
       (b* (((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
            (car-chunk-x    (loghead wc x))
            (car-chunk-y    (loghead wc y))
            (cdr-chunk-x    (logtail wc x))
            (cdr-chunk-y    (logtail wc y))
            (cdr-chunk-eq   (eqw cdr-chunk-x cdr-chunk-y))
            (car-chunk-ltuw (ltu-w car-chunk-x car-chunk-y)))
           (b-xor (b-and car-chunk-ltuw cdr-chunk-eq)
     	     (ltuwc cdr-chunk-x cdr-chunk-y wc)))))

(def-gl-thm ltuwc-<-equiv-gl
  :hyp (and (unsigned-byte-p 32 x)
  	    (unsigned-byte-p 32 y))
  :concl (equal (ltuwc x y 8)
		(if (< x y) 1 0))
  :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))



;;;;;
;;
;;   MATERIALIZE LTU SUBTABLES    ;;
;;
;;

;; Given an association list of (x y) operands, materialize an
;; association list where each element is a key-value pair
;;   key:    (x y)
;;   value:  (if (< x y) 1 0)
(defun materialize-ltu-subtable (idx-lst)
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
     ;;   value:  (if (= x y) 1 0)
     ;; and append it to the rest of the ltu subtable
     (cons (cons hd (if (< x y) 1 0))
           (materialize-ltu-subtable tl))))


(defthm alistp-of-materialize-ltu-subtable
 (alistp (materialize-ltu-subtable idx-lst)))

(defthm member-idx-lst-assoc-materialize-ltu-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-ltu-subtable idx-lst))))

(defthm assoc-member-ltu-subtable
 (implies (assoc (cons i j) (materialize-ltu-subtable idx-lst))
          (member (cons i j) idx-lst)))

(defthm assoc-ltu-subtable
 (implies (assoc (cons i j) (materialize-ltu-subtable idx-lst))
          (equal (assoc (cons i j) (materialize-ltu-subtable idx-lst))
                 (cons (cons i j) (if (< i j) 1 0)))))

(defthm ltu-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi) )
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-ltu-subtable indices)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j) (if (< i j) 1 0))))))

;; Lookup values within the bounds of the subtable are
;; equivalent to "<"
(defthm lookup-ltu-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi) )
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-ltu-subtable indices)))
              (equal (tuple-lookup i j subtable)
                     (if (< i j) 1 0))))
 :hints (("Goal" :in-theory (enable tuple-lookup))))


