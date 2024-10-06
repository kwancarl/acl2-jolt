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
;;    EQ    ;;
;;	    ;;
;;;;;;;;;;;;;;

;; Equality of bit
;; (x_0*y_0 + (1-x_0)*(1-y_0)) == 1
(define b-eqw ((x0 bitp) (y0 bitp))
  (b-xor (b-and x0 y0)
	 (b-and (b-xor 1 x0)
		(b-xor 1 y0)))
  ///
  (defthm b-eqw-equal-equiv
    (implies (and (bitp x0) (bitp y0))
             (equal (b-eqw x0 y0)
               	    (if (equal x0 y0) 1 0)))
    :hints (("Goal" :cases ((equal x0 0)))))

 (defthmd symmetry-of-b-ewq
   (equal (b-eqw x y) (b-eqw y x)))

 (defthmd transitivity-of-b-ewq
   (implies (and (b-eqw x y) (b-eqw y w))
            (b-eqw x w))))

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

;; Equality of a chunk of size w/c
;; (x_0*y_0 + (1-x_0)*(1-y_0)) * recurse
(define eqw ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (+ (integer-length x) (integer-length y))
  :returns (eq? bitp)
  (b* (((unless (and (natp x) (natp y))) 0)
       ((if (and (bitp x) (bitp y))) (b-eqw x y))
       ((if (xor (bitp x) (bitp y))) 0)
       (x0  	(loghead 1 x))
       (y0  	(loghead 1 y))
       (eq0 	(b-eqw x0 y0))
       (x-rest  (ash x -1))
       (y-rest  (ash y -1)))
      (b-and eq0 (eqw x-rest y-rest)))
  ///

  (local (defthm lemma-1 
    (implies (natp x)
	     (equal x (logapp 1 (loghead 1 x) (logtail 1 x))))
    :rule-classes nil))

  (defthm equal-logapp-loghead-logtail-1
    (implies (and (equal (logtail 1 x) (logtail 1 y))
		  (equal (loghead 1 x) (loghead 1 y))
		  (natp x) 
 		  (natp y))
 	     (equal x y))
    :hints (("Goal" :use ((:instance lemma-1)
			  (:instance lemma-1 (x y)))))
    :rule-classes nil)


  (defthmd eqw-equal-equiv
    (implies (and (natp x) (natp y))
	     (equal (eqw x y)
	            (if (equal x y) 1 0)))
    :hints (("Subgoal *1/3" :use ((:instance equal-logapp-loghead-logtail-1)))))) ;; end define

(gl::def-gl-thm eqw-equal-equiv-gl
  :hyp   (and (unsigned-byte-p 128 x)
              (unsigned-byte-p 128 y))
  :concl (equal (eqw x y)
      	  (if (equal x y) 1 0))
  :g-bindings (gl::auto-bindings (:mix (:nat x 128) (:nat y 128))))

(local
  (defthm natp-lemma-1
    (implies (and (posp a) (posp c))
	     (< (nfix (- a c))
		a))))

(local
  (defthm natp-lemma-2
    (implies (and (natp a) (natp b) (natp c) (natp d) (< a b) (< c d))
	     (< (+ a c) (+ b d)))))


(local
  (defthm natp-lemma-3
    (implies (and (natp a) (natp b) (posp c) (not (zerop a)) (not (zerop b)))
	     (< (+ (nfix (- a c)) (nfix (- b c)))
		(+ a b)))
    :hints (("Goal" :use ((:instance natp-lemma-1)
			  (:instance natp-lemma-1 (a b)))))))


(define eqwc ((x :type unsigned-byte)
	     (y :type unsigned-byte)
	     (wc natp))
  :measure (+ (integer-length x) (integer-length y))
  :hints (("Goal" :use ((:instance natp-lemma-3
				   (a (integer-length x))
				   (b (integer-length y))
				   (c wc)))))
  (b* (((unless (and (natp x) (natp y))) 0)
       ((unless (posp wc)) 0)
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 1)
       ((if (xor (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (car-chunk-x  (loghead wc x))
       (car-chunk-y  (loghead wc y))
       (car-chunk-eq (eqw car-chunk-x car-chunk-y))
       (cdr-chunk-x  (logtail wc x))
       (cdr-chunk-y  (logtail wc y)))
      (b-and car-chunk-eq 
	     (eqwc cdr-chunk-x cdr-chunk-y wc)))
  ///

  (local (defthm lemma-1 
    (implies (and (natp x) (natp k))
	     (equal x (logapp k (loghead k x) (logtail k x))))
    :rule-classes nil))

  (defthm equal-logapp-loghead-logtail-k
      (implies (and (equal (logtail k x) (logtail k y))
  		    (equal (loghead k x) (loghead k y))
  		    (natp x) 
   		    (natp y)
   	 	    (natp k))
   	     (equal x y))
      :hints (("Goal" :use ((:instance lemma-1)
  			  (:instance lemma-1 (x y)))))
      :rule-classes nil)

  (local
    (defthm integer-length-0-implies-0
      (implies (and (natp x) (zerop (integer-length x)))
	       (zerop x))
      :hints (("Goal" :in-theory (enable integer-length)))
      :rule-classes :type-prescription))

  (local (in-theory (enable eqw-equal-equiv)))
  (defthm eqwc-equal-equiv
    (implies (and (natp x)
		  (natp y)
		  (posp wc))
	     (equal (eqwc x y wc)
		    (if (equal x y) 1 0)))
    :hints (("Subgoal *1/1" :use ((:instance integer-length-0-implies-0)
				  (:instance integer-length-0-implies-0 (x y))))
            ("Subgoal *1/3" :use ((:instance equal-logapp-loghead-logtail-k
					     (k wc)))))))

;;
;(include-book "arithmetic/top" :dir :system)
(defthm foo 
 (implies (and (natp x) (not (equal x 0)) (not (equal x 1)))
	  (< (integer-length (logcdr x))
	     (integer-length x)))
 :hints (("Goal" :in-theory (enable integer-length logcdr))))
;
;(def-gl-thm bar
; :hyp (and (bitp x) (bitp y))
; :concl (equal (b-xor (b-and x y) (b-and (b-xor x 1) (b-xor y 1)))
;	       (if (equal x y) 1 0))
; :g-bindings (gl::auto-bindings (:nat x 1) (:nat y 1)))
;
;(def-gl-thm bar-2
; :hyp (and (bitp x) (bitp y))
; :concl (equal (equal (b-xor (b-and x y) (b-and (b-xor x 1) (b-xor y 1))) 1)
;	       (equal x y))
; :g-bindings (gl::auto-bindings (:nat x 1) (:nat y 1)))

;; Equality of two bit, computes
;; x * y + (1 - x) * (1 - y)
(define b-eq-w ((x bitp) (y bitp))
  (b-xor (b-and x y)
	 (b-and (b-xor 1 x)
		(b-xor 1 y)))
  ///
  ;; Theorem for the correctness of b-eq-w:
  ;; x * y + (1 - x) * (1 - y) == if (x = y) then 1 else 0
  (defthm b-eq-w-equal-equiv
    (implies (and (bitp x) (bitp y))
             (equal (b-eq-w x y)
               	    (if (equal x y) 1 0)))
    :hints (("Goal" :cases ((equal x 0))))))

;; Equality of two bitvectors, computes
;; Prod (xi * yi + (1 - xi) * (1 - yi)) for each bit of x, y
(define eq-w ((x :type unsigned-byte) (y :type unsigned-byte))
  (b* (;; Edge cases
       ((unless (and (natp x) (natp y)))           0)
       ((if (xor (bitp x) (bitp y)))               0)
       ;; Base case
       ((if (and (bitp x) (bitp y)))    (b-eq-w x y))
       ;; Bindings for x and y
       (x-0  	(logcar x))		;; LSB of x
       (y-0  	(logcar y))		;; LSB of y
       (x-rest  (logcdr x))		;; Rest of x
       (y-rest  (logcdr y)))		;; Rest of y
      ;; Recursive case
      (b-and (b-eq-w x-0 y-0)
	     (eq-w x-rest y-rest)))
  ///
 ;; eq-w correctness theorem for 32-bit integers
 (defthm eq-w-equal-equiv-32
  (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
	   (equal (eq-w x y) (if (equal x y) 1 0)))))

 ;; eq-w correctness theorem for arbitrary bitwidths
 (defthmd eq-w-equal-equiv
  (implies (and (natp x) (natp y))
 	   (equal (eq-w x y) (if (equal x y) 1 0)))
  :hints (("Goal" :in-theory (enable eq-w))))



;;
;;
;;    MATERIALIZE EQ SUBTABLE
;;
;;

;; Given an association list of (x y) operands, materialize an
;; association list where each element is a key-value pair
;;   key:    (x y)
;;   value:  (if (= x y) 1 0)
(defun materialize-eq-subtable (idx-lst)
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
     ;; and append it to the rest of the eq subtable
     (cons (cons hd (if (= x y) 1 0))
           (materialize-eq-subtable tl))))

(defthm alistp-of-materialize-eq-subtable
 (alistp (materialize-eq-subtable idx-lst)))

(defthm member-idx-lst-assoc-materialize-eq-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-eq-subtable idx-lst))))

(defthm assoc-member-eq-subtable
 (implies (assoc (cons i j) (materialize-eq-subtable idx-lst))
          (member (cons i j) idx-lst)))

(defthm assoc-eq-subtable
 (implies (assoc (cons i j) (materialize-eq-subtable idx-lst))
          (equal (assoc (cons i j) (materialize-eq-subtable idx-lst))
                 (cons (cons i j) (if (= i j) 1 0)))))

(defthm eq-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi) )
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-eq-subtable indices)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j) (if (= i j) 1 0))))))

;; Lookup values within the bounds of the subtable are
;; equivalent to "equal"
(defthm lookup-eq-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-eq-subtable indices)))
              (equal (tuple-lookup i j subtable)
                     (if (= i j) 1 0))))
 :hints (("Goal" :in-theory (enable tuple-lookup))))

