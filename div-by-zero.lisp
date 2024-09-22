(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

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

(gl::def-gl-thm eqw-equal-equiv-gl
  :hyp   (and (unsigned-byte-p 32 x)
              (unsigned-byte-p 32 y))
  :concl (equal (div-by-zero-w x y 32)
	        (if (and (equal y (1- (expt 2 32)))
                         (equal x 0)) 
                            1 
                            0))
  :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

;(local
;  (defthm natp-lemma-1
;    (implies (and (posp a) (posp c))
;	     (< (nfix (- a c))
;		a))))
;
;(local
;  (defthm natp-lemma-2
;    (implies (and (natp a) (natp b) (natp c) (natp d) (< a b) (< c d))
;	     (< (+ a c) (+ b d)))))
;
;
;(local
;  (defthm natp-lemma-3
;    (implies (and (natp a) (natp b) (posp c) (not (zerop a)) (not (zerop b)))
;	     (< (+ (nfix (- a c)) (nfix (- b c)))
;		(+ a b)))
;    :hints (("Goal" :use ((:instance natp-lemma-1)
;			  (:instance natp-lemma-1 (a b)))))))
;
;
;(define eqwc ((x :type unsigned-byte)
;	     (y :type unsigned-byte)
;	     (wc natp))
;  :measure (+ (integer-length x) (integer-length y))
;  :hints (("Goal" :use ((:instance natp-lemma-3
;				   (a (integer-length x))
;				   (b (integer-length y))
;				   (c wc)))))
;  (b* (((unless (and (natp x) (natp y))) 0)
;       ((unless (posp wc)) 0)
;       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 1)
;       ((if (xor (zerop (integer-length x)) (zerop (integer-length y)))) 0)
;       (car-chunk-x  (loghead wc x))
;       (car-chunk-y  (loghead wc y))
;       (car-chunk-eq (eqw car-chunk-x car-chunk-y))
;       (cdr-chunk-x  (logtail wc x))
;       (cdr-chunk-y  (logtail wc y)))
;      (b-and car-chunk-eq 
;	     (eqwc cdr-chunk-x cdr-chunk-y wc)))
;  ///
;
;  (local (defthm lemma-1 
;    (implies (and (natp x) (natp k))
;	     (equal x (logapp k (loghead k x) (logtail k x))))
;    :rule-classes nil))
;
;  (defthm equal-logapp-loghead-logtail-k
;      (implies (and (equal (logtail k x) (logtail k y))
;  		    (equal (loghead k x) (loghead k y))
;  		    (natp x) 
;   		    (natp y)
;   	 	    (natp k))
;   	     (equal x y))
;      :hints (("Goal" :use ((:instance lemma-1)
;  			  (:instance lemma-1 (x y)))))
;      :rule-classes nil)
;
;  (local
;    (defthm integer-length-0-implies-0
;      (implies (and (natp x) (zerop (integer-length x)))
;	       (zerop x))
;      :hints (("Goal" :in-theory (enable integer-length)))
;      :rule-classes :type-prescription))
;
;  (local (in-theory (enable eqw-equal-equiv)))
;  (defthm eqwc-equal-equiv
;    (implies (and (natp x)
;		  (natp y)
;		  (posp wc))
;	     (equal (eqwc x y wc)
;		    (if (equal x y) 1 0)))
;    :hints (("Subgoal *1/1" :use ((:instance integer-length-0-implies-0)
;				  (:instance integer-length-0-implies-0 (x y))))
;            ("Subgoal *1/3" :use ((:instance equal-logapp-loghead-logtail-k
;					     (k wc)))))))
