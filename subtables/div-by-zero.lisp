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


