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

(define b-ltu ((x0 bitp) (y0 bitp))
  :returns (lt bitp)
  :enabled t
  (b-and (b-xor 1 x0) y0)
  ///
  (defthm b-ltu-<-equiv
    (implies (and (bitp x) (bitp y))
	     (equal (b-ltu x y)
		    (if (< x y) 1 0)))))

(define ltu-i ((x :type unsigned-byte)
	       (y :type unsigned-byte)
               (i natp))
  :returns (lti bitp)
  (b-and (b-ltu (logbit i x) (logbit i y))
	 (eqw (logtail i x) (logtail i y))))

(define ltu-0 ((x :type unsigned-byte) (y :type unsigned-byte))
  :enabled t
  (b-and (b-ltu (logbit 1 x) (logbit 1 y))
	 (eqw (logtail 1 x) (logtail 1 y))))

(define ltuw ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (max (integer-length x) (integer-length y))
  (b* (((unless (and (natp x) (natp y))) 0)
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (xcar (loghead 1 x))
       (ycar (loghead 1 y))
       (xcdr (logtail 1 x))
       (ycdr (logtail 1 y))
       (ltu0 (b-and (b-and (b-xor 1 xcar) ycar)
		    (eqw xcdr ycdr))))
      (b-xor ltu0 (ltuw xcdr ycdr))))

(gl::def-gl-thm ltu-<-equiv-gl
  :hyp   (and (unsigned-byte-p 32 x)
              (unsigned-byte-p 32 y))
  :concl (equal (ltuw x y)
      	  	(if (< x y) 1 0))
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
            (car-chunk-ltuw (ltuw car-chunk-x car-chunk-y)))
           (b-xor (b-and car-chunk-ltuw cdr-chunk-eq)
     	     (ltuwc cdr-chunk-x cdr-chunk-y wc)))
       :exec
       (b* (((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
            (car-chunk-x    (loghead wc x))
            (car-chunk-y    (loghead wc y))
            (cdr-chunk-x    (logtail wc x))
            (cdr-chunk-y    (logtail wc y))
            (cdr-chunk-eq   (eqw cdr-chunk-x cdr-chunk-y))
            (car-chunk-ltuw (ltuw car-chunk-x car-chunk-y)))
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

(defun materialize-ltu-subtable (idx-lst)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons x y)                    idx))
     (cons (cons idx (if (< x y) 1 0))
           (materialize-ltu-subtable rst))))

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


;(verify-guards materialize-ltu-subtable)
;;
;;
;;
;;
;;
