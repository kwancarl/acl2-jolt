(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

;; MATERIALIZE SUBTABLES FOR "Sign-extend"

(include-book "centaur/gl/gl" :dir :system)
(local (include-book "ihs/basic-definitions" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(include-book "centaur/bitops/part-select" :dir :system)

(include-book "eq")
(include-book "subtable")

;; SRA-sign intended function & MLE correctness

;; 1...1 0...0
;; w - k   k
;; w = 32
(define masked-ones-slow ((k natp) (w natp))
  :guard (< k w)
  :enabled t
  (mbe
    :logic (if (not (and (natp k) (natp w) (< k w)))
               0
               (if (zp k)
                   0
                   (+ (expt2 (- w k)) (masked-ones-slow (1- k) w))))
    :exec (if (zp k) 
	      0 
	      (+ (expt2 (- w k)) (masked-ones-slow (1- k) w)))))

(define masked-ones ((k natp) (w natp))
  :enabled t
  (mbe 
   :logic (if (not (natp w))
              0
              (if (zp w) 
		  0
		  (if (< k w)
      	              (logcons 0 (masked-ones k (1- w)))
      	              (logcons 1 (masked-ones k (1- w))))))
   :exec (if (zp w)
              0
              (if (< k w)
      	          (logcons 0 (masked-ones k (1- w)))
      	          (logcons 1 (masked-ones k (1- w)))))))

(defthm natp-of-expt2-when-nat
 (implies (natp w) (natp (expt2 w))))

(define masked-ones-fast ((k natp) (w natp))
  :guard-hints (("Goal" :use ((:instance natp-of-expt2-when-nat))))
  (mbe 
   :logic
    (if (not (and (natp k) (natp w)))
        0
        (ash (ash (1- (expt2 w)) (- k w)) (- w k)))
   :exec
    (ash (ash (1- (expt2 w)) (- k w)) (- w k))))


(local (in-theory (enable logcons)))

(define sra-sign-helper ((sign bitp) (y natp) (k natp) (w natp))
 (if (zp k)
     (* (eqw k y) sign (masked-ones k w))
     (+ (* (eqw k y) sign (masked-ones k w))
        (sra-sign-helper sign y (1- k) w)))
 ///

 (local (in-theory (enable eqw-equal-equiv)))

 (local (defthm sra-sign-helper-when-k-<-y
  (implies (and (natp y) (natp k) (< k y))
           (equal (sra-sign-helper sign y k w) 0))))

 (local (defthm sra-sign-helper-when-k-=-y
  (implies (and (natp y) (natp k) (= k y))
           (equal (sra-sign-helper sign y k w) 
		  (* sign (masked-ones y w))))))

 (local (defthm sra-sign-helper-when-y-<-k
  (implies (and (natp y) (natp k) (< y k))
           (equal (sra-sign-helper sign y k w)
		  (* sign (masked-ones y w))))))
 
 (defthm sra-sign-helper-correctness
  (implies (and (natp y) (natp k))
           (equal (sra-sign-helper sign y k w)
                  (if (< k y)
                      0
                      (* sign (masked-ones y w)))))))

(define sra-sign-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 5 y)))
  (* (logbit 31 x) (masked-ones y 32)))

(define sra-sign-8 ((x :type unsigned-byte) (y  :type unsigned-byte))
  (* (logbit 7 x) (masked-ones y 32)))

(gl::def-gl-thm sra-sign-32-chunk-correctness
  :hyp (and (unsigned-byte-p 32 x)) 
  :concl (equal (logbit 7 (part-select x :low 24 :width 8)) 
		(logbit 31 x))
  :g-bindings (gl::auto-bindings (:nat x 32)))

(defthm sra-sign-8-sra-sign-32-equiv
 (implies (unsigned-byte-p 32 x)
	  (equal (sra-sign-8 (part-select x :low 24 :width 8) y) 
		 (sra-sign-32 x y)))
 :hints (("Goal" :in-theory (enable sra-sign-8 sra-sign-32))))

(gl::def-gl-thm masked-one-easy-gl
 :hyp (unsigned-byte-p 5 y)
 :concl (equal (masked-ones y 32)
	       (masked-ones-fast y 32))
 :g-bindings (gl::auto-bindings (:nat y 5)))

(gl::def-gl-thm masked-ones-slow-and-fast
 :hyp (unsigned-byte-p 5 y)
 :concl (equal (masked-ones-slow y 32)
	       (masked-ones-fast y 32))
 :g-bindings (gl::auto-bindings (:nat y 5)))

(gl::def-gl-thm masked-ones-correctness
  :hyp (and (unsigned-byte-p 5 y) 
	    (unsigned-byte-p 32 x))
  :concl (equal (logextu 32 (- 32 y) (ash x (- y)))
		(+ (* (logbit 31 x) (masked-ones y 32))
		   (ash x (- y))))
  :g-bindings (gl::auto-bindings (:nat y 5) (:nat x 32)))

(gl::def-gl-thm sra-sign-32-correctness
  :hyp (and (unsigned-byte-p 5 y) 
	    (unsigned-byte-p 32 x))
  :concl (equal (logextu 32 (- 32 y) (ash x (- y)))
		(+ (sra-sign-32 x y)
		   (ash x (- y))))
  :g-bindings (gl::auto-bindings (:nat y 5) (:nat x 32)))
(in-theory (disable sra-sign-32-correctness))

(gl::def-gl-thm sra-sign-8-correctness-gl
  :hyp (and (unsigned-byte-p 8 y) 
	    (unsigned-byte-p 32 x))
  :concl (equal (ashu 32 x (- (mod y 32)))
		(+ (sra-sign-8 (part-select x :low 24 :width 8) (mod y 32))
		   (ash x (- (mod y 32)))))
  :g-bindings (gl::auto-bindings (:nat y 8) (:nat x 32)))

(defthmd sra-sign-8-correctness
  (implies (and (unsigned-byte-p 8 y) (unsigned-byte-p 32 x))
           (equal (ashu 32 x (- (mod y 32)))
		(+ (sra-sign-8 (part-select x :low 24 :width 8) (mod y 32))
		   (ash x (- (mod y 32))))))
  :hints (("Goal" :use ((:instance sra-sign-8-correctness-gl)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;					;;
;;    MATERIALIZE SRA-SIGN SUBTABLES    ;;
;;					;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 11...100...0 = (ash (1- (expt 2 k)) (- w k)),
;; where there are `k` ones and word size `w`

(defund sra-sign (x y word-size)
  (* (logbit 7 x) (ash (1- (expt 2 (logand (1- word-size) y))) 
                             (- word-size (logand (1- word-size) y)))))

(gl::def-gl-thm sra-sign-sra-sign-8-equiv
 :hyp (and (unsigned-byte-p 8 y) (unsigned-byte-p 32 x))
 :concl (equal (sra-sign x (mod y 32) 32)
	       (sra-sign-8 x (mod y 32)))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm sra-sign-correctness
  (implies (and (unsigned-byte-p 8 y) (unsigned-byte-p 32 x))
  	   (equal (ashu 32 x (- (mod y 32)))
	  	  (+ (sra-sign (part-select x :low 24 :width 8) (mod y 32) 32) (ash x (- (mod y 32))))))
  :hints (("Goal" :use ((:instance sra-sign-sra-sign-8-equiv)
			(:instance sra-sign-8-correctness)))))

;; This subtable assumes that we will instantiate it with `m = 8`, hence we take `logbit 7 x`
;; i.e. `idx-lst` is `(create-tuple-indices (1- (expt 2 8)) (1- (expt 2 8)))`
(defun materialize-sra-sign-subtable (idx-lst word-size)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons x y)                    idx))
     (cons (cons idx (sra-sign x y word-size))
           (materialize-sra-sign-subtable rst word-size))))


(defthm alistp-of-materialize-sra-sign-subtabl
 (alistp (materialize-sra-sign-subtable idx-lst word-size)))

(defthm member-idx-lst-assoc-materialize-sra-sign-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-sra-sign-subtable idx-lst word-size))))

(defthm assoc-member-materialize-sra-sign-subtable
 (implies (assoc (cons x y) (materialize-sra-sign-subtable idx-lst word-size))
          (member (cons x y) idx-lst)))

(defthm assoc-materialize-sra-sign-subtable
 (implies (assoc (cons i j) (materialize-sra-sign-subtable idx-lst word-size))
          (equal (assoc (cons i j) (materialize-sra-sign-subtable idx-lst word-size))
                 (cons (cons i j) (sra-sign i j word-size)))))

(defthm materialize-sra-sign-subtable-correctness
 (implies (and (natp x-hi) 
   	       (natp y-hi) 
               (natp i) 
               (natp j) 
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-sra-sign-subtable indices word-size)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j)
                           (sra-sign i j word-size))))))

(defthm lookup-materialize-sra-sign-subtable-correctness
 (implies (and (natp x-hi) 
   	       (natp y-hi) 
               (natp i) 
               (natp j) 
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-sra-sign-subtable indices word-size)))
              (equal (tuple-lookup i j subtable)
                     (sra-sign i j word-size))))
 :hints (("Goal" :in-theory (e/d (tuple-lookup) ()))))

(encapsulate
 nil
 (local (include-book "arithmetic/top" :dir :system))
 (defthm natp-of-expt-2-n
  (implies (natp n) (natp (expt 2 n)))))

(defthm lookup-sra-sign-logtail-24-x-lemma
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 8 y))
          (b* ((indices  (create-tuple-indices (expt 2 8) (expt 2 8)))
               (subtable (materialize-sra-sign-subtable indices 32)))
              (equal (tuple-lookup (logtail 24 x) (loghead 8 y) subtable)
                     (sra-sign (logtail 24 x) (loghead 8 y) 32))))
 :hints (("Goal" :in-theory (disable loghead-identity materialize-sra-sign-subtable (:e create-tuple-indices) (:e expt)))))


