(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

;; MATERIALIZE SUBTABLES FOR "Sign-extend"

(include-book "centaur/gl/gl" :dir :system)
(local (include-book "ihs/basic-definitions" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "centaur/bitops/part-select" :dir :system))


(include-book "eq")
(include-book "subtable")


;(local (include-book "arithmetic/top" :dir :system))
;(local (include-book "ihs/logops-lemmas" :dir :system))




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

;(en
;(defthm masked-ones-slow-and-fast
; (implies (and (natp w) (natp k) (< k w))
;	  (equal (masked-ones-slow k w) (masked-ones k w)))
; :hints (("Subgoal *1/4" :expand (masked-ones k w))))
;:i-am-here

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

(define sra-sign-8 ((x (unsigned-byte-p 8 x)) (y (unsigned-byte-p 5 y)))
  (* (logbit 7 x) (masked-ones y 32)))

(gl::def-gl-thm sra-sign-32-chunk-correctness
  :hyp (and ;(unsigned-byte-p  5 y) 
            (unsigned-byte-p 32 x)) 
  :concl (equal (logbit 7 (part-select x :low 24 :width 8)) 
		(logbit 31 x))
  :g-bindings (gl::auto-bindings (:nat x 32)))

(defthm sra-sign-8-sra-sign-32-equiv
 (implies (unsigned-byte-p 32 x)
	  (equal (sra-sign-8 (part-select x :low 24 :width 8) y) 
		 (sra-sign-32 x y)))
 :hints (("Goal" :in-theory (enable sra-sign-8 sra-sign-32))))

;(include-book "centaur/fgl/top" :dir :system)
;(value-triple (acl2::tshell-ensure))

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


;:i-am-here
;
;(gl::def-gl-param-thm masked-one-fast-and-slow
; :hyp (unsigned-byte-p 5 y)
; :concl (equal (masked-ones y 32)
;	       (masked-ones-fast y 32))
; :param-bindings
; `((((low  0) (high  8)) ,(gl::auto-bindings (:nat y 5)))
;   (((low  8) (high 12)) ,(gl::auto-bindings (:nat y 5)))
;   (((low 12) (high 32)) ,(gl::auto-bindings (:nat y 5)))
;   )
; :param-hyp (and (<= low y) (< y high))
; :cov-bindings (gl::auto-bindings (:nat y 5)))
;:i-am-here


;(fgl::def-fgl-thm logbitp-<-equiv-1
; :hyp (and (unsigned-byte-p 24 x)
;	   (logbitp 23 x))
; :concl (and (<= (expt 2 23) x)
;	     (<  x (expt 2 24))))


;(fgl::def-fgl-thm logbitp-<-equiv-2
; :hyp (and (unsigned-byte-p 25 x)
;	   (<= (expt 2 24) x)   
;	   (<  x (expt 2 25)))
; :concl (logbitp 24 x))

;(gl::def-gl-param-thm masked-ones-correctness
;  :hyp (and (unsigned-byte-p 5 y) 
;	    (unsigned-byte-p 32 x))
;  :concl (equal (logextu 32 (- 32 y) (ash x (- y)))
;		(+ (* (logbit 31 x) (masked-ones y 32))
;		   (ash x (- y))))
; :param-bindings
; `((((low  0) (high 32)) ,(gl::auto-bindings (:nat y 5) (:nat x 32))))
;   ;(((low 16) (high 32)) ,(gl::auto-bindings (:nat y 5) (:nat x 32))))
; :param-hyp (and (<= low y) (< y high))
; :cov-bindings (gl::auto-bindings (:nat y 5) (:nat x 32)))

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

(gl::def-gl-thm sra-sign-8-correctness
  :hyp (and (unsigned-byte-p 5 y) 
	    (unsigned-byte-p 32 x))
  :concl (equal (logextu 32 (- 32 y) (ash x (- y)))
		(+ (sra-sign-8 (part-select x :low 24 :width 8) y)
		   (ash x (- y))))
  :g-bindings (gl::auto-bindings (:nat y 5) (:nat x 32)))

(defthm sra-sign-8-correctness
  (implies (and (unsigned-byte-p 5 y) (unsigned-byte-p 32 x))
 	   (equal (logextu 32 (- 32 y) (ash x (- y)))
		  (+ (sra-sign-8 (part-select x :low 24 :width 8) y)
		     (ash x (- y))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;					;;
;;    MATERIALIZE SRA-SIGN SUBTABLES    ;;
;;					;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun materialize-sra-sign-subtable-32 (idx-lst)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons x y)                    idx))
     (cons (cons idx (sra-sign-8 x y))
           (materialize-sra-sign-subtable-32 rst))))

(defthm alistp-of-materialize-sra-sign-subtable-32
 (alistp (materialize-sra-sign-subtable-32 idx-lst)))

(defthm member-idx-lst-assoc-materialize-sra-sign-subtable-32
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-sra-sign-subtable-32 idx-lst))))

(defthm assoc-member-materialize-sra-sign-subtable-32
 (implies (assoc (cons x y) (materialize-sra-sign-subtable-32 idx-lst))
          (member (cons x y) idx-lst)))

(defthm assoc-materialize-sra-sign-subtable-32
 (implies (assoc (cons i j) (materialize-sra-sign-subtable-32 idx-lst))
          (equal (assoc (cons i j) (materialize-sra-sign-subtable-32 idx-lst))
                 (cons (cons i j) (sra-sign-8 i j)))))

(defthm materialize-sra-sign-subtable-32-correctness
 (implies (and (natp x-hi) 
   	       (natp y-hi) 
               (natp i) 
               (natp j) 
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-sra-sign-subtable-32 indices)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j)
                           (sra-sign-8 i j))))))

(defthm lookup-materialize-sra-sign-subtable-32-correctness
 (implies (and (natp x-hi) 
   	       (natp y-hi) 
               (natp i) 
               (natp j) 
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-sra-sign-subtable-32 indices)))
              (equal (tuple-lookup i j subtable)
                     (sra-sign-8 i j))))
 :hints (("Goal" :in-theory (e/d (tuple-lookup) ()))))










