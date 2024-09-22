(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)
;; idk why the following two books are necessary
(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "../srl")

;;;;;;;;;;;;;
;;
;; Chunking and append
;;
;;;;;;;;;;;;;
;(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "ihs/logops-lemmas" :dir :system)

;(local (in-theory (disable ash)))

(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(gl::def-gl-thm part-select-lemma-1
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (ash (part-select x :low 8 :width 8) 8)
	       (logand x #b1111111100000000))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm part-select-lemma-2
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (part-select x :low 0 :width 8)
	       (logand x #b11111111))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-param-thm lemma-3
 :hyp (and (unsigned-byte-p 12 x) (unsigned-byte-p 5 y))
 :concl (equal (+ (ash (logand x #x000000ff) y)
	          (ash (logand x #x0000ff00) y)
	          (ash (logand x #x00ff0000) y)
	          (ash (logand x #xff000000) y))
	       (ash (+ (logand x #x000000ff)
                       (logand x #x0000ff00)
                       (logand x #x00ff0000)
                       (logand x #xff000000))
		      y))
    :param-bindings
    `((((low  0) (high  4)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low  4) (high  8)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low  8) (high 12)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 12) (high 16)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 16) (high 20)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 20) (high 24)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 24) (high 28)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 28) (high 32)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 32) (high 33)) ,(gl::auto-bindings (:nat x 32) (:nat y 5))))
    :param-hyp (or (and (<= (expt 2 low) x) (< x (expt 2 high))) (= x 0))
    :cov-bindings (gl::auto-bindings (:nat x 32) (:nat y 5)))

;(gl::def-gl-thm part-select-lemma-3
; :hyp (and (unsigned-byte-p 5 y) (unsigned-byte-p 32 x))
; :concl (equal (ash (part-select x :low 8 :width 8) 8)
;	       (ash (logand x #b1111111100000000) (- y))
; :g-bindings (gl::auto-bindings (:nat x 32)))


;; SRL-semantics-32
(define chunk-and-shift-32 (x y)
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p  5 y)) 0)
       ;; chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       ;; shift chunks
       (u8-0 (ash      u8-0     (- y)))
       (u8-1 (ash (ash u8-1  8) (- y)))
       (u8-2 (ash (ash u8-2 16) (- y)))
       (u8-3 (ash (ash u8-3 24) (- y))))
       ;; add chunks
      (+ u8-3 u8-2 u8-1 u8-0)))

(defthm part-select-width-8
 (implies (natp x)
	  (and (unsigned-byte-p 8 (part-select x :low  0 :width 8))
	       (unsigned-byte-p 8 (part-select x :low  8 :width 8))
	       (unsigned-byte-p 8 (part-select x :low 16 :width 8))
	       (unsigned-byte-p 8 (part-select x :low 24 :width 8)))))

(defthm srl-0-subtable-part-select
 (implies (and (unsigned-byte-p 32 x)
	       (natp j)
	       (<= j (expt 2 5)))
          (b* ((indices  (create-x-indices (expt 2 8) (expt 2 5)))
               (subtable (create-srli-subtable indices 0))
               (i (part-select x :low 0 :width 8)))
              (equal (lookup i j subtable)
                     (ash i (- j)))))
 :hints (("Goal" :in-theory (disable create-srli-subtable
				     (:e create-x-indices)
				     (:e create-srli-subtable)))))

(defthm srl-8-subtable-part-select
 (implies (and (unsigned-byte-p 32 x)
	       (natp j)
	       (<= j (expt 2 5)))
          (b* ((indices  (create-x-indices (expt 2 8) (expt 2 5)))
               (subtable (create-srli-subtable indices 8))
               (i (part-select x :low 8 :width 8)))
              (equal (lookup i j subtable)
                     (ash (ash i 8) (- j)))))
 :hints (("Goal" :in-theory (disable create-srli-subtable
				     (:e create-x-indices)
				     (:e create-srli-subtable)))))

(defthm srl-16-subtable-part-select
 (implies (and (unsigned-byte-p 32 x)
	       (natp j)
	       (<= j (expt 2 5)))
          (b* ((indices  (create-x-indices (expt 2 8) (expt 2 5)))
               (subtable (create-srli-subtable indices 16))
               (i (part-select x :low 16 :width 8)))
              (equal (lookup i j subtable)
                     (ash (ash i 16) (- j)))))
 :hints (("Goal" :in-theory (disable create-srli-subtable
				     (:e create-x-indices)
				     (:e create-srli-subtable)))))

(gl::def-gl-thm silly-bounds-lemma-due-to-logtail-rewrite
 :hyp  (and (integerp x)
	       (<= 0 x)
	       (< x 4294967296))
 :concl (not (< 256 (logtail 24 x)))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(defthm srl-24-subtable-part-select
 (implies (and (unsigned-byte-p 32 x)
	       (natp j)
	       (<= j (expt 2 5)))
          (b* ((indices  (create-x-indices (expt 2 8) (expt 2 5)))
               (subtable (create-srli-subtable indices 24))
               (i (part-select x :low 24 :width 8)))
              (equal (lookup i j subtable)
                     (ash (ash i 24) (- j)))))
 :hints (("Goal" :in-theory (disable create-srli-subtable
				     (:e create-x-indices)
				     (:e create-srli-subtable))
	         :use ((:instance lookup-srl-24-subtable-correctness (i (logtail 24 x)))))))

;; SRL-32 (with lookups)
(define srl-chunk-lookup-combine-32 (x y)
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p  5 y)) 0)
       ;; setup subtables
       (indices (create-x-indices (expt 2 8) (expt 2 5)))
       (subtable-0 (create-srli-subtable indices  0))
       (subtable-1 (create-srli-subtable indices  8))
       (subtable-2 (create-srli-subtable indices 16))
       (subtable-3 (create-srli-subtable indices 24))
       ;; chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       ;; shift chunks
       (u8-0 (lookup u8-0 y subtable-0))
       (u8-1 (lookup u8-1 y subtable-1))
       (u8-2 (lookup u8-2 y subtable-2))
       (u8-3 (lookup u8-3 y subtable-3)))
       ;; add chunks
      (+ u8-3 u8-2 u8-1 u8-0)))

(defthm srl-equal-stuff
 (equal (srl-chunk-lookup-combine-32 x y)
        (chunk-and-shift-32 x y))
 :hints (("Goal" :in-theory (disable (:e create-x-indices)))))



(include-book "centaur/fgl/top" :dir :system)
;; start an external shell from which the SAT solver can be called
(value-triple (acl2::tshell-ensure))


;(defthm lookup-srl-0-subtable-correctness
;  (implies (and (natp i)
;                (natp j)
;                (<= i (expt 2  8))
;                (<= j (expt 2  5)))
;           (b* ((indices  (create-x-indices (expt 2 8) (expt 2 5)))
;                (subtable (create-srli-subtable indices 0)))
;               (equal (lookup i j subtable)
;                      (ash i (- j)))))
;  :hints (("Goal" :in-theory (disable (:e create-srli-subtable) (:e create-x-indices))
;                  :use ((:instance lookup-srli-subtable-correctness (x-hi (expt 2 8)) (y-hi (expt 2 5)))))))
;
;(fgl::def-fgl-param-thm lemma-1
; :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
; :concl (equal (+ (ash (logand x #x000000ff) (- y))
;	          (ash (logand x #x0000ff00) (- y))
;	          (ash (logand x #x00ff0000) (- y))
;	          (ash (logand x #xff000000) (- y)))
;	       (ash (+ (logand x #x000000ff)
;                       (logand x #x0000ff00)
;                       (logand x #x00ff0000)
;                       (logand x #xff000000))
;		      (- y)))
;    :param-bindings
;    `((((low  0) (high  4)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
;      (((low  4) (high  8)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
;      (((low  8) (high 12)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
;      (((low 12) (high 16)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
;      (((low 16) (high 20)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
;      (((low 20) (high 24)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
;      (((low 24) (high 28)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
;      (((low 28) (high 32)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
;      (((low 32) (high 33)) ,(gl::auto-bindings (:nat x 32) (:nat y 5))))
;    :param-hyp (or (and (<= (expt 2 low) x) (< x (expt 2 high))) (= x 0))
;    :cov-bindings (gl::auto-bindings (:nat x 32) (:nat y 5)))


(fgl::def-fgl-thm chunk-and-shift-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
 :concl (equal (chunk-and-shift-32 x y)
               (ash x (- y))))

(defthm srl-chunk-lookup-combine-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
          (equal (srl-chunk-lookup-combine-32 x y)
                 (ash x (- y))))
 :hints (("Goal" :in-theory (disable srl-chunk-lookup-combine-32)
	         :use ((:instance chunk-and-shift-32-correctness) (:instance srl-equal-stuff)))))



(define chunk-for-shift (x n)
  :enabled t
  :returns (chunks true-listp)
  :measure (acl2-count n)
  (if (or (not (natp n)) (not (natp x)))
      nil
      (if (zerop n)
          nil
          (cons (loghead 8 x)
    	        (chunk-for-shift (logtail 8 x) (1- n))))))

(define concat-chunks (chunks)
  :returns (word natp)
  (if (atom chunks)
      0 
      (logapp 8 (nfix (car chunks)) (concat-chunks (cdr chunks)))))

(gl::def-gl-thm concat-chunks-32
  :hyp (unsigned-byte-p 32 x)
  :concl (equal (concat-chunks (chunk-for-shift x 4)) x)
  :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm concat-chunks-64
  :hyp (unsigned-byte-p 64 x)
  :concl (equal (concat-chunks (chunk-for-shift x 8)) x)
  :g-bindings (gl::auto-bindings (:nat x 64)))

;; Chunk and shifting
;; takes the i-th chunk and shifts it right by y
(define shift-chunk (chunk i y)
 :enabled t
 :returns (shifted natp)
 (if (not (and (natp i) (natp chunk) (natp y)))
     0
     (ash (ash chunk i) (- y))))

(define shift-chunks (chunks i y)
 :enabled t
 :returns (shifted-chunks true-listp)
 (if (or (atom chunks) (not (natp i)))
     nil
     (cons (shift-chunk  (car chunks) i y)
	   (shift-chunks (cdr chunks) (+ i 8) y))))

(defthm chunk-for-shift-32-expand
  (implies (unsigned-byte-p 32 x)
           (equal (chunk-for-shift x 4)
		  (list (loghead 8 x) 
			(loghead 8 (logtail 8 x)) 
			(loghead 8 (logtail 16 x)) 
			(loghead 8 (logtail 24 x)) )))
  :hints (("Goal" :expand ((chunk-for-shift x 4)
  		 	   (chunk-for-shift (logtail 8 x) 3)
  		 	   (chunk-for-shift (logtail 16 x) 2)))))

(defthm shift-chunks-chunk-for-shift-32
  (implies (and (unsigned-byte-p 32 x) (natp y))
           (equal (shift-chunks (chunk-for-shift x 4) 0 y)
		  (list (ash (loghead 8 x) (- y))
			(ash (ash (loghead 8 (logtail 8 x)) 8) (- y))
			(ash (ash (loghead 8 (logtail 16 x)) 16) (- y))
			(ash (ash (loghead 8 (logtail 24 x)) 24) (- y)))))
  :hints (("Goal" :expand ((chunk-for-shift x 4)
  		 	   (chunk-for-shift (logtail 8 x) 3)
  		 	   (chunk-for-shift (logtail 16 x) 2)))))


;(gl::def-gl-thm lemma-1
; :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
; :concl (equal (ash (ash (loghead 8 (logtail 8 x)) 8) (- y))
;	       (ash (




(define srl-combine (chunks)
  (if (atom chunks)
      0
      (+ (nfix (car chunks)) (srl-combine (cdr chunks)))))

(fgl::def-fgl-thm shift-and-concat-chunks-32
  :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
  :concl (equal (srl-combine
		  (shift-chunks 
		    (chunk-for-shift x 4)
		    0
		    y))
		(ash x (- y))))








