(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

;; MATERIALIZE SUBTABLES FOR XOR
(include-book "subtable")
(encapsulate 
 nil
 (defun materialize-xor-subtable (idx-lst)
  (b* (((unless (alistp idx-lst))     nil)
       ((if (atom idx-lst))           nil)
       ((cons idx rst)            idx-lst)
       ((unless (consp idx))          nil)
       ((cons x y)                    idx))
      (cons (cons idx (logxor x y))
            (materialize-xor-subtable rst))))
 
 (defthm alistp-of-materialize-xor-subtable
  (alistp (materialize-xor-subtable idx-lst)))
 
 (defthm member-idx-lst-assoc-materialize-xor-subtable
  (implies (and (alistp idx-lst) (member idx idx-lst))
           (assoc idx (materialize-xor-subtable idx-lst))))
 
 (defthm assoc-member-xor-subtable
  (implies (assoc (cons i j) (materialize-xor-subtable idx-lst))
           (member (cons i j) idx-lst)))
 
 (defthm assoc-xor-subtable
  (implies (assoc (cons i j) (materialize-xor-subtable idx-lst))
           (equal (assoc (cons i j) (materialize-xor-subtable idx-lst))
                  (cons (cons i j) (logxor i j)))))
 
 (defthm xor-subtable-correctness
  (implies (and (natp x-hi) 
                (natp y-hi) 
                (natp i) 
                (natp j) 
                (<= i x-hi) 
                (<= j y-hi) )
           (b* ((indices  (create-x-indices x-hi y-hi))
                (subtable (materialize-xor-subtable indices)))
               (equal (assoc-equal (cons i j) subtable)
                      (cons (cons i j) (logxor i j))))))

 (defthm lookup-xor-subtable-correctness
  (implies (and (natp x-hi)
                (natp y-hi)
                (natp i)
                (natp j)
                (<= i x-hi)
                (<= j y-hi) )
           (b* ((indices  (create-x-indices x-hi y-hi))
                (subtable (materialize-xor-subtable indices)))
               (equal (lookup i j subtable) (logxor i j))))))
;; end encapsulate

(include-book "centaur/gl/gl" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "ihs/basic-definitions" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (Include-book "centaur/fty/top" :dir :system))

;;;;;;;;;;;;;;;
;;	     ;;
;;    XOR    ;;
;;	     ;;
;;;;;;;;;;;;;;;

;; EVALUATE MLE & CORRECTNESS

(define xorw ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (+ (integer-length x) (integer-length y))
  ;:returns (r integerp)
  :enabled t
  :hints (("Goal" :in-theory (enable logcdr integer-length)))
  (b* (((unless (and (natp x) (natp y) 0)))
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (x0 (logcar x))
       (y0 (logcar y)))
      (+ (b-xor (b-and x0 (b-xor 1 y0)) (b-and y0 (b-xor 1 x0)))
         (* 2 (xorw (logcdr x) (logcdr y))))))

(local (defthm b-xowr-b-xor-equiv
  (implies (and (bitp x0) (bitp y0))
           (equal (b-xor (b-and x0 (b-xor 1 y0)) (b-and y0 (b-xor 1 x0)))
		  (b-xor x0 y0)))
  :hints (("Goal" :cases ((equal x0 0))))))

(gl::def-gl-thm xorw-logxor-equiv-gl
  :hyp   (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
  :concl (equal (xorw x y) (logxor x y))
  :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))


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
(local
  (defthm natp-lemma-4
    (implies (and (natp a) (posp c) (not (zerop a)))
             (< (nfix (- a c)) a))))

(define xor-wc ((x :type unsigned-byte)
                (y :type unsigned-byte)
                (wc natp))
  :verify-guards nil
  :measure (max (integer-length x) (integer-length y))
  :hints (("Goal" :use ((:instance natp-lemma-4 (a (integer-length y)) (c wc)))))
  (b* (((unless (and (natp x) (natp y))) 0)
       ((unless (posp wc)) 0)
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (car-chunk-x   (loghead wc x))
       (car-chunk-y   (loghead wc y))
       (car-chunk-xor (xorw car-chunk-x car-chunk-y))
       (cdr-chunk-x   (logtail wc x))
       (cdr-chunk-y   (logtail wc y)))
      (logapp wc
              car-chunk-xor
              (xor-wc cdr-chunk-x cdr-chunk-y wc))))

(gl::def-gl-thm xorw-xor-wc-equiv-32-gl
 :hyp (and (unsigned-byte-p 32 x)
           (unsigned-byte-p 32 y))
 :concl (equal (xor-wc x y 8) (xorw x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(gl::def-gl-thm xorw-xor-wc-equiv-64-gl
 :hyp (and (unsigned-byte-p 64 x)
           (unsigned-byte-p 64 y))
 :concl (equal (xor-wc x y 8) (xorw x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))


