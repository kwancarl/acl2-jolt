(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

;; Note: In ACL2, the OR operation is named `ior` for inclusive OR

(include-book "subtable")

;; Materialize subtables for "or"

(defun materialize-or-subtable (idx-lst)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons x y)                    idx))
     (cons (cons idx (logior x y))
           (materialize-or-subtable rst))))

(defthm alistp-of-materialize-or-subtable
 (alistp (materialize-or-subtable idx-lst)))

(defthm member-idx-lst-assoc-materialize-or-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-or-subtable idx-lst))))

(defthm assoc-member-or-subtable
 (implies (assoc (cons i j) (materialize-or-subtable idx-lst))
          (member (cons i j) idx-lst)))

(defthm assoc-or-subtable
 (implies (assoc (cons i j) (materialize-or-subtable idx-lst))
          (equal (assoc (cons i j) (materialize-or-subtable idx-lst))
                 (cons (cons i j) (logior i j)))))

(defthm or-subtable-correctness
 (implies (and (natp x-hi) 
               (natp y-hi) 
               (natp i) 
               (natp j) 
               (<= i x-hi) 
               (<= j y-hi) )
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-or-subtable indices)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j) (logior i j))))))
                 
(defthm lookup-or-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi) )
          (b* ((indices  (create-tuple-indices x-hi y-hi))
               (subtable (materialize-or-subtable indices)))
              (equal (tuple-lookup i j subtable)
                     (logior i j))))
 :hints (("Goal" :in-theory (enable tuple-lookup))))

;;;;;;;;;;;;;;
;;	    ;;
;;    OR    ;;
;;	    ;;
;;;;;;;;;;;;;;

(define or-w ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (+ (integer-length x) (integer-length y))
  :hints (("Goal" :in-theory (enable logcdr integer-length)))
  (b* (((unless (and (natp x) (natp y) 0)))
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (x0 (logcar x))
       (y0 (logcar y)))
      (+ (b-xor (b-xor x0 y0) (b-and x0 y0))
         (* 2 (or-w (logcdr x) (logcdr y))))))

(defthmd b-or-w-b-ior-equiv
  (implies (and (bitp x) (bitp y))
	   (equal (b-xor (b-xor x y) (b-and x y)) (b-ior x y)))
  :hints (("Goal" :cases ((equal x 0)))))

(defthm or-w-logior-equiv
  (implies (and (natp x) (natp y))
	   (equal (or-w x y) (logior x y)))
  :hints (("Goal" :in-theory (enable or-w))))

(gl::def-gl-thm or-w-logior-equiv-gl
  :hyp   (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
  :concl (equal (or-w x y) (logior x y))
  :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32 ))))

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
(define or-wc  ((x :type unsigned-byte)
                (y :type unsigned-byte)
                (wc natp))
  :measure (max (integer-length x) (integer-length y))
  :hints (("Goal" :use ((:instance natp-lemma-4 (a (integer-length y)) (c wc)))))
  (b* (((unless (and (natp x) (natp y))) 0)
       ((unless (posp wc)) 0)
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (car-chunk-x   (loghead wc x))
       (car-chunk-y   (loghead wc y))
       (car-chunk-or  (or-w car-chunk-x car-chunk-y))
       (cdr-chunk-x   (logtail wc x))
       (cdr-chunk-y   (logtail wc y)))
      (logapp wc
              car-chunk-or
              (or-wc cdr-chunk-x cdr-chunk-y wc))))

(gl::def-gl-thm or-w-or-wc-equiv-32-gl
 :hyp (and (unsigned-byte-p 32 x)
           (unsigned-byte-p 32 y))
 :concl (equal (or-wc x y 8) (or-w x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(gl::def-gl-thm or-w-or-wc-equiv-64-gl
 :hyp (and (unsigned-byte-p 64 x)
           (unsigned-byte-p 64 y))
 :concl (equal (or-wc x y 8) (or-w x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))
