(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

;; MATERIALIZE SUBTABLES FOR "SIGN-EXTEND"

(include-book "subtable")

(defun sign-extend (z width)
  (* (logbit (1- width) z) (1- (expt 2 width))))

(define materialize-sign-extend-subtable (x-hi width)
 :enabled t
 :returns (lst alistp)
 :measure (acl2-count x-hi)
 :verify-guards nil
 (if (or (not (natp x-hi)) (not (natp width)))
     nil
     (if (zerop x-hi)
         (cons (cons x-hi (sign-extend x-hi width)) nil)
         (cons (cons x-hi (sign-extend x-hi width))
               (materialize-sign-extend-subtable (1- x-hi) width)))))

(defthm assoc-materialize-sign-extend-subtable
 (implies (and (natp x-hi)
               (natp width) 
               (natp i) 
               (<= i x-hi))
          (b* ((subtable (materialize-sign-extend-subtable x-hi width)))
              (assoc-equal i subtable))))

(defthm materialize-sign-extend-subtable-correctness
 (implies (and (natp x-hi)
               (natp width) 
               (natp i) 
               (<= i x-hi))
          (b* ((subtable (materialize-sign-extend-subtable x-hi width)))
              (equal (assoc-equal i subtable)
                     (cons i (sign-extend i width))))))

(defthm lookup-materialize-sign-extend-subtable-correctness
 (implies (and (natp x-hi) 
               (natp width)
               (natp i) 
               (<= i x-hi))
          (b* ((subtable (materialize-sign-extend-subtable x-hi width)))
              (equal (single-lookup i subtable)
                     (sign-extend i width))))
 :hints (("Goal" :in-theory (e/d (single-lookup) (materialize-sign-extend-subtable)))))

;; CORRECTNESS OF SUBTABLES WRT LOGAPP

(local (include-book "ihs/basic-definitions" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

(defthmd loghead-logextu-reverse-32
  (implies (and (<= width 32)
                (logextu-guard 32 width i)
                (natp width))
           (equal (loghead width i)
                  (loghead width (logextu 32 width i)))))

(defthmd loghead-logextu-reverse-64
  (implies (and (<= width 64)
                (logextu-guard 64 width i)
                (natp width))
           (equal (loghead width i)
                  (loghead width (logextu 64 width i)))))

;; (defthm logapp-materialize-sign-extend-subtable-64-correctness
;;  (implies (and (natp i) 
;;                (natp z-hi) 
;;                (natp width)
;;                (<= i z-hi)
;;                (<= width 64))
;;           (b* ((indices  (sign-extend-idx z-hi width))
;;                (subtable (materialize-sign-extend-subtable-64 indices)))
;;               (equal (logapp width 
;;                              (loghead width i)
;;                              (tuple-lookup i width subtable))
;;                      (logextu 64 width i))))
;;  :hints (("Goal" :use ((:instance loghead-logextu-reverse-64))
;;                  :in-theory (disable logextu
;;                                      loghead-logextu 
;;                                      bitops::logapp-of-loghead))))

;; (defthm logapp-materialize-sign-extend-subtable-32-correctness
;;  (implies (and (natp i) 
;;                (natp z-hi) 
;;                (natp width)
;;                (<= i z-hi)
;;                (<= width 32))
;;           (b* ((indices  (sign-extend-idx z-hi width))
;;                (subtable (materialize-sign-extend-subtable-32 indices)))
;;               (equal (logapp width 
;;                              (loghead width i)
;;                              (tuple-lookup i width subtable))
;;                      (logextu 32 width i))))
;;  :hints (("Goal" :use ((:instance loghead-logextu-reverse-32))
;;                  :in-theory (disable logextu
;;                                      loghead-logextu 
;;                                      bitops::logapp-of-loghead))))


;; EVALUATE MLE and CORRECTNESS OF LOOKUP
(gl::def-gl-thm sign-extend-logtail-logextu-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 z) (unsigned-byte-p 5 width))
 :concl (equal (logtail width (logextu 32 width z))
               (* (1- (expt 2 (- 32 width))) (logbit (1- width) z)))
 :g-bindings (gl::auto-bindings (:nat width 5) (:nat z 32)))

(gl::def-gl-thm sign-extend-logtail-logextu-equiv-64-bit-gl
 :hyp   (and (unsigned-byte-p 64 z) (unsigned-byte-p 6 width))
 :concl (equal (logtail width (logextu 64 width z))
               (* (1- (expt 2 (- 64 width))) (logbit (1- width) z)))
 :g-bindings (gl::auto-bindings (:nat width 6) (:nat z 64)))


#|
;; SUBTABLES FOR MLE
(defun materialize-sign-extend-mle-subtable-32 (idx-lst)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons z width)                 idx))
     (cons (cons idx (* (1- (expt 2 (- 32 width))) 
                        (logbit (1- width) z)))
           (materialize-sign-extend-mle-subtable-32 rst))))

(defthm alistp-of-materialize-sign-extend-mle-subtable-32
 (alistp (materialize-sign-extend-mle-subtable-32 idx-lst)))

(defthm member-idx-lst-assoc-materialize-sign-extend-mle-subtable-32
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-sign-extend-mle-subtable-32 idx-lst))))

(defthm assoc-member-materialize-sign-extend-mle-subtable-32
 (implies (assoc (cons z width) (materialize-sign-extend-mle-subtable-32 idx-lst))
          (member (cons z width) idx-lst)))

(defthm assoc-materialize-sign-extend-mle-subtable-32
 (implies (assoc (cons i width) (materialize-sign-extend-mle-subtable-32 idx-lst))
          (equal (assoc (cons i width) (materialize-sign-extend-mle-subtable-32 idx-lst))
                 (cons (cons i width) (logtail width (logextu 32
width i))))))

(defthm materialize-sign-extend-mle-subtable-32-correctness
 (implies (and (natp z-hi) 
               (natp i) 
               (<= i z-hi))
          (b* ((indices  (sign-extend-mle-idx z-hi width))
               (subtable (materialize-sign-extend-mle-subtable-32 indices)))
              (equal (assoc-equal (cons i width) subtable)
                     (cons (cons i width)
                           (logtail width (logextu 32 width i)))))))

(defthm lookup-materialize-sign-extend-mle-subtable-32-correctness
 (implies (and (natp z-hi) 
               (natp i) 
               (<= i z-hi))
          (b* ((indices  (sign-extend-mle-idx z-hi width))
               (subtable (materialize-sign-extend-mle-subtable-32 indices)))
              (equal (tuple-lookup i width subtable)
                     (logtail width (logextu 32 width i)))))
 :hints (("Goal" :in-theory (e/d (tuple-lookup) ()))))
|#
