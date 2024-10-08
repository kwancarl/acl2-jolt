(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "subtable")

;; Materialize subtables for "sign-extend"

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

;; Correctness of subtables wrt logapp

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

;; Evaluate mle and correctness of lookup
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

