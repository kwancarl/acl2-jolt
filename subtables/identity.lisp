(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/bitops/ihsext-basics" :dir :system)

(include-book "subtable")

;; Materialize subtables for "identity"

(define materialize-identity-subtable (x-hi)
 :enabled t
 :returns (lst alistp)
 :measure (acl2-count x-hi)
 (if (not (natp x-hi))
     nil
     (if (zerop x-hi)
         (cons (cons x-hi x-hi) nil)
         (cons (cons x-hi x-hi)
               (materialize-identity-subtable (1- x-hi))))))

(defthm identity-subtable-correctness
 (implies (and (natp x-hi) 
               (natp i) 
               (<= i x-hi))
          (b* ((subtable (materialize-identity-subtable x-hi)))
              (equal (assoc-equal i subtable)
                     (cons i i)))))

(defthm lookup-identity-subtable-correctness
 (implies (and (natp x-hi) 
               (natp i) 
               (<= i x-hi))
          (b* ((subtable (materialize-identity-subtable x-hi)))
              (equal (single-lookup i subtable) i)))
 :hints (("Goal" :in-theory (e/d (single-lookup) (materialize-identity-subtable))
	         :use ((:instance identity-subtable-correctness)))))
