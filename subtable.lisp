(in-package "ACL2")
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(defun cons-fix (x)
 (if (consp x) x (cons x nil)))
(verify-guards cons-fix)

(fty::deffixtype cons
 :pred consp
 :fix  cons-fix
 :equiv cons-equiv
 :define t
 :forward t)

(fty::defalist subtable
 :key-type cons
 :val-type nat
 :true-listp t)

(defun create-y-indices (fixed-x y-hi)
 (if (or (not (natp y-hi)) (not (natp fixed-x)))
     nil
     (if (zerop y-hi)
         (cons (cons fixed-x y-hi) nil)
         (cons (cons fixed-x y-hi)
               (create-y-indices fixed-x (1- y-hi))))))

(defthmd create-y-indices-correctness
 (implies (and (natp x) (natp y-hi) (natp i) (<= i y-hi))
          (member (cons x i) (create-y-indices x y-hi))))

(defun create-x-indices (x-hi y-hi)
 (if (or (not (natp x-hi)) (not (natp y-hi)))
     nil
     (if (zerop x-hi)
         (create-y-indices x-hi y-hi)
         (append (create-y-indices x-hi y-hi)
                 (create-x-indices (1- x-hi) y-hi)))))
(defthm alistp-of-create-x-indices
 (alistp (create-x-indices x-hi y-hi)))
(verify-guards create-y-indices)
(verify-guards create-x-indices)

(defthm create-x-indices-correctness
 (implies (and (natp x-hi) 
               (natp y-hi) 
               (natp i) 
               (natp j) 
               (<= i x-hi) 
               (<= j y-hi) )
          (member (cons i j) (create-x-indices x-hi y-hi))))

(defund lookup (x y table)
 (cdr (assoc-equal (cons x y) table)))
(verify-guards lookup)

(defthm unsigned-byte-p-natp-bounds-equiv
 (implies (unsigned-byte-p 8 x)
          (and (natp x)
               (natp (expt 2 8))
               (<= x (expt 2 8)))))
