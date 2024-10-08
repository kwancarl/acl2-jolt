(in-package "ACL2")
(include-book "centaur/fty/top" :dir :system)

;; Check if `x` is a `cons` (i.e. a pair of values). If yes, return `x`. If no,
;; return `(cons x nil)`, i.e. `x` as the first value and `nil` as the second
;; value.
(defun cons-fix (x)
 (if (consp x) x (cons x nil)))
(verify-guards cons-fix)

;; Define a new fixed type `cons`
(fty::deffixtype cons
 :pred consp
 :fix  cons-fix
 :equiv cons-equiv
 :define t
 :forward t)

;; Define a new association list type called `subtable`
(fty::defalist subtable
 :key-type cons
 :val-type nat
 ;; The subtable is a true list (i.e. `nil` as the last value).
 :true-listp t)

;; Generate a list of `cons` values, where the first element is `fixed-x` and
;; the second element is a natural number that ranges from `y-hi` to `0`.  If
;; `y-hi` or `fixed-x` is not a natural number, return `nil`.  If `y-hi` is
;; `0`, return a list containing the `cons` value `(cons fixed-x y-hi)`.
;; Otherwise, return a list containing the `cons` value `(cons fixed-x y-hi)`
;; appended to the result of recursively calling `create-y-indices` with
;; `fixed-x` and `(y-hi - 1)`.
(defun create-y-indices (fixed-x y-hi)
 (if (or (not (natp y-hi)) (not (natp fixed-x)))
     nil
     (if (zerop y-hi)
         (cons (cons fixed-x y-hi) nil)
         (cons (cons fixed-x y-hi)
               (create-y-indices fixed-x (1- y-hi))))))

;; For any natural numbers `x`, `y-hi`, and `i`, if `i` is less than or equal
;; to `y-hi`, then `(cons x i)` is a member of the list returned by
;; `create-y-indices` with `x` and `y-hi`.
(defthmd create-y-indices-correctness
 (implies (and (natp x) (natp y-hi) (natp i) (<= i y-hi))
          (member (cons x i) (create-y-indices x y-hi))))

;; Generate a list of `cons` values, where pairs are of the form `(cons i j)`
;; with `i` ranging from `x-hi` to `0` and `j` ranging from `y-hi` to `0`.  If
;; `x-hi` or `y-hi` is not a natural number, return `nil`.  If `x-hi` is `0`,
;; return the list returned by `create-y-indices` with `x-hi` and `y-hi`.
;; Otherwise, return the list returned by `create-y-indices` with `x-hi` and
;; `y-hi` appended to the result of recursively calling `create-tuple-indices`
;; with `(x-hi - 1)` and `y-hi`.
(defun create-tuple-indices (x-hi y-hi)
 (if (or (not (natp x-hi)) (not (natp y-hi)))
     nil
     (if (zerop x-hi)
         (create-y-indices x-hi y-hi)
         (append (create-y-indices x-hi y-hi)
                 (create-tuple-indices (1- x-hi) y-hi)))))

(defthm alistp-of-create-tuple-indices
 (alistp (create-tuple-indices x-hi y-hi)))

(verify-guards create-y-indices)
(verify-guards create-tuple-indices)

(defthm create-tuple-indices-correctness
 (implies (and (natp x-hi) 
               (natp y-hi) 
               (natp i) 
               (natp j) 
               (<= i x-hi) 
               (<= j y-hi) )
          (member (cons i j) (create-tuple-indices x-hi y-hi))))

;; Lookup the value associated with the key `(cons x y)` in the association
;; list `table`.  `assoc-equal` is a function that returns the `cons` pair
;; associated with the key `(cons x y)` in the association list `table`. We
;; then return the value (i.e. second element) of this pair.
(defund tuple-lookup (x y table)
 (cdr (assoc-equal (cons x y) table)))

;; (verify-guards tuple-lookup)

;; Lookup the value associated with the key `x` in the association list `subtable`.
(defund single-lookup (x subtable) (cdr (assoc x subtable)))

;; (verify-guards single-lookup)

(defthm unsigned-byte-p-natp-bounds-equiv
 (implies (unsigned-byte-p 8 x)
          (and (natp x)
               (natp (expt 2 8))
               (<= x (expt 2 8)))))
