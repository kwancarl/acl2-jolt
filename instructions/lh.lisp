(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "../subtables/identity")
(include-book "../subtables/sign-extend")

(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)


(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

;; LH returns the lower 16 bits of the input, sign-extended to word size
;; Note: semantics for loads and stores are handled in different parts of Jolt,
;; and not the scope of this formalization

(defun sign-extend (z width)
  (* (logbit (1- width) z) (1- (expt 2 width))))

(define lh-semantics-32 ((x (unsigned-byte-p 32 x)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16))
       ;; LOOKUP SEMANTICS
       (?x8-0 x8-0)
       (?x8-1 x8-1)
       (?x8-2 x8-2)
       (x8-3  x8-3)
       (s (sign-extend x8-3 16)))
      ;; COMBINE
      (merge-2-u16s s x8-3)))


(define lh-32 ((x (unsigned-byte-p 32 x)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low  0 :width 16))
       (x8-2 (part-select x :low 16 :width 16))
       (x8-1 (part-select x :low 32 :width 16))
       (x8-0 (part-select x :low 48 :width 16))
       ;; MATERIALIZE SUBTABLES
       (id-subtable          (materialize-identity-subtable (expt 2 16)))
       (sign-extend-subtable (materialize-sign-extend-subtable (expt 2 16) 16))
       ;; LOOKUP SEMANTICS
       ;; Note that the `id` lookups are present in the Jolt codebase for reasons not related to the immediate semantics of SB
       ;; Instead they are used as range checks for the input value, which is necessary for other parts of the Jolt's constraint system
       ;; We include them here for completeness
       (?x8-0 (single-lookup x8-0 id-subtable))
       (?x8-1 (single-lookup x8-1 id-subtable))
       (?x8-2 (single-lookup x8-2 id-subtable))
       (x8-3  (single-lookup x8-3 id-subtable))
       (s     (single-lookup x8-3 sign-extend-subtable)))
      ;; COMBINE
      (merge-2-u16s s x8-3)))


(defthm lh-32-lh-semantics-32-equiv
 (equal (lh-32 x) (lh-semantics-32 x))
 :hints (("Goal" :in-theory (e/d (lh-semantics-32) ((:e materialize-sign-extend-subtable) (:e materialize-identity-subtable))))))

;; SEMANTIC CORRECTNESS OF LB
(gl::def-gl-thm lh-semantics-32-correctness
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (lh-semantics-32 x)
	       (logextu 32 16 x))
 :g-bindings (gl::auto-bindings (:nat x 32)))

;; Equivalence of lb-32 with its semantics
(defthm lh-32-correctness
 (implies (unsigned-byte-p 32 x)
          (equal (lh-32 x) (logextu 32 16 x))))
