(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
;; (include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "../subtables/identity")

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "centaur/fgl/top" :dir :system)
(value-triple (acl2::tshell-ensure))

;; 32-BIT VERSION

(define mulhu-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Unsigned multiplication in circuit
       (z (* x y))
       ;; Chunk operand
       (?z8-3 (part-select z :low  0 :width 16))
       (?z8-2 (part-select z :low 16 :width 16))
       (z8-1 (part-select z :low 32 :width 16))
       (z8-0 (part-select z :low 48 :width 16))
       ;; Lookup semantics
       (z8-0 z8-0)
       (z8-1 z8-1))
      ;; Combine results
      (merge-2-u16s z8-0 z8-1)))

(define mulhu-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Unsigned multiplication in circuit
       (z (* x y))
       ;; Chunk operand
       (?z8-3 (part-select z :low  0 :width 16))
       (?z8-2 (part-select z :low 16 :width 16))
       (z8-1 (part-select z :low 32 :width 16))
       (z8-0 (part-select z :low 48 :width 16))
       ;; Materialize subtable 
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       ;; Perform lookups
       (z8-0 (single-lookup z8-0 id-subtable))
       (z8-1 (single-lookup z8-1 id-subtable)))
      ;; Combine results
      (merge-2-u16s z8-0 z8-1)))

(defthm mulhu-32-mulhu-semantics-32-equiv
 (equal (mulhu-32 x y) (mulhu-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (mulhu-semantics-32)
                                 ((:e materialize-identity-subtable))))))


;; SEMANTIC CORRECTNESS OF MULHU
(fgl::def-fgl-thm mulhu-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (mulhu-semantics-32 x y) (logtail 32 (* x y))))

(defthm mulhu-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (mulhu-32 x y) (logtail 32 (* x y))))) 



;; 64-BIT VERSION

(define mulhu-semantics-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Unsigned multiplication in circuit
       (z (* x y))
       ;; Chunk operand
       (?z8-7 (part-select z :low  0 :width 16))
       (?z8-6 (part-select z :low 16 :width 16))
       (?z8-5 (part-select z :low 32 :width 16))
       (?z8-4 (part-select z :low 48 :width 16))
       (z8-3 (part-select z :low 64 :width 16))
       (z8-2 (part-select z :low 80 :width 16))
       (z8-1 (part-select z :low 96 :width 16))
       (z8-0 (part-select z :low 112 :width 16))
       ;; Lookup semantics
       (z8-0 z8-0)
       (z8-1 z8-1)
       (z8-2 z8-2)
       (z8-3 z8-3))
      ;; Combine results
      (merge-4-u16s z8-0 z8-1 z8-2 z8-3)))

(define mulhu-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Unsigned multiplication in circuit
       (z (* x y))
       ;; Chunk operand
       (?z8-7 (part-select z :low  0 :width 16))
       (?z8-6 (part-select z :low 16 :width 16))
       (?z8-5 (part-select z :low 32 :width 16))
       (?z8-4 (part-select z :low 48 :width 16))
       (z8-3 (part-select z :low 64 :width 16))
       (z8-2 (part-select z :low 80 :width 16))
       (z8-1 (part-select z :low 96 :width 16))
       (z8-0 (part-select z :low 112 :width 16))
       ;; Materialize subtable
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       ;; Lookup semantics
       (z8-0 (single-lookup z8-0 id-subtable))
       (z8-1 (single-lookup z8-1 id-subtable))
       (z8-2 (single-lookup z8-2 id-subtable))
       (z8-3 (single-lookup z8-3 id-subtable)))
      ;; Combine results
      (merge-4-u16s z8-0 z8-1 z8-2 z8-3)))

(defthm mulhu-64-mulhu-semantics-64-equiv
 (equal (mulhu-64 x y) (mulhu-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (mulhu-semantics-64)
                                 ((:e materialize-identity-subtable))))))

;; SEMANTIC CORRECTNESS OF MULHU
(fgl::def-fgl-thm mulhu-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (mulhu-semantics-64 x y) (logtail 64 (* x y))))

(defthm mulhu-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (mulhu-64 x y) (logtail 64 (* x y)))))
