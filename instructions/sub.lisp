(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "../subtables/truncate-overflow")
(include-book "../subtables/identity")

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

;; 32-BIT VERSION

(define sub-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; sub in circuit
       (z (- x y))
       ;; CHUNK
       (z8-3 (part-select z :low  0 :width 16))
       (z8-2 (part-select z :low 16 :width 16))
       (z8-1 (part-select z :low 32 :width 16))
       (z8-0 (part-select z :low 48 :width 16))
       ;; LOOKUP SEMANTICS
       (z8-0 (truncate-overflow z8-0 0))
       (z8-1 (truncate-overflow z8-1 0))
       (z8-2 z8-2)
       (z8-3 z8-3))
      ;; COMBINE
      (merge-4-u16s z8-0 z8-1 z8-2 z8-3)))

(define sub-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; sub in circuit
       (z (- x y))
       ;; CHUNK
       (z8-3 (part-select z :low  0 :width 16))
       (z8-2 (part-select z :low 16 :width 16))
       (z8-1 (part-select z :low 32 :width 16))
       (z8-0 (part-select z :low 48 :width 16))
       ;; MATERIALIZE SUBTABLES 
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       (truncate-subtable (materialize-truncate-subtable (expt 2 16) 0))
       ;; LOOKUP SEMANTICS
       (z8-0 (single-lookup z8-0 truncate-subtable))
       (z8-1 (single-lookup z8-1 truncate-subtable))
       (z8-2 (single-lookup z8-2 id-subtable))
       (z8-3 (single-lookup z8-3 id-subtable)))
      ;; COMBINE
      (merge-4-u16s z8-0 z8-1 z8-2 z8-3)))

(defthm sub-32-sub-semantics-32-equiv
 (equal (sub-32 x y) (sub-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (sub-semantics-32) 
                                 ((:e materialize-identity-subtable) 
                                  (:e materialize-truncate-subtable))))))

;; SEMANTIC CORRECTNESS OF SUB
(gl::def-gl-thm sub-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (sub-semantics-32 x y)
	       (loghead 32 (- x y)))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm sub-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (sub-32 x y) (loghead 32 (- x y))))) 


;; 64-BIT VERSION

(define sub-semantics-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; sub in circuit
       (z (- x y))
       ;; CHUNK
       (z8-7 (part-select z :low  0 :width 16))
       (z8-6 (part-select z :low 16 :width 16))
       (z8-5 (part-select z :low 32 :width 16))
       (z8-4 (part-select z :low 48 :width 16))
       (z8-3 (part-select z :low 64 :width 16))
       (z8-2 (part-select z :low 80 :width 16))
       (z8-1 (part-select z :low 96 :width 16))
       (z8-0 (part-select z :low 112 :width 16))
       ;; LOOKUP SEMANTICS
       (z8-0 (truncate-overflow z8-0 0))
       (z8-1 (truncate-overflow z8-1 0))
       (z8-2 (truncate-overflow z8-2 0))
       (z8-3 (truncate-overflow z8-3 0))
       (z8-4 z8-4)
       (z8-5 z8-5)
       (z8-6 z8-6)
       (z8-7 z8-7))
      ;; COMBINE
      (merge-8-u16s z8-0 z8-1 z8-2 z8-3 z8-4 z8-5 z8-6 z8-7)))

(define sub-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; sub in circuit
       (z (- x y))
       ;; CHUNK
       (z8-7 (part-select z :low  0 :width 16))
       (z8-6 (part-select z :low 16 :width 16))
       (z8-5 (part-select z :low 32 :width 16))
       (z8-4 (part-select z :low 48 :width 16))
       (z8-3 (part-select z :low 64 :width 16))
       (z8-2 (part-select z :low 80 :width 16))
       (z8-1 (part-select z :low 96 :width 16))
       (z8-0 (part-select z :low 112 :width 16))
       ;; MATERIALIZE SUBTABLES 
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       (truncate-subtable (materialize-truncate-subtable (expt 2 16) 0))
       ;; LOOKUP SEMANTICS
       (z8-0 (single-lookup z8-0 truncate-subtable))
       (z8-1 (single-lookup z8-1 truncate-subtable))
       (z8-2 (single-lookup z8-2 truncate-subtable))
       (z8-3 (single-lookup z8-3 truncate-subtable))
       (z8-4 (single-lookup z8-4 id-subtable))
       (z8-5 (single-lookup z8-5 id-subtable))
       (z8-6 (single-lookup z8-6 id-subtable))
       (z8-7 (single-lookup z8-7 id-subtable)))
      ;; COMBINE
      (merge-8-u16s z8-0 z8-1 z8-2 z8-3 z8-4 z8-5 z8-6 z8-7)))

(defthm sub-64-sub-semantics-64-equiv
 (equal (sub-64 x y) (sub-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (sub-semantics-64) 
                                 ((:e materialize-identity-subtable) 
                                  (:e materialize-truncate-subtable))))))


;; SEMANTIC CORRECTNESS OF SUB
(gl::def-gl-thm sub-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (sub-semantics-64 x y)
	       (loghead 64 (- x y)))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))

(defthm sub-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (sub-64 x y) (loghead 64 (- x y))))) 
