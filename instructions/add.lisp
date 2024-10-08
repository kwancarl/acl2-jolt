(in-package "ACL2")
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)
(include-book "centaur/gl/gl" :DIR :SYSTEM)

(include-book "../subtables/truncate-overflow")
(include-book "../subtables/identity")

;; 32-bit intermediary semantics version
(define add-semantics-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Add in circuit
       (z (+ x y))
       ;; Chunk
       (z8-3 (part-select z :low  0 :width 16))
       (z8-2 (part-select z :low 16 :width 16))
       (z8-1 (part-select z :low 32 :width 16))
       (z8-0 (part-select z :low 48 :width 16))
       ;; Lookup semantics
       (z8-0 (truncate-overflow z8-0 0))
       (z8-1 (truncate-overflow z8-1 0))
       (z8-2 z8-2)
       (z8-3 z8-3))
      ;; Combine
      (merge-4-u16s z8-0 z8-1 z8-2 z8-3)))

(define add-32 ((x (unsigned-byte-p 32 x)) (y (unsigned-byte-p 32 y)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Add in circuit
       (z (+ x y))
       ;; Chunk
       (z8-3 (part-select z :low  0 :width 16))
       (z8-2 (part-select z :low 16 :width 16))
       (z8-1 (part-select z :low 32 :width 16))
       (z8-0 (part-select z :low 48 :width 16))
       ;; Materialize subtables 
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       (truncate-subtable (materialize-truncate-subtable (expt 2 16) 0))
       ;; Perform lookups
       (z8-0 (single-lookup z8-0 truncate-subtable))
       (z8-1 (single-lookup z8-1 truncate-subtable))
       (z8-2 (single-lookup z8-2 id-subtable))
       (z8-3 (single-lookup z8-3 id-subtable)))
      ;; Combine
      (merge-4-u16s z8-0 z8-1 z8-2 z8-3)))

(defthm add-32-add-semantics-32-equiv
 (equal (add-32 x y) (add-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (add-32 add-semantics-32) 
                                 ((:e materialize-identity-subtable) 
                                  (:e materialize-truncate-subtable))))))

;; Semantic correctness of add
(gl::def-gl-thm add-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (add-semantics-32 x y)
	       (logand (+ x y) (1- (expt 2 32))))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(defthm add-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (add-32 x y) (logand (+ x y) (1- (expt 2 32)))))) 


;; 64-BIT VERSION

;; 64-bit intermediary semantics version
(define add-semantics-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Add in circuit
       (z (+ x y))
       ;; Chunk
       (z8-7 (part-select z :low  0 :width 16))
       (z8-6 (part-select z :low 16 :width 16))
       (z8-5 (part-select z :low 32 :width 16))
       (z8-4 (part-select z :low 48 :width 16))
       (z8-3 (part-select z :low 64 :width 16))
       (z8-2 (part-select z :low 80 :width 16))
       (z8-1 (part-select z :low 96 :width 16))
       (z8-0 (part-select z :low 112 :width 16))
       ;; Lookup semantics
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

(define add-64 ((x (unsigned-byte-p 64 x)) (y (unsigned-byte-p 64 y)))
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Add in circuit
       (z (+ x y))
       ;; Chunk
       (z8-7 (part-select z :low  0 :width 16))
       (z8-6 (part-select z :low 16 :width 16))
       (z8-5 (part-select z :low 32 :width 16))
       (z8-4 (part-select z :low 48 :width 16))
       (z8-3 (part-select z :low 64 :width 16))
       (z8-2 (part-select z :low 80 :width 16))
       (z8-1 (part-select z :low 96 :width 16))
       (z8-0 (part-select z :low 112 :width 16))
       ;; Materialize subtables 
       (id-subtable       (materialize-identity-subtable (expt 2 16)))
       (truncate-subtable (materialize-truncate-subtable (expt 2 16) 0))
       ;; Lookup semantics
       (z8-0 (single-lookup z8-0 truncate-subtable))
       (z8-1 (single-lookup z8-1 truncate-subtable))
       (z8-2 (single-lookup z8-2 truncate-subtable))
       (z8-3 (single-lookup z8-3 truncate-subtable))
       (z8-4 (single-lookup z8-4 id-subtable))
       (z8-5 (single-lookup z8-5 id-subtable))
       (z8-6 (single-lookup z8-6 id-subtable))
       (z8-7 (single-lookup z8-7 id-subtable)))
      ;; Combine
      (merge-8-u16s z8-0 z8-1 z8-2 z8-3 z8-4 z8-5 z8-6 z8-7)))

(defthm add-64-add-semantics-64-equiv
 (equal (add-64 x y) (add-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (add-64 add-semantics-64) 
                                 ((:e materialize-identity-subtable) 
                                  (:e materialize-truncate-subtable))))))

;; Semantic correctness of add
(gl::def-gl-thm add-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (add-semantics-64 x y)
	       (logand (+ x y) (1- (expt 2 64))))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))

(defthm add-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (add-64 x y) (logand (+ x y) (1- (expt 2 64)))))) 
