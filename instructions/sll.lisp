(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../subtables/sll")

;;; 32-BIT

;; SLL-semantics-32 (including truncation)
(define sll-semantics-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; CHUNK
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (shift-amount (part-select y :low 0 :width 5))
       ;; Lookup semantics
       (u8-0 (slli-rust u8-0 shift-amount  0 32)) 
       (u8-1 (slli-rust u8-1 shift-amount  8 32))
       (u8-2 (slli-rust u8-2 shift-amount 16 32))
       (u8-3 (slli-rust u8-3 shift-amount 24 32)))
      ;; Combine
      (+ (* u8-3 (expt 2 24))
         (* u8-2 (expt 2 16))
         (* u8-1 (expt 2  8))
            u8-0	     )))

(gl::def-gl-thm sll-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (sll-semantics-32 x y) 
	       (mod (ash x (part-select y :low 0 :width 5))
		    (expt 2 32)))
 :g-bindings (gl::auto-bindings (:mix (:nat y 32) (:nat x 32))))

;; New version of SLL-32 with truncation
(define sll-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       (shift-amount (part-select y :low 0  :width 5))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (slli-subtable-0 (materialize-slli-subtable indices  0 32))
       (slli-subtable-1 (materialize-slli-subtable indices  8 32))
       (slli-subtable-2 (materialize-slli-subtable indices 16 32))
       (slli-subtable-3 (materialize-slli-subtable indices 24 32))
       ;; Perform lookups
       (u8-0 (tuple-lookup u8-0 shift-amount slli-subtable-0))
       (u8-1 (tuple-lookup u8-1 shift-amount slli-subtable-1))
       (u8-2 (tuple-lookup u8-2 shift-amount slli-subtable-2))
       (u8-3 (tuple-lookup u8-3 shift-amount slli-subtable-3)))
      ;; Combine
      (+ (* u8-3 (expt 2 24)) 
         (* u8-2 (expt 2 16)) 
         (* u8-1 (expt 2  8)) 
            u8-0	    )))


(defthm sll-32-sll-semantics-32-equiv
 (equal (sll-32 x y) (sll-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (sll-semantics-32 sll-32) ((:e expt) (:e create-tuple-indices) slli-rust)))))

(defthm sll-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (sll-32 x y) 
	         (mod (ash x (part-select y :low 0 :width 5))
		      (expt 2 32)))))
