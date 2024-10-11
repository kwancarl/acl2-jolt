(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "../subtables/sll")

;;; 32-BIT VERSION

;; SLL-semantics-32
(define sll-semantics-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; CHUNK
       (x8-3 (part-select x :low  0 :width 8))
       (x8-2 (part-select x :low  8 :width 8))
       (x8-1 (part-select x :low 16 :width 8))
       (x8-0 (part-select x :low 24 :width 8))
       (y8-3 (part-select y :low 0 :width 8))
       ;; Lookup semantics
       (u8-3 (slli-rust x8-3 y8-3  0 32)) 
       (u8-2 (slli-rust x8-2 y8-3  8 32))
       (u8-1 (slli-rust x8-1 y8-3 16 32))
       (u8-0 (slli-rust x8-0 y8-3 24 32)))
      ;; Combine
      (+ (* u8-0 (expt 2 24))
         (* u8-1 (expt 2 16))
         (* u8-2 (expt 2  8))
            u8-3	        )))

;; sll-32 is supposed to shift x left by (mod y 32), then truncate to 32 bits
(gl::def-gl-thm sll-semantics-32-correctness
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
 :concl (equal (sll-semantics-32 x y) 
	       (loghead 32 (ash x (mod y 32))))
 :g-bindings (gl::auto-bindings (:mix (:nat y 32) (:nat x 32))))

;; SLL-32
(define sll-32 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p 32 y)) 0)
       ;; Chunk
       (x8-3 (part-select x :low  0 :width 8))
       (x8-2 (part-select x :low  8 :width 8))
       (x8-1 (part-select x :low 16 :width 8))
       (x8-0 (part-select x :low 24 :width 8))
       (y8-3 (part-select y :low 0 :width 8))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (slli-subtable-3 (materialize-slli-subtable indices  0 32))
       (slli-subtable-2 (materialize-slli-subtable indices  8 32))
       (slli-subtable-1 (materialize-slli-subtable indices 16 32))
       (slli-subtable-0 (materialize-slli-subtable indices 24 32))
       ;; Perform lookups
       (u8-3 (tuple-lookup x8-3 y8-3 slli-subtable-3))
       (u8-2 (tuple-lookup x8-2 y8-3 slli-subtable-2))
       (u8-1 (tuple-lookup x8-1 y8-3 slli-subtable-1))
       (u8-0 (tuple-lookup x8-0 y8-3 slli-subtable-0)))
      ;; Combine
      (+ (* u8-0 (expt 2 24)) 
         (* u8-1 (expt 2 16)) 
         (* u8-2 (expt 2  8)) 
            u8-3	        )))

(defthm sll-32-sll-semantics-32-equiv
 (equal (sll-32 x y) (sll-semantics-32 x y))
 :hints (("Goal" :in-theory (e/d (sll-semantics-32 sll-32) ((:e expt) (:e create-tuple-indices) slli-rust)))))

(defthm sll-32-correctness
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
          (equal (sll-32 x y) 
	         (loghead 32 (ash x (mod y 32))))))


;;; 64-BIT VERSION

;; SLL-semantics-64
(define sll-semantics-64 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; CHUNK
       (x8-7 (part-select x :low  0 :width 8))
       (x8-6 (part-select x :low  8 :width 8))
       (x8-5 (part-select x :low 16 :width 8))
       (x8-4 (part-select x :low 24 :width 8))
       (x8-3 (part-select x :low 32 :width 8))
       (x8-2 (part-select x :low 40 :width 8))
       (x8-1 (part-select x :low 48 :width 8))
       (x8-0 (part-select x :low 56 :width 8))
       (y8-7 (part-select y :low 0 :width 8))
       ;; Lookup semantics
       (u8-7 (slli-rust x8-7 y8-7  0 64)) 
       (u8-6 (slli-rust x8-6 y8-7  8 64))
       (u8-5 (slli-rust x8-5 y8-7 16 64))
       (u8-4 (slli-rust x8-4 y8-7 24 64))
       (u8-3 (slli-rust x8-3 y8-7 32 64))
       (u8-2 (slli-rust x8-2 y8-7 40 64))
       (u8-1 (slli-rust x8-1 y8-7 48 64))
       (u8-0 (slli-rust x8-0 y8-7 56 64)))
      ;; Combine
      (+ (* u8-0 (expt 2 56))
         (* u8-1 (expt 2 48))
         (* u8-2 (expt 2 40))
         (* u8-3 (expt 2 32))
         (* u8-4 (expt 2 24))
         (* u8-5 (expt 2 16))
         (* u8-6 (expt 2  8))
            u8-7	        )))

;; sll-64 is supposed to shift x left by (mod y 64), then truncate to 64 bits
(gl::def-gl-thm sll-semantics-64-correctness
 :hyp (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
 :concl (equal (sll-semantics-64 x y) 
	       (loghead 64 (ash x (mod y 64))))
 :g-bindings (gl::auto-bindings (:mix (:nat y 64) (:nat x 64))))

;; SLL-64
(define sll-64 (x y)
  :verify-guards nil
  (b* (((unless (unsigned-byte-p 64 x)) 0)
       ((unless (unsigned-byte-p 64 y)) 0)
       ;; Chunk
       (x8-7 (part-select x :low  0 :width 8))
       (x8-6 (part-select x :low  8 :width 8))
       (x8-5 (part-select x :low 16 :width 8))
       (x8-4 (part-select x :low 24 :width 8))
       (x8-3 (part-select x :low 32 :width 8))
       (x8-2 (part-select x :low 40 :width 8))
       (x8-1 (part-select x :low 48 :width 8))
       (x8-0 (part-select x :low 56 :width 8))
       (y8-7 (part-select y :low 0 :width 8))
       ;; Materialize subtables
       (indices (create-tuple-indices (expt 2 8) (expt 2 8)))
       (slli-subtable-7 (materialize-slli-subtable indices  0 64))
       (slli-subtable-6 (materialize-slli-subtable indices  8 64))
       (slli-subtable-5 (materialize-slli-subtable indices 16 64))
       (slli-subtable-4 (materialize-slli-subtable indices 24 64))
       (slli-subtable-3 (materialize-slli-subtable indices 32 64))
       (slli-subtable-2 (materialize-slli-subtable indices 40 64))
       (slli-subtable-1 (materialize-slli-subtable indices 48 64))
       (slli-subtable-0 (materialize-slli-subtable indices 56 64))
       ;; Perform lookups
       (u8-7 (tuple-lookup x8-7 y8-7 slli-subtable-7))
       (u8-6 (tuple-lookup x8-6 y8-7 slli-subtable-6))
       (u8-5 (tuple-lookup x8-5 y8-7 slli-subtable-5))
       (u8-4 (tuple-lookup x8-4 y8-7 slli-subtable-4))
       (u8-3 (tuple-lookup x8-3 y8-7 slli-subtable-3))
       (u8-2 (tuple-lookup x8-2 y8-7 slli-subtable-2))
       (u8-1 (tuple-lookup x8-1 y8-7 slli-subtable-1))
       (u8-0 (tuple-lookup x8-0 y8-7 slli-subtable-0)))
      ;; Combine
      (+ (* u8-0 (expt 2 56)) 
         (* u8-1 (expt 2 48)) 
         (* u8-2 (expt 2 40)) 
         (* u8-3 (expt 2 32)) 
         (* u8-4 (expt 2 24)) 
         (* u8-5 (expt 2 16)) 
         (* u8-6 (expt 2  8)) 
            u8-7	        )))

(defthm sll-64-sll-semantics-64-equiv
 (equal (sll-64 x y) (sll-semantics-64 x y))
 :hints (("Goal" :in-theory (e/d (sll-semantics-64 sll-64) ((:e expt) (:e create-tuple-indices) slli-rust)))))

(defthm sll-64-correctness
 (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
          (equal (sll-64 x y) 
	         (loghead 64 (ash x (mod y 64))))))
