(in-package "ACL2")

(include-book "misc/file-io" :dir :system)

(include-book "centaur/bitops/part-select" :dir :system)

(include-book "centaur/gl/gl" :dir :system)

(include-book "instructions/add")
(include-book "instructions/and")
(include-book "instructions/beq")
(include-book "instructions/bge")
(include-book "instructions/bgeu")
(include-book "instructions/bne")
(include-book "instructions/lb")
(include-book "instructions/lh")
(include-book "instructions/or")
(include-book "instructions/sb")
(include-book "instructions/sh")
(include-book "instructions/sll")
(include-book "instructions/slt")
(include-book "instructions/sltu")
(include-book "instructions/sra")
(include-book "instructions/srl")
(include-book "instructions/sub")
(include-book "instructions/sw")
(include-book "instructions/xor")

;; Output directory
(defconst *output-dir* "validation/instructions")

;; Fuzzing inputs for instructions (32-bit)
(defconst *test-inputs-32*
  '((#x00000000 . #x00000000)  ; Both zero
    (#xFFFFFFFF . #xFFFFFFFF)  ; Both maximum value
    (#x00000001 . #x00000001)  ; Both one
    (#x7FFFFFFF . #x7FFFFFFF)  ; Both middle value
    (#x00000000 . #xFFFFFFFF)  ; Min and max
    (#xFFFFFFFF . #x00000000)  ; Max and min
    (#x80000000 . #x80000000)  ; Both minimum negative (signed interpretation)
    (#x7FFFFFFF . #x7FFFFFFF)  ; Both maximum positive (signed interpretation)
    (#xAAAAAAAA . #x55555555)  ; Alternating bit patterns
    (#x55555555 . #xAAAAAAAA)  ; Inverse alternating bit patterns
    (#xFFFF0000 . #x0000FFFF)  ; Upper half set, lower half set
    (#x0000FFFF . #xFFFF0000)  ; Lower half set, upper half set
    (#x12345678 . #x87654321)  ; Random-looking values
    (#xDEADBEEF . #xCAFEBABE)  ; Common debug values
    (#x00000001 . #xFFFFFFFF)  ; Smallest positive and largest value
    (#xFFFFFFFF . #x00000001)  ; Largest value and smallest positive
    (#x80000000 . #x7FFFFFFF)  ; Minimum negative and maximum positive (signed)
    (#x01234567 . #x89ABCDEF)  ; Ascending and descending hex digits
    (#xF0F0F0F0 . #x0F0F0F0F)  ; Alternating nibble patterns
    (#x00FF00FF . #xFF00FF00))) ; Alternating byte patterns

;; Fuzzing inputs for instructions (64-bit)
(defconst *test-inputs-64*
  '((#x0000000000000000 . #x0000000000000000)  ; Both zero
    (#xFFFFFFFFFFFFFFFF . #xFFFFFFFFFFFFFFFF)  ; Both maximum value
    (#x0000000000000001 . #x0000000000000001)  ; Both one
    (#x7FFFFFFFFFFFFFFF . #x7FFFFFFFFFFFFFFF)  ; Both middle value
    (#x0000000000000000 . #xFFFFFFFFFFFFFFFF)  ; Min and max
    (#xFFFFFFFFFFFFFFFF . #x0000000000000000)  ; Max and min
    (#x8000000000000000 . #x8000000000000000)  ; Both minimum negative (signed interpretation)
    (#x7FFFFFFFFFFFFFFF . #x7FFFFFFFFFFFFFFF)  ; Both maximum positive (signed interpretation)
    (#xAAAAAAAAAAAAAAAA . #x5555555555555555)  ; Alternating bit patterns
    (#x5555555555555555 . #xAAAAAAAAAAAAAAAA)  ; Inverse alternating bit patterns
    (#xFFFFFFFF00000000 . #x00000000FFFFFFFF)  ; Upper half set, lower half set
    (#x00000000FFFFFFFF . #xFFFFFFFF00000000)  ; Lower half set, upper half set
    (#x123456789ABCDEF0 . #xFEDCBA9876543210)  ; Random-looking values
    (#xDEADBEEFCAFEBABE . #xBADC0FFEEBADF00D)  ; Common debug values
    (#x0000000000000001 . #xFFFFFFFFFFFFFFFF)  ; Smallest positive and largest value
    (#xFFFFFFFFFFFFFFFF . #x0000000000000001)  ; Largest value and smallest positive
    (#x8000000000000000 . #x7FFFFFFFFFFFFFFF)  ; Minimum negative and maximum positive (signed)
    (#x0123456789ABCDEF . #xFEDCBA9876543210)  ; Ascending and descending hex digits
    (#xF0F0F0F0F0F0F0F0 . #x0F0F0F0F0F0F0F0F)  ; Alternating nibble patterns
    (#x00FF00FF00FF00FF . #xFF00FF00FF00FF00))) ; Alternating byte patterns

;; For each test input, print the inputs along with the result of the instruction.

;; Future work: turn this process into a macro so that we don't have to repeat ourselves

;; ===================

;; Function to generate test results for add-32
(defun generate-add-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (add-semantics-32 x y)))
      (cons (cons input result)
            (generate-add-32-results (cdr inputs))))))

;; Generate and write results for add-32
(write-list (generate-add-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/add_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for add-64
(defun generate-add-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (add-semantics-64 x y)))
      (cons (cons input result)
            (generate-add-64-results (cdr inputs))))))

;; Generate and write results for add-64
(write-list (generate-add-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/add_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for sub-32
(defun generate-sub-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (sub-semantics-32 x y)))
      (cons (cons input result)
            (generate-sub-32-results (cdr inputs))))))

;; Generate and write results for sub-32
(write-list (generate-sub-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/sub_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for sub-64
(defun generate-sub-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (sub-semantics-64 x y)))
      (cons (cons input result)
            (generate-sub-64-results (cdr inputs))))))

;; Generate and write results for sub-64
(write-list (generate-sub-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/sub_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for and-32
(defun generate-and-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (and-semantics-32 x y)))
      (cons (cons input result)
            (generate-and-32-results (cdr inputs))))))

;; Generate and write results for and-32
(write-list (generate-and-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/and_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for and-64
(defun generate-and-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (and-semantics-64 x y)))
      (cons (cons input result)
            (generate-and-64-results (cdr inputs))))))

;; Generate and write results for and-64
(write-list (generate-and-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/and_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for or-32
(defun generate-or-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (or-semantics-32 x y)))
      (cons (cons input result)
            (generate-or-32-results (cdr inputs))))))

;; Generate and write results for or-32
(write-list (generate-or-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/or_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for or-64
(defun generate-or-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (or-semantics-64 x y)))
      (cons (cons input result)
            (generate-or-64-results (cdr inputs))))))

;; Generate and write results for or-64
(write-list (generate-or-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/or_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for xor-32
(defun generate-xor-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (xor-semantics-32 x y)))
      (cons (cons input result)
            (generate-xor-32-results (cdr inputs))))))

;; Generate and write results for xor-32
(write-list (generate-xor-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/xor_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for xor-64
(defun generate-xor-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (xor-semantics-64 x y)))
      (cons (cons input result)
            (generate-xor-64-results (cdr inputs))))))

;; Generate and write results for xor-64
(write-list (generate-xor-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/xor_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for beq-32
(defun generate-beq-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (beq-semantics-32 x y)))
      (cons (cons input result)
            (generate-beq-32-results (cdr inputs))))))

;; Generate and write results for beq-32
(write-list (generate-beq-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/beq_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for beq-64
(defun generate-beq-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (beq-semantics-64 x y)))
      (cons (cons input result)
            (generate-beq-64-results (cdr inputs))))))

;; Generate and write results for beq-64
(write-list (generate-beq-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/beq_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for bne-32
(defun generate-bne-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (bne-semantics-32 x y)))
      (cons (cons input result)
            (generate-bne-32-results (cdr inputs))))))

;; Generate and write results for bne-32
(write-list (generate-bne-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/bne_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for bne-64
(defun generate-bne-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (bne-semantics-64 x y)))
      (cons (cons input result)
            (generate-bne-64-results (cdr inputs))))))

;; Generate and write results for bne-64
(write-list (generate-bne-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/bne_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for bge-32
(defun generate-bge-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (bge-semantics-32 x y)))
      (cons (cons input result)
            (generate-bge-32-results (cdr inputs))))))

;; Generate and write results for bge-32
(write-list (generate-bge-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/bge_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for bge-64
(defun generate-bge-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (bge-semantics-64 x y)))
      (cons (cons input result)
            (generate-bge-64-results (cdr inputs))))))

;; Generate and write results for bge-64
(write-list (generate-bge-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/bge_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for bgeu-32
(defun generate-bgeu-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (bgeu-semantics-32 x y)))
      (cons (cons input result)
            (generate-bgeu-32-results (cdr inputs))))))

;; Generate and write results for bgeu-32
(write-list (generate-bgeu-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/bgeu_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for bgeu-64
(defun generate-bgeu-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (bgeu-semantics-64 x y)))
      (cons (cons input result)
            (generate-bgeu-64-results (cdr inputs))))))

;; Generate and write results for bgeu-64
(write-list (generate-bgeu-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/bgeu_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for slt-32
(defun generate-slt-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (slt-semantics-32 x y)))
      (cons (cons input result)
            (generate-slt-32-results (cdr inputs))))))

;; Generate and write results for slt-32
(write-list (generate-slt-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/slt_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for slt-64
(defun generate-slt-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (slt-semantics-64 x y)))
      (cons (cons input result)
            (generate-slt-64-results (cdr inputs))))))

;; Generate and write results for slt-64
(write-list (generate-slt-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/slt_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for sltu-32
(defun generate-sltu-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (sltu-semantics-32 x y)))
      (cons (cons input result)
            (generate-sltu-32-results (cdr inputs))))))

;; Generate and write results for sltu-32
(write-list (generate-sltu-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/sltu_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for sltu-64
(defun generate-sltu-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (sltu-semantics-64 x y)))
      (cons (cons input result)
            (generate-sltu-64-results (cdr inputs))))))

;; Generate and write results for sltu-64
(write-list (generate-sltu-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/sltu_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Note: LB takes only one argument

;; Function to generate test results for lb-32
(defun generate-lb-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (lb-semantics-32 x)))
      (cons (cons x result)
            (generate-lb-32-results (cdr inputs))))))

;; Generate and write results for lb-32
(write-list (generate-lb-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/lb_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for lb-64
(defun generate-lb-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (lb-semantics-64 x)))
      (cons (cons x result)
            (generate-lb-64-results (cdr inputs))))))

;; Generate and write results for lb-64
(write-list (generate-lb-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/lb_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Note: LH takes only one argument

;; Function to generate test results for lh-32
(defun generate-lh-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (lh-semantics-32 x)))
      (cons (cons x result)
            (generate-lh-32-results (cdr inputs))))))

;; Generate and write results for lh-32
(write-list (generate-lh-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/lh_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for lh-64
(defun generate-lh-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (lh-semantics-64 x)))
      (cons (cons x result)
            (generate-lh-64-results (cdr inputs))))))

;; Generate and write results for lh-64
(write-list (generate-lh-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/lh_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Note: SB takes only one argument

;; Function to generate test results for sb-32
(defun generate-sb-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (sb-semantics-32 x)))
      (cons (cons x result)
            (generate-sb-32-results (cdr inputs))))))

;; Generate and write results for sb-32
(write-list (generate-sb-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/sb_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for sb-64
(defun generate-sb-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (sb-semantics-64 x)))
      (cons (cons x result)
            (generate-sb-64-results (cdr inputs))))))

;; Generate and write results for sb-64
(write-list (generate-sb-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/sb_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Note: SH takes only one argument

;; Function to generate test results for sh-32
(defun generate-sh-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (sh-semantics-32 x)))
      (cons (cons x result)
            (generate-sh-32-results (cdr inputs))))))

;; Generate and write results for sh-32
(write-list (generate-sh-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/sh_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for sh-64
(defun generate-sh-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (sh-semantics-64 x)))
      (cons (cons x result)
            (generate-sh-64-results (cdr inputs))))))

;; Generate and write results for sh-64
(write-list (generate-sh-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/sh_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Note: SW takes only one argument

;; Function to generate test results for sw-32
(defun generate-sw-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (sw-semantics-32 x)))
      (cons (cons x result)
            (generate-sw-32-results (cdr inputs))))))

;; Generate and write results for sw-32
(write-list (generate-sw-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/sw_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for sw-64
(defun generate-sw-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
          ;;  (y (cdr input))
           (result (sw-semantics-64 x)))
      (cons (cons x result)
            (generate-sw-64-results (cdr inputs))))))

;; Generate and write results for sw-64
(write-list (generate-sw-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/sw_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for sll-32
(defun generate-sll-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (sll-semantics-32 x y)))
      (cons (cons input result)
            (generate-sll-32-results (cdr inputs))))))

;; Generate and write results for sll-32
(write-list (generate-sll-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/sll_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for sll-64
(defun generate-sll-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (sll-semantics-64 x y)))
      (cons (cons input result)
            (generate-sll-64-results (cdr inputs))))))

;; Generate and write results for sll-64
(write-list (generate-sll-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/sll_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for srl-32
(defun generate-srl-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (srl-semantics-32 x y)))
      (cons (cons input result)
            (generate-srl-32-results (cdr inputs))))))

;; Generate and write results for srl-32
(write-list (generate-srl-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/srl_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for srl-64
(defun generate-srl-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (srl-semantics-64 x y)))
      (cons (cons input result)
            (generate-srl-64-results (cdr inputs))))))

;; Generate and write results for srl-64
(write-list (generate-srl-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/srl_instruction_64_acl2.txt")
            'top-level
            state)

;; ===================

;; Function to generate test results for sra-32
(defun generate-sra-32-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (sra-semantics-32 x y)))
      (cons (cons input result)
            (generate-sra-32-results (cdr inputs))))))

;; Generate and write results for sra-32
(write-list (generate-sra-32-results *test-inputs-32*)
            (concatenate 'string *output-dir* "/sra_instruction_32_acl2.txt")
            'top-level
            state)

;; Function to generate test results for sra-64
(defun generate-sra-64-results (inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (x (car input))
           (y (cdr input))
           (result (sra-semantics-64 x y)))
      (cons (cons input result)
            (generate-sra-64-results (cdr inputs))))))

;; Generate and write results for sra-64
(write-list (generate-sra-64-results *test-inputs-64*)
            (concatenate 'string *output-dir* "/sra_instruction_64_acl2.txt")
            'top-level
            state)