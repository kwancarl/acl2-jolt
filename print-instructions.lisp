(in-package "ACL2")

(include-book "misc/file-io" :dir :system)

(include-book "centaur/bitops/part-select" :dir :system)

(include-book "centaur/gl/gl" :dir :system)

;; (include-book "centaur/fgl/top" :dir :system)
;; (value-triple (acl2::tshell-ensure))

;; (include-book "instructions/add")
;; (include-book "instructions/and")
;; (include-book "instructions/beq")
;; (include-book "instructions/bge")
;; (include-book "instructions/bgeu")
;; (include-book "instructions/bne")
;; (include-book "instructions/lb")
;; (include-book "instructions/lh")
;; (include-book "instructions/or")
;; (include-book "instructions/sb")
;; (include-book "instructions/sh")
(include-book "instructions/sll")
;; (include-book "instructions/slt")
;; (include-book "instructions/sltu")
(include-book "instructions/sra")
(include-book "instructions/srl")
;; (include-book "instructions/sub")
;; (include-book "instructions/sw")
;; (include-book "instructions/xor")

;; Output directory
(defconst *output-dir* "validation/instructions")

;; Fuzzing inputs for instructions (32-bit)
(defconst *test-inputs*
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

;; For each test input, print the inputs along with the result of the instruction.
;; It should use (write-list ...) to print to file, plus the format should be `((x . y) . result)`

;; Do this for the instructions sll-32, srl-32, and sra-32.

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
(write-list (generate-sra-32-results *test-inputs*)
            (concatenate 'string *output-dir* "/sra_instruction_32_acl2.txt")
            'top-level
            state)

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
(write-list (generate-srl-32-results *test-inputs*)
            (concatenate 'string *output-dir* "/srl_instruction_32_acl2.txt")
            'top-level
            state)

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
(write-list (generate-sll-32-results *test-inputs*)
            (concatenate 'string *output-dir* "/sll_instruction_32_acl2.txt")
            'top-level
            state)