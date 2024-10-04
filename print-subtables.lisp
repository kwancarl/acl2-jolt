(in-package "ACL2")

(include-book "misc/file-io" :dir :system)

(include-book "subtables/and")
(include-book "subtables/eq")
(include-book "subtables/eq-abs")
(include-book "subtables/left-msb")
(include-book "subtables/lt-abs")
(include-book "subtables/ltu")
(include-book "subtables/or")
(include-book "subtables/right-msb")
(include-book "subtables/sll")
(include-book "subtables/sra-sign")
(include-book "subtables/srl")
(include-book "subtables/xor")
(include-book "subtables/identity")
(include-book "subtables/sign-extend")
(include-book "subtables/truncate-overflow")

(defconst *indices* (create-tuple-indices 255 255))

(defconst *output-dir* "validation/subtables")

(write-list (materialize-and-subtable *indices*)
              (concatenate 'string *output-dir* "/and_subtable_acl2.txt")
              'top-level
              state)

(write-list (materialize-eq-subtable *indices*)
              (concatenate 'string *output-dir* "/eq_subtable_acl2.txt")
              'top-level
              state)

(write-list (materialize-eq-abs-subtable-8 *indices*)
              (concatenate 'string *output-dir* "/eq_abs_subtable_acl2.txt")
              'top-level
              state)

(write-list (materialize-left-msb-subtable-8 *indices*)
              (concatenate 'string *output-dir* "/left_msb_subtable_acl2.txt")
              'top-level
              state)

(write-list (materialize-lt-abs-subtable-8 *indices*)
              (concatenate 'string *output-dir* "/lt_abs_subtable_acl2.txt")
              'top-level
              state)

(write-list (materialize-ltu-subtable *indices*)
              (concatenate 'string *output-dir* "/ltu_subtable_acl2.txt")
              'top-level
              state)

(write-list (materialize-ior-subtable *indices*)
              (concatenate 'string *output-dir* "/or_subtable_acl2.txt")
              'top-level
              state)

(write-list (materialize-right-msb-subtable-8 *indices*)
              (concatenate 'string *output-dir* "/right_msb_subtable_acl2.txt")
              'top-level
              state)

(write-list (materialize-xor-subtable *indices*)
              (concatenate 'string *output-dir* "/xor_subtable_acl2.txt")
              'top-level
              state)

;; Shift subtables

(write-list (materialize-slli-subtable-prime *indices* (* 8 0) 5)
              (concatenate 'string *output-dir* "/sll_subtable_0_32_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 1) 5)
              (concatenate 'string *output-dir* "/sll_subtable_1_32_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 2) 5)
              (concatenate 'string *output-dir* "/sll_subtable_2_32_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 3) 5)
              (concatenate 'string *output-dir* "/sll_subtable_3_32_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 0) 6)
              (concatenate 'string *output-dir* "/sll_subtable_0_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 1) 6)
              (concatenate 'string *output-dir* "/sll_subtable_1_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 2) 6)
              (concatenate 'string *output-dir* "/sll_subtable_2_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 3) 6)
              (concatenate 'string *output-dir* "/sll_subtable_3_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 4) 6)
              (concatenate 'string *output-dir* "/sll_subtable_4_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 5) 6)
              (concatenate 'string *output-dir* "/sll_subtable_5_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 6) 6)
              (concatenate 'string *output-dir* "/sll_subtable_6_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-slli-subtable-prime *indices* (* 8 7) 6)
              (concatenate 'string *output-dir* "/sll_subtable_7_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-sra-sign-subtable-prime *indices* 32)
              (concatenate 'string *output-dir* "/sra_sign_subtable_32_acl2.txt")
              'top-level
              state)

(write-list (materialize-sra-sign-subtable-prime *indices* 64)
              (concatenate 'string *output-dir* "/sra_sign_subtable_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 0) 5)
              (concatenate 'string *output-dir* "/srl_subtable_0_32_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 1) 5)
              (concatenate 'string *output-dir* "/srl_subtable_1_32_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 2) 5)
              (concatenate 'string *output-dir* "/srl_subtable_2_32_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 3) 5)
              (concatenate 'string *output-dir* "/srl_subtable_3_32_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 0) 6)
              (concatenate 'string *output-dir* "/srl_subtable_0_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 1) 6)
              (concatenate 'string *output-dir* "/srl_subtable_1_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 2) 6)
              (concatenate 'string *output-dir* "/srl_subtable_2_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 3) 6)
              (concatenate 'string *output-dir* "/srl_subtable_3_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 4) 6)
              (concatenate 'string *output-dir* "/srl_subtable_4_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 5) 6)
              (concatenate 'string *output-dir* "/srl_subtable_5_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 6) 6)
              (concatenate 'string *output-dir* "/srl_subtable_6_64_acl2.txt")
              'top-level
              state)

(write-list (materialize-srli-subtable-prime *indices* (* 8 7) 6)
              (concatenate 'string *output-dir* "/srl_subtable_7_64_acl2.txt")
              'top-level
              state)


;; These subtables have the form `(x . val)` instead of `((x . y) . val)`
(defconst *range* (1- (expt 2 16)))

(write-list (materialize-identity-subtable *range*)
              (concatenate 'string *output-dir* "/identity_subtable_acl2.txt")
              'top-level
              state)

(write-list (materialize-sign-extend-subtable *range* 8)
              (concatenate 'string *output-dir* "/sign_extend_subtable_8_acl2.txt")
              'top-level
              state)

(write-list (materialize-sign-extend-subtable *range* 16)
              (concatenate 'string *output-dir* "/sign_extend_subtable_16_acl2.txt")
              'top-level
              state)

(write-list (materialize-truncate-subtable *range* (1- (expt 2 8)))
              (concatenate 'string *output-dir* "/truncate_overflow_subtable_8_acl2.txt")
              'top-level
              state)

(write-list (materialize-truncate-subtable *range* 0)
              (concatenate 'string *output-dir* "/truncate_overflow_subtable_32_acl2.txt")
              'top-level
              state)