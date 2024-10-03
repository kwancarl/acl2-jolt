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

(defconst *indices* (create-tuple-indices 255 255))

(write-list (materialize-and-subtable *indices*)
              "validation/and_subtable_acl2.txt"
              'top-level
              state)

(write-list (materialize-eq-subtable *indices*)
              "validation/eq_subtable_acl2.txt"
              'top-level
              state)

(write-list (materialize-eq-abs-subtable-8 *indices*)
              "validation/eq_abs_subtable_acl2.txt"
              'top-level
              state)

(write-list (materialize-left-msb-subtable-8 *indices*)
              "validation/left_msb_subtable_acl2.txt"
              'top-level
              state)

(write-list (materialize-lt-abs-subtable-8 *indices*)
              "validation/lt_abs_subtable_acl2.txt"
              'top-level
              state)

(write-list (materialize-ltu-subtable *indices*)
              "validation/ltu_subtable_acl2.txt"
              'top-level
              state)

(write-list (materialize-ior-subtable *indices*)
              "validation/or_subtable_acl2.txt"
              'top-level
              state)

(write-list (materialize-right-msb-subtable-8 *indices*)
              "validation/right_msb_subtable_acl2.txt"
              'top-level
              state)

(write-list (materialize-xor-subtable *indices*)
              "validation/xor_subtable_acl2.txt"
              'top-level
              state)

(defconst *shift-indices-32* (create-tuple-indices 255 31))

(write-list (materialize-slli-subtable *shift-indices-32* (* 8 0))
              "validation/sll_subtable_0_32_acl2.txt"
              'top-level
              state)

(write-list (materialize-slli-subtable *shift-indices-32* (* 8 1))
              "validation/sll_subtable_1_32_acl2.txt"
              'top-level
              state)

(write-list (materialize-slli-subtable *shift-indices-32* (* 8 2))
              "validation/sll_subtable_2_32_acl2.txt"
              'top-level
              state)

(write-list (materialize-slli-subtable *shift-indices-32* (* 8 3))
              "validation/sll_subtable_3_32_acl2.txt"
              'top-level
              state)

(write-list (materialize-sra-sign-subtable-8 *shift-indices-32*)
              "validation/sra_sign_subtable_8_acl2.txt"
              'top-level
              state)

(write-list (materialize-srli-subtable *shift-indices-32* (* 8 0))
              "validation/srl_subtable_0_32_acl2.txt"
              'top-level
              state)

(write-list (materialize-srli-subtable *shift-indices-32* (* 8 1))
              "validation/srl_subtable_1_32_acl2.txt"
              'top-level
              state)

(write-list (materialize-srli-subtable *shift-indices-32* (* 8 2))
              "validation/srl_subtable_2_32_acl2.txt"
              'top-level
              state)

(write-list (materialize-srli-subtable *shift-indices-32* (* 8 3))
              "validation/srl_subtable_3_32_acl2.txt"
              'top-level
              state)


;; These subtables have the form `(x . val)` instead of `((x . y) . val)`

(include-book "subtables/identity")
(include-book "subtables/sign-extend")
(include-book "subtables/truncate-overflow")

(defconst *range* (1- (expt 2 16)))

(write-list (materialize-identity-subtable *range*)
              "validation/identity_subtable_acl2.txt"
              'top-level
              state)

(write-list (materialize-sign-extend-subtable *range* 8)
              "validation/sign_extend_subtable_8_acl2.txt"
              'top-level
              state)

(write-list (materialize-sign-extend-subtable *range* 16)
              "validation/sign_extend_subtable_16_acl2.txt"
              'top-level
              state)

;; 8 MOD 16 = 8
(write-list (materialize-truncate-subtable *range* (1- (expt 2 8)))
              "validation/truncate_overflow_subtable_8_acl2.txt"
              'top-level
              state)

;; 32 MOD 16 = 0
(write-list (materialize-truncate-subtable *range* 0)
              "validation/truncate_overflow_subtable_32_acl2.txt"
              'top-level
              state)