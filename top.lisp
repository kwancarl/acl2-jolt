;; This is the top-level file for the ACL2 books in this directory.
;; To certify this repository, we only need to run "cert.pl" on this file.
(in-package "ACL2")

;; Subtables
(include-book "subtables/and")
(include-book "subtables/eq")
(include-book "subtables/eq-abs")
(include-book "subtables/identity")
(include-book "subtables/left-msb")
(include-book "subtables/lt-abs")
(include-book "subtables/ltu")
(include-book "subtables/or")
(include-book "subtables/right-msb")
(include-book "subtables/sign-extend")
(include-book "subtables/sll")
(include-book "subtables/srl")
(include-book "subtables/sra-sign")
(include-book "subtables/truncate-overflow")
(include-book "subtables/xor")

;; Instructions
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