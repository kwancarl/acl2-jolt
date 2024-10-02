(in-package "ACL2")

(include-book "misc/file-io" :dir :system)

(include-book "subtables/and")
(include-book "subtables/eq")
(include-book "subtables/eq_abs")
(include-book "subtables/identity")
(include-book "subtables/left_msb")
(include-book "subtables/lt_abs")
(include-book "subtables/ltu")
(include-book "subtables/or")
(include-book "subtables/right_msb")
(include-book "subtables/sign_extend")
(include-book "subtables/sll")
(include-book "subtables/srl")
(include-book "subtables/sra-sign")
(include-book "subtables/truncate_overflow")
(include-book "subtables/xor")

;; not certified is ok


(set-state-ok t)

;; (mv-let (chan state)
;;         (open-output-channel "tmp.out" :character state)
;;         (set-standard-co chan state))

;; (set-standard-co (standard-co state) state)

;; (ld "tmp.lisp")

;; (set-standard-co *standard-co* state)
;; (close-output-channel (proofs-co state) state)
;; (set-proofs-co *standard-co* state)

;; (mv-let (chan state)
;;         (open-output-channel "tmp.out" :character state)
;;         (assign tmp-channel chan))
;; (ld "tmp.lisp" 
;;             ;;    :proofs-co (@ tmp-channel)
;;                :standard-co (@ tmp-channel))
;; (close-output-channel (@ tmp-channel) state)

(mv-let (chan state)
        (open-output-channel "output.txt" :character state)
        (assign tmp-channel chan))

;; (mv-let
;;     (state)
;;     (let ((lst (materialize-and-subtable (create-tuple-indices 3 3))))
;;       (fmt! "~*0" `("Whoa!" "~x*~%" "~x*~%" "~x*~%" ,lst)
;;             :state state
;;             :channel (@ tmp-channel)))
;;     (close-output-channel (@ tmp-channel) state))

;; (mv-let
;;     (?discard state)
;;     (let ((lst (materialize-and-subtable (create-tuple-indices 3 3))))
;;       (fmx "~*0" `("Whoa!" "~x*~%" "~x*~%" "~x*~%" ,lst)))
;;     (declare (ignore ?discard))
;;     (close-output-channel (@ tmp-channel) state))

;; (good-bye)

;; (let ((lst (materialize-and-subtable (create-tuple-indices 3 3)))) ; a true-list whose elements we exhibit
    ;; (fmx "~*0"
    ;;     `("Whoa!"          ; what to print if there's nothing to print
    ;;     "~x*~%"           ; how to print the last element
    ;;     "~x*~%"       ; how to print the 2nd to last element
    ;;     "~x*~%"          ; how to print all other elements
    ;;     ,lst)))          ; the list of elements to print