(in-package "ACL2")
(include-book "std/io/top" :dir :system)

(set-state-ok t)

;; (defun process-file (filename state)
;;   (mv-let
;;    (channel state)
;;    (open-input-channel filename :object state)
;;    (mv-let (result state)
;;            (process-file1 nil channel state) ;see below
;;            (let ((state (close-input-channel channel state)))
;;              (mv result state)))))

;; (mv-let (chan state)
;;         (open-output-channel "tmp.out" :character state)
;;         (set-standard-co chan state))

;; (set-standard-co (standard-co state) state)

;; (ld "tmp.lisp")

;; (set-standard-co *standard-co* state)
;; (close-output-channel (proofs-co state) state)
;; (set-proofs-co *standard-co* state)

(mv-let (chan state)
        (open-output-channel "tmp.out" :character state)
        (assign tmp-channel chan))
(ld "tmp.lisp" 
            ;;    :proofs-co (@ tmp-channel)
               :standard-co (@ tmp-channel))
(close-output-channel (@ tmp-channel) state)

(good-bye)

(let ((lst (materialize-and-subtable (create-tuple-indices 3 3)))) ; a true-list whose elements we exhibit
    (fmx "~*0"
        `("Whoa!"          ; what to print if there's nothing to print
        "~x*~%"           ; how to print the last element
        "~x*~%"       ; how to print the 2nd to last element
        "~x*~%"          ; how to print all other elements
        ,lst)))          ; the list of elements to print