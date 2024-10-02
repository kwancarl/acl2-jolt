;; Validation of subtables and instructions
(in-package "ACL2")
;; (include-book "io-utilities" :dir :system)
(include-book "std/io/top" :dir :system)
;; (include-book "std/util/bstar" :dir :system)
;; (include-book "std/util/define" :dir :system)

(include-book "subtables/and")

;; Function to format a single subtable entry
(defun format-subtable-entry (entry)
  (declare (xargs :mode :program))
  (let ((input (car entry))
        (output (cdr entry)))
    (concatenate 'string
                 (str::nat-to-dec-string (car input)) ","
                 (str::nat-to-dec-string (cdr input)) ","
                 (str::nat-to-dec-string output) ","
                 (str::nat-to-dec-string (logand (car input) (cdr input)))
                 (coerce (list #\Newline) 'string))))

;; Function to format the entire subtable as a string
(defun format-subtable (subtable)
  (declare (xargs :mode :program))
  (if (endp subtable)
      ""
    (concatenate 'string 
                 (format-subtable-entry (car subtable))
                 (format-subtable (cdr subtable)))))

;; Function to write a string to a file
(defun write-string-to-file (str filename state)
  (declare (xargs :stobjs state))
  (mv-let (channel state)
    (open-output-channel filename :character state)
    (if (null channel)
        (mv nil state)
      (mv-let (state)
        (princ$ str channel state)
        (mv-let (state)
          (close-output-channel channel state)
          (mv t state))))))

;; Main function to generate and write subtable
(defun generate-and-write-subtable (x-hi y-hi filename state)
  (declare (xargs :stobjs state))
  (let* ((indices (create-tuple-indices x-hi y-hi))
         (subtable (materialize-and-subtable indices))
         (subtable-str (format-subtable subtable)))
    (write-string-to-file subtable-str filename state)))

;; Example usage (can be called in the ACL2 REPL)
(defun example-generate-subtable (state)
  (declare (xargs :stobjs state))
  (generate-and-write-subtable 255 255 "and_subtable.txt" state))