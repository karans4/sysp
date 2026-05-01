;;;; Surface .sysp source → list of forms.
;;;; Recursive descent. Tracks source locations on cons cells. Comments are
;;;; line-only (`;` to EOL); commas are whitespace; brackets read as lists.

(in-package :sysp-ir)

(defvar *source-locations* (make-hash-table :test 'eq))

;;; --- pstate ---

(defstruct pstate source pos line col file)

(defun ps-eof-p (ps) (>= (pstate-pos ps) (length (pstate-source ps))))

(defun ps-peek (ps)
  (and (not (ps-eof-p ps)) (char (pstate-source ps) (pstate-pos ps))))

(defun ps-peek2 (ps)
  (let ((p (1+ (pstate-pos ps))))
    (and (< p (length (pstate-source ps))) (char (pstate-source ps) p))))

(defun ps-advance (ps)
  (let ((c (char (pstate-source ps) (pstate-pos ps))))
    (incf (pstate-pos ps))
    (if (char= c #\Newline)
        (progn (incf (pstate-line ps)) (setf (pstate-col ps) 1))
        (incf (pstate-col ps)))
    c))

;;; --- whitespace + line comments ---

(defun ps-skip-ws (ps)
  (loop while (not (ps-eof-p ps)) do
    (let ((c (ps-peek ps)))
      (cond
        ((member c '(#\Space #\Tab #\Newline #\Return #\,))
         (ps-advance ps))
        ((char= c #\;)
         (loop while (and (not (ps-eof-p ps))
                          (not (char= (ps-peek ps) #\Newline)))
               do (ps-advance ps)))
        (t (return))))))

;;; --- atoms: number, keyword, symbol ---

(defun symbol-char-p (c)
  (and c (not (member c '(#\( #\) #\[ #\] #\" #\; #\'
                          #\` #\~ #\Space #\Tab #\Newline #\Return #\,)))))

(defun ps-read-atom-string (ps)
  (let ((start (pstate-pos ps)))
    (loop while (and (not (ps-eof-p ps)) (symbol-char-p (ps-peek ps)))
          do (ps-advance ps))
    (subseq (pstate-source ps) start (pstate-pos ps))))

(defun try-parse-number (s)
  "Return number if s parses as one; else nil. Supports decimal, 0x hex,
   0b binary, 0o octal, floats. Negative leading sign allowed."
  (let* ((neg (and (> (length s) 1) (char= (char s 0) #\-)))
         (rest (if neg (subseq s 1) s))
         (sign (if neg -1 1)))
    (handler-case
        (cond
          ((zerop (length rest)) nil)
          ((and (>= (length rest) 2) (string-equal rest "0x" :end1 2))
           (* sign (parse-integer rest :start 2 :radix 16)))
          ((and (>= (length rest) 2) (string-equal rest "0b" :end1 2))
           (* sign (parse-integer rest :start 2 :radix 2)))
          ((and (>= (length rest) 2) (string-equal rest "0o" :end1 2))
           (* sign (parse-integer rest :start 2 :radix 8)))
          ((find #\. rest)
           (let ((*read-eval* nil))
             (* sign (read-from-string rest))))
          ((digit-char-p (char rest 0))
           (* sign (parse-integer rest)))
          (t nil))
      (error () nil))))

(defun parse-atom (s)
  ;; Match CL reader convention: identifiers (symbols + keywords) are
  ;; case-folded to upper. Numbers are case-insensitive but kept literal.
  ;; Use vertical bars in the future if case-preservation is wanted.
  (cond
    ((zerop (length s)) (error "sysp: empty atom"))
    ;; Try number first (handles negative leading sign too).
    ((try-parse-number s))
    ((string-equal s "t")   cl:t)
    ((string-equal s "nil") cl:nil)
    ((char= (char s 0) #\:)
     (intern (string-upcase (subseq s 1)) :keyword))
    (t (intern (string-upcase s)))))

;;; --- string literal ---

(defun ps-read-string-literal (ps)
  (ps-advance ps)    ; consume opening "
  (let ((buf (make-array 0 :element-type 'character :adjustable t :fill-pointer 0)))
    (loop
      (when (ps-eof-p ps)
        (error "sysp: unterminated string at line ~d col ~d"
               (pstate-line ps) (pstate-col ps)))
      (let ((c (ps-advance ps)))
        (cond
          ((char= c #\") (return (coerce buf 'string)))
          ((char= c #\\)
           (when (ps-eof-p ps) (error "sysp: trailing backslash in string"))
           (let ((esc (ps-advance ps)))
             (vector-push-extend
              (case esc
                (#\n #\Newline) (#\t #\Tab) (#\r #\Return)
                (#\0 (code-char 0)) (#\\ #\\) (#\" #\")
                (otherwise esc))
              buf)))
          (t (vector-push-extend c buf)))))))

;;; --- char literal: #\c | #\name ---

(defun ps-read-char-literal (ps)
  (ps-advance ps) (ps-advance ps)   ; consume # and \
  (when (ps-eof-p ps) (error "sysp: incomplete char literal"))
  (let ((c (ps-advance ps)))
    (cond
      ((and (alpha-char-p c) (not (ps-eof-p ps)) (alpha-char-p (ps-peek ps)))
       (let ((buf (make-array 1 :element-type 'character :adjustable t
                              :fill-pointer 1 :initial-element c)))
         (loop while (and (not (ps-eof-p ps)) (alpha-char-p (ps-peek ps)))
               do (vector-push-extend (ps-advance ps) buf))
         (let ((name (string-downcase (coerce buf 'string))))
           (cond
             ((string= name "newline") #\Newline)
             ((string= name "space")   #\Space)
             ((string= name "tab")     #\Tab)
             ((string= name "return")  #\Return)
             ((string= name "null")    (code-char 0))
             (t (error "sysp: unknown char name #\\~a" name))))))
      (t c))))

;;; --- form dispatch ---

(defun ps-read-form (ps)
  "Read one form. Returns (values form has-form-p)."
  (ps-skip-ws ps)
  (when (ps-eof-p ps) (return-from ps-read-form (values nil nil)))
  (let ((line (pstate-line ps)) (col (pstate-col ps)) (c (ps-peek ps)))
    (let ((form
            (cond
              ((char= c #\() (ps-read-list ps #\( #\) line col))
              ((char= c #\[) (ps-read-list ps #\[ #\] line col))
              ((char= c #\") (ps-read-string-literal ps))
              ((char= c #\')
               (ps-advance ps)
               (list 'quote (nth-value 0 (ps-read-form ps))))
              ((char= c #\`)
               (ps-advance ps)
               (list 'quasiquote (nth-value 0 (ps-read-form ps))))
              ((char= c #\~)
               (ps-advance ps)
               (if (eql (ps-peek ps) #\@)
                   (progn (ps-advance ps)
                          (list 'splice (nth-value 0 (ps-read-form ps))))
                   (list 'unquote (nth-value 0 (ps-read-form ps)))))
              ((and (char= c #\#) (eql (ps-peek2 ps) #\\))
               (ps-read-char-literal ps))
              (t (parse-atom (ps-read-atom-string ps))))))
      (when (consp form)
        (setf (gethash form *source-locations*)
              (list (pstate-file ps) line col)))
      (values form t))))

(defun ps-read-list (ps open close open-line open-col)
  (ps-advance ps)   ; consume open
  (let (elems)
    (loop
      (ps-skip-ws ps)
      (when (ps-eof-p ps)
        (error "sysp: unclosed ~c from line ~d col ~d (~a)"
               open open-line open-col (pstate-file ps)))
      (let ((c (ps-peek ps)))
        (cond
          ((char= c close) (ps-advance ps) (return (nreverse elems)))
          ((member c '(#\) #\]))
           (error "sysp: mismatched ~c at line ~d col ~d (~c opened at ~d:~d)"
                  c (pstate-line ps) (pstate-col ps) open open-line open-col))
          (t (multiple-value-bind (form has) (ps-read-form ps)
               (when has (push form elems)))))))))

;;; --- public API ---

(defun parse-string (source &optional (file "<string>"))
  (let ((ps (make-pstate :source source :pos 0 :line 1 :col 1 :file file))
        (forms nil))
    (loop
      (multiple-value-bind (form has) (ps-read-form ps)
        (unless has (return))
        (push form forms)))
    (nreverse forms)))

(defun parse-file (path)
  (with-open-file (s path :direction :input)
    (let ((src (make-string (file-length s))))
      (read-sequence src s)
      (parse-string src (namestring path)))))

;;; --- source-aware errors ---

(defun loc-of (form)
  "Return (file line col) for a parsed form, or nil."
  (and (consp form) (gethash form *source-locations*)))

(defun read-source-line (file line)
  (when (and file (probe-file file))
    (with-open-file (s file)
      (loop for cur from 1
            for l = (read-line s nil nil)
            while l
            when (= cur line) return l))))

(defun error-at (form fmt &rest args)
  "Signal an error pointing at form's source location, with caret if available."
  (let ((loc (loc-of form)))
    (if loc
        (let* ((file (first loc)) (line (second loc)) (col (third loc))
               (src-line (read-source-line file line))
               (msg (apply #'format nil fmt args)))
          (if src-line
              (error "~a:~d:~d: ~a~%~a~%~a^"
                     file line col msg src-line
                     (make-string (max 0 (1- col)) :initial-element #\Space))
              (error "~a:~d:~d: ~a" file line col msg)))
        (error "sysp: ~a" (apply #'format nil fmt args)))))
