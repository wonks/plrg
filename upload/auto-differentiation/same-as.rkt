#lang racket

(require  malt
         (for-syntax syntax/parse))

(provide same-as*)

(define-syntax (same-as* stx)
  (syntax-parse stx
    [(same-as* (~optional (~seq #:precision prec:expr)))
     (printf "\n")]
    [(same-as* (~optional (~seq #:precision prec:expr))
               (~optional (~seq #:verify verify:expr))
               e es ...)
     (with-syntax ([verify (if (attribute verify) (attribute verify) #'#t)]
                   [prec (if (attribute prec) (attribute prec) #'1e-5)])
       #'(let ((v e))
           (same-as-imp* prec verify 1 v e es ...)))]))

(define-syntax same-as-imp*
  (syntax-rules ()
    ((same-as-imp* _ _ _ value)
     (begin
       (printf "\n")
       value))
    ((same-as-imp* prec verify start value e es ...)
     (begin
       (let ((v e))
         (if (or (not verify) ((value= prec) v value))
             (begin
               (printf "~a.| " (line-id start))
               (parameterize ((pretty-print-columns 60))
                 (pretty-print
                  (syntax->datum #'e)
                  (current-output-port)
                  1)))
             (error 'same-as* "~a on line ~a does not match the first value ~a"
                    ((format-value-0 (inexact->exact (round (abs-ρ (log prec 10))))) v)
                    start
                    ((format-value-0 (inexact->exact (round (abs-ρ (log prec 10))))) value))))
       (same-as-imp* prec verify (ρ (add1 start)) value es ...)))))

(define ((value= prec) v1 v2)
  (cond
    ((or (dual? v1) (dual? v2))
     ((value= prec) (ρ v1) (ρ v2)))
    ((and (number? v1) (number? v2))
     (<-0-0 (abs-ρ (--ρ v1 v2)) prec))
    ((and (integer? v1) (integer? v2))
     (eq? v1 v2))
    ((and (list? v1) (list? v2)
          (len v1) (len v2))
     (andmap (value= prec) v1 v2))
    ((and (tensor? v1) (tensor? v2)
          (equal? (shape v1) (shape v2)))
     (ands (vector-map (value= prec) v1 v2)))
    (else (equal? v1 v2))))

(define (ands t)
  (cond
    ((eq? t #f) #f)
    ((eq? t #t) #t)
    ((= (tlen t) 0) #t)
    ((= (tlen t) 1)
     (ands (tref t 0)))
    ((ands (tref t 0))
     (ands (trefs t (range 1 (tlen t)))))
    (else #f)))

(define (line-id id)
  (let* ((str (number->string id))
         (str-len (string-length str))
         (space-num (--ρ 4 str-len)))
    (string-append (make-string space-num #\space) str)))

(define pick-notation
  (lambda (x)
    (if (or (< (abs x) 0.001) (> (abs x) 1000))
        'exponential
        'positional)))

(define ((format-value-0 rounding) v)
  (cond
    ((dual? v)
     (if (nan? (ρ v))
         (number->string (ρ v))
         (~r (ρ v) #:precision rounding #:notation pick-notation)))
    ((real? v)
     (if (nan? v)
         (number->string v)
         (~r v #:precision rounding #:notation pick-notation)))
    ((list? v) `(list . ,(map (format-value-0 rounding) v)))
    ((vector? v) `(tensor . ,(vector->list (vector-map (format-value-0 rounding) v))))
    (else v)))
