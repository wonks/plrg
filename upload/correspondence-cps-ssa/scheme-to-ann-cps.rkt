#lang racket/base

;; "_F__P" below is the function "F" from the Figure 1 in the paper that
;; converts a subset of Scheme to annotated CPS. Check the end of this file for
;; an example.
;;
;; Disclaimer: I'm sure this code has some bugs but it's better than no code at
;; all. One obvious problem is that I haven't kept track of the variables that
;; are defined using "letrec" so it will behave inappropriately in the
;; F(⟦(E ...), C⟧) case. Still, it should work fine most of the time.

(require
 (only-in racket/syntax format-symbol)
 (only-in racket/dict dict-has-key? dict-set! dict-ref)
 (only-in racket/list first second third))

(define fourth cadddr)

(define sym->idx (make-hash))

(define (fresh-uniq sym)
  (unless (dict-has-key? sym->idx sym)
    (dict-set! sym->idx sym 0))
  (define idx (dict-ref sym->idx sym))
  (dict-set! sym->idx sym (+ idx 1))
  (format-symbol "~a_~a" sym idx))

(define (_F__M^ m c l* j*)
  (cond
    ;; IF_VAR
    [(and (list? m) (eq? (first m) 'if) (symbol? c))
     `(if ,(second m)
          ,(_F__M (third m) c)
          ,(_F__M (fourth m) c))]
    ;; IF_FUN
    [(and (list? m) (eq? (first m) 'if) (list? c))
     (let ((x (first (second c)))
           (fresh-j (fresh-uniq 'j)))
       `(letrec ((,fresh-j (lambda_jump ,(second c) ,(third c))))
          (if ,(second m)
              ,(_F__M (third m) fresh-j)
              ,(_F__M (fourth m) fresh-j))))]
    ;; LOOP
    [(and (list? m) (eq? (first m) 'loop))
     (let ((l (second m))
           (x* (map first (third m)))
           (E* (map second (third m))))
       `(letrec ((,l (lambda_jump ,x* ,(_F__M (fourth m) c))))
          ,(append `(,l) E*)))]
    ;; LET
    [(and (list? m) (eq? (first m) 'let))
     (_F__M
      (second (first (second m)))
      `(lambda_cont (,(first (first (second m))))
         ,(_F__M (third m) c)))]
    ;; APP_JUMP
    [(and (list? m) (not (member (first m) '(+ - =)))
          (symbol? c) (member c j*))
     (let ((fresh-v (fresh-uniq 'v)))
       `(let ((,fresh-v ,m)) (,c ,fresh-v)))]
    ;; APP_PROC
    [(and (list? m) (not (member (first m) '(+ - =))))
     (append m `(,c))]
    ;; EXP_VAR
    [(symbol? c) 
     `(,c ,m)]
    ;; EXP_FUN
    [else
     `(let ((,(first (second c)) ,m)) ,(third c))]))

(define (_F__M m c)
  (_F__M^ m c '() '()))

(define (_F__P p)
  (let ((fresh-k (fresh-uniq 'k)))
    `(lambda_proc
      ,(append (second p) `(,fresh-k))
      ,(_F__M (third p) fresh-k))))


#;(_F__M^ '(let ((y 1)) y) 'k '() '())

#;(_F__M '(loop mylabel ((a 0) (b 1)) (+ a b))
                       'k)

#;(_F__M '(loop mylabel ((a 0) (b 1)) (+ a b))
                       '(lambda_cont (c) c))

#;(_F__P
   '(lambda (f limit)
      (loop l ((i 0) (c 0))
            (if (= i limit)
                c
                (let ((x (f i)))
                  (let ((c^ (if (= x 0)
                                (+ c 1)
                                c)))
                    (l (+ i 1) c^)))))))
