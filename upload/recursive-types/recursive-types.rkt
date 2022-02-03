#lang typed/racket/base

(struct (S) inj1 ([s : S]))
(struct (T) inj2 ([t : T]))
(define-type (Sum S T) (U (inj1 S) (inj2 T)))

(define-type A (U False 1 2)) 
(define-type B Boolean)

(define ex1 : (U A B) 2)
(define ex2 : (Intersection A B) #f)
(define ex3 : (Pair A B) (cons 1 #t))
(define ex4 : (Sum A B) (inj1 (ann 2 A)))
(define ex5 : (-> A B) (lambda ([a : A]) (if a #t a)))

;; * * * * * * * * * * * * * * * * * * * * * * * * *
(define-type Natural^ (Sum Null Natural^))

(define ex6 : Natural^ (inj2 (inj2 (inj1 null))))
;; * * * * * * * * * * * * * * * * * * * * * * * * *
(define-type IntList (U Null (Pair Integer IntList)))

(define ex7 : IntList null)
(define ex8 : IntList (cons 1 (cons 5 (cons 4 null))))
;; * * * * * * * * * * * * * * * * * * * * * * * * *
(struct Leaf ())
(struct (T) Node ([left : T]
                  [value : Integer]
                  [right : T]))
(define-type Tree (U Leaf (Node Tree)))

(define ex9 : Tree (Node (Leaf) 1 (Leaf)))
(define ex10 : Tree (Node ex9 0 ex9))
;; * * * * * * * * * * * * * * * * * * * * * * * * *
(define-type IntFun (U Integer (-> Integer IntFun)))

(define ex11 : IntFun
  (lambda ([x : Integer])
    (if (> x 0) x ex11)))
;; * * * * * * * * * * * * * * * * * * * * * * * * *
(struct Lit ([b : Boolean]))
(struct Var ([s : Symbol]))
(struct (BE) And ([beL : BE] [beR : BE]))
(struct (BE) Or ([beL : BE] [beR : BE]))
(struct (BE) Not ([be : BE]))
(define-type BoolExp
  (U Lit Var (And BoolExp) (Or BoolExp) (Not BoolExp)))

(define ex12 : BoolExp (Not (And (Lit #t) (Var 'x))))
;; * * * * * * * * * * * * * * * * * * * * * * * * *
(define-type Conatural (-> Null (Sum Null Conatural)))

(define inj2_infty : Conatural 
  (lambda ([_ : Null]) (inj2 inj2_infty)))
;; * * * * * * * * * * * * * * * * * * * * * * * * *
