(import (Framework match))
(import (Framework helpers))
(case-sensitive #t)
(optimize-level 2)
(print-gensym 'pretty)
(load "mk.scm")


(define-syntax λ
  (syntax-rules ()
    [(_ (x ...) body ...)
     (lambda (x ...) body ...)]))


(define (cps1 program k)
  (match program
    [,s (guard (symbol? s)) (k s)]
    [(λ (,x) ,body) (guard (symbol? x))
                    (k `(λ (,x k) ,(cps1 body (λ (x) `(k ,x)))))]
    [(,app ,rator)
     (cps1 app (λ (acode)
                 (cps1 rator (λ (rcode)
                               (let ([sym (gensym)])
                                 `(,acode ,rcode (λ (,sym)
                                                   ,(k sym))))))))]))

(define (subst o n s-exp)
  (match s-exp
    [() '()]
    [,a (guard (symbol? a)) (if (eq? a o) n a)]
    [(,[a] . ,[d]) `(,a . ,d)]))


(define (substᵒ o n s-exp out)
  (conde
   [(== s-exp '()) (== '() out)]
   [(symbolo s-exp)
    (conde
     [(== s-exp o) (== n out)]
     [(=/= s-exp o) (== s-exp out)])]
   [(fresh (a d ares dres)
      (== `(,ares . ,dres) out)
      (== `(,a . ,d) s-exp)
      (substᵒ o n a ares)
      (substᵒ o n d dres))]))

(define (cps-i cpsed-program k)
  (match cpsed-program
    [,s (guard (symbol? s)) (k s)]
    [(λ (,x k) ,body) (guard (symbol? x))
                      (cps-i body (λ (rbody)
                                    (k `(λ (,x) ,rbody))))]
    [(k ,sth) (k sth)]
    [(,app ,rator (λ (,ressymbol) ,body))
     (cps-i app (λ (rapp)
                  (cps-i rator (λ (rrator)
                                 (let* ([body-res (cps-i body k)])
                                   (subst ressymbol `(,rapp ,rrator) body-res))))))]))

; defunc cps-i
;we treat subst as atomic here to save some strength
(define (cps-i-defunc cpsed-program k)
  (match cpsed-program
    [,s (guard (symbol? s)) (apply-cps-i-defunc k s)]
    [(λ (,x k) ,body) (guard (symbol? x))
                      (cps-i-defunc body `(K-λ-final ,x ,k))]
    [(k ,sth) (apply-cps-i-defunc k sth)]
    [(,app ,rator (λ (,sym) ,body))
     (cps-i-defunc app
            `(K-app-rator ,rator ,sym ,body ,k))]))

(define (apply-cps-i-defunc k-struct code)
  (match k-struct
    [K-id code]
    [(K-λ-final ,x ,k) (apply-cps-i-defunc k `(λ (,x) ,code))]
    [(K-app-rator ,rator ,sym ,body ,k)
     (cps-i-defunc rator `(K-app-body ,code ,sym ,body ,k))]
    [(K-app-body ,rapp ,sym ,body ,k)
     (cps-i-defunc body `(K-app-final ,rapp ,code ,sym ,k))]
    [(K-app-final ,rapp ,rrator ,sym ,k)
     (apply-cps-i-defunc k (subst sym `(,rapp ,rrator) code))]))

;now,ready to create cps-iᵒ
(define (cps-iᵒ program k out)
  (conde
   [(symbolo program) (apply-cps-iᵒ k program out)]
   [(fresh (x body)
      (== program `(λ (,x k) ,body))
      (symbolo x)
      (cps-iᵒ body `(K-λ-final ,x ,k) out))]
   [(fresh (sth)
      (== program `(k ,sth))
      (apply-cps-iᵒ k sth out))]
   
   [(fresh (app rator sym body)
      (== program `(,app ,rator (λ (,sym) ,body)))
      (cps-iᵒ app
              `(K-app-rator ,rator ,sym ,body ,k) out))]))

(define (apply-cps-iᵒ k-struct code out)
  (conde
   [(== k-struct 'K-id) (== code out)]
   [(fresh (x k)
      (== k-struct `(K-λ-final ,x ,k))
      (apply-cps-iᵒ k `(λ (,x) ,code) out))]
   [(fresh (rator sym body k)
      (== k-struct `(K-app-rator ,rator ,sym ,body ,k))
      (cps-iᵒ rator `(K-app-body ,code ,sym ,body ,k) out))]
   [(fresh (rapp sym body k)
      (== k-struct `(K-app-body ,rapp ,sym ,body ,k))
      (cps-iᵒ body `(K-app-final ,rapp ,code ,sym ,k) out))]
   [(fresh (rapp rrator sym k subst-res)
      (== k-struct `(K-app-final ,rapp ,rrator ,sym ,k))
      (substᵒ sym `(,rapp ,rrator) code subst-res)
      (apply-cps-iᵒ k subst-res out))]))

(define-syntax display-expr
  (syntax-rules ()
    [(_ expr) (begin
                (display expr)
                (display "\n")
                expr)]))


#!eof

(load "cpsers.ss")



(run 50 (res)
  (cps-iᵒ res 'K-id 'x))


(run* (out)
  (cps-iᵒ '(p (λ (x k) (k z)) (λ (g0) (g0 q (λ (g1) g1))))
 'K-id out))


(run 1 (out)
  (cps-iᵒ '(p (λ (x k) (k z)) (λ (g0) (g0 q (λ (g1) g1))))
          out
          '(((p (λ (x) z)) q))
))




(cps-i '(λ (x k) (k x)) (λ (x) x))


(cps-i
 '(p (λ (x k) (k z)) (λ (g4) (g4 q (λ (g5) g5))))
 (λ (x) x))

(cps-i-defunc
 '(p (λ (x k) (k z)) (λ (g4) (g4 q (λ (g5) g5))))
 'K-id)

(run* (q)
  (substᵒ 'x 'y '(x y z) q))

(run 1 (out)
  (cps-iᵒ
   '(p (λ (x k) (k z)) (λ (g4) (g4 q (λ (g5) g5))))
   'K-id
   out))



(run* (out)
  (cps-iᵒ
   '(λ (x k) (k x))
   'K-id
   out))

(run* (out)
  (cps-iᵒ
   '(p q (λ (x) x))
   'K-id
   out))

(run* (out)
  (cps-iᵒ '(p (λ (x k) (k z)) (λ (g0) (g0 q (λ (g1) g1))))
 'K-id out))



(cps1 `((p (λ (x) z)) q) (λ (x) x))

(define-syntax display-expr
  (syntax-rules ()
    [(_ expr) (begin
                (display expr)
                (display "\n")
                expr)]))
