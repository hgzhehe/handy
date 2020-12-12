(import (Framework match))
(import (Framework helpers))
(case-sensitive #t)
(optimize-level 2)

(define-syntax λ
  (syntax-rules ()
    [(_ (x ...) body ...)
     (lambda (x ...) body ...)]))


(define prim1 '(make-vector vector-length
                            car cdr
                            not
                            boolean? integer? null? pair? procedure? vector? zero?
                            add1 sub1))
(define prim2 '(* + - < <= = >= >
                  eq?
                  cons
                  set-car! set-cdr!
                  vector-ref))

(define (constant? c)
  (or (boolean? c) (number? c)))

(define (id x) x)

(define (C0 code) `(C ,code))

#|
Expr −→ constant
| (quote datum)
| var
| (set! var Expr)
| (if Expr Expr)
| (if Expr Expr Expr)
| (begin Expr Expr*)
| (lambda (var*) Expr Expr*)
| (let ([var Expr]*) Expr Expr*)
| (letrec ([var Expr]*) Expr Expr*)
| (primitive Expr*)
| (Expr Expr*)
|#

(define (cps program)
  (cps1 program id))

(define (cps1 program C)  
  (match program
    [,c (guard (constant? c)) (C program)]
    [(quote ,d) (C program)]
    [,x (guard (symbol? x))
        (C x)]
    [(set! ,x ,expr) (cps1 expr (λ (ecode)
                                  (C `(set! ,x ,ecode))))]
    [(begin ,e) (cps1 e C)]
    [(begin ,[cps -> e*] ... ,e)
     `(begin (let ([C (λ (x) x)])
               ,e* ...) ,(cps1 e C))]
    [(λ (,x ...) ,body)
     (C `(λ (,x ... C) ,(cps1 body C0)))]
    [(if ,p ,c ,a)
     (cps1 p (λ (pcode)
               (if (member C `(,id ,C0))
                   (C `(if ,pcode
                           ,(cps c)
                           ,(cps a)))
                   (let ([psym (gensym)])
                     `(let ([C (λ (,psym) ,(C psym))])
                        (if ,pcode ,(cps1 c C0) ,(cps1 a C0)))))))]
    [(,p1 ,e) (guard (member p1 prim1))
              (cps1 e (λ (e)
                        (C `(,p1 ,e))))]
    [(,p2 ,e1 ,e2) (guard (member p2 prim2))
                   (cps1 e1 (λ (e1)
                              (cps1 e2 (λ (e2)
                                         (C `(,p2 ,e1 ,e2))))))]
    [(let () ,body ,body* ...)
     (cps1 `(begin ,body ,body* ...) C)]
    [(let ([,var ,expr] [,var* ,expr*] ...) ,body ,body* ...)
     (cps1 expr (λ (e)
                  `(let ([,var ,e])
                     ,(cps1 `(let ([,var* ,expr*] ...) ,body ,body* ...) C))))]
    [(,rator . ,rand*)
     (cps1 rator
           (lambda (ra)
             (cps1* rand*
                    (lambda (rd*)
                      (add-let-bound (cons ra rd*) C)))))]))

(define cps1*
  (lambda (exp* k)
    (if (null? exp*)
        (k '())
        (cps1 (car exp*)
              (lambda (a)
                (cps1* (cdr exp*)
                       (lambda (d)
                         (k (cons a d)))))))))

(define add-let-bound
  (lambda (exp k)
    (cond
      [(member k `(,id ,C0)) `(,@exp C)]
      [else (let ([n (gensym)])
              `(,@exp (λ (,n)
                        ,(k n))))])))



(define (eval-cps-p p)  
  (begin
    (define C id)
    (display (cps p))
    (display "\n")
    (eval (cps p))))

#!eof
(load "cpser.ss")

(cps '(let ([x y]
            [z (p q (c v))])
        (+ x z)))

(cps '(begin (set! x 5)
             (q w e)
             (set! y (p q (c)))
             y))

(cps1 '(x (add1 ((if (y) m n) 10)) z) id)

(eval-cps-p '((λ (x) (add1 x)) 5))


(cps1 '(z d (x) (q y z)) id)

(cps1 '((if ((if p c a) x) (m n) n) z) id)

(define primitives '(* + - < <= = >= > add1 sub1 zero?
                       boolean? integer? null? pair? procedure? vector? not eq? cons car cdr set-car! set-cdr!
                       make-vector vector-length vector-ref vector-set! void))

(define prim0 '(void))
(define prim3 '(vector-set!))


Expr −→ constant
| (quote datum)
| var
| (set! var Expr)
| (if Expr Expr)
| (if Expr Expr Expr)
| (begin Expr Expr*)
| (lambda (var*) Expr Expr*)
| (let ([var Expr]*) Expr Expr*)
| (letrec ([var Expr]*) Expr Expr*)
| (primitive Expr*)
| (Expr Expr*)


;the naive one
(define (cps1 program C)  
  (define (C0 code) `(C ,code))
  (match program
    [,x (guard (symbol? x))
        (C x)]
    [(λ (,x) ,body)
     (C `(λ (,x C) ,(cps1 body C0)))]
    [(if ,p ,c ,a)
     (cps1 p (λ (pcode)
               (if (member C `(,id ,C0))
                   (C `(if ,pcode
                           ,(cps1 c id)
                           ,(cps1 a id)))
                   (let ([psym (gensym)])
                     `(let ([C (λ (,psym) ,(C psym))])
                        (if ,pcode ,(cps1 c C0) ,(cps1 a C0)))))))]
    [(,app ,rator)
     (cps1 app (λ (acode)
                 (cps1 rator (λ (rcode)
                               `(,acode ,rcode
                                        ,(if (member C `(,id ,C0))
                                             'C
                                             (let ([sym (gensym)])
                                               `(λ (,sym)
                                                  ,(C sym)))))))))]))
