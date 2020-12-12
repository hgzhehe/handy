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

(define (anf program)
  (anf1 program id))

(define (anf1 program C)  
  (match program
    [,c (guard (constant? c)) (C program)]
    [(quote ,d) (C program)]
    [,x (guard (symbol? x))
        (C x)]
    [(set! ,x ,expr) (anf1 expr (λ (ecode)
                                  (C `(set! ,x ,ecode))))]
    [(begin ,e) (anf1 e C)]
    [(begin ,[anf -> e*] ... ,e)
     `(begin ,e* ... ,(anf1 e C))]
    [(λ (,x ...) ,body)
     (C `(λ (,x ...) ,(anf1 body id)))]
    [(if ,p ,c ,a)
     (anf1 p (λ (pcode)
               (let ([icode `(if ,pcode
                                 ,(anf c)
                                 ,(anf a))])
                 (if (eq? C id)
                     icode
                     (let ([isym (gensym)])
                       `(let ([,isym ,icode])
                          ,(C isym)))))))]
    [(,p1 ,e) (guard (member p1 prim1))
              (anf1 e (λ (e)
                        (C `(,p1 ,e))))]
    [(,p2 ,e1 ,e2) (guard (member p2 prim2))
                   (anf1 e1 (λ (e1)
                              (anf1 e2 (λ (e2)
                                         (C `(,p2 ,e1 ,e2))))))]
    [(let () ,body ,body* ...)
     (anf1 `(begin ,body ,body* ...) C)]
    [(let ([,var ,expr] [,var* ,expr*] ...) ,body ,body* ...)
     (anf1 expr (λ (e)
                  `(let ([,var ,e])
                     ,(anf1 `(let ([,var* ,expr*] ...) ,body ,body* ...) C))))]
    [(,rator . ,rand*)
     (anf1 rator
           (lambda (ra)
             (anf1* rand*
                    (lambda (rd*)
                      (add-let-bound (cons ra rd*) C)))))]))

(define anf1*
  (lambda (exp* k)
    (if (null? exp*)
        (k '())
        (anf1 (car exp*)
              (lambda (a)
                (anf1* (cdr exp*)
                       (lambda (d)
                         (k (cons a d)))))))))

(define add-let-bound
  (lambda (exp k)
    (cond
      [(eq? k id) exp]
      [else (let ([n (gensym)])
              `(let ([,n ,exp])
                 ,(k n)))])))



(define (eval-anf-p p)  
  (begin
    (define C id)
    (display (anf p))
    (display "\n")
    (eval (anf p))))

#!eof
(load "anfer.ss")

(anf '(λ (x) (if (p (if (d w e)
                        x #t))
                 (begin (set! q (d w)) y)
                 (x))))

(anf '(let ([x y]
            [z (p q (c v))])
        (d s (+ x z)) v))

(anf '(begin (set! x 5)
             (q w e)
             (set! y (p q (c)))
             y))

(anf1 '(x (add1 ((if (y) m n) 10)) z) id)

(eval-anf-p '((λ (x) (add1 x)) 5))


(anf1 '(z d (x) (q y z)) id)

(anf1 '((if ((if p c a) x) (m n) n) z) id)

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
(define (anf1 program C)  
  (define (C0 code) `(C ,code))
  (match program
    [,x (guard (symbol? x))
        (C x)]
    [(λ (,x) ,body)
     (C `(λ (,x C) ,(anf1 body C0)))]
    [(if ,p ,c ,a)
     (anf1 p (λ (pcode)
               (if (member C `(,id ,C0))
                   (C `(if ,pcode
                           ,(anf1 c id)
                           ,(anf1 a id)))
                   (let ([psym (gensym)])
                     `(let ([C (λ (,psym) ,(C psym))])
                        (if ,pcode ,(anf1 c C0) ,(anf1 a C0)))))))]
    [(,app ,rator)
     (anf1 app (λ (acode)
                 (anf1 rator (λ (rcode)
                               `(,acode ,rcode
                                        ,(if (member C `(,id ,C0))
                                             'C
                                             (let ([sym (gensym)])
                                               `(λ (,sym)
                                                  ,(C sym)))))))))]))
