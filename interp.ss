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


(define (interp expr env)
  (match expr
    [,sym (guard (symbol? sym)) (lookup env sym)]
    [(λ (,x) ,body)
     `(closure ,x ,body ,env)]
    [(,app ,rator)
     (let ([rv (interp rator env)])
       (match (interp app env)
         [(closure ,appx ,appbody ,appenv)
          (interp appbody (ext-env appenv appx rv))]))]))

;maybe
(define (lookup env x)
  (letrec
      ([r
        (λ (env x k)
          (match env
            [() (k 'Nothing)]
            [((,a . ,res) . ,rest)
             (if (equal? a x)
                 (k `(Just ,res))
                 (r rest x k))]))])
    (r env x (λ (res)
               (match res
                 [Nothing (error 'lookup "lookup failed" x env)]
                 [(Just ,v) v])))))
(define (ext-env env k v)
  `((,k . ,v) . ,env))

;cps
;ext-env treated as trivial
(define (id x) x)
(define (interp-cps expr env k)
  (match expr
    [,sym (guard (symbol? sym)) (lookup-cps env sym k)]
    [(λ (,x) ,body)
     (k `(closure ,x ,body ,env))]
    [(,app ,rator)
     (interp-cps rator env (λ (rv)
        (interp-cps app env (λ (appv)
           (match appv
             [(closure ,appx ,appbody ,appenv)
              (interp-cps appbody (ext-env appenv appx rv) k)])))))]))

;maybe
(define (lookup-cps env x k)
  (letrec
      ([r
        (λ (env x k)
          (match env
            [() (k 'Nothing)]
            [((,a . ,res) . ,rest)
             (if (equal? a x)
                 (k `(Just ,res))
                 (r rest x k))]))])
    (r env x (λ (res)
               (match res
                 [Nothing (error 'lookup "lookup failed" x env)]
                 [(Just ,v) (k v)])))))
(define (ext-env env k v)
  `((,k . ,v) . ,env))


;defunc
(define (id x) x)
(define (interp-cps-defunc expr env k)
  (match expr
    [,sym (guard (symbol? sym)) (lookup-cps-defunc env sym k)]
    [(λ (,x) ,body)
     (apply-interp k `(closure ,x ,body ,env))]
    [(,app ,rator)
     (interp-cps-defunc rator env
                        `(K-app-a-rator ,app ,env ,k))]))

(define (apply-interp k-struct value)
  (match k-struct
    [K-id value]
    [(K-app-a-rator ,app ,env ,k) (interp-cps-defunc app env `(K-app-a-app ,value ,k))]
    [(K-app-a-app ,ratorv ,k)
     (match value
       [(closure ,appx ,appbody ,appenv)
        (interp-cps-defunc appbody (ext-env appenv appx ratorv) k)])]    
    [(K-lookup-final ,k)
     (match value
       [Nothing (error 'lookup "lookup failed" x env)]
       [(Just ,v) (apply-interp k v)])]))


(define (r env x k)
  (match env
    [() (apply-interp k 'Nothing)]
    [((,a . ,res) . ,rest)
     (if (equal? a x)
         (apply-interp k `(Just ,res))
         (r rest x k))]))


;interpᵒ
(define idᵒ ==)
(define (interpᵒ expr env k out)
  (conde
   [(symbolo expr)
    (lookupᵒ env expr k out)]
   [(fresh (x body)
      (== expr `(λ (,x) ,body))
      (applyᵒ k `(closure ,x ,body ,env) out))]
   [(fresh (app rator)
      (== expr `(,app ,rator))
      (interpᵒ rator env
               `(K-app-a-rator ,app ,env ,k) out))]))

(define (applyᵒ k-struct value out)
  (conde
   [(== k-struct 'K-id) (== value out)]
   [(fresh (app k env)
      (== k-struct `(K-app-a-rator ,app ,env ,k))
      (interpᵒ app env `(K-app-a-app ,value ,k) out))]
   [(fresh (ratorv k appx appbody eenv appenv)
      (== k-struct `(K-app-a-app ,ratorv ,k))
      (== value `(closure ,appx ,appbody ,appenv))
      (ext-envᵒ appenv appx ratorv eenv)
      (interpᵒ appbody eenv k out))]  
   [(fresh (k)
      (== k-struct `(K-lookup-final ,k))
      (conde
       [(fresh (v)
          (== value `(Just ,v))
          (applyᵒ k v out))]
       ;#[(== value Nothing) fail]
       ))]))


(define (rᵒ env x k out)
  (conde
   [(== env '()) (applyᵒ k 'Nothing out)]
   [(fresh (a res rest)
      (== env `((,a . ,res) . ,rest))
      (conde
       [(== a x) (applyᵒ k `(Just ,res) out)]
       [(=/= a x) (rᵒ rest x k out)]))]))

;maybe
(define (lookupᵒ env x k out)
  (rᵒ env x `(K-lookup-final ,k) out))

(define (ext-envᵒ env k v out)
  (== `((,k . ,v) . ,env) out))


#!eof
(load "interp.ss")

(lookup  `((x . 5) (y . 6)) 'z)


(r  `((x . Nothing) (y . 6)) 'x (λ (x) x))

(interp 'x `((x . 5)))
(interp '(λ (x) x) '())


(interp '(((λ (y) (λ (x) x)) x) y) `((x . x) (y . y)))
(interp '(((λ (y) (λ (x) y)) x) y) `((x . x) (y . y)))


(interp-cps '(((λ (y) (λ (x) x)) x) y) `((x . x) (y . y)) id)
(interp-cps '(((λ (y) (λ (x) y)) x) y) `((x . x) (y . y)) id)


(interp-cps-defunc '(((λ (y) (λ (x) x)) x) y) `((x . x) (y . y)) 'K-id)
(interp-cps-defunc '(((λ (y) (λ (x) y)) x) y) `((x . x) (y . y)) 'K-id)


(run* (out)
      (interpᵒ '(((λ (y) (λ (x) x)) x) y) `((x . x) (y . y)) 'K-id out))

(run* (out)
      (interpᵒ '(((λ (y) (λ (x) y)) x) y) `((x . x) (y . y)) 'K-id out))

(run 10 (out)
  (interpᵒ out `((x . x) (y . y)) 'K-id 'x))

