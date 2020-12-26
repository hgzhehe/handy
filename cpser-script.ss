
(cps1 '(λ (x) x) '() id)

(cps1 '(λ (x) (λ (y) (x y))) '() id)

(run 11 (res)
  (proper-memberᵒ 'x res))


(run 40 (res)
  (termᵒ '() res))

(map car
 (run 40 (res)
   (ctermᵒ '() #f res)))


(define (id x) x)
(define (k0 x) `(k ,x))

(define (cps1 program met k)
  (match program
    [,s (guard (symbol? s)
               (member s met)) (k s)]
    [(λ (,x) ,body) (guard (symbol? x))
                    (k `(λ (,x k) ,(cps1 body (cons x met) (λ (x) `(k ,x)))))]
    [(,app ,rator)
     (cps1 app met (λ (acode)
                     (cps1 rator met (λ (rcode)
                                       (let ([sym (gensym)])
                                         `(,acode ,rcode (λ (,sym)
                                                           ,(k sym))))))))]))

(define (subst o n expr)
  (match expr
    [() '()]
    [,a (guard (symbol? a))
        (if (eq? a o) n a)]
    [(,[a] . ,[d]) `(,a . ,d)]))


(define (cps-i cterm met k-it k)
  (match cterm
    [,sym (guard (symbol? sym)
                 (member sym met)) (k sym)]
    [(λ (,x k) ,body)
     (k `(λ (,x) ,(cps-i body (cons x met) #t id)))]
    [(,app ,rator (λ (,x) ,body))
     (cps-i app met #f (λ (acode)
                         (cps-i rator met #f (λ (rcode)
                                               (cps-i body (cons x met) k-it (λ (bcode)
                                                                               (k (subst x `(,acode ,rcode) bcode))))))))]
    [(k ,sth) (guard (eq? k-it #t)) (cps-i sth met #f k)]))



(define (cps-i-d cterm met k-it k)
  (match cterm
    [,sym (guard (symbol? sym)
                 (member sym met)) (apply-cps-i-d k sym)]
    [(λ (,x k) ,body)
     (apply-cps-i-d k `(λ (,x) ,(cps-i-d body (cons x met) #t 'k-id)))]
    [(,app ,rator (λ (,x) ,body))
     (cps-i-d app met #f `(k-app-2 ,rator ,met ,body ,x ,met ,k-it ,k))]
    [(k ,sth) (guard (eq? k-it #t)) (cps-i-d sth met #f k)]))


(define (apply-cps-i-d k-strcut code)
  (match k-strcut
    [k-id code]
    [(k-app-0 ,k ,x ,acode ,rcode)
     (apply-cps-i-d k (subst x `(,acode ,rcode) code))]
    [(k-app-1 ,body ,x, met ,k-it ,k ,acode)
     (cps-i-d body (cons x met) k-it `(k-app-0 ,k ,x ,acode ,code))]
    [(k-app-2 ,rator ,body ,x ,met ,k-it ,k)
     (cps-i-d rator met #f `(k-app-1 ,body ,x ,met ,k-it ,k ,code))]))
