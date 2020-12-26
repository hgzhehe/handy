(define (cps-iᵒ cterm met k-it k out)
  (conde
   [(symbolo cterm)
    (proper-memberᵒ cterm met)
    (apply-cps-iᵒ k cterm out)]
   [(fresh (x body m1 bodyres)
      (== cterm `(λ (,x k) ,body))
      (consᵒ x met m1)
      (cps-iᵒ body m1 #t 'k-id bodyres)
      (apply-cps-iᵒ k `(λ (,x) ,bodyres) out))]
   [(fresh (app rator x body)
      (== cterm `(,app ,rator (λ (,x) ,body)))
      (cps-iᵒ app met #f `(k-app-2 ,rator ,body ,x ,met ,k-it ,k) out))]
   [(fresh (sth)
      (== cterm `(k ,sth))
      (== k-it #t)
      (cps-iᵒ sth met #f k out))]))


(define (apply-cps-iᵒ k-strcut code out)
  (conde
   [(== k-strcut 'k-id) (== out code)]
   [(fresh (k x acode rcode substout)
      (== k-strcut `(k-app-0 ,k ,x ,acode ,rcode))
      (substᵒ x `(,acode ,rcode) code substout)
      (apply-cps-iᵒ k substout out))]
   [(fresh (body x met k-it k acode m1)
      (== k-strcut `(k-app-1 ,body ,x ,met ,k-it ,k ,acode))
      (consᵒ x met m1)
      (cps-iᵒ body m1 k-it `(k-app-0 ,k ,x ,acode ,code) out))]
   [(fresh (rator met body x k-it k)
      (== k-strcut `(k-app-2 ,rator ,body ,x ,met ,k-it ,k))
      (cps-iᵒ rator met #f `(k-app-1 ,body ,x, met ,k-it ,k ,code) out))]))
