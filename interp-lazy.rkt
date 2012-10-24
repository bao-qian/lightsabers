;; A call-by-need interpreter for lambda calculus with some primitives.
;; Used with my SKI-compiler to demostrate the properties of my so-called
;; lazy-SKI combinators.

;; author: Yin Wang (yw21@cs.indiana.edu)


(load "pmatch.scm")


(define interp1
  (lambda (exp env)
    (pmatch exp
      [,x (guard (symbol? x)) ((env x))]
      [,x (guard (number? x)) x]
      [(lambda (,x) ,e)
       (lambda (v)
         (interp1 e (lambda (x^)
                      (if (eq? x^ x) v (env x^)))))]
      [(,op ,e1 ,e2) (guard (memq op '(+ - * /)))
       (let ([v1 (interp1 e1 env)]
             [v2 (interp1 e2 env)])
         (cond
          [(and (number? v1) (number? v2))
           ((eval op) v1 v2)]
          [else
           `(,op ,v1 ,v2)]))]
      [(,f ,x) (guard (procedure? f))
       (f (interp1 x env))]
      [(,e1 ,e2)
       (let ([v1 (interp1 e1 env)])
         (cond
          [(procedure? v1)
           (v1 (let ([val? #f]
                     [e (lambda () (interp1 e2 env))])
                 (lambda ()
                   (cond
                    [val? e]
                    [else
                     (begin
                       (set! val? #t)
                       (set! e (e))
                       e)]))))]
          [else
           `(,v1 ,(interp1 e2 env))]))]
      [,exp (eval exp)])))


(define interp
  (lambda (exp)
    (interp1 exp (lambda (x) (lambda () x)))))



;; ------------------------ tests -------------------------
(interp
 '((lambda (x) 42)
   ((lambda (x) (x x))
    (lambda (x) (x x)))))
