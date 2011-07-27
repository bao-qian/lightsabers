;; A call-by-need interpreter for lambda calculus with some primitives.
;; Used with my SKI-compiler to demostrate the properties of my so-called
;; lazy-SKI combinators.

;; author: Yin Wang (yw21@cs.indiana.edu)



(load "pmatch.scm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; a compositional version:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-syntax memo
  (syntax-rules ()
    [(_ body)
     (let ([val? #f] [e (lambda () body)])
       (lambda ()
         (if val?
             e
             (begin
               (set! val? #t)
               (set! e (e))
               e))))]))

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
         (if (and (number? v1) (number? v2))
             ((eval op) v1 v2)
             `(,op ,v1 ,v2)))]
      [(,f . ,x*) (guard (procedure? f))
       (apply f (map (lambda (x) (interp1 x env)) x*))]
      [(,e1 ,e2)
       (let ([v1 (interp1 e1 env)])
         (if (procedure? v1)
             (v1 (memo (interp1 e2 env)))
             `(,v1 ,(interp1 e2 env))))]
      [,exp (eval exp)])))

(define interp
  (lambda (exp)
    (interp1 exp (lambda (x) (lambda () x)))))

