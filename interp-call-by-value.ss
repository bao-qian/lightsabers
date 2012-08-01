;; A call-by-value interpreter for lambda calculus with primitive operators

;; author: Yin Wang (yw21@cs.indiana.edu)


;; environment
(define env0 '())

(define ext-env
  (lambda (x v env)
    (cons `(,x . ,v) env)))

(define lookup
  (lambda (x env)
    (let ([p (assq x env)])
      (cond
       [(not p) x]
       [else (cdr p)]))))


;; closure "structure"
(struct Closure (f env))


;; cbv interpreter
(define interp1
  (lambda (exp env)
    (match exp
      [(? symbol? x) (lookup x env)]
      [(? number? x) x]
      [`(lambda (,x) ,e)
       (Closure exp env)]
      [`(,e1 ,e2)
       (let ([v1 (interp1 e1 env)]
             [v2 (interp1 e2 env)])
         (match v1
           [(Closure `(lambda (,x) ,e) env1)
            (interp1 e (ext-env x v2 env1))]
           [other
            (eval `(,v1 ,v2))]))]
      [`(,op ,e1 ,e2)
       (let ([v1 (interp1 e1 env)]
             [v2 (interp1 e2 env)])
         (eval `(,op ,v1 ,v2)))]
      [exp (eval exp)])))


(define interp
  (lambda (exp)
    (interp1 exp env0)))



;; ------------------------ tests -------------------------
(interp (add1 1))
;; => 2

(interp (+ 1 2))
;; => 3

(interp (((lambda (x) (lambda (y) (* x y))) 2) 3))
;; => 6

(interp ((lambda (x) (* 2 x)) 3))
;; => 6
