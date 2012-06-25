;; A call-by-value interpreter for lambda calculus with primitive operators

;; author: Yin Wang (yw21@cs.indiana.edu)


(load "pmatch.scm")
(load "encoding.scm")


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
(define make-closure
  (lambda (f env)
    (list 'closure f env)))

(define closure-func cadr)
(define closure-env caddr)

(define closure?
  (lambda (x)
    (and (pair? x)
         (eq? (car x) 'closure))))



;; cbv interpreter
(define interp1
  (lambda (exp env)
    (pmatch exp
      [,x (guard (symbol? x)) (lookup x env)]
      [,x (guard (number? x)) x]
      [(lambda (,x) ,e)
       (make-closure exp env)]
      [(,e1 ,e2)
       (let ([v1 (interp1 e1 env)]
             [v2 (interp1 e2 env)])
         (pmatch v1
           [(closure (lambda (,x) ,e) ,env1)
            (interp1 e (ext-env x v2 env1))]
           [,other
            (eval `(,v1 ,v2))]))]
      [,exp (eval exp)])))


(define interp
  (lambda (exp)
    (interp1 exp env0)))



;; ------------------------ tests -------------------------
(interp `(((,ltwo ,ltwo) add1) 1))
;; => 5
