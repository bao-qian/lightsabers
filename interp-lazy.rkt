;; A lazy interpreter for lambda calculus with some primitives


(define env0 '())

(define ext
  (lambda (x v env)
    (cons (cons x v) env)))

(define lookup
  (lambda (x env)
    (cond
     [(assq x env) => cdr]
     [else #f])))



;; Thunk structure. Fields:
;; 1. the function or the value depending on whether cached? is #t
;; 2. whether the function has been forced already
(struct thunk (fv cached?) #:transparent #:mutable)


;; Closure structure
(struct closure (fun env))



;; Redefining "delay" and "force" of Scheme just for independence

(define make-thunk
  (lambda (fun)
    (thunk fun #f)))

(define force-thunk
  (lambda (th)
    (cond
     [(thunk-cached? th)
      (thunk-fv th)]
     [else
      (let loop ([val ((thunk-fv th))])
        (cond
         [(thunk? val)
          (loop ((thunk-fv val)))]
         [else
          (set-thunk-fv! th val)
          (set-thunk-cached?! th #t)
          val]))])))



(define interp1
  (lambda (exp env)
    (match exp
      [(? number? x) x]
      [(? symbol? x)
       (lookup x env)]
      [`(lambda (,x) ,e)
       (closure exp env)]
      [`(,e1 ,e2)
       (let ([v1 (make-thunk (lambda () (interp1 e1 env)))]
             [v2 (make-thunk (lambda () (interp1 e2 env)))])
         (make-thunk
          (lambda ()
            (let ([v1+ (force-thunk v1)])
              (match v1+
                [(closure `(lambda (,x) ,e) env1)
                 (interp1 e (ext x v2 env1))])))))])))


(define interp
  (lambda (exp)
    (force-thunk (interp1 exp env0))))




;; ------------------------ tests -------------------------

(interp
 '((lambda (x) 42)
   ((lambda (x) (x x))
    (lambda (x) (x x)))))

(interp
 '((lambda (x) 42)
   ((lambda (x) x)
    ((lambda (x) (x x))
     (lambda (x) (x x))))))

;;; infinite loop
;; (interp
;;  '((lambda (x) (x x))
;;    (lambda (x) (x x))))
