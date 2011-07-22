(case-sensitive #t)
(load "pmatch.scm")

(define value?
  (lambda (exp)
    (pmatch exp
      [,x (guard (atom? x)) #t]
      [((lambda (,x) ,e) ,env) #t]
      [else #f])))

(define mt-env 'mt-env)
(define mt-h 'mt-h)
(define mt-k 'mt-k)

(define -->
  (lambda (s)
    (pmatch s
      [(,v^ (ARG (,rand ,env) ,k) ,h) (guard (value? v^))
       `((,rand ,env) (FUN ,v^ ,k) (ARG ,@h))]
      [(,v^ (FUN ((lambda (,x) ,body) ,env) ,k) ,h) (guard (value? v^))
       `((,body ((,x ,v^) ,env)) ,k (FUN ,@h))]
      [((,x ,env) ,k ,h) (guard (atom? x))
       `(, (apply-env env x) ,k ((ENV ,x ,env) ,@h))]
      [(((,rator ,rand) ,env) ,k ,h)
       `((,rator ,env) (ARG (,rand ,env) ,k) (APP ,@h))])))

(define <--
  (lambda (s)
    (pmatch s
      [((,rand ,env) (FUN ,v^ ,k) (ARG . ,h))
       `(,v^ (ARG (,rand ,env) ,k) ,h)]
      [((,body ((,x ,v^) ,env)) ,k (FUN . ,h))
       `(,v^ (FUN ((lambda (,x) ,body) ,env) ,k) ,h)]
      [(,y ,k ((ENV ,x ,env) . ,h))
       `((,x ,env) ,k ,h)]
      [((,rator ,env) (ARG (,rand ,env) ,k) (APP . ,h))
       `(((,rator ,rand) ,env) ,k ,h)])))


; For the convenience of experiments, lookup will output unbound variables
; symbolically instead of raising errors
(define apply-env
  (lambda (env x)
    (pmatch env
      [,env (guard (eq? env mt-env)) x]
      [((,x^ ,v^) ,env)
       (if (eq? x x^) v^ (apply-env env x))])))

(define de-closure
  (lambda (clos)
    (letrec ([dec
              (lambda (exp bound env)
                (pmatch exp
                  [,u (guard (symbol? u) (not (memq u bound))) (apply-env env u)]
                  [(lambda (,u) ,e)
                   `(lambda (,u) , (dec e (cons u bound) env))]
                  [(,e1 ,e2) `(, (dec e1 bound env) , (dec e2 bound env))]
                  [,exp exp]))])
      (dec (car clos) '() (cadr clos)))))

(define ==>
  (lambda (exp)
    (letrec ((step
              (lambda (s n)
                (pmatch s
                  [(,exp ,k ,h) (guard (value? exp) (eq? k mt-k))
                   (printf "~a steps\n" n)
                   s]
                  [else (step (--> s) (add1 n))]))))
      (step exp 0))))

(define <==
  (lambda (exp)
    (letrec ((step
              (lambda (s n)
                (pmatch s
                  [(,exp ,k ,h) (guard (eq? h mt-h))
                   (printf "~a steps\n" n)
                   s]
                  [else (step (<-- s) (add1 n))]))))
      (step exp 0))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; go forwards, backwards, back-and-forth, ...

; source state
(define s `((((lambda (x) x) ((lambda (u) u) y)) ,mt-env) ,mt-k ,mt-h))

; go forwards (evaluate multiple times)
(define s
  (let ([s^ (--> s)])
    (printf "~a\n" s^)
    s^))

;; =>
;; (((lambda (x) x) mt-env) (ARG (((lambda (u) u) y) mt-env) mt-k) (APP . mt-h))
;; ((((lambda (u) u) y) mt-env) (FUN ((lambda (x) x) mt-env) mt-k) (ARG APP . mt-h))
;; (((lambda (u) u) mt-env) (ARG (y mt-env) (FUN ((lambda (x) x) mt-env) mt-k)) (APP ARG APP . mt-h))
;; ((y mt-env) (FUN ((lambda (u) u) mt-env) (FUN ((lambda (x) x) mt-env) mt-k)) (ARG APP ARG APP . mt-h))
;; (y (FUN ((lambda (u) u) mt-env) (FUN ((lambda (x) x) mt-env) mt-k)) ((ENV y mt-env) ARG APP ARG APP . mt-h))
;; ((u ((u y) mt-env)) (FUN ((lambda (x) x) mt-env) mt-k) (FUN (ENV y mt-env) ARG APP ARG APP . mt-h))
;; (y (FUN ((lambda (x) x) mt-env) mt-k) ((ENV u ((u y) mt-env)) FUN (ENV y mt-env) ARG APP ARG APP . mt-h))
;; ((x ((x y) mt-env)) mt-k (FUN (ENV u ((u y) mt-env)) FUN (ENV y mt-env) ARG APP ARG APP . mt-h))
;; (y mt-k ((ENV x ((x y) mt-env)) FUN (ENV u ((u y) mt-env)) FUN (ENV y mt-env) ARG APP ARG APP . mt-h))


; go backwards
(define s
  (let ([s^ (<-- s)])
    (printf "~a\n" s^)
    s^))

;; =>
;; ((x ((x y) mt-env)) mt-k (FUN (ENV u ((u y) mt-env)) FUN (ENV y mt-env) ARG APP ARG APP . mt-h))
;; (y (FUN ((lambda (x) x) mt-env) mt-k) ((ENV u ((u y) mt-env)) FUN (ENV y mt-env) ARG APP ARG APP . mt-h))
;; ((u ((u y) mt-env)) (FUN ((lambda (x) x) mt-env) mt-k) (FUN (ENV y mt-env) ARG APP ARG APP . mt-h))
;; (y (FUN ((lambda (u) u) mt-env) (FUN ((lambda (x) x) mt-env) mt-k)) ((ENV y mt-env) ARG APP ARG APP . mt-h))
;; ((y mt-env) (FUN ((lambda (u) u) mt-env) (FUN ((lambda (x) x) mt-env) mt-k)) (ARG APP ARG APP . mt-h))
;; (((lambda (u) u) mt-env) (ARG (y mt-env) (FUN ((lambda (x) x) mt-env) mt-k)) (APP ARG APP . mt-h))
;; ((((lambda (u) u) y) mt-env) (FUN ((lambda (x) x) mt-env) mt-k) (ARG APP . mt-h))
;; (((lambda (x) x) mt-env) (ARG (((lambda (u) u) y) mt-env) mt-k) (APP . mt-h))
;; ((((lambda (x) x) ((lambda (u) u) y)) mt-env) mt-k mt-h)

;; or switch directions any time you like


;;; Example 2: factorial
(load "encoding.scm")

(define s `(((,! ,lfive) ,mt-env) ,mt-k ,mt-h))

(define r1 (==> s))
; => 1420 steps (result too large to print)

(define r2 (<== r1))
; => 1420 steps

(equal? r2 s)
; => #t


(define test
  (lambda (name exp)
    (let* ([s `((,exp ,mt-env) ,mt-k ,mt-h)]
           [r1 (==> s)]
           [r2 (<== r1)])
      (if (equal? r2 s)
          (printf "test \"~a\" ... succeeded\n" name)
          (printf "test \"~a\" ... failed\n" name)))))

(test "succ" `(,lsucc ,lfive))
(test "pred" `(,lpred ,lfive))
(test "times" `((,ltimes ,ltwo) ,lthree))
(test "plus" `((,lplus ,ltwo) ,lthree))
(test "sub" `((,lsub ,lthree) ,ltwo))
(test "pow" `((,lpow ,ltwo) ,lthree))
(test "car" `(,lcar ((,lpair ,lone) ,ltwo)))
(test "!5" `(,! ,lfive))
(test "!7" `(,! ,l7))

