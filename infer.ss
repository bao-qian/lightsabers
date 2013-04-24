;; infer.ss
;; a type inferencer for simply typed lambda calculus


(load "pmatch.scm")

;; utilities
(define-syntax letv*
  (syntax-rules ()
    [(_ () body ...) (begin body ...)]
    [(_ ([x0 v0] [x1 v1] ...) body ...)
     (let-values ([x0 v0])
       (letv* ([x1 v1] ...)
              body ...))]))

(define fatal
  (lambda (who . args)
    (display who) (display ": ")
    (for-each display args)
    (display "\n")
    (error 'infer "")))

(define add1
  (lambda (x)
    (+ x 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;; types ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define var (lambda (v) (vector v)))
(define var? vector?)
(define ext (lambda (x v s) `((,x . ,v) . ,s)))
(define s0 '())

;;;;;;;;;;;;;;;;;;;;;;;; unification ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define walk
  (lambda (x s)
    (let ([slot (assq x s)])
      (cond
       [(not slot) x]
       [(var? (cdr slot)) (walk (cdr slot) s)]
       [else (cdr slot)]))))

(define occurs
  (lambda (u v)
    (cond
     [(eq? u v) #t]
     [(pair? v)
      (or (occurs u (car v)) (occurs u (cdr v)))]
     [else #f])))

(define unify
  (lambda (u v s)
    (let ([u (walk u s)] 
          [v (walk v s)])
      (cond
       [(eq? u v) s]
       [(var? u) (and (not (occurs u v)) (ext u v s))]
       [(var? v) (and (not (occurs v u)) (ext v u s))]
       [(and (pair? u) (pair? v))
        (let ((s^ (unify (car u) (car v) s)))
          (and s^ (unify (cdr u) (cdr v) s^)))]
       [(equal? u v) s]
       [else #f]))))

(define reify
  (lambda (x s)
    (define name
      (lambda (n) 
        (string->symbol 
         (string-append "t" (number->string n)))))
    (define reify1
      (lambda (x n s)
        (let ((x (walk x s)))
          (cond
           [(pair? x)
            (letv* ([(u n1 s1) (reify1 (car x) n s)]
                    [(v n2 s2) (reify1 (cdr x) n1 s1)])
              (values (cons u v) n2 s2))]
           [(var? x)
            (let ([v* (name n)])
              (values v* (add1 n) (ext x v* s)))]
           [else (values x n s)]))))
    (letv* ([(x* n* s*) (reify1 x 0 s)]) x*)))

;;;;;;;;;;;;;;;;;;;;;;;;;; environment ;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define ext-env (lambda (x v s) `((,x . ,v) . ,s)))

(define lookup
  (lambda (x env)
    (let ((slot (assq x env)))
      (cond 
       [(not slot) (error 'lookup "unbound variable ~a" x)]
       [else (cdr slot)]))))

(define env0
  `((zero? . (int -> bool))
    (add1  . (int -> int))
    (sub1  . (int -> int))
    (=     . (int -> (int -> bool)))
    (<=    . (int -> (int -> bool)))
    (<     . (int -> (int -> bool)))
    (>=    . (int -> (int -> bool)))
    (>     . (int -> (int -> bool)))
    (*     . (int -> (int -> int)))
    (-     . (int -> (int -> int)))
    (+     . (int -> (int -> int)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;; inferencer ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define infer
  (lambda (exp)
    (define infer1
      (lambda (exp env s)
        (pmatch exp
          [,x (guard (number? x)) (values 'int s)]
          [,x (guard (boolean? x)) (values 'bool s)]
          [,x (guard (string? x)) (values 'string s)]
          [,x (guard (symbol? x)) (values (lookup x env) s)]
          [(if ,test ,conseq ,alt)
           (letv* ([(t1 s1) (infer1 test env s)]
                   [(s1^) (unify t1 'bool s1)])
             (cond
              [s1^
               (letv* ([(t2 s2) (infer1 conseq env s1^)]
                       [(t3 s3) (infer1 alt env s2)]
                       [(s4) (unify t2 t3 s3)])
                 (cond
                  [s4 (values t3 s4)]
                  [else 
                   (fatal 'infer 
                          "branches must have the same type       \n\n"
                          " - expression:        "  exp            "\n"
                          " - true branch type:  " (reify t2 s3)   "\n"
                          " - false branch type: " (reify t3 s3))  ]))]
              [else 
               (fatal 'infer 
                      "test is not of type bool       \n\n" 
                      "expression:   " exp             "\n"
                      "irritant:     " test            "\n"
                      "type:         " (reify t1 s1)  )]))]
          [(lambda (,x) ,body)
           (letv* ([(t1) (var x)]
                   [(env*) (ext-env x t1 env)]
                   [(t2 s^) (infer1 body env* s)])
             (values `(,t1 -> ,t2) s^))]
          [(,e1 ,e2)
           (letv* ([(t1 s1) (infer1 e1 env s)]
                   [(t2 s2) (infer1 e2 env s1)]
                   [(t3) (var 't3)]
                   [(t4) (var 't4)]
                   [(s3) (unify t1 `(,t3 -> ,t4) s2)])
             (cond
              [(not s3)
               (fatal 'infer 
                      "trying to apply non-function:\n\n"
                      " - irritant: " e1             "\n"
                      " - type:     " (reify t1 s1)    )]
              [else
               (let ([s4 (unify t2 t3 s3)])
                 (cond
                  [(not s4)
                   (fatal 'infer 
                          "wrong argument type:              \n\n"
                          " - function:      " e1             "\n"
                          " - function type: " (reify t1 s3)  "\n"
                          " - expected type: " (reify t3 s3)  "\n"
                          " - argument type: " (reify t2 s3)  "\n"
                          " - argument:      " e2               )]
                  [else
                   (values t4 s4)]))]))])))
    (letv* ([(t s) (infer1 exp env0 s0)])
      (reify t s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; tests ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; correct programs
(infer 1)
; => int

(infer #t)
; => bool

(infer '(lambda (v) v))
; => (t0 -> t0)

(infer '(lambda (f) (lambda (x) (f x))))
; => ((t0 -> t1) -> (t0 -> t1))

(infer '(lambda (f) (lambda (x) (f (f x)))))
; => ((t0 -> t0) -> (t0 -> t0))

(infer '((lambda (f) (lambda (x) (f (f x)))) add1))
; => (int -> int)

(infer '(if (zero? 1) #t #f))
; => bool

(infer '(lambda (f) (lambda (x) (f ((+ x) 1)))))
; => ((int -> t0) -> (int -> t0))

(infer '(lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m (n f)) x))))))
; => ((t0 -> (t1 -> t2)) -> ((t3 -> t0) -> (t3 -> (t1 -> t2))))

(infer '((lambda (f) (f 1)) (lambda (v) v)))
; => int

(infer '(if (zero? 1) #f #t))
; => bool

(define S '(lambda (x) (lambda (y) (lambda (z) ((x z) (y z))))))
(define K '(lambda (x) (lambda (y) x)))

(infer S)
; => ((t0 -> (t1 -> t2)) -> ((t0 -> t1) -> (t0 -> t2)))

(infer `(,S ,K))
; => ((t0 -> t1) -> (t0 -> t0))

(infer `((,S ,K) ,K))
; => (t0 -> t0)

; incorrect programs
(infer '(lambda (f) (f f)))
;; infer: trying to apply function to wrong type argument:
;;  - function:      f
;;  - function type: (t0 -> t1)
;;  - expected type: t0
;;  - argument type: (t0 -> t1)
;;  - argument: f

(infer '(if (zero? 1) #t 1))
;; infer: branches of conditional must have the same type
;;  - expression:        (if (zero? 1) #t 1)
;;  - true branch type:  bool
;;  - false branch type: int

(infer '((lambda (x) ((+ 1) x)) "hello"))
;; infer: trying to apply function to wrong type argument:
;;  - function:      (lambda (x) ((+ 1) x))
;;  - function type: (int -> int)
;;  - expected type: int
;;  - argument type: string
;;  - argument: hello
