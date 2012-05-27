(load "pmatch.scm")

(define occur-free?
  (lambda (y exp)
    (pmatch exp
      [,x (guard (symbol? x)) (eq? y x)]
      [(lambda (,x) ,e) (and (not (eq? y x)) (occur-free? y e))]
      [(,rator ,rand) (or (occur-free? y rator) (occur-free? y rand))])))

(define value?
  (lambda (exp)
    (pmatch exp
      [,x (guard (symbol? x)) #t]
      [(lambda (,x) ,e) #t]
      [(,rator ,rand) #f])))

(define app? (lambda (x) (not (value? x))))

(define term-length
  (lambda (exp)
    (pmatch exp
      [,x (guard (symbol? x)) 0]
      [(lambda (,x) ,e) (+ 1 (term-length e))]
      [(,rator ,rand) (+ 1 (term-length rator) (term-length rand))])))

; call-by-name compiler to S, K, I
(define compile
  (lambda (exp)
    (pmatch exp
      [,x (guard (symbol? x)) x]
      [(,M ,N) `(,(compile M) ,(compile N))]
      [(lambda (,x) (,M ,y))
       (guard (eq? x y) (not (occur-free? x M))) (compile M)]
      [(lambda (,x) ,y) (guard (eq? x y)) `I]
      [(lambda (,x) (,M ,N)) (guard (or (occur-free? x M) (occur-free? x N)))
       `((S ,(compile `(lambda (,x) ,M))) ,(compile `(lambda (,x) ,N)))]
      [(lambda (,x) ,M) (guard (not (occur-free? x M))) `(K ,(compile M))]
      [(lambda (,x) ,M) (guard (occur-free? x M))
       (compile `(lambda (,x) ,(compile M)))])))

; call-by-name compiler to S, K, I, B, C
(define compile-bc
  (lambda (exp)
    (pmatch exp
      [,x (guard (symbol? x)) x]
      [(,M ,N) `(,(compile-bc M) ,(compile-bc N))]
      [(lambda (,x) ,y) (guard (eq? x y)) `I]
      [(lambda (,x) (,M ,y))
       (guard (eq? x y) (not (occur-free? x M))) (compile-bc M)]
      [(lambda (,x) (,M ,N)) (guard (and (not (occur-free? x M)) (occur-free? x N)))
       `((B ,(compile-bc M)) ,(compile-bc `(lambda (,x) ,N)))]
      [(lambda (,x) (,M ,N)) (guard (and (occur-free? x M) (not (occur-free? x N))))
       `((C ,(compile-bc `(lambda (,x) ,M))) ,(compile-bc N))]
      [(lambda (,x) (,M ,N)) (guard (or (occur-free? x M) (occur-free? x N)))
       `((S ,(compile-bc `(lambda (,x) ,M))) ,(compile-bc `(lambda (,x) ,N)))]
      [(lambda (,x) ,M) (guard (not (occur-free? x M))) `(K ,(compile-bc M))]
      [(lambda (,x) ,M) (guard (occur-free? x M))
       (compile-bc `(lambda (,x) ,(compile-bc M)))])))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ski->lanbda converter
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; create gensyms
(define fv
  (let ((n -1))
    (lambda (x)
      (set! n (+ 1 n))
      (string->symbol
       (string-append (symbol->string x) "." (number->string n))))))

;; substitution with free variable capturing avoiding
(define subst
  (lambda (x y exp)
    (pmatch exp
      [,u (guard (symbol? u)) (if (eq? u x) y u)]
      [(lambda (,u) ,e)
       (cond
        [(eq? u x) exp]
        [(occur-free? u y)              ; possible capture, switch names
         (let* ([u* (fv u)]
                [e* (subst u u* e)])
           `(lambda (,u*) ,(subst x y e*)))]
        [else
         `(lambda (,u) ,(subst x y e))])]
      [(,e1 ,e2) `(,(subst x y e1) ,(subst x y e2))]
      [,exp exp])))


; combinator definitions
(define com-table
  '((S . (lambda (f) (lambda (g) (lambda (x) ((f x) (g x))))))
    (K . (lambda (x) (lambda (y) x)))
    (I . (lambda (x) x))
    (B . (lambda (f) (lambda (g) (lambda (x) (f (g x))))))
    (C . (lambda (a) (lambda (b) (lambda (c) ((a c) b)))))))

; substitute combinator with their lambda term definitions
(define sub-com
  (lambda (exp defs)
    (cond
     [(null? defs) exp]
     [else (sub-com (subst (caar defs) (cdar defs) exp) (cdr defs))])))

(define ski->lambda
  (lambda (exp)
    (sub-com exp com-table)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define to-number `(lambda (n) ((n (lambda (x) (,add1 x))) 0)))

(interp `(,to-number ,(ski->lambda (compile-bc `(,!-n ,lfive)))))
; => 120
(term-length `(,! ,lfive))
; => 93
(term-length (compile `(,! ,lfive)))
; => 144
(term-length (compile-bc `(,! ,lfive)))
; => 73

