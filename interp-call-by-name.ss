;; call-by-name interpreter (reducer)


(load "pmatch.scm")
(load "encoding.scm")


(define occur-free?
  (lambda (y exp)
    (pmatch exp
      [(lambda (,x) ,e) (and (not (eq? y x)) (occur-free? y e))]
      [(,rator ,rand) (or (occur-free? y rator) (occur-free? y rand))]
      [,exp (eq? y exp)])))

(define value?
  (lambda (exp)
    (pmatch exp
      [,x (guard (symbol? x)) #t]
      [(lambda (,x) ,e) #t]
      [(,rator ,rand) #f])))

(define gensym
  (let ((n -1))
    (lambda (x)
      (set! n (+ 1 n))
      (string->symbol
       (string-append (symbol->string x) "." (number->string n))))))

(define subst
  (lambda (x y exp)
    (pmatch exp
      [,u (guard (symbol? u)) (if (eq? u x) y u)]
      [(lambda (,u) ,e)
       (cond
        [(eq? u x) exp]
        [(and (occur-free? u y) (occur-free? x e))
         (let* ([u* (gensym u)]
                [e* (subst u u* e)])
           `(lambda (,u*) ,(subst x y e*)))]
        [else
         `(lambda (,u) ,(subst x y e))])]
      [(,e1 ,e2) `(,(subst x y e1) ,(subst x y e2))]
      [,exp exp])))

(define redex-of car)
(define ctx-of cdr)
(define find-redexes
  (lambda (exp)
    (letrec ([find
              (lambda (exp C)
                (pmatch exp
                  [(lambda (,x) ,e)
                   (find e (lambda (v) (C `(lambda (,x) ,v))))]
                  [((lambda (,x) ,e1) ,e2)
                   (append `((,exp . ,C))
                           (find e1 (lambda (v) (C `((lambda (,x) ,v) ,e2))))
                           (find e2 (lambda (v) (C `((lambda (,x) ,e1) ,v)))))]
                  [(,e1 ,e2)
                   (append (find e1 (lambda (v) (C `(,v ,e2))))
                           (find e2 (lambda (v) (C `(,e1 ,v)))))]
                  [,exp '()]))])
      (find exp (lambda (v) v)))))


;; do one beta-reduction if the operand is a lambda, otherwise output it
;; verbatically.
(define beta
  (lambda (redex)
    (pmatch redex
      [((lambda (,x) ,e1) ,e2) (subst x e2 e1)]
      [,other other])))

;; deterministic reducer
(define reducer
  (lambda (exp)
    (let ([redexes (find-redexes exp)])
      (cond
       [(null? redexes) exp]
       [else
        (let ([first (car redexes)])
          (reducer ((ctx-of first) (beta (redex-of first)))))]))))

;;; random reducer
(define random-reducer
  (lambda (exp tick)
    (cond
     [(zero? tick) exp]
     [else
      (let ([redexes (find-redexes exp)])
        (cond
         [(null? redexes) exp]
         [else
          (let* ([pick (list-ref redexes (random (length redexes)))]
                 [new-exp ((ctx-of pick) (beta (redex-of pick)))])
            (random-reducer new-exp (sub1 tick)))]))])))


;;; tests
(reducer `(,!-n ,lthree))
; => (lambda (f) (lambda (x) (f (f (f (f (f (f x))))))))

(reducer (random-reducer `(,!-n ,lthree) 300))
; => (lambda (f) (lambda (x.42) (f (f (f (f (f (f x.42))))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (reducer '((lambda (y) z) ((lambda (x) (x x)) (lambda (x) (x x)))))

;; (nd-reducer '((lambda (y) z) ((lambda (x) (x x)) (lambda (x) (x x)))) 3)
;; (map reducer (nd-reducer `(,! ,ltwo) 1))



; non-deterministic reducer
(define nd-reducer
  (lambda (exp tick)
    (letrec ([reduce1
              (lambda (redexes tick)
                (cond
                 [(null? redexes) '()]
                 [(zero? tick) (map (lambda (x) ((ctx-of x) (redex-of x))) redexes)]
                 [else
                  (let ([pick (list-ref redexes (random (length redexes)))])
                    (cond
                     [(value? pick)
                      (reduce1 redexes tick)]
                     [else
                      (let ([pick* ((ctx-of pick) (beta (redex-of pick)))]
                            [new-redexes (append (remq pick redexes)
                                                 (find-redexes pick*) `((,pick* . ,(lambda (v) v))))])
                        (if (null? new-redexes)
                            'haha
                            (reduce1 new-redexes (sub1 tick))))]))]))])
      (reduce1 (find-redexes exp) tick))))

