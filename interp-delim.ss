(load "pmatch.scm")

(define *debug* #t)
(define-syntax peek
  (syntax-rules ()
    [(_ name args ...)
     (if *debug*
         (begin
           (printf "~s: ~s = ~s~n" name 'args args)
           ...)
         (void))]))

(define lookup
  (lambda (x env)
    (cond
     [(assq x env) => cdr]
     [else #f])))


(define apply-all
  (lambda (cs x)
    (cond
     [(null? cs) x]
     [else
      (apply-all (cdr cs) ((car cs) x))])))


(define interp
  (lambda (exp)
    (define interp1
      (lambda (exp env c mc)
        (pmatch exp
          [,x (guard (number? x))
              (c x)]
          [,x (guard (not (pair? x)))
           (let ([v (lookup x env)])
             (cond
              [(not v)
               (error 'interp "unbound variable ~a" x)]
              [else
               (c v)]))]
          [(lambda (,x) ,body)
           (c (lambda (v)
                (interp1 body
                         (cons `(,x . ,v) env)
                         (lambda (x) x)
                         '())))]
          [(reset ,e)
           (interp1 e env
                    (lambda (x) x)
                    (cons c mc))]
          [(shift0 (,k) ,e)
           (interp1 e (cons `(,k . ,c) env)
                    (car mc)
                    (cdr mc))]
          [(+ ,a ,b)
           (interp1 a env
                    (lambda (va)
                      (interp1 b env
                               (lambda (vb)
                                 (c (+ va vb)))
                               mc))
                    mc)]
          [(,rator ,rand)
           (interp1 rator env
                    (lambda (f)
                      (interp1 rand env
                               (lambda (v) (c (f v)))
                               mc))
                    mc)])))
    (interp1 exp '() (lambda (x) x) '())))


(interp '(+ 1 (+ 2 (+ 4 8))))

(interp '(+ 1 (reset (+ 2 (+ (shift0 (k) 4) 8)))))

(interp '(+ 10 (reset (+ 2 (shift0 (k) (+ 100 (k (k 3))))))))

(interp '(reset (+ 1 (reset (+ 2 (reset (+ 4 (shift0 (k1) (shift0 (k2) 8)))))))))

(interp '(reset (+ 1 (reset (+ 2 ((shift0 (k1) (k1 (lambda (x) x))) (shift0 (k2) 4)))))))

(interp '(+ 1 (reset (+ 2 3))))

