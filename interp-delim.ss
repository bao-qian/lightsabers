(define-syntax pmatch
  (syntax-rules (else guard)
    ((_ (rator rand ...) cs ...)
     (let ((v (rator rand ...)))
       (pmatch v cs ...)))
    ((_ v) (error 'pmatch "failed: ~s" v))
    ((_ v (else e0 e ...)) (begin e0 e ...))
    ((_ v (pat (guard g ...) e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch v cs ...))))
       (ppat v pat (if (and g ...) (begin e0 e ...) (fk)) (fk))))
    ((_ v (pat e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch v cs ...))))
       (ppat v pat (begin e0 e ...) (fk))))))

(define-syntax ppat
  (syntax-rules (_ quote unquote)
    ((_ v _ kt kf) kt)
    ((_ v () kt kf) (if (null? v) kt kf))
    ((_ v (quote lit) kt kf) (if (equal? v (quote lit)) kt kf))
    ((_ v (unquote var) kt kf) (let ((var v)) kt))
    ((_ v (x . y) kt kf)
     (if (pair? v)
       (let ((vx (car v)) (vy (cdr v)))
	 (ppat vx x (ppat vy y kt kf) kf))
       kf))
    ((_ v lit kt kf) (if (equal? v (quote lit)) kt kf))))

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



;; Danvy-filinski test
(interp '(+ 10 (reset (+ 2 (shift0 (k) (+ 100 (k (k 3))))))))
; => 117 (pass)

;; Danvy-filinski paper
(interp '(+ 5 (reset (+ 3 (shift0 (c) (+ (c 0) (c 1)))))))
; => 12 (pass)

(interp '(+ 1 (+ 2 (+ 4 8))))
; => 15 (pass)

(interp '(+ 1 (reset (+ 2 (+ (shift0 (k) 4) 8)))))
; => 5 (pass)

(interp '(reset (+ 1 (reset (+ 2 (reset (+ 4 (shift0 (k1) (shift0 (k2) 8)))))))))
; => 9 (pass)

(interp '(reset (+ 1 (reset (+ 2 ((shift0 (k1) (k1 (lambda (x) x)))
                                  (shift0 (k2) 4)))))))
; => 6 (fail, should be 5)

(interp '(+ 1 (reset (+ 2 3))))
; => 5 (fail, should be 6)
