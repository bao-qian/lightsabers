(require racket/control)

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

(define ext
  (lambda (x v env)
    (cons `(,x . ,v) env)))

(define lookup
  (lambda (x env)
    (cond
     [(assq x env) => cdr]
     [else #f])))


;; using high-order representation, can't model shift0
(define interp-ho
  (lambda (exp)
    (define interp1
      (lambda (exp env k r)
        (pmatch exp
          [,x (guard (number? x))
              ((k r) x)]
          [,x (guard (not (pair? x)))
           (let ([v (lookup x env)])
             (cond
              [(not v)
               (error 'interp "unbound variable ~a" x)]
              [else
               ((k r) v)]))]
          [(lambda (,x) ,body)
           ((k r)
            (lambda (k)
              (lambda (r)
                (lambda (v)
                  (interp1 body (ext x v env) k r)))))]
          [(reset ,e)
           (interp1 e env
                    (lambda (r) r)
                    (k r))]
          [(shift ,x ,e)
           (interp1 e (ext x (lambda (k^)
                               (lambda (r)
                                 (lambda (v)
                                   ((k (k^ r)) v)))) env)
                    (lambda (r) r)
                    r)]
          [(+ ,a ,b)
           (interp1 a env
                    (lambda (r)
                      (lambda (a^)
                        (interp1 b env
                                 (lambda (r)
                                   (lambda (b^)
                                     ((k r) (+ a^ b^))))
                                 r)))
                    r)]
          [(,rator ,rand)
           (interp1 rator env
                    (lambda (r)
                      (lambda (f)
                        (interp1 rand env (f k) r)))
                    r)])))
    (interp1 exp '() (lambda (r) (lambda (v) (r v))) (lambda (v) v))))



;; using list representation, can model shift0
(define interp
  (lambda (exp)
    (define idK (lambda (r v) ((car r) (cdr r) v)))
    (define idR (list (lambda (r v) v)))
    (define interp1
      (lambda (exp env k r)
        (pmatch exp
          [,x (guard (number? x))
              (k r x)]
          [,x (guard (not (pair? x)))
           (let ([v (lookup x env)])
             (cond
              [(not v)
               (error 'interp "unbound variable ~a" x)]
              [else
               (k r v)]))]
          [(lambda (,x) ,body)
           (k r (lambda (k r v)
                  (interp1 body (ext x v env) k r)))]
          [(reset ,e)
           (interp1 e env idK (cons k r))]
          [(reset0 ,e)                  ; same as reset
           (interp1 e env idK (cons k r))]
          [(shift ,x ,e)
           (interp1 e (ext x (lambda (k^ r v)
                               (k (cons k^ r) v)) env)
                    idK r)]
          [(shift0 ,x ,e)
           (interp1 e (ext x (lambda (k^ r v)
                               (k (cons k^ r) v)) env)
                    (car r) (cdr r))]   ; the only difference from shift
          [(+ ,a ,b)
           (interp1 a env
                    (lambda (r a^)
                      (interp1 b env
                               (lambda (r b^)
                                 (k r (+ a^ b^)))
                               r))
                    r)]
          [(,rator ,rand)
           (interp1 rator env
                    (lambda (r f)
                      (interp1 rand env (lambda (r v) (f k r v)) r))
                    r)])))
    (interp1 exp '() idK idR)))




;-------------------- tests ---------------------------
(define test-control
  (lambda (e)
    (let ([expected (eval e)]
          [actual (interp e)])
      (cond
       [(eqv? expected actual)
        (printf "succeed. answer = ~a~n" actual)]
       [else
        (printf "error. answer = ~a, but should be ~a~n" actual expected)]))))




;; Danvy-filinski test
(test-control '(+ 10 (reset (+ 2 (shift k (+ 100 (k (k 3))))))))
; => 117

;; Danvy-filinski paper example
(test-control '(+ 5 (reset (+ 3 (shift c (+ (c 0) (c 1)))))))
; => 12

(test-control '(+ 1 (+ 2 (+ 4 8))))
; => 15

(test-control '(+ 1 (reset (+ 2 (+ (shift k 4) 8)))))
; => 5

(test-control '(reset (+ 1 (reset (+ 2 (reset (+ 4 (shift k1 (shift k2 8)))))))))
; => 11

;; compare reset0 & shift0
(test-control '(reset0 (+ 1 (reset0 (+ 2 (reset0 (+ 4 (shift0 k1 (shift0 k2 8)))))))))
; => 9


(test-control '(reset (+ 1 (reset (+ 2 ((shift k1 (k1 (lambda (x) x)))
                                  (shift k2 4)))))))
; => 5

(test-control '(+ 1 (reset (+ 2 3))))
; => 6

(test-control
 '((lambda (f) (+ 1 (reset (+ 2 (f 3)))))
   (lambda (x) (shift k x))))
; => 4

(test-control '(reset (+ 10 (+ (shift k (+ 1 (k 1))) (shift k 2)))))
; => 3



;------------------------ from Oleg's Shift0.hs -------------------------------

; ts0 = run $ reset (return 1)
(test-control '(reset0 1))
;=> 1

; ts1 = run $ reset (return 1 `add` abort 2)
(test-control '(reset0 (+ 1 (shift0 k 2))))
;=> 2

; ts2 = run $ reset (return 1 `add` shift0 (\k -> k 2))
(test-control '(reset0 (+ 1 (shift0 k (k 2)))))
;=> 3


; -- shift0 spcifically
;; ts41 = run $ reset (return 1 `add` reset (return 2 `add`
;;       (shift0 (\k -> k 10))))
(test-control '(reset0 (+ 1 (reset0 (+ 2 (shift0 k (k 10)))))))
;=> 13


;; ts42 = run $ reset (return 1 `add` reset (return 2 `add`
;;       (shift0 (\k -> return 10))))

(test-control (reset0 (+ 1 (reset0 (+ 2 (shift0 k 10))))))
;=> 11


;; ts43 = run $ reset (return 1 `add` reset (return 2 `add`
;;       (shift0 (\k -> abort 10))))
;; -- 10
(test-control '(reset0 (+ 1 (reset0 (+ 2 (shift0 k (shift0 k 10)))))))


;; ts44 = run $ reset (return 1 `add` reset (return 2 `add`
;;       reset ((shift0 (\k -> abort 10)))))
(test-control '(reset0 (+ 1 (reset0 (+ 2 (reset0 (shift0 k (shift0 k 10))))))))
;; -- 11

;; -- left-to-right evaluation
;; ts5 = run $ reset (abort 1 `add` abort 2)

(test-control '(reset0 (+ (shift0 k 1) (shift0 k 2))))
;=> 1


;; ts61 = run $ reset (return 10 `add`
;;            reset (shift0 (\k -> k 1) `add`
;;                   shift0 (\k -> k 2)))
;; -- 13
(test-control '(reset0 (+ 10 (reset0 (+ (shift0 k (k 1)) (shift0 k (k 2)))))))


;; ts62 = run $ reset (return 10 `add`
;;            reset (shift0 (\k -> k 1) `add`
;;                   shift0 (\_ -> return 2)))
;; -- 12
(test-control '(reset (+ 10 (reset (+ (shift0 k (k 1)) (shift0 k 2))))))


;; ts63 = run $ reset (return 10 `add`
;;            reset (shift0 (\k -> k 1) `add`
;;                   shift0 (\_ -> abort 2)))
;; -- 2
(test-control '(reset0 (+ 10 (reset0 (+ (shift0 k (k 1)) (shift0 k (shift0 k 2)))))))

