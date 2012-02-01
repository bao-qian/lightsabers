;; A simple CPS transformer which does proper tail-call and does not
;; duplicate contexts for if-expressions.

;; author: Yin Wang (yw21@cs.indiana.edu)


(load "pmatch.scm")


(define cps
  (lambda (exp)
    (letrec
        ([trivs '(zero? sub1)]
         [id (lambda (v) v)]
         [C~ (lambda (v) `(k ,v))]      ; tail context
         [fv (let ((n -1))
               (lambda ()
                 (set! n (+ 1 n))
                 (string->symbol (string-append "v" (number->string n)))))]
         [cps1
          (lambda (exp C)
            (pmatch exp
              [,x (guard (not (pair? x))) (C x)]
              [(if ,test ,conseq ,alt)
               (cps1 test
                     (lambda (t)
                       (if (memq C (list C~ id))
                           `(if ,t ,(cps1 conseq C) ,(cps1 alt C))
                           (let ((v* (fv)))
                             `(let ((k (lambda (,v*) ,(C v*))))
                                (if ,t ,(cps1 conseq C~) ,(cps1 alt C~)))))))]
              [(lambda (,x) ,body)
               (C `(lambda (,x k) ,(cps1 body C~)))]
              [(,op ,a ,b)
               (cps1 a (lambda (v1)
                         (cps1 b (lambda (v2)
                                   (C `(,op ,v1 ,v2))))))]
              [(,rator ,rand)
               (cps1 rator
                     (lambda (r)
                       (cps1 rand
                             (lambda (d)
                               (cond
                                [(memq r trivs) (C `(,r ,d))]
                                [(eq? C C~) `(,r ,d k)] ; tail call
                                [else
                                 (let ((v* (fv)))
                                   `(,r ,d (lambda (,v*) ,(C v*))))])))))]))])
      (cps1 exp id))))




;;; tests

;; var
(cps 'x)
(cps '(lambda (x) x))
(cps '(lambda (x) (x 1)))


; no lambda (will generate identity functions to return to the toplevel)
(cps '(if (f x) a b))
(cps '(if x (f a) b))


; if stand-alone (tail)
(cps '(lambda (x) (if (f x) a b)))


; if inside if-test (non-tail)
(cps '(lambda (x) (if (if x (f a) b) c d)))


; both branches are trivial, should do some more optimizations
(cps '(lambda (x) (if (if x (zero? a) b) c d)))


; if inside if-branch (tail)
(cps '(lambda (x) (if t (if x (f a) b) c)))


; if inside if-branch, but again inside another if-test (non-tail)
(cps '(lambda (x) (if (if t (if x (f a) b) c) e w)))


; if as operand (non-tail)
(cps '(lambda (x) (h (if x (f a) b))))


; if as operator (non-tail)
(cps '(lambda (x) ((if x (f g) h) c)))


; why we need more than two names
(cps '(((f a) (g b)) ((f c) (g d))))



; factorial
((eval
  (cps
   '(lambda (n)
      ((lambda (fact)
         ((fact fact) n))
       (lambda (fact)
         (lambda (n)
           (if (zero? n)
               1
               (* n ((fact fact) (sub1 n))))))))))
 5
 (lambda (v) v))

