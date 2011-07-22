;; A simple CPS transformer which does tail-call elimination
;; and does not duplicate contexts for if-expressions.

;; author: Yin Wang (yw21@cs.indiana.edu)


(load "pmatch.scm")

(define CPSer
  (lambda (exp)
    (letrec 
        ([trivs '(zero? sub1)]
         [id (lambda (v) v)]
         [C~ (lambda (v) `(k ,v))]
         [fv (let ((n -1))
               (lambda ()
                 (set! n (+ 1 n))
                 (string->symbol 
                  (string-append "v" (number->string n)))))]
         [CPS
          (lambda (exp C)
            (pmatch exp
              [,x (guard (atom? x)) (C x)]
              [(if ,test ,conseq ,alt)
               (CPS test
                    (lambda (t)
                      (if (memq C (list C~ id))
                          `(if ,t ,(CPS conseq C) ,(CPS alt C))
                          (let ((v* (fv)))
                            `(let ((k (lambda (,v*) ,(C v*))))
                               (if ,t ,(CPS conseq C~) ,(CPS alt C~)))))))]
              [(lambda (,x) ,body)
               (C `(lambda (,x k) ,(CPS body C~)))]
              [(,op ,a ,b)
               (CPS a (lambda (v1)
                        (CPS b (lambda (v2)
                                 (C `(,op ,v1 ,v2))))))]
              [(,rator ,rand)
               (CPS rator
                    (lambda (r)
                      (CPS rand
                           (lambda (d)
                             (cond 
                              [(memq r trivs) (C `(,r ,d))]
                              [(eq? C C~) `(,r ,d k)] ; tail call
                              [else
                               (let ((v* (fv)))
                                 `(,r ,d (lambda (,v*) ,(C v*))))])))))]))])
      (CPS exp id))))




;;; tests

;; var
(CPSer 'x)
(CPSer '(lambda (x) x))


; no lambda (will generate identity functions to return to the toplevel)
(CPSer '(if (f x) a b))
(CPSer '(if x (f a) b))

; if stand-alone (tail)
(CPSer '(lambda (x) (if (f x) a b)))

; if inside if-test (non-tail)
(CPSer '(lambda (x) (if (if x (f a) b) c d)))

; both branches are trivial, should do some more optimizations
(CPSer '(lambda (x) (if (if x (zero? a) b) c d)))

; if inside if-branch (tail)
(CPSer '(lambda (x) (if t (if x (f a) b) c)))

; if inside if-branch, but again inside another if-test (non-tail)
(CPSer '(lambda (x) (if (if t (if x (f a) b) c) e w)))

; if as operand (non-tail)
(CPSer '(lambda (x) (h (if x (f a) b))))

; if as operator (non-tail)
(CPSer '(lambda (x) ((if x (f g) h) c)))

; why we need more than two names
(CPSer '(((f a) (g b)) ((f c) (g d))))


; factorial
((eval
  (CPSer
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

