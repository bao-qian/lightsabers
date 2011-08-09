;; Boolean expression simplification into sum-of-products
;; author: Yin Wang (yinwang0@gmail.com)


;; (1) Push 'and' into 'or'
;; (2) Push 'not' into 'and' or 'or'
;; Do (1) and (2) recursively until no more simplification can be made
(define simpl
  (lambda (exp)
    (match exp
      [`(and (or ,a ,b) ,c)
       `(or ,(simpl `(and ,(simpl a) ,(simpl c)))
            ,(simpl `(and ,(simpl b) ,(simpl c))))]
      [`(and ,c (or ,a ,b))
       `(or ,(simpl `(and ,(simpl c) ,(simpl a)))
            ,(simpl `(and ,(simpl c) ,(simpl b))))]
      [`(not (and ,a ,b))
       `(or ,(simpl `(not ,a)) ,(simpl `(not ,b)))]
      [`(not (or ,a ,b))
       `(and ,(simpl `(not ,a)) ,(simpl `(not ,b)))]

      [`(and ,a ,b)
       `(and ,(simpl a) ,(simpl b))]
      [`(or ,a ,b)
       `(or ,(simpl a) ,(simpl b))]
      [`(not ,a ,b)
       `(not ,(simpl a) ,(simpl b))]
      [other other])))



;; Combine nested expressions with same operator, for example
;; (and (and a b) c) ==> (and a b c)
(define combine
  (lambda (exp)
    (define combine1
      (lambda (exp ct C)
        (match exp
          [`((and ,x* ...))
           (combine1 x* 'and
             (lambda (v*)
               (cond
                 [(eq? 'and ct) (C v*)]
                 [else (C `((and ,@v*)))])))]
          [`((or ,x* ...))
           (combine1 x* 'or
             (lambda (v*)
               (cond
                 [(eq? 'or ct) (C v*)]
                 [else (C `((or ,@v*)))])))]
          [`(,a ,b ,c* ...)
           (combine1 (list a) ct
             (lambda (vx)
               (C `(,@vx ,@(combine1 `(,b ,@c*) ct (lambda (x) x))))))]
          [other (C other)])))
    (car (combine1 (list exp) 'id (lambda (x) x)))))


;; (combine '(and (and a (and b (and c (and d e))))))
;; (combine '(and (and (and (and a b) c) d) e))
;; (combine '(and (and a (and b c)) (and d e)))
;; (combine '(or (and a b) c))



;; simpl then combine
(define simplify
  (lambda (exp)
    (combine (simpl exp))))




;------------------ examples ------------------
(simplify '(and (or football basketball) baby))

;; ==>
;; '(or (and football baby) (and basketball baby))

(simplify '(and (not (and a (or b c))) (or d e)))

;; ==>
;; '(or (and (not a) d)
;;      (and (not b) (not c) d)
;;      (and (not a) e)
;;      (and (not b) (not c) e))

