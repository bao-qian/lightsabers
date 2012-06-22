;; deriving a "Y combinator" for mutual recursion

(define even
  (lambda (x)
    (cond
     [(zero? x) #t]
     [(= 1 x) #f]
     [else (odd (sub1 x))])))


(define odd
  (lambda (x)
    (cond
     [(zero? x) #f]
     [(= 1 x) #t]
     [else (even (sub1 x))])))



;; Step 1: package up functions, make a copy, create a cycle
(let ([p ((lambda (eo)
            (cons
             (lambda (x)
               (cond
                [(zero? x) #t]
                [(= 1 x) #f]
                [else ((cdr (eo eo)) (sub1 x))]))
             (lambda (x)
               (cond
                [(zero? x) #f]
                [(= 1 x) #t]
                [else ((car (eo eo)) (sub1 x))]))))

          (lambda (eo)
            (cons
             (lambda (x)
               (cond
                [(zero? x) #t]
                [(= 1 x) #f]
                [else ((cdr (eo eo)) (sub1 x))]))
             (lambda (x)
               (cond
                [(zero? x) #f]
                [(= 1 x) #t]
                [else ((car (eo eo)) (sub1 x))])))))])
  (let ([even (car p)]
        [odd (cdr p)])
    (even 21)))



;; Step 2: extract the outer self-application pattern
(let ([p ((lambda (x) (x x))
          (lambda (eo)
            (cons
             (lambda (x)
               (cond
                [(zero? x) #t]
                [(= 1 x) #f]
                [else ((cdr (eo eo)) (sub1 x))]))
             (lambda (x)
               (cond
                [(zero? x) #f]
                [(= 1 x) #t]
                [else ((car (eo eo)) (sub1 x))])))))])
  (let ([even (car p)]
        [odd (cdr p)])
    (even 22)))



;; Step 3: extract inner self-application pattern
(let ([p ((lambda (x) (x x))
          (lambda (eo)
            (cons
             (lambda (x)
               ((lambda (y)
                  (cond
                   [(zero? x) #t]
                   [(= 1 x) #f]
                   [else ((cdr y) (sub1 x))]))
                (eo eo)))
             (lambda (x)
               ((lambda (y)
                  (cond
                   [(zero? x) #f]
                   [(= 1 x) #t]
                   [else ((car y) (sub1 x))]))
                (eo eo))))))])
  (let ([even (car p)]
        [odd (cdr p)])
    (even 22)))


;; Oh no~ The nice form of Y combinator doesn't seem to work for
;; mutual recursion! backtrack to Step 2 would be close enough.

