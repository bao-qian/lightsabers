;; booleans and pairs
(define ltrue `(lambda (x) (lambda (y) x)))
(define lfalse `(lambda (x) (lambda (y) y)))
(define lpair `(lambda (x) (lambda (y) (lambda (p) ((p x) y)))))
(define lcar `(lambda (p) (p ,ltrue)))
(define lcdr `(lambda (p) (p ,lfalse)))

;; numbers and operations
(define decode-number (lambda (n) ((n add1) 0)))
(define lzero `(lambda (f) (lambda (x) x)))
(define lone `(lambda (f) (lambda (x) (f x))))
(define ltwo `(lambda (f) (lambda (x) (f (f x)))))
(define lthree `(lambda (f) (lambda (x) (f (f (f x))))))
(define lfour `(lambda (f) (lambda (x) (f (f (f (f x)))))))
(define lfive `(lambda (f) (lambda (x) (f (f (f (f (f x))))))))
(define l6 `(lambda (f) (lambda (x) (f (f (f (f (f (f x)))))))))
(define l7 `(lambda (f) (lambda (x) (f (f (f (f (f (f (f x))))))))))

(define lzero? `(lambda (n) ((n (lambda (x) ,lfalse)) ,ltrue)))
(define lsucc `(lambda (n) (lambda (f) (lambda (x) (f ((n f) x))))))

; Daniel Smith's pred
(define lpred
  '(lambda (n)
     (lambda (w)
       (lambda (z)
         (((n (lambda (l) (lambda (h) (h (l w))))) (lambda (d) z))
          (lambda (x) x))))))

(define lpred `(lambda (n)
                 (,lcar ((n (lambda (p) 
                              ((,lpair (,lcdr p)) (,lsucc (,lcdr p)))))
                         ((,lpair ,lzero) ,lzero)))))

(define lplus `(lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m f) ((n f) x)))))))
(define lsub `(lambda (m) (lambda (n) ((n ,lpred) m))))
(define ltimes `(lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m (n f)) x))))))
(define lpow `(lambda (m) (lambda (n) (lambda (f) (lambda (x) (((m n) f) x))))))

;; call-by-value Y combinator
(define Y
  `(lambda (f)
     ((lambda (u) (u u))
      (lambda (x) (f (lambda (t) ((x x) t)))))))

;; version 1 (using poorman's Y)
(define !-half
  `(lambda (!)
     (lambda (n)
       ((((,lzero? n)
          (lambda (t) ,lone))
         (lambda (t) ((,ltimes n) ((! !) (,lpred n)))))
        (lambda (v) v)))))

(define ! `(,!-half ,!-half))
(define !-5 `(,! ,lfive))


;; version 2 (using CBV Y)
(define !-gen
  `(lambda (!)
     (lambda (n)
       ((((,lzero? n)
          (lambda (t) ,lone))
         (lambda (t) ((,ltimes n) (! (,lpred n)))))
        (lambda (v) v)))))

(define ! `(,Y ,!-gen))

;; version 3 (CBN)
;; call-by-name Y
(define Y-n
  `(lambda (f)
     ((lambda (x) (f (x x)))
      (lambda (x) (f (x x))))))

(define !-gen-n
  `(lambda (!)
     (lambda (n)
       (((,lzero? n) ,lone) ((,ltimes n) (! (,lpred n)))))))

(define !-n `(,Y-n ,!-gen-n))


;; example use:
(decode-number (eval `(,! ,lfive)))

