;; Unit tests for the type system

(load "infer.ss")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; unit test framework ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; automatic test utility. Run transformation forwards then backwards,
;; and compare with the input term.
(define-syntax test-equals
  (syntax-rules () 
    [(_ name exp expected)
     (begin
       (printf "testing ~s ...~n" name)
       (let ([result exp])
         (cond 
          [(equal? expected exp) 
           (printf " succeeded\n")]
          [else 
           (error 'test "test ~a failed~nexpected: ~a~nbut got: ~a~nexpression: ~a~n"
                  name expected result 'exp)])))]))

(define-syntax test-infer-type
  (syntax-rules () 
    [(_ name exp expected)
     (begin
       (printf "testing ~s ...~n" name)
       (let* ([t1 (infer 'exp)]
              [result (parse-type t1)]
              [s^ (unify (parse-type 'expected) result s0)])
         (cond
          [s^ (printf " succeeded\n")]
          [else 
           (error 'test "test ~a failed~nexpected type: ~a~nactual type: ~a~nexpression: ~a~n"
                  name 'expected t1 'exp)])))]))


(define-syntax test-isomorphism
  (syntax-rules () 
    [(_ name e1 e2)
     (begin
       (printf "testing ~s ...~n" name)
       (if (isomorphic-type? e1 e2)
           (printf " succeeded~n")
           (error 'test "test ~a failed. expressions are not isomorphic~n: e1=~a~ne2=~a~n"
                  name 'e1 'e2)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;; parse-type ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test parse-type
(let ([t (parse-type '(t0 -> (t1 -> t0)))])
  (test-equals "parse-type-1" (arr-to (arr-to t)) (arr-from t)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; unify ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Test 1: loop of length 2, with one type var
;;      __
;;    /    \
;;   v      \
;;   int -> t1

(define t1 (make-tvar 't1))
(define t2 (make-tvar 't2))
(define s1 `((,t1 . ,(make-arr 'int t1 #f))))

(test-equals "unify-1" (unify (make-arr 'int t1 #f) (make-arr 'int t1 #f) s0) '())

(test-equals "unify-2" 
             (unify (make-arr 'int t1 #f) 
                    (make-arr 'int (make-arr 'int t1 #f) #f)
                    s1)
             s1)


;;; Test 2:
;; redefining s2 such that t1 and t2 to form the shape like Escher's lithograph of two
;; hands drawing each other:
;;
;;   t1 = (int -> t2)
;;         ^
;;        /         \
;;       |           |
;;       |           |
;;        \         v
;;   t2 = (t1 -> int)


(define s2 `((,t1 . ,(make-arr 'int t2 #f)) (,t2 . ,(make-arr t1 'int #f))))
(test-equals "unify-3" (unify t1 (make-arr 'int t2 #f) s2) s2)
(test-equals "unify-4" (unify t1 (make-arr 'int (make-arr t1 'int #f) #f) s2) s2)
(test-equals "unify-5" (unify t1 (make-arr 'int (make-arr (make-arr 'int t2 #f) 'int #f) #f) s2) s2)



;;; Test3: degenerated structure test (self-arrow)
;;     t1 = (t1 -> t1) = (t1 -> (t1 -> t1)) = ((t1 -> t1) -> (t1 -> t1))
;;
;;       -> 
;;     /     \         
;;     \     |
;;      \   v 
;;        t1

(define s3 `((,t1 . ,(make-arrow t1 t1))))
(define arr1 (make-arrow t1 t1))
(define arr2 (make-arrow (make-arrow t1 t1) t1))
(define arr3 (make-arrow t1 (make-arrow t1 t1)))
(define arr4 (make-arrow (make-arrow t1 t1) (make-arrow t1 t1)))
(define arr1-1 (make-arrow arr1 arr1))
(define arr1-2 (make-arrow arr1 arr2))
(define arr3-4 (make-arrow arr3 arr4))
(define arr1-2-3-4 (make-arrow arr1-2 arr3-4))

(test-equals "unify-6" (unify t1 arr1 s3) s3)
(test-equals "unify-7" (unify t1 arr2 s3) s3)
(test-equals "unify-8" (unify t1 arr3 s3) s3)
(test-equals "unify-9" (unify t1 arr4 s3) s3)
(test-equals "unify-10" (unify arr1 arr2 s3) s3)
(test-equals "unify-11" (unify arr1 arr2 s3) s3)
(test-equals "unify-12" (unify arr1 arr3 s3) s3)
(test-equals "unify-13" (unify arr1 arr4 s3) s3)
(test-equals "unify-14" (unify arr2 arr3 s3) s3)
(test-equals "unify-15" (unify arr2 arr4 s3) s3)
(test-equals "unify-16" (unify arr3 arr4 s3) s3)
(test-equals "unify-17" (unify arr4 arr4 s3) s3)
(test-equals "unify-18" (unify t1 arr1-1 s3) s3)
(test-equals "unify-19" (unify t1 arr1-2 s3) s3)
(test-equals "unify-20" (unify arr1-2 arr3-4 s3) s3)
(test-equals "unify-21" (unify arr3-4 arr1-2-3-4 s3) s3)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; reify ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define ta (make-tvar 'a))
(define tb (make-tvar 'b))

(test-equals "reify-1"
 (unparse (reify ta `((,ta . ,(make-arrow tb 'int)) (,tb . ,(make-arrow 'bool tb)))))
 '((%0 bool -> !0) -> int))


(test-equals "reify-2"
 (unparse (reify ta `((,ta . ,(make-arrow tb ta)) (,tb . ,(make-arrow 'bool tb)))))
 '(%1 (%0 bool -> !0) -> !1))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; inferencer ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equals "infer-int" (infer 1) 'int)
(test-equals "infer-string" (infer "hi") 'string)
(test-equals "infer-boolean" (infer #t) 'bool)

(test-equals "infer-function-1" (infer '(lambda (f) ((f 1) "hi"))) 
    '((int -> (string -> t0)) -> t0))

(test-equals "infer-function-2" (infer '(lambda (f) (lambda (g) (f (g 1)))))
    '((t0 -> t1) -> ((int -> t0) -> t1)))


(define id '(lambda (x) x))
(test-equals "infer-1" (infer id) '(t0 -> t0))

;; booleans and pairs
(define Ltrue `(lambda (x) (lambda (y) x)))
(define Lfalse `(lambda (x) (lambda (y) y)))
(define Lpair `(lambda (x) (lambda (y) (lambda (p) ((p x) y)))))
(define Lcar `(lambda (p) (p ,Ltrue)))
(define Lcdr `(lambda (p) (p ,Lfalse)))

(test-equals "infer-2" (infer Ltrue) '(t0 -> (t1 -> t0)))
(test-equals "infer-3" (infer Lfalse) '(t0 -> (t1 -> t1)))
(test-equals "infer-4" (infer Lpair) '(t0 -> (t1 -> ((t0 -> (t1 -> t2)) -> t2))))
(test-equals "infer-5" (infer Lcar) '(((t0 -> (t1 -> t0)) -> t2) -> t2))
(test-equals "infer-6" (infer Lcdr) '(((t0 -> (t1 -> t1)) -> t2) -> t2))


;; Church numerals and their operations
(define L0 `(lambda (f) (lambda (x) x)))
(define L1 `(lambda (f) (lambda (x) (f x))))
(define L2 `(lambda (f) (lambda (x) (f (f x)))))
(define L3 `(lambda (f) (lambda (x) (f (f (f x))))))
(define L4 `(lambda (f) (lambda (x) (f (f (f (f x)))))))
(define L5 `(lambda (f) (lambda (x) (f (f (f (f (f x))))))))
(define L6 `(lambda (f) (lambda (x) (f (f (f (f (f (f x)))))))))
(define L7 `(lambda (f) (lambda (x) (f (f (f (f (f (f (f x))))))))))

(define Lzero? `(lambda (n) ((n (lambda (x) ,Lfalse)) ,Ltrue)))
(define Lsucc `(lambda (n) (lambda (f) (lambda (x) (f ((n f) x))))))

(test-equals "infer-7" (infer L0) '(t0 -> (t1 -> t1)))
(test-equals "infer-8" (infer L1) '((t0 -> t1) -> (t0 -> t1)))
(test-equals "infer-9" (infer L2) '((t0 -> t0) -> (t0 -> t0)))
(test-equals "infer-10" (infer L3) '((t0 -> t0) -> (t0 -> t0)))
(test-equals "infer-11" (infer L4) '((t0 -> t0) -> (t0 -> t0)))
(test-equals "infer-12" (infer L5) '((t0 -> t0) -> (t0 -> t0)))
(test-equals "infer-13" (infer L6) '((t0 -> t0) -> (t0 -> t0)))
(test-equals "infer-14" (infer L7) '((t0 -> t0) -> (t0 -> t0)))


; Stephen Kleene's pred
(define Lpred-K `(lambda (n)
                 (,Lcar ((n (lambda (p)
                              ((,Lpair (,Lcdr p)) (,Lsucc (,Lcdr p)))))
                         ((,Lpair ,L0) ,L0)))))

; Daniel Smith (my classmate in B621)'s pred
(define Lpred-D
  '(lambda (n)
     (lambda (w)
       (lambda (z)
         (((n (lambda (l) (lambda (h) (h (l w))))) (lambda (d) z))
          (lambda (x) x))))))

(define Lplus `(lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m f) ((n f) x)))))))
(define Lsub `(lambda (m) (lambda (n) ((n ,Lpred-K) m))))
(define Ltimes `(lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m (n f)) x))))))
(define Lpow `(lambda (m) (lambda (n) (lambda (f) (lambda (x) (((m n) f) x))))))

(test-equals "infer-15" (infer Lpred-K)
     '(((((t0 -> (t1 -> t1)) -> ((t2 -> t3) -> (t4 -> t2)))
         ->
         ((((t2 -> t3) -> (t4 -> t2))
            ->
            (((t2 -> t3) -> (t4 -> t3)) -> t5))
           ->
           t5))
        ->
        ((((t6 -> (t7 -> t7)) -> ((t8 -> (t9 -> t9)) -> t10))
           ->
           t10)
          ->
          ((t11 -> (t12 -> t11)) -> t13)))
       ->
       t13))

(test-equals "infer-16" (infer Lpred-D)
     '((((t0 -> t1) -> ((t1 -> t2) -> t2))
        ->
        ((t3 -> t4) -> ((t5 -> t5) -> t6)))
       ->
       (t0 -> (t4 -> t6))))

(test-isomorphism "isomorphism-pred" Lpred-K Lpred-D)



; SKI combinators
(define S '(lambda (f) (lambda (g) (lambda (x) ((f x) (g x))))))
(define K '(lambda (x) (lambda (y) x)))
(define I '(lambda (x) x))
(define B '(lambda (f) (lambda (g) (lambda (x) (f (g x))))))
(define C '(lambda (a) (lambda (b) (lambda (c) ((a c) b)))))

(test-equals "infer-S" (infer S)
  '((t0 -> (t1 -> t2)) -> ((t0 -> t1) -> (t0 -> t2))))

(test-equals "infer-K" (infer K)
  '(t0 -> (t1 -> t0)))

(test-equals "infer-I" (infer I)
  '(t0 -> t0))

(test-equals "infer-B" (infer B)
  '((t0 -> t1) -> ((t2 -> t0) -> (t2 -> t1))))

(test-equals "infer-C" (infer C)
  '((t0 -> (t1 -> t2)) -> (t1 -> (t0 -> t2))))

(test-equals "infer-SKK" (infer `((,S ,K) ,K))
  '(t0 -> t0))

;; ((S I) I) = (lambda (x) (x x)
(test-equals "infer-SII" (infer `((,S ,I) ,I))
  '((%0 !0 -> t0) -> t0))

(test-equals "infer-S(SKK)(SKK)" (infer `((,S ((,S ,K) ,K)) ((,S ,K) ,K)))
  '((%0 !0 -> t0) -> t0))

(test-isomorphism "isomorphism-SKK-I" `((,S ,K) ,K) I)




;;;;;;;;;;;;;;;;;;;;; Recursive Types ;;;;;;;;;;;;;;;;;;;;;;;
;; self application
(define selfapp '(lambda (x) (x x)))

(test-equals "selfapp" (infer selfapp)
  '((%0 !0 -> t0) -> t0))


(define Omega '((lambda (x) (x x)) (lambda (x) (x x))))

(test-equals "infer-Omega" (infer Omega)
  't0)



;; call-by-value Y combinator
(define Yv
  `(lambda (f)
     ((lambda (u) (u u))
      (lambda (x) (f (lambda (t) ((x x) t)))))))

(test-equals "infer-Yv" (infer Yv)
  '(((t0 -> t1) -> (t0 -> t1)) -> (t0 -> t1)))


;; call-by-name Y combinator
(define Yn
  `(lambda (f)
     ((lambda (x) (f (x x)))
      (lambda (x) (f (x x))))))

(test-equals "infer-Yn" (infer Yn)
  '((t0 -> t0) -> t0))

(test-isomorphism "isomorphism-Yv-Yn" Yv Yn)


;; factorial (using CBV Y)
(define !v-gen
  `(lambda (!)
     (lambda (n)
       ((((,Lzero? n)
          (lambda (t) ,L1))
         (lambda (t) ((,Ltimes n) (! (,Lpred-K n)))))
        (lambda (v) v)))))

(define !v `(,Yv ,!v-gen))

(test-equals "infer-!v" (infer !v)
  '((%1 ((((%0 !0 -> ((%1 !0 -> (!1 -> !1)) -> !1))
         ->
         (!1 -> !1))
        ->
        ((!0 -> (!1 -> !1)) -> (!0 -> !0)))
       ->
       ((((!0 -> (!1 -> !1)) -> (!0 -> !0))
          ->
          (((!0 -> (!1 -> !1)) -> (!0 -> (!1 -> !1)))
            ->
            (((%1 !1 -> (!0 -> (!0 -> !2))) -> (!0 -> !1))
              ->
              (!1 -> (!0 -> !1)))))
         ->
         ((!1 -> (!0 -> !1))
           ->
           (((!0 -> (!2 -> !2))
              ->
              ((!0 -> (!2 -> !2)) -> (!0 -> (!2 -> !2))))
             ->
             !3))))
     ->
     ((!0 -> !0) -> !2))
  ->
  ((((!0 -> (!2 -> !2)) -> (!0 -> !0))
     ->
     (((!0 -> (!2 -> !2)) -> (!0 -> (!2 -> !2)))
       ->
       ((!3 -> (!0 -> !3)) -> (!3 -> (!0 -> !3)))))
    ->
    (((!0 -> (!2 -> !2)) -> ((!0 -> (!2 -> !2)) -> (!0 -> !0)))
      ->
      ((((!0 -> (!2 -> !2)) -> (!0 -> !0))
         ->
         (((!0 -> (!2 -> !2)) -> (!0 -> (!2 -> !2)))
           ->
           ((!3 -> (!0 -> !3)) -> (!3 -> (!0 -> !3)))))
        ->
        ((!3 -> (!0 -> !3)) -> (!3 -> (!0 -> !3))))))))



;; factorial (using CBN Y)
(define !n-gen
  `(lambda (!)
     (lambda (n)
       (((,Lzero? n) ,L1) ((,Ltimes n) (! (,Lpred-K n)))))))

(define !n `(,Yn ,!n-gen))

(test-equals "infer-!n" (infer !n)
  '((%1 ((((%0 (%1 (!0 -> (!1 -> !1))
                ->
                ((!1 -> ((!0 -> (!1 -> !1)) -> (!0 -> (!1 -> !1))))
                  ->
                  (!1 -> !1)))
            ->
            ((!0 -> (!1 -> !1))
              ->
              ((!1 -> ((!0 -> (!1 -> !1)) -> (!0 -> (!1 -> !1)))) -> !0)))
         ->
         (!1 -> !1))
        ->
        ((!0 -> (!1 -> !1))
          ->
          ((!1 -> ((!0 -> (!1 -> !1)) -> (!0 -> (!1 -> !1)))) -> !0)))
       ->
       ((((!0 -> (!1 -> !1))
           ->
           ((!1 -> ((!0 -> (!1 -> !1)) -> (!0 -> (!1 -> !1)))) -> !0))
          ->
          !0)
         ->
         (((%1 !1 -> !2) -> (!2 -> !1)) -> !3)))
     ->
     !2)
  ->
  (((!0 -> (!2 -> !2))
     ->
     ((!0 -> (!2 -> !2))
       ->
       ((!2 -> ((!0 -> (!2 -> !2)) -> (!0 -> (!2 -> !2)))) -> !0)))
    ->
    (((!0 -> (!2 -> !2))
       ->
       ((!0 -> (!2 -> !2))
         ->
         ((!2 -> ((!0 -> (!2 -> !2)) -> (!0 -> (!2 -> !2)))) -> !0)))
      ->
      ((((!0 -> (!2 -> !2))
          ->
          ((!2 -> ((!0 -> (!2 -> !2)) -> (!0 -> (!2 -> !2)))) -> !0))
         ->
         (!2 -> ((!0 -> (!2 -> !2)) -> (!0 -> (!2 -> !2)))))
        ->
        ((!0 -> (!2 -> !2)) -> (!0 -> (!2 -> !2))))))))


(test-isomorphism "isomorphism-!v-!n ... may take longer ..." !v !n)




;; =========================================================
;; Oleg's test for a type inferencer in Prolog
;; http://muaddibspace.blogspot.com/2008/01/type-inference-for-simply-typed-lambda.html

(test-equals "infer-oleg-1"
   (infer '(lambda (f) (lambda (x) (f (x 1)))))
   '((t0 -> t1) -> ((int -> t0) -> t1)))

;; 
;; => 

;; (infer '(lambda (f) (lambda (x) ((f (x 1)) (x #t)))))
;; => infer: incompatible argument type:
;;  - function:      x
;;  - function type: (int -> t0)
;;  - expected type: int
;;  - argument type: bool
;;  - argument:      #t

;; (infer '(lambda (f) (lambda (x) (lambda (x) ((f (x 1)) (x #t))))))
;; => infer: incompatible argument type:
;;  - function:      x
;;  - function type: (int -> t0)
;;  - expected type: int
;;  - argument type: bool
;;  - argument:      #t

;; The inferencer can type the following term which wasn't supposed to be typable in HM system:

(test-equals "infer-oleg-2"
   (infer '(lambda (f) (lambda (x) ((f (x (lambda (z) z))) (x (lambda (u) (lambda (v) u)))))))
   '((t0 -> (t0 -> t1))
     ->
     ((((%0 t2 -> !0) -> !0) -> t0) -> t1)))

