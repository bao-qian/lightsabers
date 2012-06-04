;; a bottom-up type inferencer for Hindley-Milner type system
;; author: Yin Wang (yw21@cs.indiana.edu)



;;------------------------------ utilities -------------------------------
;; utility for error reporting
(define fatal
  (lambda (who . args)
    (define display1
      (lambda (x)
        (cond
         [(string? x) (printf "~a" x)]
         [else (printf "~s" x)])))
    (printf "~s: " who)
    (for-each display1 args)
    (display "\n")
    (error 'infer "")))


(define union
  (lambda (x y)
    (cond
     [(null? x) y]
     [(memq (car x) y)
      (union (cdr x) y)]
     [else
      (cons (car x) (union (cdr x) y))])))


;; debug switch
(define *debug* #f)
(define undebug (lambda () (set! *debug* #f)))
(define debug (lambda () (set! *debug* #t)))


;; list of names to debug
(define *dblist* '())
(define db (lambda ls (set! *dblist* (union ls *dblist*))))
(define undb (lambda ls (set! *dblist* (set- *dblist* ls))))


(define-syntax peek
  (syntax-rules ()
    [(_ name args ...)
     (and *debug* (memq name *dblist*)
          (begin
            (printf "[~s]---------------------------~n" name)
            (printf "\t~s = ~s~n" 'args (unparse args))
            ...))]))


(define-syntax letv*
  (syntax-rules ()
    [(_ e ...) (let*-values e ...)]))


(define-syntax fst
  (syntax-rules ()
    [(_ e) (letv* ([(x y) e]) x)]))



;;------------------------------ terms  -------------------------------
(struct Const   (value)      #:transparent)
(struct Var     (name)       #:transparent)
(struct Lam     (x e)        #:transparent)
(struct App     (e1 e2)      #:transparent)

;;------------------------------ types -------------------------------
(struct Prim   (name)        #:transparent)
(struct Arrow  (from to)     #:transparent)
(struct TVar   (nr)          #:transparent)
(struct Tp     (t s)         #:transparent)

;; make a fresh type variable
(define *serial* 0)
(define fresh
  (lambda ()
    (set! *serial* (add1 *serial*))
    (TVar *serial*)))
(define reset
  (lambda ()
    (set! *serial* 0)))



;; parse-term :: Sexp -> Term
;; parser from sexps and types into records
;; Example:
;; (parse-term '(lambda (f) (f 16)))
;; => (Arrow (Var 'f) (App (Var 'f) (Const 16)))
(define parse-term
  (lambda (sexp)
    (define parse
      (lambda (sexp)
        (match sexp
          [(? (lambda (x) (or (number? x) (string? x) (boolean? x))) x) (Const x)]
          [(? symbol? x) (Var x)]
          [`(lambda (,x) ,body) (Lam (parse x) (parse body))]
          [`(,e1 ,e2) (App (parse e1) (parse e2))])))
    (parse sexp)))


(define unparse
  (lambda (t)
    (match t
      ;; types
      [(Prim name)
       name]
      [(TVar nr)
       nr]
      [(Tp t s)
       `(,(unparse t bd) @ ,(unparse s bd))]
      [(Arrow from to)
       `(,(unparse from) -> ,(unparse to))]
      ;; terms
      [(Const obj) obj]
      [(Var name) name]
      [(Lam x e) `(lambda (,(unparse x)) ,(unparse e))]
      [(App e1 e2)
       `(,(unparse e1) ,(unparse e2))]
      [(cons e1 e2)
       (cons (unparse e1) (unparse e2))]
      [else t])))



;; initial substitution is empty
(define s0 '())
(define ext (lambda (x v s) (cons `(,x . ,v) s)))

;; lookup :: Any -> Subst -> Maybe Any
(define lookup
  (lambda (x s)
    (let ([p (assq x s)])
      (cond
       [(not p) #f]
       [else (cdr p)]))))


;; walk :: Any -> Subst -> Any
(define walk
  (lambda (x s)
    (let ([p (assq x s)])
      (cond
       [(not p) x]
       [else
        (walk (cdr p) s)]))))


;; reify - homomorphism which generalizes walk
;; "inlines" the substitution into the term
;; reify :: Term -> Subst -> Term
(define reify
  (lambda (x s)
    (let ([x (walk x s)])
     (match x
       [(Arrow from to)
        (Arrow (reify from s) (reify to s))]
       [else x]))))


;; report: reify the term, then unparse it into human readable format
(define report
  (lambda (x s)
    (unparse (reify x s))))


(define rem-s
  (lambda (ls s)
    (filter (lambda (p) (not (memq (car p) ls))) s)))


(define int-s
  (lambda (s1i s2i)
    (peek 'int s1i s2i)
    (let ([s12 (append s1i s2i)])
      (let loop ([s1 s1i]
                 [s2 s2i]
                 [out '()])
        (cond
         [(null? s1) (append s2 out)]
         [(assq (caar s1) s2)
          => (lambda (p)
               (let ([s^ (unify (cdar s1) (cdr p) s12)])
                 (cond
                  [(not s^)
                   (fatal 'int-s "incompatible types: "
                          (report (cdar s1) s1) " and "
                          (report (cdr p) s2))]
                  [else
                   (loop (cdr s1)
                         (remove p s2)
                         (cons (car s1) (append s^ out)))])))]
         [else
          (loop (cdr s1) s2 (cons (car s1) out))])))))



(define unify
  (lambda (t1 t2 s-in)
    (define unify1
      (lambda (t1 t2 s)
        (let ([t1 (walk t1 (append s s-in))]
              [t2 (walk t2 (append s s-in))])
          (match (list t1 t2)
            [(list (Prim x) (Prim x)) s]
            [(list (TVar nr) (TVar nr)) s]
            [(list _ (TVar nr))
             (ext t2 t1 s)]
            [(list (TVar nr) _)
             (ext t1 t2 s)]
            [(list (Arrow from1 to1)
                   (Arrow from2 to2))
             (let ([s (unify1 from1 from2 s)])
               (and s (unify1 to1 to2 s)))]
            [else #f]))))
    (unify1 t1 t2 '())))



(define infer1
  (lambda (exp)
    (peek 'infer exp)
    (match exp
      [(Const x)
       (cond
        [(number? x)
         (Tp (Prim 'int) s0)]
        [(string? x)
         (Tp (Prim 'string) s0)]
        [(boolean? x)
         (Tp (Prim 'bool) s0)])]
      [(Var x)
       (let ([v (fresh)])
         (Tp v (ext x v s0)))]
      [(Lam (Var x) e)
       (let* ([tp2 (infer1 e)]
              [t2 (Tp-t tp2)]
              [s2 (Tp-s tp2)]
              [t1 (or (lookup x s2) (fresh))])
         (Tp (Arrow t1 t2) (rem-s (list x) s2)))]
      [(App e1 e2)
       (let* ([tp1 (infer1 e1)]
              [tp2 (infer1 e2)]
              [t1 (Tp-t tp1)]
              [out (fresh)]
              [t1e (Arrow (Tp-t tp2) out)]
              [s3 (int-s (Tp-s tp2) (Tp-s tp1))])
         (peek 'infer s3)
         (let ([s4 (unify t1 t1e s3)])
           (cond
            [(not s4)
             (fatal 'infer "incompatible argument in: " exp)]
            [else
             (Tp out (append s4 s3))])))])))



(define infer
  (lambda (exp)
    (reset)
    (let ([tp (infer1 (parse-term exp))])
      (unparse (reify (Tp-t tp) (Tp-s tp))))))



;; infer+display
(define infer-test
  (lambda (exp)
    (printf "--------------------------------------------~n~s~n" exp)
    (let ([t (infer exp)])
      (printf ";; ~s~n" t)
      t)))



;; ------------------------- tests --------------------------

;; I
(infer '(lambda (x) x))
;; => '(1 -> 1)


;; K
(infer '(lambda (x) (lambda (y) x)))
;; => '(1 -> (2 -> 1))


;; S
(infer '(lambda (f) (lambda (g) (lambda (x) ((f x) (g x))))))
;; => '((5 -> (6 -> 7)) -> ((5 -> 6) -> (5 -> 7)))


;; compose
(infer '(lambda (f) (lambda (g) (lambda (x) (f (g x))))))
;; => '((4 -> 5) -> ((3 -> 4) -> (3 -> 5)))


;; 2
(infer '(lambda (f) (lambda (x) (f (f x)))))
;; => '((3 -> 3) -> (3 -> 3))


;; 2*2
(infer '((lambda (f) (lambda (x) (f (f x))))
         (lambda (f) (lambda (x) (f (f x))))))
;; => '((8 -> 8) -> (8 -> 8))


(infer '(lambda (x) (x 1)))
;; => '((int -> 2) -> 2)


(infer '((lambda (x) (x 1)) (lambda (x) x)))
;; => 'int


;; should fail
;; (infer '(lambda (f) ((f #t) (f 1))))

(infer '(lambda (f) (f (lambda (x) x))))

