;; A type inferencer for lambda calculus which can handle recursive types
;; such as self-application, Y-combinators and Omega.

;; author: Yin Wang (yw21@cs.indiana.edu)

;; COMPATIBILITY: Although this version has only been tested on Chez
;; Scheme. It should be able to run on most R5RS Scheme implementations.
;; Minor changes are needed for record types because R5RS and R6RS hasn't
;; standardized record types.

;; ask Chez Scheme not to print long gensyms (please comment out if you
;; don't use Chez)
(print-gensym #f)
(optimize-level 3)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pmatch, a pattern match macro taken from Dan Friedman's course C311 (B521)
;; derived with small chnages to Oleg Kiselyov's pattern matcher.
(define-syntax pmatch
  (syntax-rules (else guard)
    [(_ (rator rand ...) cs ...)
     (let ((v (rator rand ...)))
       (pmatch v cs ...))]
    [(_ v) (error 'pmatch "failed: ~s" v)]
    [(_ v (else e0 e ...)) (begin e0 e ...)]
    [(_ v (pat (guard g ...) e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch v cs ...))))
       (ppat v pat (if (and g ...) (begin e0 e ...) (fk)) (fk)))]
    [(_ v (pat e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch v cs ...))))
       (ppat v pat (begin e0 e ...) (fk)))]))

(define-syntax ppat
  (syntax-rules (_ quote unquote)
    [(_ v _ kt kf) kt]
    [(_ v () kt kf) (if (null? v) kt kf)]
    [(_ v (quote lit) kt kf) (if (equal? v (quote lit)) kt kf)]
    [(_ v (unquote var) kt kf) (let ((var v)) kt)]
    [ (_ v (x . y) kt kf)
      (if (pair? v)
          (let ((vx (car v)) (vy (cdr v)))
            (ppat vx x (ppat vy y kt kf) kf))
          kf)]
    [(_ v lit kt kf) (if (equal? v (quote lit)) kt kf)]))



;; utility for binding multiple values
(define-syntax letv*
  (syntax-rules ()
    [(_ () body ...) (begin body ...)]
    [(_ ([x0 v0] [x1 v1] ...) body ...)
     (let-values ([x0 v0])
       (letv* ([x1 v1] ...)
              body ...))]))



;; utility for error reporting
(define fatal
  (lambda (who . args)
    (printf "~s: " who)
    (for-each display args)
    (display "\n")
    (error 'infer "")))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; record types ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; switched from sexps to records because using sexps to represent records
;; are error-prone
;;;;;;;;;;;;;;;;;;;; lambda terms ;;;;;;;;;;;;;;;;;;;;;;;
(define-record const (obj))             ; constant
(define-record var (name))              ; lambda's var
(define-record lam (var body))          ; lambda
(define-record app (rator rand))        ; application

;;;;;;;;;;;;;;;;;;;; types ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-record type (main))             ; sum type of three things: Type = Symbol | TVar | Arr
(define-record tvar (name))             ; type variable (used for substitution)
(define-record arr (from to serial))    ; function (arrow) type, serial is for printing recursive types

;; convenience function for constructing normal arrow types (without cycle)
(define make-arrow
  (lambda (from to)
    (make-arr from to #f)))




;; parser from sexps and types into records
;; Example:
;; (parse '(lambda (f) (f 16)))
;; => #[lam f #[app #[var f] #[const 16]]]
(define parse
  (lambda (sexp)
    (pmatch sexp
      [,x (guard (or (number? x) (string? x) (boolean? x))) (make-const x)]
      [,x (guard (symbol? x)) (make-var x)]
      [(lambda (,x) ,body) (make-lam x (parse body))]
      [(,e1 ,e2) (make-app (parse e1) (parse e2))])))




;; utility function for constructing types from sexps
;; Note:
;; - Type variables are assumed to start with 't'.
;; - It doens't convert recursive types.

;; Example:
;;   (parse-type '(t0 -> (t1 -> t0)))
;;       => #[arr #[tvar t0] #[arr #[tvar t1] #[tvar t0] #f] #f]
;;            where the first and second #[tvar ?a] are the SAME object

(define parse-type
  (lambda (t)
    (define parse1
      (lambda (t s)
        (pmatch t
          [(,a -> ,b)
           (letv* ([(a^ s1) (parse1 a s)]
                   [(b^ s2) (parse1 b s1)])
             (values (make-arrow a^ b^) s2))]
          [,x (guard (and (symbol? x)
                          (eq? #\t (string-ref (symbol->string x) 0))))
              (cond
               [(assq x s) => (lambda (p) (values (cdr p) s))]
               [else (let ([tv (make-tvar x)])
                       (values tv (cons `(,x . ,tv) s)))])]
          [,x (values x s)])))
    (letv* ([(t^ _s) (parse1 t '())])
      t^)))



;; Convert expr in record format into sexp

;; It works for both expressions and types. Recusive types are converted to
;; something like (%0 (int -> !0)), where %n signifies a "handle", and !n
;; refers to it.

(define unparse
  (lambda (t)
    (cond
     [(type? t) (unparse (type-main t))]
     [(tvar? t) (tvar-name t)]
     [(arr? t)
      (let ([serial (arr-serial t)])
        (cond
         [(not serial)
          `(,(unparse (arr-from t)) -> ,(unparse (arr-to t)))]
         [else
          (let ([lb (string->symbol (string-append "%" (number->string serial)))])
            `(,lb ,(unparse (arr-from t)) -> ,(unparse (arr-to t))))]))]
     [(pair? t)
      (cons (unparse (car t)) (unparse (cdr t)))]
     [(const? t) (const-obj t)]
     [(var? t) (var-name t)]
     [(app? t)
      `(,(unparse (app-rator t)) ,(unparse (app-rand t)))]
     [(lam? t)
      `(lambda ,(unparse (lam-var t)) ,(unparse (lam-body t)))]
     [else t])))

; (parse-type '(int -> (int -> int)))
; (unparse (parse-type '(int -> (int -> int))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; substitution ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; substitutions and environments use the same data structure---association
;; list, but they are defined separately to keep them abstract.

;; initial substitution is empty
(define s0 '())
(define ext-sub (lambda (x v s) `((,x . ,v) . ,s)))



;;;;;;;;;;;;;;;;;;;;;;;;;; environment ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; initial environment
;; This contains primitive operations only.
(define env0
  `((add1       .  ,(make-type (parse-type '(int -> int))))
    (*          .  ,(make-type (parse-type '(int -> (int -> int)))))
    (-          .  ,(make-type (parse-type '(int -> (int -> int)))))
    (+          .  ,(make-type (parse-type '(int -> (int -> int)))))
    (reverse    .  ,(make-type (parse-type '(string -> string))))))

(define ext-env (lambda (x v s) `((,x . ,v) . ,s)))

;; lookup :: (Var * Env) -> Maybe Type
(define lookup
  (lambda (x env)
    (let ((slot (assq x env)))
      (cond
       [(not slot) #f]                  ; Nothing
       [else (cdr slot)]))))            ; Some Type



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; unification ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Walk - union find.

;; It traces the type variable in the substitution until it finds something
;; that's not a type variable.

;; walk :: (TVar * Subst) -> {TVar, Type}
(define walk
  (lambda (x s)
    (let ([slot (assq x s)])
      (cond
       [(not slot) x]
       [(tvar? (cdr slot)) (walk (cdr slot) s)]
       [else (cdr slot)]))))



;; Unify - "coinductive" unification.

;; The unifer use a stack to record the pairs of terms whose unification is
;; "in progress". It pushes the pair of terms (u,v) onto the stack before
;; recursive calls to unify the subterms. The sub-unifications consider
;; their pairs of terms unified if they are already in the stack, because
;; that means a "parent unification" has been trying to unify them, in
;; which case going on will lead to infinite loops.

;; The correctness of this stop condition can be justified by considering
;; unification as a graph isomorphism algorithm between two graphs A and B,
;; with fixed starting vertices u and v. We recursively compare each pair
;; of vertices from corresponding out-edges from u and v. Before we follow
;; those edges, we push the pair (u,v) onto a stack, which signifies that
;; we have "established the correspondence" of u and v. All later
;; comparisons must be consistent with this correspondence. If there is any
;; inconsistence, the graphs will not be isomorphic. There are several
;; possibilities:

;; 1) If both graphs are acyclic, then this is just a normal type-checking
;; unifier, but without occurs check. Occurs check is not needed for
;; acyclic graphs, because acyclic graphs corresponds to types whose
;; components don't contain themselves. In essence, they are finite trees.

;; 2) If the current edge of graph A points back to an earlier vertex V1 on
;; the path (thus form a cycle), but the corresponding edge of graph B
;; doesn't point to the vertex V2 such that (V1,V2) is on the stack, then
;; unification should fail. This is because: a) If the pair (V1,V3) where
;; V3=/=V2 is on the stack, then we have already considered V1 and V3 to be
;; correspondent vertices in the isomorphism. Now the fact that V1 "meets" V2
;; contradicts our earlier decision. b) It is not possible that V1 doesn't
;; appear in any pair in the stack, because that means V1 is not on the
;; path, thus the edge would not form a cycle as the premise.

;; 3) If the current edge of graph A points back to an earlier vertex V1 on
;; the path (thus form a cycle), and the corresponding edge of graph B
;; points to the vertex V2 such that (V1,V2) is already on the stack, then
;; the recursive comparison should succeed, and control should return to
;; its parent. This is because there is no point following V1 and V2's
;; edges. This is justified by two possiblities: a) we have already
;; compared all the "decendents" of V1 and V2 and they are all isomorphic.
;; b) We WILL consider other edges of V1 and V2 at some point after the
;; current recursive call returns, because the pair (V1,V2) is on the
;; stack!

;; Thus we have reduced the type checking problem of infinite types to
;; isomorphism of graphs.


;; unify :: (Term * Term * Subst) -> Subst
(define unify
  (lambda (u v s)
    (define onStack?
      (lambda (u v stk)
        (cond
         [(null? stk) #f]
         [else
          (let ([head (car stk)])
            (cond
             [(and (eq? u (car head)) (eq? v (cdr head))) #t]
             [(and (eq? v (car head)) (eq? u (cdr head))) #t]
             [else (onStack? u v (cdr stk))]))])))
    (define unify1
      (lambda (u v s stk)
        (let ([u (walk u s)] [v (walk v s)])
          (cond
           [(and (symbol? u) (symbol? v) (eq? u v)) s]
           [(and (tvar? u) (tvar? v) (eq? u v)) s]
           [(onStack? u v stk) s]
           [(tvar? u) (ext-sub u v s)]
           [(tvar? v) (ext-sub v u s)]
           [(and (arr? u) (arr? v))
            (let ((s^ (unify1 (arr-from u) (arr-from v) s (cons `(,u . ,v) stk))))
              (and s^ (unify1 (arr-to u) (arr-to v) s^ (cons `(,u . ,v) stk))))]
           [else #f]))))
    (unify1 u v s '())))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reify - convert type variables inside types into consistent symbols
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reify will handle cyclic types with a similar trick as the unifier. It
;; pushes arrow types (or other compound types if we have them) into a
;; stack before recursion into the subterms. If at some point the subterms
;; refers back to this arrow type A, it is given a unique number n. An
;; arrow structure will be constructed with a "serial number", and the
;; association (A, n) is put into an association list occur, which is
;; threaded throughout the reifying process (In other words, occur is a
;; state) so that the numbering is consistent.

;; reify :: Term -> Subst -> Term
(define reify
  (lambda (x s)
    (define reify1
      (lambda (x n s stk occur)
        (define name
          (lambda (s n)
            (string->symbol
             (string-append s (number->string n)))))
        (define get-serial
          (lambda (x occur n)
            (let ([occur (reverse occur)])
              (cond
               [(null? occur) #f]
               [(eq? x (car occur)) n]
               [else (get-serial x (cdr occur) (add1 n))]))))
        (let ((x (walk x s)))
          (cond
           [(or (memq x stk) (memq x occur))
            (let ([serial (get-serial x occur 0)])
              (cond
               [(not serial)
                (values (name "!" (length occur)) n s (cons x occur))]
               [else
                (values (name "!" serial) n s occur)]))]
           [(symbol? x) (values x n s occur)]
           [(tvar? x)
            (let ([v* (name "t" n)])
              (values v* (add1 n) (ext-sub x v* s) occur))]
           [(arr? x)
            (letv* ([(u n1 s1 o1) (reify1 (arr-from x) n s (cons x stk) occur)]
                    [(v n2 s2 o2) (reify1 (arr-to x) n1 s1 (cons x stk) o1)]
                    [(serial) (get-serial x o2 0)])
              (values (make-arr u v serial) n2 s2 o2))]
           [else
            (fatal "[reify] Type contains illegal object: " x)]))))
    (letv* ([(x^ _n _s _o) (reify1 x 0 s '() '())]) x^)))


;; for pretty-print the type record
(define reify-type
  (lambda (x s)
    (cond
     [(type? x)
      (make-type (reify-type (type-main x) s))]
     [(null? x) '()]
     [(pair? x)
      (cons (reify-type (car x) s)
            (reify-type (cdr x) s))]
     [else (reify x s)])))




;;;;;;;;;;;;;;;;;;;;;;;;;;; inferencer ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This outputs the type structure. Probably not human readable.
;; Please use the human readable driver infer instead.
(define infer-type
  (lambda (exp)
    (define infer1
      (lambda (exp env s)
        (cond
         [(const? exp)
          (let ([x (const-obj exp)])
            (cond
             [(number? x) (values (make-type 'int) s)]
             [(string? x) (values (make-type 'string) s)]
             [(boolean? x) (values (make-type 'bool) s)]))]

         [(var? exp)
          (let* ([x (var-name exp)]
                 [t (lookup x env)])
            (cond
             [(not t)                   ; generate type var for unbound variable
              (fatal 'infer "unbound variable:  x \n")]
             [else (values t s)]))]

         [(lam? exp)
          (let ([x (lam-var exp)]
                [body (lam-body exp)])
            (letv* ([(t1) (make-type (make-tvar x))]
                    [(env*) (ext-env x t1 env)]
                    [(t2 s^) (infer1 body env* s)])
              (let ([t1main (type-main t1)]
                    [t2main (type-main t2)])
                (values (make-type (make-arr t1main t2main #f)) s^))))]

         [(app? exp)
          (let ([e1 (app-rator exp)]
                [e2 (app-rand exp)])
            (letv* ([(t1 s1) (infer1 e1 env s)]
                    [(t2 s2) (infer1 e2 env s1)]
                    [(tv3) (make-tvar 'tv3)]
                    [(tv4) (make-tvar 'tv4)]
                    [(s3) (unify (type-main t1) (make-arr tv3 tv4 #f) s2)])
              (cond
               [(not s3)
                (let ([t* (reify (type-main t1) s1)])
                  (fatal 'infer
                         "trying to apply non-function:  \n"
                         " - term:" (unparse e1)        "\n"
                         " - type:" (unparse t*)         ))]
               [else
                (let ([s4 (unify (type-main t2) tv3 s3)]) ; shouldn't unify
                  (cond
                   [(not s4)
                    (let ([t1* (reify (type-main t1) s3)]
                          [tv3* (reify tv3 s3)]
                          [t2* (reify (type-main t2) s3)])
                      (fatal 'infer
                             "incompatible argument type:          \n"
                             " - function:      " (unparse e1)    "\n"
                             " - function type: " (unparse t1*)   "\n"
                             " - expected type: " (unparse tv3*)  "\n"
                             " - argument type: " (unparse t2*)   "\n"
                             " - argument:      " (unparse e2)     ))]
                   [else
                    (values (make-type tv4) s4)]))])))])))
    (infer1 (parse exp) env0 s0)))


;; driver for infer-type for human readable output
(define infer
  (lambda (exp)
    (letv* ([(t^ s^) (infer-type exp)])
      (unparse (reify (type-main t^) s^)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                      Test utils                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Utility for checking the isomorphism of the types of two implementations
;; for the same thing. For example the tests contain two versions of the
;; Y-combinator (CBN and CBV), two versions of Church numberal's
;; predecessor operator. They are indeed isomorphic!

;; set substraction
(define set-
  (lambda (s1 s2)
    (cond
     [(null? s1) '()]
     [(member (car s1) s2) (set- (cdr s1) s2)]
     [else (cons (car s1) (set- (cdr s1) s2))])))


;; checking whether the types of e1 and e2 are isomorphic (can be
;; unified) - If they are, output the *additional* associations
;; created in order to make them isomorphic - Otherwise, return #f
(define isomorphic-type?
  (lambda (e1 e2)
    (letv* ([(t1 s1) (infer-type e1)]
            [(t2 s2) (infer-type e2)]
            [(s3) (append s1 s2)]
            [(s4) (unify (type-main t1) (type-main t2) s3)])
      (cond
       [(not s4) #f]
       [else (set- s4 s3)]))))

