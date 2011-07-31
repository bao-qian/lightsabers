;; zipper code adapted from
;; http://okmij.org/ftp/Scheme/zipper-in-scheme.txt

;; Changes:
;; - replaced all do statements by (let loop ...)
;; - fixed some minor bugs


;; use Racket's implementation of reset and shift
(require racket/control)



; deterministic, left-to-right map
; It preserves sharing as much as possible: that is, if given the pair
; l == (cons h t), (and (eq? h (f h)) (eq? t (map* f t))) holds, then
; (eq? (map* f l) l) holds as well.
(define map*
  (lambda (f ls)
    (cond
     [(null? ls) ls]
     [else
      (let* ([h1 (f (car ls))]
             [t1 (map* f (cdr ls))])
        (cond
         [(and (eq? h1 (car ls)) (eq? t1 (cdr ls))) ls]
         [else (cons h1 t1)]))])))


(define depth-first
  (lambda (handle tree)
    (cond
     [(null? tree) tree]
     [(handle tree) => (lambda (x) x)]
     [(not (pair? tree)) tree]
     [else
      (let ((r (map* (lambda (x) (depth-first handle x)) (cdr tree))))
        (cond
         [(eq? r (cdr tree)) tree]
         [else
          (cons (car tree) r)]))])))


(eq? tree1
     (depth-first (lambda (node) (display node) (newline) #f) tree1))

;; ===>
;; (a (b) (c (d 1 2)) e)
;; (b)
;; (c (d 1 2))
;; (d 1 2)
;; 1
;; 2
;; e
;; #t  <---- shared!



(define tree1 '(a (b) (c (d 1 2)) e))
(define tree2 '(z (u) (v (w 10 12)) y))

(depth-first (lambda (node) (display node) (newline) #f) tree1)
;; ==> prints
;;   (a (b) (c (d 1 2)) e)
;;   (b)
;;   (c (d 1 2))
;;   (d 1 2)
;;   1
;;   2
;;   e
;; ==> yields
;; '(a (b) (c (d 1 2)) e)


;; zipper data structure
(struct zipper (curr-node k) #:transparent)


(define zip-tree
  (lambda (tree)
    (reset (depth-first (lambda (tree) (shift f (zipper tree f))) tree))))


(define print-tree
  (lambda (tree)
    (let loop ([cursor (zip-tree tree)])
      (cond
       [(not (zipper? cursor))
        (void)]
       [else
        (display (zipper-curr-node cursor))
        (newline)
        (loop ((zipper-k cursor) #f))]))))


(print-tree tree1)
; prints as before

(print-tree tree2)
;; =>
;; (z (u) (v (w 10 12)) y)
;; (u)
;; (v (w 10 12))
;; (w 10 12)
;; 10
;; 12
;; y



(define zip-all-the-way-up
  (lambda (zipper)
    (cond
     [(zipper? zipper)
      (zip-all-the-way-up ((zipper-k zipper) (zipper-curr-node zipper)))]
     [else zipper])))


(define locate-nth-node
  (lambda (n tree)
    (let loop ([i 0] (cursor (zip-tree tree)))
      (cond
       [(not (zipper? cursor))
        (error "too few nodes")]
       [(= i n) cursor]
       [else
        (loop (add1 i) ((zipper-k cursor) #f))]))))



; replace the 3rd node of tree1 with 'xxx
(let ((desired-node (locate-nth-node 3 tree1)))
  (display "Replacing the node: ")
  (display (zipper-curr-node desired-node))
  (newline)
  (zip-all-the-way-up ((zipper-k desired-node) 'xxx)))



; cross-over of the 3d node of tree1 and 1st node of tree2
(let* ((desired-node1 (locate-nth-node 3 tree1))
       (_ (begin
            (display "Cross-over the node1: ")
            (display (zipper-curr-node desired-node1))
            (newline)))
       (desired-node2 (locate-nth-node 1 tree2))
       (_ (begin
            (display "Cross-over the node2: ")
            (display (zipper-curr-node desired-node2))
            (newline)))
       (new-tree1
        (zip-all-the-way-up ((zipper-k desired-node1)
                             (zipper-curr-node desired-node2))))
       (new-tree2
        (zip-all-the-way-up ((zipper-k desired-node2)
                             (zipper-curr-node desired-node1))))
       )
  (display "new tree1: ") (display new-tree1) (newline)
  (display "new tree2: ") (display new-tree2) (newline))




;;---------------- sharing test ----------------
(define tree2*
  (let ([desired-node (locate-nth-node 6 tree2)])
    (zip-all-the-way-up ((zipper-k desired-node) 'newy))))

tree2*
;; ===> (z (u) (v (w 10 12)) newy)


(define tree-compare-sharing
  (lambda (t1 t2)
    (let loop ([cursor1 (zip-tree t1)]
               [cursor2 (zip-tree t2)])
      (cond
       [(and (zipper? cursor1) (zipper? cursor2))
        (let [(n1 (zipper-curr-node cursor1))
              (n2 (zipper-curr-node cursor2))]
          (cond
           [(eq? n1 n2)
            (display "shared node: ") (printf "~a~n" n1)]
           [else (display "t1 node: ") (printf "~a~n" n1)
                 (display "t2 node: ") (printf "~a~n" n2)]))
        (loop ((zipper-k cursor1) #f) ((zipper-k cursor2) #f))]
       [(zipper? cursor1) (printf "t2 finished early~n")]
       [(zipper? cursor2) (printf "t1 finished early~n")]))))

(tree-compare-sharing tree2 tree2*)

;; ===>
;; t1 node: (z (u) (v (w 10 12)) y)
;; t2 node: (z (u) (v (w 10 12)) newy)
;; shared node: (u)
;; shared node: (v (w 10 12))
;; shared node: (w 10 12)
;; shared node: 10
;; shared node: 12
;; t1 node: y
;; t2 node: newy

