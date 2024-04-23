#lang r7rs

(import (scheme base)
        (scheme write)
        (prefix (a-d stack linked) stack:)
        (a-d graph unweighted config)
        (a-d graph-traversing dft-unweighted)
        (a-d graph examples directed-unweighted))

; Net zoals bij de algoritmes van boogsamenhangendheid en bigeconnecteerdheid in ONgerichte grafen,
; worden er om sterke samenhangendheid te gaan bepalen, preorder-nummers uitgedeeld aan iedere knoop en
; wordt er bekeken wat het kleinste preorder-nummer is dat we vanuit een knoop kunnen bereiken
; (cref. principe van Hopcroft-Tarjan)

(define (scc-tarjan g)
  (define preorder-time 0)
  (define order-g (order g))
  (define preorder-numbers (make-vector order-g -1))
  (define highest-back-edge (make-vector order-g -1))
  (define sc-components (make-vector order-g -1))
  (define included (make-vector order-g #f))
  (define nr-of-components 0)
  (define stack (stack:new))
  
  (define stack-representation '())
  (define (add-stack-representation value) (set! stack-representation (append stack-representation (list value))))
  (define pop-representation (unless (null? stack-representation)
                               (set! stack-representation (cdr stack-representation))))
  (define (in-stack? value) (member value stack-representation))

  (define fw (new #t order-g))
  (define bw (new #t order-g))

  (define (low node)
    (let* ((highest (vector-ref highest-back-edge node)))
      (if (< highest 0)
          node
          (vector-ref preorder-numbers highest))))

  (dft
   g
   root-nop
   (lambda (node)
     (stack:push! stack node)
     (vector-set! preorder-numbers node preorder-time)
     (vector-set! highest-back-edge node preorder-time)
     (set! preorder-time (+ preorder-time 1)))
   (lambda (node)
     (when (= (vector-ref highest-back-edge node)
              (vector-ref preorder-numbers node)) 
       (set! nr-of-components (+ 1 nr-of-components))
       (let loop
         ((t (stack:pop! stack))) 
         (vector-set! sc-components t nr-of-components)
         (vector-set! included t #t)
         (unless (eq? t node)
           (loop (stack:pop! stack))))))
   (lambda (from to) ; before =>
     (when (not (vector-ref included to))
       ;(newline)
       ;(display from)
       ;(display " =fw=> ")
       ;(display to)         ;used to show edges added to FW
       (add-edge! fw from to)))  
   (lambda (from to) ; after => 
     (when (not (vector-ref included to))
       (vector-set! highest-back-edge
                    from (min (vector-ref highest-back-edge from)
                              (vector-ref highest-back-edge to)))
       
       (when #t;(< (vector-ref highest-back-edge to)  from)
         (newline)
         (display highest-back-edge)
         (newline)
         (display preorder-numbers)
         (newline)
         (display from)
         (display " =bw=> ")
         (display to)         ;used to show edges added to BW
         (add-edge! bw from to))
         )
       (when (not (= (vector-ref sc-components to) (vector-ref sc-components from)))
         ;(newline)
         ;(display from)
         ;(display " =XfwX=> ")
         ;(display to)         ;used to show edges removed from FW
         (delete-edge! fw from to)))
     (lambda (from to) ; bump  => avoid cross-edges
       (if (not (vector-ref included to))
           (vector-set! highest-back-edge
                        from (min (vector-ref highest-back-edge from)
                                  (vector-ref preorder-numbers to))))
       (when (= (low from) (low to))
         ;(newline)
         ;(display from)
         ;(display " =bw=> ")
         ;(display to)         ;used to show edges removed from BW
         (add-edge! bw from to))
       ;(newline)
       ;(display highest-back-edge)
       ;(newline)
       ;(display preorder-numbers)
       ;(newline)
       ;(display sc-components)
       ))


  
   (cons nr-of-components sc-components))


  (define paper-example 
    (let ((g (new #t 8)))
      (add-edge! g 0 1)
      (add-edge! g 1 2)
      (add-edge! g 2 0)
      (add-edge! g 1 3)
      (add-edge! g 3 4)
      (add-edge! g 4 5)
      (add-edge! g 4 6)
      (add-edge! g 5 3)
      (add-edge! g 6 3)
      (add-edge! g 7 1)
      (add-edge! g 7 2)
      (add-edge! g 7 3)
      (add-edge! g 7 4)
      g))


  ;;TESTS
  (display (list "SCC-tarj    paper-example" (scc-tarjan             paper-example)))
  (newline)  ;{3 . #(2 2 2 1 1 1 1 3)}
  (display (list "SCC-tarj    sedgewick172" (scc-tarjan             sedgewick172)))
  (newline)  ;{3 . #(2 2 2 3 1 1)}
  (display (list "SCC-tarj    full-cycle"   (scc-tarjan             full-cycle)))
  (newline)  ;;{1 . #(1 1 1 1 1 1)}
  (display (list "SCC-tarj    a-list"       (scc-tarjan             a-list)))
  (newline)  ;{6 . #(6 5 4 1 2 3)}
  (display (list "SCC-tarj    scc4"         (scc-tarjan             scc4)))
  (newline)  ;{4 . #(3 1 3 3 3 3 3 4 4 2 2 2 2)}

  ;
  ;
  ;(define (connect from to v)
  ;  (let ((index from)
  ;        (low to))
  ;    (set! count (+ count 1))
  ;    (stack:push! stack v)
  ;    (for-each (lambda (x)
  ;                (if (not-marked? x)
  ;                    (begin
  ;                      (add-edge! fw v x)
  ;                      (connect x)
  ;                      (if (< (vertex-low x) low)
  ;                          (begin
  ;                            (set-vertex-low! v (vertex-low x))
  ;                            (bw:addEdge! bw v x))))
  ;                    (if (stack:contains? stack x)
  ;                                (if (< (vertex-index x) low)
  ;                                    (begin
  ;                                      (set-vertex-low! v (vertex-index x))
  ;                                      (bw:addEdge! bw v x)))))
  ;              (neighbors v))
  ;    (if (= index low)
  ;        (let ((comp '()))
  ;          (do ((top (stack:pop! stack) (stack:pop! stack)))
  ;              ((not (eq? top v))
  ;               (comp:add top)))
  ;          (result:add! comp (fw comp) (bw comp))))))