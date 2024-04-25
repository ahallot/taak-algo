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


  

(define (scc-tarjan g)  ;scc-tarjan-vectorstack
  (define order-g (order g))
  (define preorder-time 0)
  (define preorder-numbers (make-vector order-g -1))
  (define highest-back-edge (make-vector order-g -1))
  (define sc-components (make-vector order-g -1))
  (define nr-of-components 0)
  (define stack (make-vector order-g '())) ;!!! stack als vector
  (define top '()) ;!!!
  (define included-tag 'included) ;!!! ipv aparte included-vector
  
  (define fw (new #t order-g))
  (define bw (new #t order-g))

  (define bw-from '())

  (define (low node)
    (let* ((highest (vector-ref highest-back-edge node)))
      (if (< highest 0)
          node
          (vector-ref preorder-numbers highest))))
  
  (dft g
       root-nop                                                    ;root-discovered
       (lambda (node)                                              ;node-discovered
         (vector-set! stack node top) ;!!! onthou de "parent" in het pad op de stack-vector
         (set! top node) ;!!! nieuwe top = push
         (vector-set! preorder-numbers node preorder-time)
         (vector-set! highest-back-edge node preorder-time)
         (set! preorder-time (+ preorder-time 1)))
       (lambda (node)                                              ;node-processed
         (when (= (vector-ref highest-back-edge node)
                  (vector-ref preorder-numbers node)) 
           (set! nr-of-components (+ 1 nr-of-components))
           (let loop
             ((t top)) ;!!! = #
             (set! top (vector-ref stack t)) ;!!! pop! = reset top naar de "vorige op het pad"
             (vector-set! stack t included-tag) ;!!! registreer in je stack-vector dat de node t tot een component behoort
             (vector-set! sc-components t nr-of-components)
             (unless (eq? t node)
               (loop top))))) ;!!! = # (voor volgende pop!)
       (lambda (from to) ; before =>
         (when (not (eq? (vector-ref stack to) included-tag))
           ;(newline)
           ;(display from)
           ;(display " =fw=> ")
           ;(display to)         ;used to show edges added to FW
           (add-edge! fw from to)))                                                      ;edge-discovered
       (lambda (from to)                                           ;edge-processed
         (when (not (eq? (vector-ref stack to) included-tag)) ;!!!
           (vector-set! highest-back-edge
                        from (min (vector-ref highest-back-edge from)
                                  (vector-ref highest-back-edge to)))
           ;(newline)
           ;(display "CONS =======>")(display (cons from to))
           ;(if (and (= from 11)
           ;         (= to 12))
           ;    (begin
           ;      (newline)
           ;(display highest-back-edge)
           ;(newline)
           ;(display preorder-numbers)))
           (when (and (< (vector-ref highest-back-edge to)  (vector-ref preorder-numbers from))
                      (not (member from bw-from)))
             (set! bw-from (append bw-from (list from)))
             (newline)
             (display from)
             (display " =bw=> ")
             (display to)         ;used to show edges added to BW
             (add-edge! bw from to)))
         
         (when (not (= (vector-ref sc-components to) (vector-ref sc-components from)))
           ;(newline)
           ;(display from)
           ;(display " XfwX> ")
           ;(display to)         ;used to show edges removed from FW
           (delete-edge! fw from to)))
       (lambda (from to)                                           ;edge-bumped 
         (when (not (eq? (vector-ref stack to) included-tag)) ;!!!
             (vector-set! highest-back-edge
                          from (min (vector-ref highest-back-edge from)
                                    (vector-ref preorder-numbers to)))
           ;(newline)
           ;(display "CONS-2 =======>")(display (cons from to))
           (when (and (= (vector-ref highest-back-edge from) (vector-ref preorder-numbers to))
                    (not (member from bw-from)))
           (set! bw-from (append bw-from (list from)))
           (newline)
           (display from)
           (display " =bw=> ")
           (display to)         ;used to show edges removed from BW
           (add-edge! bw from to)))))

;  (define (make-dag)
;     (let ((dag (new #t nr-of-components
         
         
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

(define (construct-dag scc-graph scc-result)
  (let ((dag (new #f (vector-length scc-result))))
    (define representatives (vector->list scc-result))
    (define components-count (length representatives))
    (define representative-map (make-vector components-count #f))
    
    ;; Create a mapping from component representative to index
    (let loop ((index 0) (reps representatives))
      (cond
        ((null? reps) #f)
        (else
          (vector-set! representative-map (car reps) index)
          (loop (+ index 1) (cdr reps)))))
    
    ;; Iterate through the original graph and add edges to the DAG
    (for-each-node scc-graph
      (lambda (node)
        (for-each-edge scc-graph node
          (lambda (neighbor)
            (let ((node-rep (vector-ref representative-map (vector-ref scc-result node)))
                  (neighbor-rep (vector-ref representative-map (vector-ref scc-result neighbor))))
              (when (not (= node-rep neighbor-rep)) ; Only add edge if from different components
                (add-edge! dag node-rep neighbor-rep)))))))

    dag)) ; Return the constructed DAG



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

(display (construct-dag paper-example (vector 2 2 2 1 1 1 1 3)))

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