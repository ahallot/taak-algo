#lang r7rs

(import (scheme base)
        (scheme write)
        (prefix (a-d stack linked) stack:)
        (a-d graph unweighted config)
        (prefix (a-d graph labeled config) lb:)
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

  
  
  (define dag-representation '())

  (define (add-representation cons-cel)
    (set! dag-representation (append dag-representation (list cons-cel))))
  
  ;(define (low node)
  ;  (let* ((highest (vector-ref highest-back-edge node)))
  ;    (if (< highest 0)
  ;        node
  ;        (vector-ref preorder-numbers highest))))
  
  (dft g
       root-nop                                                    ;root-discovered
       (lambda (node) ;node-discovered
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
           (when (and (< (vector-ref highest-back-edge to)  (vector-ref preorder-numbers from))
                      (not (member from bw-from)))
             
             (set! bw-from (append bw-from (list from)))
             ;(newline)
             ;(display from)
             ;(display " =bw=> ")
             ;(display to)         ;used to show edges added to BW
             (add-edge! bw from to)))
         (if (not(= (vector-ref highest-back-edge from) (vector-ref highest-back-edge to)))
             (add-representation (cons from to)))
         
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
          (when (and (= (vector-ref highest-back-edge from) (vector-ref preorder-numbers to))
                      (not (member from bw-from)))
             (set! bw-from (append bw-from (list from)))
             ;(newline)
             ;(display from)
             ;(display " =bw=> ")
             ;(display to)         ;used to show edges removed from BW
             (add-edge! bw from to)))))

  (let ((DAG (lb:new #t nr-of-components))
        (seen-sc-representative '())
        (sc-node-representor (make-vector nr-of-components #f)))

    (define (add-dag-edge from to cons-cel)
      (let*((new-from (- (vector-ref sc-components from) 1))
            (new-to(- (vector-ref sc-components to) 1))
            (label (lb:edge-label DAG new-from new-to)))
        (if label
            (lb:add-edge! DAG new-from new-to (append label (list cons-cel)))
            (lb:add-edge! DAG new-from new-to (list cons-cel)))))
      
    
    (dft
     g
     root-nop
     (lambda (node) (let((DAG-index (- (vector-ref sc-components node) 1)))
                        (if (not (member DAG-index seen-sc-representative))
                        (begin
                          ;(newline)
                          ;(display (cons (list node) node))
                          (lb:label! DAG DAG-index (cons (list node) node))
                          (set! seen-sc-representative (append seen-sc-representative (list DAG-index))))
                        (let ((label (lb:label DAG DAG-index)))
                          (set-car! label (append (car label) (list node)))
                          (lb:label! DAG DAG-index label)
                          ))))
     root-nop
     edge-nop
     (lambda (from to)(if (not(= (vector-ref sc-components from) (vector-ref sc-components to)))
             (add-dag-edge from to (cons from to))))
     (lambda (from to)(if (not(= (vector-ref sc-components from) (vector-ref sc-components to)))
             (add-dag-edge from to (cons from to)))))
    
  (list DAG fw bw nr-of-components sc-components)))

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
;(display (list "SCC-tarj    paper-example" (scc-tarjan             paper-example)))
;(newline)  ;{3 . #(2 2 2 1 1 1 1 3)}
;(display (list "SCC-tarj    sedgewick172" (scc-tarjan             sedgewick172)))
;(newline)  ;{3 . #(2 2 2 3 1 1)}
;(display (list "SCC-tarj    full-cycle"   (scc-tarjan             full-cycle)))
;(newline)  ;;{1 . #(1 1 1 1 1 1)}
;(display (list "SCC-tarj    a-list"       (scc-tarjan             a-list)))
;(newline)  ;{6 . #(6 5 4 1 2 3)}
;(display (list "SCC-tarj    scc4"         (scc-tarjan             scc4)))
;(newline)  ;{4 . #(3 1 3 3 3 3 3 4 4 2 2 2 2)}




(define (test g)
  (define preorder-time 0)
  (define preorder-numbers (make-vector (order g) -1))
  (define highest-back-edge (make-vector (order g) -1))
  (define sc-components (make-vector (order g) -1))
  (define included (make-vector (order g) #f))
  (define nr-of-components 0)
  (define stack (stack:new))
  (dft
   g
   root-nop
   (lambda (node)
     ;(display "Discovered Node: ")
     ;(display node)
     ;(newline)
     (stack:push! stack node)
     (vector-set! preorder-numbers node preorder-time)
     (vector-set! highest-back-edge node preorder-time)
     (set! preorder-time (+ preorder-time 1)))
   (lambda (node)
     ;(display "Marked Node : ")
     ;(display node)
     ;(newline)
     (when (= (vector-ref highest-back-edge node)
              (vector-ref preorder-numbers node)) 
       (set! nr-of-components (+ 1 nr-of-components))
       (let loop
         ((t (stack:pop! stack))) 
         (vector-set! sc-components t nr-of-components)
         (vector-set! included t #t)
         (unless (eq? t node)
           (loop (stack:pop! stack))))))
   ;(lambda (from to)
   ;(display "Discovered Edge: ")
   ;(display "From  ")
   ;(display from)
   ;(display" To ")
   ;(display to)
   ;(newline)); before
   edge-nop
   (lambda (from to) ; after =>
     ;(display "AFTER Edge: ")
     ;(display "From  ")
     ;(display from)
     ;(display" To ")
     ;(display to)
     ;(newline)
     (if (not (vector-ref included to))
         (vector-set! highest-back-edge
                      from (min (vector-ref highest-back-edge from)
                                (vector-ref highest-back-edge to)))))
   (lambda (from to) ; bump  => avoid cross-edges
     ;(display "BUMP Edge: ")
     ;(display "From  ")
     ;(display from)
     ;(display" To ")
     ;(display to)
     ;(newline)
     (if (not (vector-ref included to))
         (vector-set! highest-back-edge
                      from (min (vector-ref highest-back-edge from)
                                (vector-ref preorder-numbers to))))))
  (cons nr-of-components sc-components))

(define (checker g certified )
  (let* ((DAG (car certified))
         (fw (cadr certified))
         (bw (cadr (cdr certified)))
         (nr-of-components (cadr (cddr certified)))
         (sc-components (cadr (cddr (cdr certified))))
         (first-check (first-check-func g DAG fw bw))
         (second-check (second-check-func fw bw g))
         (third-check (third-check-func DAG fw bw sc-components))
         (fourth-check #t))
    (display "First Check Result : ")(display first-check)
    (newline)
    (display "Second Check Result : ")(display second-check)
    (newline)
    (display "Third Check Result : ")(display third-check)
    (newline)
    (display "Fourth Check Result : ")(display fourth-check)
    (newline)
    (display "Checker final Result : ")(display(and first-check second-check third-check fourth-check))
    (and first-check second-check third-check fourth-check)
    ))

(define (first-check-func g DAG fw bw)
  (let* ((result #t)
        (order-g (order g))
        (total-node-gerepresenteerd-in-dag 0)
        (fw-elements '())
        (vector-g (make-vector order-g 0)))
    (lb:for-each-node
     DAG
     (lambda (node-index info-node)
       (let ((component-elementen (car info-node)))
                         (for-each
                          (lambda (g-node)
                            (if (< g-node order-g)
                                (let ((value (vector-ref vector-g g-node)))
                                  (if (= value 0)
                                      (begin
                                        (vector-set! vector-g g-node (+ value 1))
                                        (set! total-node-gerepresenteerd-in-dag
                                              (+ total-node-gerepresenteerd-in-dag 1)))
                                      (set! result #f)))
                                (set! result #f)))
                          component-elementen))))
    (unless (= total-node-gerepresenteerd-in-dag order-g)
         (set! result #f))
    (for-each-node
     fw
     (lambda (node) (set! fw-elements (append fw-elements (list node)))))
    (for-each-node
     bw
     (lambda (node) (unless (member node fw-elements)
                      (set! result #f))))
    result))

(define (second-check-func fw bw g)
  (let ((result #t))
    (define (set-res g from to)
      (unless (adjacent? g from to)
        (set! result #f)))
    (for-each-node fw (lambda (from)(for-each-edge fw from (lambda (to)(set-res g from to)))))
    (for-each-node bw (lambda (from)(for-each-edge bw from (lambda (to)(set-res g from to)))))
    result))

(define (third-check-func DAG fw bw sc-components)
  (let ((result #t)
        (current-reachables '())
        (result-dag (make-vector (order fw) '())))
    
    (define (add-to-reachable-elements value)
      (unless (member value current-reachables)
      (set! current-reachables (append current-reachables (list value))))
      (for-each
       (lambda (node)
         (let((reachables (vector-ref result-dag node)))
      (unless (member value reachables)
             (vector-set! result-dag node current-reachables))))
       current-reachables))
    
    (define (check-fw-or-bw fw-or-bw)
      (dft
       fw-or-bw
       (lambda (node)(set! current-reachables '()))
       (lambda (node)(add-to-reachable-elements node))
       (lambda (node)(add-to-reachable-elements node))
       (lambda (from to)(add-to-reachable-elements to))
       (lambda (from to)(add-to-reachable-elements to))
       (lambda (from to)(add-to-reachable-elements to))))
    (check-fw-or-bw fw)
    (check-fw-or-bw bw)
    (lb:for-each-node
     DAG
     (lambda (index-node info-node)
       (let ((component-elementen (car info-node)))
         (for-each
          (lambda (element) (unless(equal? (vector-ref result-dag element) component-elementen)
                              (set! result #f)))
          component-elementen))))
     
    (newline)
    (display result-dag)
    (newline)
    
    result))

(define (fourth-check-func fw bw g)
  (let ((result #t))
    (define (set-res g from to)
      (unless (adjacent? g from to)
        (set! result #f)))
    (for-each-node fw (lambda (from)(for-each-edge fw from (lambda (to)(set-res g from to)))))
    (for-each-node bw (lambda (from)(for-each-edge bw from (lambda (to)(set-res g from to)))))
    result))

(define (call-all-on-graph g  text)
  (newline)
  (display (list (string-append "SCC-tarj-original  :  "   text)(test g)))
  (newline)
  (display (list (string-append "SCC-tarj-certifier  :  "  text)(scc-tarjan g)))
  (newline)
  (checker g (scc-tarjan g))
  (newline)
  )

(define (call-all-on-graphs list-graph)
  (for-each
   (lambda (cons-cell) (call-all-on-graph (car cons-cell) (cdr cons-cell)))
   list-graph))

(define empty-graph (new #t 1))
(define list-graph-test (list (cons empty-graph "empty-graph")
                              (cons paper-example "paper-example")
                              (cons sedgewick172 "sedgewick172")
                              (cons sedgewick172-bis "sedgewick172-bis")
                              (cons sedgewick172-tris "sedgewick172-tris")
                              (cons full-cycle "full-cycle")
                              (cons a-list "a-list")
                              (cons dag-1 "dag-1")
                              (cons scc4 "scc4")
                              ))

(call-all-on-graphs list-graph-test)

;(dft
; graph
; lambda-root
; lambda-discover-node
; lambda-mark-node
; lambda-discover-edge
; lambda-mark-edge
; lambda-bumb-edge)

