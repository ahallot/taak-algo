#lang r7rs

(import (scheme base)
        (scheme write)
        (prefix (a-d stack linked) stack:)
        (a-d graph unweighted config)
        (prefix (a-d graph labeled config) lb:)
        (a-d graph-traversing dft-unweighted)
        (a-d graph-algorithms directed connectivity)
        (a-d graph examples directed-unweighted))

;My certified algorithme is based on the vector-stack version of the WPO to have it
;improved compared to the one in a-d.

(define (scc-tarjan-certified g)  
  (define order-g (order g))
  (define preorder-time 0)
  (define preorder-numbers (make-vector order-g -1))
  (define highest-back-edge (make-vector order-g -1))
  (define sc-components (make-vector order-g -1))      ;strongly connected components
  (define nr-of-components 0)
  (define stack (make-vector order-g '()))
  (define top '()) 
  (define included-tag 'included) 

  ;we make two graph: Forwardtree(fw) and Backwardtree(bw)
  (define fw (new #t order-g))
  (define bw (new #t order-g))

  (define DAG-representation '())

  ;this function add to the list DAG-representation the from . to of a node of a sc to a node of a other sc.
  ;we do this to keep all the potential edges represented by the edge in the DAG
  (define (add-representation cons-cel)
    (set! DAG-representation (append DAG-representation (list cons-cel))))

  ;this is out main DFT to do tarjan and make the witnesses. Nothing changes for the node-lambda's.
  ;I have only extended the edge-lambda's to keep needed information.
  (dft g
       root-nop                                                   
       (lambda (node) 
         (vector-set! stack node top) 
         (set! top node)
         (vector-set! preorder-numbers node preorder-time)
         (vector-set! highest-back-edge node preorder-time)
         (set! preorder-time (+ preorder-time 1)))
       (lambda (node)                                             
         (when (= (vector-ref highest-back-edge node)
                  (vector-ref preorder-numbers node)) 
           (set! nr-of-components (+ 1 nr-of-components))
           (let loop
             ((t top))
             (set! top (vector-ref stack t)) 
             (vector-set! stack t included-tag) 
             (vector-set! sc-components t nr-of-components)
             (unless (eq? t node)
               (loop top)))))
       (lambda (from to)                                       ;When we discover an edge we add it to the fw
         (when (not (eq? (vector-ref stack to) included-tag))
           (add-edge! fw from to)))                                                     
       (lambda (from to)
         (when (not (eq? (vector-ref stack to) included-tag))
           (vector-set! highest-back-edge
                        from (min (vector-ref highest-back-edge from)
                                  (vector-ref highest-back-edge to)))

           ;When we Process an edge and that the edges can go backward we add it to the bw
         (when (< (vector-ref highest-back-edge to) (vector-ref preorder-numbers from))                    
           (add-edge! bw from to)))
         
         ;when from and to have different highest-back-egde we find a edge between two different sc
         (if (not(= (vector-ref highest-back-edge from) (vector-ref highest-back-edge to)))
             (add-representation (cons from to)))
         ;with the same idea if from and to are from different sc we delete the edge from to from the fw.
         (when (not (= (vector-ref sc-components to) (vector-ref sc-components from)))
           (delete-edge! fw from to)))
       (lambda (from to)
         ;when edge bumped we add the edge in the bw, if the highest-back-edge is equal to the preorder number of its to                               
         (when (not (eq? (vector-ref stack to) included-tag)) 
           (vector-set! highest-back-edge
                        from (min (vector-ref highest-back-edge from)
                                  (vector-ref preorder-numbers to)))
          (when (= (vector-ref highest-back-edge from) (vector-ref preorder-numbers to))
             (add-edge! bw from to)))))

  ;Now that the main DFT ended we have our fw and bw, next to it we have now to make the DAG
  ;with the other information we got in the DFT we did
  (let ((DAG (lb:new #t nr-of-components)) ;there is a node for each component
        (seen-sc-representative '())
        (sc-node-representor (make-vector nr-of-components #f)))
    ;effectivly makes an edge between two nodes of DAG
    (define (add-dag-edge from to cons-cel) 
      (let*((new-from (- (vector-ref sc-components from) 1)) ;from for the DAG 
            (new-to(- (vector-ref sc-components to) 1))      ;to for the DAG 
            (label (lb:edge-label DAG new-from new-to)))     ;label/labels of the edge from to
        (if label  ;if there are no label there is no edge in our dag (because we always add an label when we make an edge in this code)
            (lb:add-edge! DAG new-from new-to (append label (list cons-cel))) ;if there is already an edge we append the list of (from.to) of graph g 
            (lb:add-edge! DAG new-from new-to (list cons-cel)))))   ;if there is no edge between from and to, we start our list (from.to) of graph g
    (dft
     g ;original graph
     root-nop
     (lambda (node) (let((DAG-index (- (vector-ref sc-components node) 1))) ;add a node to the dag as either
                        (if (not (member DAG-index seen-sc-representative))
                        (begin                                              ;add a representatif node
                          (lb:label! DAG DAG-index (cons (list node) node))
                          (set! seen-sc-representative (append seen-sc-representative (list DAG-index))))
                        (let ((label (lb:label DAG DAG-index)))             ;add a represented node
                          (set-car! label (append (car label) (list node)))
                          (lb:label! DAG DAG-index label)))))
     root-nop
     edge-nop
     ;We connect the DAG node each to an other, with add-dag-edge if they are from different sc
     (lambda (from to)(if (not(= (vector-ref sc-components from) (vector-ref sc-components to)))
             (add-dag-edge from to (cons from to))))
     (lambda (from to)(if (not(= (vector-ref sc-components from) (vector-ref sc-components to)))
             (add-dag-edge from to (cons from to)))))
    ;we give our result as a list with 
  (certify (list DAG fw bw) (list nr-of-components sc-components))))

(define certify cons)
(define output cdr)
(define witness car)

;our checker will use our certification to apply 4 different check for this algorithme
(define (check-tarjan g certification)
  (let* ((w (witness certification))
         (DAG (car w))
         (fw (cadr w))
         (bw (cadr (cdr w)))
         (out-put (output certification))
         (nr-of-components (car out-put))
         (sc-components (cadr  out-put))
         (first-check (first-check-func g DAG fw bw))
         (second-check (second-check-func fw bw g))
         (third-check (third-check-func DAG fw bw))
         (fourth-check (fourth-check-func DAG g sc-components)))
    (display "Checker final Result : ")(display(and first-check second-check third-check fourth-check))
    (newline)
    (and first-check second-check third-check fourth-check)))

(define (first-check-func g DAG fw bw) ;check if all node in g are exactly once in the DAG and if the fw and bw uses the same nodes.
  (let* ((result #t)
        (order-g (order g))
        (total-node-gerepresenteerd-in-dag 0)
        (fw-elements '())
        (vector-g (make-vector order-g 0)))
    (lb:for-each-node  ;we check the dag
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
    ;we check fw and bw
    (for-each-node
     fw
     (lambda (node) (set! fw-elements (append fw-elements (list node)))))
    (for-each-node
     bw
     (lambda (node) (unless (member node fw-elements)
                      (set! result #f))))
    result))

(define (second-check-func fw bw g) ;checks if all edges in fw and bw exist in original input (graph g)
  (let ((result #t))
    (define (set-res g from to)
      (unless (adjacent? g from to)
        (set! result #f)))
    (for-each-node fw (lambda (from)(for-each-edge fw from (lambda (to)(set-res g from to)))))
    (for-each-node bw (lambda (from)(for-each-edge bw from (lambda (to)(set-res g from to)))))
    result))

(define (third-check-func DAG fw bw)
  (let ((result #t)
        (current-reachables '()))
    ;checks if end is reacheable starting from start in fw or bw
    (define (check-reachability? start end)
    (unless (or(check-fw-or-bw fw start end)
               (check-fw-or-bw bw start end))
      (set! result #f)))
    ;DFT on the fw or bw that will give is if a end is reachable from the start node or not
    (define (check-fw-or-bw fw-or-bw start end)
      (let ((start-found #f)
            (res #f))
      (dft
       fw-or-bw
       (lambda (node)(set! current-reachables '()))
       (lambda (node)(cond ((= node start)(set! start-found node))
                           ((and start-found (= node end))(set! res #t))))
       root-nop
       edge-nop
       edge-nop
       edge-nop)))
    ;if for sc all nodes can reach there neighbours element in the same sc. if only one is not reachable set result false.
    (lb:for-each-node
     DAG
     (lambda (index-node info-node)
       (let ((component-elementen (car info-node)))
         (for-each
          (lambda (start)
            (for-each
             (lambda (end) (unless (= start end)
                             (check-reachability? start end)))
             component-elementen))            
          component-elementen))))   
    result
    ))

;similar working as check 3. We check if all element we can reach from representatif are actualy in the component
(define (fourth-check-func DAG g sc-components)
  (let ((result #t))
    ;count the number of node element of the sc. we give the representatif to know when we should start counting.
    (define (c4-dft component-elements representatif)
      (let ((res #f)
            (start-found #f)
            (count 0))
        ;add 1 to count 
        (define (add-count node)
          (set! count (+ count 1)))
        ;check via dft all if nodes are reachable from representatif.
        (dft
         g
         root-nop
         (lambda (node)(if (check-reachable representatif node)
                           (add-count node)))
         root-nop
         edge-nop
         edge-nop
         edge-nop)
        (if (= count (length component-elements)) 
            (set! res #t))
        res))
    ;check if a start can reach an end
    (define (check-reachable start end)
      (if (= start end)
          #t
          (let ((start-found #f)
                (res #f))
            (dft
             g
             root-nop
             (lambda (node)(cond ((= node start)(set! start-found node))
                                 ((and start-found
                                       (= node end)
                                       (= (vector-ref sc-components start)
                                          (vector-ref sc-components end)))(set! res #t))))
             root-nop
             edge-nop
             edge-nop
             edge-nop)
            res)))
;check for all representatif if they have with their component-elements all the reachable elements
(lb:for-each-node
     DAG
     (lambda (index-node info-node)
       (let ((component-elements (car info-node))
             (representatif (cdr info-node)))
         (unless (c4-dft component-elements representatif)
           (set! result #f)))))  
    result))
;call original tarjan , cerified one & checker for a given graph and display it with given text (name graph usualy)
(define (call-all-on-graph g text)
  (newline)
  (display (list (string-append "SCC-TARJAN ORIGINAL  :  "   text)(scc-tarjan g)))
  (newline)
  (display (list (string-append "SCC-TARJAN CERTIFIED  :  "  text)(scc-tarjan-certified g)))
  (newline)
  (check-tarjan g (scc-tarjan-certified g)))

;call for all graph in a list of graphs the previous function & gives you number of successes for the amount of try we did
(define (call-all-on-graphs list-graphs)
  (let ((count 0)
        (total (length list-graphs)))
  (for-each
   (lambda (cons-cell) (if (call-all-on-graph (car cons-cell) (cdr cons-cell))
                           (set! count (+ count 1))))
   list-graphs)
  (newline)
  (display "Number of successes : ")(display count)(display " out of ")(display total)
  ))


(define one-node (new #t 1))

(define three-node (new #t 3))

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

(define list-graph-test (list (cons one-node "one-node")
                              (cons three-node "three-node")
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
