#lang r7rs

(import (scheme base)
        (scheme write)
        (prefix (a-d stack linked) stack:)
        (a-d graph unweighted config)
        (prefix (a-d graph labeled config) lb:)
        (a-d graph-traversing dft-unweighted)
        (a-d graph-algorithms directed connectivity)
        (a-d graph examples directed-unweighted))

(define (scc-tarjan-certified g)  
  (define order-g (order g))
  (define preorder-time 0)
  (define preorder-numbers (make-vector order-g -1))
  (define highest-back-edge (make-vector order-g -1))
  (define sc-components (make-vector order-g -1))
  (define nr-of-components 0)
  (define stack (make-vector order-g '()))
  (define top '()) 
  (define included-tag 'included) 
  
  (define fw (new #t order-g))
  (define bw (new #t order-g))

  (define dag-representation '())

  (define (add-representation cons-cel)
    (set! dag-representation (append dag-representation (list cons-cel))))
  
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
       (lambda (from to)
         (when (not (eq? (vector-ref stack to) included-tag))
           (add-edge! fw from to)))                                                     
       (lambda (from to)
         (when (not (eq? (vector-ref stack to) included-tag))
           (vector-set! highest-back-edge
                        from (min (vector-ref highest-back-edge from)
                                  (vector-ref highest-back-edge to))))
         
         (when (< (vector-ref highest-back-edge to) (vector-ref preorder-numbers from))                    
           (add-edge! bw from to))
         
         (if (not(= (vector-ref highest-back-edge from) (vector-ref highest-back-edge to)))
             (add-representation (cons from to)))
         
         (when (not (= (vector-ref sc-components to) (vector-ref sc-components from)))
           (delete-edge! fw from to)))
       (lambda (from to)                                                  
         (when (not (eq? (vector-ref stack to) included-tag)) 
           (vector-set! highest-back-edge
                        from (min (vector-ref highest-back-edge from)
                                  (vector-ref preorder-numbers to))))
          (when (= (vector-ref highest-back-edge from) (vector-ref preorder-numbers to))
             (add-edge! bw from to))))

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




(define (checker g certified )
  (let* ((DAG (car certified))
         (fw (cadr certified))
         (bw (cadr (cdr certified)))
         (nr-of-components (cadr (cddr certified)))
         (sc-components (cadr (cddr (cdr certified))))
         (first-check (first-check-func g DAG fw bw))
         (second-check (second-check-func fw bw g))
         (third-check (third-check-func DAG fw bw))
         (fourth-check (fourth-check-func DAG g)))
    (display "First Check Result : ")(display first-check)
    (newline)
    (display "Second Check Result : ")(display second-check)
    (newline)
    (display "Third Check Result : ")(display third-check)
    (newline)
    (display "Fourth Check Result : ")(display fourth-check)
    (newline)
    (display "Checker final Result : ")(display(and first-check second-check third-check fourth-check))
    (newline)
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

(define (third-check-func DAG fw bw)
  (let ((result #t)
        (current-reachables '()))
    

    (define (check-reachability? start end)
    (unless (or(check-fw-or-bw fw start end)
               (check-fw-or-bw bw start end))
      (set! result #f)))
    
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

(define (fourth-check-func DAG g)
  (let ((result #t))
    (define (c4-dft component-elements representatif)
      (let ((res #f)
            (start-found #f)
            (count 0))
        (define (add-count node)
          (if (member node component-elements)
              (set! count (+ count 1))))
        (dft
         g
         root-nop
         (lambda (node)(cond ((= node representatif)(set! start-found node)(add-count node))
                             (start-found (add-count node))))
         root-nop
         edge-nop
         edge-nop
         edge-nop)
        (if (= count (length component-elements))
            (set! res #t))
        res)) 

(lb:for-each-node
     DAG
     (lambda (index-node info-node)
       (let ((component-elements (car info-node))
             (representatif (cdr info-node)))
         (unless (c4-dft component-elements representatif)
           (set! result #f)))))  
    result))

(define (call-all-on-graph g text)
  (newline)
  (display (list (string-append "SCC-tarj-original  :  "   text)(scc-tarjan g)))
  (newline)
  (display (list (string-append "SCC-tarj-certifier  :  "  text)(scc-tarjan-certified g)))
  (newline)
  (checker g (scc-tarjan-certified g)))

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

