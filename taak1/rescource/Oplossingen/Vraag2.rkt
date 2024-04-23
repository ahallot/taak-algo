#lang r7rs

;; Algoritmen en datastructuren II 
;; Vraag 2: Algoritme van Tarjan

(import (scheme base)
        (scheme write)
        (prefix (a-d stack linked) stack:)
        (a-d graph unweighted config)
        (a-d graph examples directed-unweighted)
        ;voor de originele scc-tarjan (om te vergelijken in de tests)
        (a-d graph-algorithms directed connectivity) 
        (a-d graph-traversing dft-unweighted))

;;Ga best als volgt te werk:
;; - STAP 1: Vervang het stack ADT door een stack opgeslagen in een nieuwe
;;           knoop-geïndexeerde vector + een top variabele als pointer naar
;;           de knoop bovenaan van de stack.
;;           Vervang dus alle push! en pop! operaties door code die je stack-vector
;;           en de top variabele gebruikt ipv het stack ADT.
;;           Laat de included vector voorlopig ongemoeid.
;; - STAP 2: Breng de functies van de stack-vector en de included-vector samen in
;;           1 vector (de stack-vector dus). Hoe zal je nu aangeven wanneer
;;           een knoop "included" is?

;;Oplossing:
(define (scc-tarjan-vectorstack g)
  (define preorder-time 0)
  (define preorder-numbers (make-vector (order g) -1))
  (define highest-back-edge (make-vector (order g) -1))
  (define sc-components (make-vector (order g) -1))
  (define nr-of-components 0)
  (define stack (make-vector (order g) '())) ;!!! stack als vector
  (define top '()) ;!!!
  (define included-tag 'included) ;!!! ipv aparte included-vector
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
       edge-nop                                                    ;edge-discovered
       (lambda (from to)                                           ;edge-processed
         (if (not (eq? (vector-ref stack to) included-tag)) ;!!!
             (vector-set! highest-back-edge
                          from (min (vector-ref highest-back-edge from)
                                    (vector-ref highest-back-edge to)))))
       (lambda (from to)                                           ;edge-bumped 
         (if (not (eq? (vector-ref stack to) included-tag)) ;!!!
             (vector-set! highest-back-edge
                          from (min (vector-ref highest-back-edge from)
                                    (vector-ref preorder-numbers to))))))
  (cons nr-of-components sc-components))


;;TESTS
(display (list "SCC-tarj    sedgewick172" (scc-tarjan             sedgewick172)))
(newline)  ;{3 . #(2 2 2 3 1 1)}
(display (list "SCC-tarj-vs sedgewick172" (scc-tarjan-vectorstack sedgewick172)))
(newline)  ;{3 . #(2 2 2 3 1 1)}
(display (list "SCC-tarj    full-cycle"   (scc-tarjan             full-cycle)))
(newline)  ;;{1 . #(1 1 1 1 1 1)}
(display (list "SCC-tarj-vs full-cycle"   (scc-tarjan-vectorstack full-cycle)))
(newline)  ;{1 . #(1 1 1 1 1 1)}
(display (list "SCC-tarj    a-list"       (scc-tarjan             a-list)))
(newline)  ;{6 . #(6 5 4 1 2 3)}
(display (list "SCC-tarj-vs a-list"       (scc-tarjan-vectorstack a-list)))
(newline)  ;{6 . #(6 5 4 1 2 3)}
(display (list "SCC-tarj    scc4"         (scc-tarjan             scc4)))
(newline)  ;{4 . #(3 1 3 3 3 3 3 4 4 2 2 2 2)}
(display (list "SCC-tarj-vs scc4"         (scc-tarjan-vectorstack scc4)))
(newline)  ;{4 . #(3 1 3 3 3 3 3 4 4 2 2 2 2)}

