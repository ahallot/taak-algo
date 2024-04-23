#lang r7rs

;; Algoritmen en datastructuren II
;; Vraag 1: Cycliciteit in Gerichte Grafen

(import (scheme base)
        (scheme write)
        (a-d graph unweighted config)
        (a-d graph-traversing dft-unweighted)
        (a-d graph examples undirected-unweighted)
        (a-d graph examples directed-unweighted))


;; a) - Waarom werkt het niet voor gerichte grafen?
;;
;;      Onderstaand cyclic?-predicaat werkt niet voor gerichte grafen
;;      omdat het een cyclus aangeeft vanaf het moment dan de DFT een boog
;;      naar een eerder bezochte knoop tegenkomt (in het edge-bumped event)
;;      die niet de net daarvoor gevolgde boog is. In een gerichte
;;      graf wijst dat niet altijd op een cyclus omdat de bogen in tegengestelde
;;      richting kunnen wijzen en in dat geval dus geen cyclus beschrijven.

(define (cyclic? g)  
  (define tree (make-vector (order g) '()))
  (define cyclic #f)
  (dft g
       root-nop                       ;root-discovered
       node-nop                       ;node-discovered
       node-nop                       ;node-processed
       (lambda (from to)              ;edge-before
         (vector-set! tree from to))
       edge-nop                       ;edge-after
       (lambda (from to)              ;edge-bumped
         (when (not (eq? (vector-ref tree to) from))
           (set! cyclic #t)
           #f)))
  cyclic)

;; Voorbeeld grafen

(define two-node-cycle
  (let ((g (new #t 2)))
    (add-edge! g 0 1)
    (add-edge! g 1 0)
    g))

;; Tekening:
;;
;; 0 <-> 1


(define acyclic-directed-example
  (let ((g (new #t 3)))
    (add-edge! g 0 1)
    (add-edge! g 0 2)
    (add-edge! g 2 1)
    g))

;; Tekening:
;;
;;  0 --------> 1 
;;   \          ^
;;    \         |
;;     \--> 2 --/


(define acyclic-directed-example2
  (let ((g (new #t 3)))
    (add-edge! g 0 1)
    (add-edge! g 0 2)
    (add-edge! g 1 2)
    g))

;; Tekening:
;;
;;  0 ---------> 1
;;   \           |
;;    \          |
;;     \--> 2 <--/

(define cyclic-directed-example
  (let ((g (new #t 5)))
    (add-edge! g 0 1)
    (add-edge! g 0 2)
    (add-edge! g 2 3)
    (add-edge! g 3 4)
    (add-edge! g 4 2)
    (add-edge! g 4 1)
    g))

;; Tekening:
;;   0 ---------------------> 1 <--\   
;;   |                             |
;;   \--> 2 <-----------\          |    
;;        |             |          |
;;        \--> 3        |          |
;;             |        |          |
;;             \--> 4 __/          |
;;                  \______________/


;; b) De truc om cycliciteit in GERICHTE grafen te onderzoeken is om
;;    een onderscheid te maken tussen reeds bezochte knopen en afgewerkte knopen.
;;    Alleen wanneer de DFT een boog tegenkomt naar een eerder bezochte knoop (in edge-bumped dus)
;;    nDIE NOG NIET AFGEWERKT IS (!) hebben we te maken met een cyclus. In dat geval
;;    is er een cyclus in het huidige pad van de DFT. Als de edge naar
;;    een node gaat die reeds eerder bezocht EN WEL AFGEWERKT is er geen cyclus
;;    in het spel want dan hebben we te maken met een node in een reeds
;;    afgewerkte tak van de DFT-boom. In dat geval is er GEEN cycle omdat de edges
;;    tegengesteld gericht zijn.
;;
;; Voorbeeld:
;;   0 ---------------------> 1 <--\    (knoop 1 is afgewerkt!)
;;   |                             |
;;   \--> 2 <-----------\          |    (knoop 2 is nog niet afgewerkt, 
;;        |             |          |     deel van "actieve" tak van de DFT-boom)
;;        \--> 3        |cyclus!   |
;;             |        |          |geen cyclus!
;;             \--> 4 __/          |
;;                  \______________/

;; Oplossing voor gerichte en ongerichte grafen
(define (cyclic*? g)
  ; tree alleen nodig om te blijven werken voor ongerichte grafen
  (define tree (make-vector (order g) '())) 
  (define processed (make-vector (order g) #f))
  (define cyclic #f)
  (dft g
       root-nop                       ;root-discovered
       node-nop                       ;node-discovered
       (lambda (node)                 ;node-processed
         (vector-set! processed node #t)) ;!!! 
       (lambda (from to)              ;edge-discovered
         (vector-set! tree from to))  ;--> nodig om te blijven werken voor ongerichte grafen
       edge-nop                       ;edge-processed
       (lambda (from to)              ;edge-bumped
         (when (if (directed? g)                          ; !!! we maken hier een onderscheid tussen gericht en ongericht
                   (not (vector-ref processed to))        ; !!! Gericht geval: test indien de knoop reeds afgewerkt was in de DFT
                   (not (eq? (vector-ref tree to) from))) ; Ongericht geval: test op echte terugbogen
           (set! cyclic #t)
           #f)))
  cyclic)


;;Andere oplossing: werkt voor zowel ongerichte als gerichte grafen,
;;maar gebruikt slechts 1 vector and bevat geen ontdubbeld DFT-proces
(define (cyclic**? g)
  ; de tree-vector heet nu branch omdat hij
  ; alleen de actieve tak van de boom voorstelt
  (define branch (make-vector (order g) '())) 
  (define cyclic #f)
  (dft g
       root-nop               ;root-discovered
       node-nop               ;node-discovered
       (lambda (node)         ;node-processed
         ;--> aangeven dat node processed is, m.a.w.
         ;"uit de tree gooien", want de node zit
         ;niet meer in "actieve" tak (branch) van de DFT-boom
         (vector-set! branch node #f)) 
       (lambda (from to)      ;edge-discovered
         ;--> alleen nodig om te blijven werken
         ;voor ongerichte grafen
         (vector-set! branch to from)) 
       edge-nop               ;edge-processed
       (lambda (from to)      ;edge-bumped
         (when (if (directed? g)                            ; !!! we maken hier een onderscheid tussen gericht en ongericht
                   (vector-ref branch to)                   ; !!! Gericht geval: test indien de knoop reeds afgewerkt was in de DFT
                   (not (eq? (vector-ref branch from) to))) ; Ongericht geval: test op echte terugbogen
           (set! cyclic #t)
           #f)))
  cyclic)


;;TESTS

;;Testprocedure:
(define (cyclic-tests cyclic?)
  (let ((all-correct #t))
    (define (test graph graph-name correct-result)
      (define result (cyclic? graph))
      (display "  (cyclic? ")(display graph-name)(display ") = ")
      (display result)
      (if (eq? result correct-result)
          (display " --> OK")
          (begin (display " --> Wrong! (result should be ")
                 (display correct-result)(display ")")
                 (set! all-correct #f)))
      (newline))
    
    ;;Testbatterij:
    (display " Undirected graphs:")(newline)
    (test connected "connected" #t)
    (test three-cc "three-cc" #t)
    (test kite "kite" #t)
    (test cyc-no "cyc-no" #f)
    (test cyc-yes "cyc-yes" #t)
    (newline)
    (display " Directed graphs:")(newline)
    (test two-node-cycle "two-node-cycle" #t)
    (test acyclic-directed-example "acyclic-directed-example" #f)
    (test acyclic-directed-example2 "acyclic-directed-example2" #f)
    (test sedgewick172 "sedgewick172" #t)
    (test full-cycle "full-cycle" #t)
    (test a-list "a-list" #f)
    (test dag-1 "dag-1" #f) ;sedgewick195
    (newline)
    
    (if all-correct
        (display " All tests passed!")
        (display " Some tests failed!"))
    ))

;;Laat de tests los...
(display "Originele versie voor ongerichte grafen (cyclic?):")
(newline)(cyclic-tests cyclic?)    (newline)(newline)
(display "Oplossing voor gerichte en ongerichte grafen (cyclic*?):")
(newline)(cyclic-tests cyclic*?)  (newline)(newline)
(display "Andere oplossing voor gerichte en ongerichte grafen (cyclic**?):")
(newline)(cyclic-tests cyclic**?)(newline)(newline)