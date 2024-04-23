#lang r7rs
;;;; Certifying Euclidean Algorithm
;;;; Author: Youri Coppens
(import (scheme base)
        (scheme write)
        (only (racket base) format)
        (only (a-d scheme-tools) random-inbetween))

;; The classical Euclidean algorithm to compute the greatest common divisor (gcd) for 2 natural numbers.
;; Procedure type: (number number -> number)
(define (gcd a b)
  ; The actual (tail) recursive algorithm
  (define (gcd-rec a b)
    (if (= b 0)
        a
        (gcd-rec b (modulo a b))))
  ; Ensure that the input is valid
  (cond ((or (<= a 0)
             (< b 0))
         (error "Cannot compute GCD for negative number(s)." a b))
        ((< a b) (let ((temp a)) ; a must be the largest: swap a and and b whenever not the case.
                   (set! a b)
                   (set! b temp))))
  (gcd-rec a b))

; Mini-abstraction for certified output
(define certify cons)
(define output car)
(define witness cdr)

; A certifying version of the above algorithm.
; Based on section 2.3 of McConnell et al.'s survey paper.
; In addition to the gcd, 2 numbers, x and y, are computed so that gcd(a,b) = x*a + y*b
; Hence, (x, y) forms the witness (or certificate) of the computed gcd
; Procedure type: (number number -> certified-output)
(define (gcd-certified a b)
  (define (gcd-certified-rec a b)
    (if (= b 0)
        (values a 1 0) ; returning multiple values (see R7RS specification)
        (let-values (((g y x) (gcd-certified-rec b (modulo a b))))
          (values g x (- y (* (quotient a b) x)))))) ; there was a small error in the survey: (* ... x) was missing. 
  (cond ((or (<= a 0)
             (< b 0))
         (error "Cannot compute GCD for negative number(s)." a b))
        ((< a b) (let ((temp a)) ; a must be the largest: swap a and and b whenever not the case.
                   (set! a b)
                   (set! b temp))))
  (let-values (((g x y) (gcd-certified-rec a b)))
    (certify g (cons x y))))

;; A checker for the computed gcd and witness provided by the certifying algorithm
;; Besides checking the above mentioned sum, we must check whether g is a divisor of the 2 input values.
;; To conform the general structure of a checker, this procedure has 3 input arguments (algorithm input, algorithm output and certificate)
(define (check-gcd inp out cert) ; inp = (a . b); out = gcd(a,b);  cert = (x . y)
  (let ((a (car inp))
        (b (cdr inp))
        (x (car cert))
        (y (cdr cert)))
    (and (= 0 (modulo a out))
         (= 0 (modulo b out))
         (= out (+ (* x a) (* y b))))))


;;; Demonstrating the checker
;;; We generate a couple of random integers, call the certified algorithm on it and report the checker's verdict.
(define (demo-checker n)
  (define count-accept 0)
  (define count-reject 0)
  (do ((i 0 (+ i 1)))
    ((= i n)  )
    (let* ((a (random-inbetween 1 10000))
           (b (random-inbetween 0 10000))
           (res (and (when (< a b) ; a must be the largest: swap a and and b whenever not the case.
                       (let ((temp a)) 
                         (set! a b)
                         (set! b temp)))
                     (gcd-certified a b)))) 
      (display (format "--- Checking GCD(~a, ~a) ---~nOutput: ~a~nCertificate: ~a~n" a b (output res) (witness res)))
      (let ((check-res (check-gcd (cons a b)
                                  (output res)
                                  (witness res))))
        (if check-res
            (set! count-accept (+ count-accept 1))
            (set! count-reject (+ count-reject 1)))
        (display (format "Checker result: ~a~n~n" check-res )))))
  (display (format "Demo results: ~a% ACCEPT, ~a% REJECT" (* (/ count-accept n) 100) (* (/ count-reject n) 100))))

(demo-checker 200)