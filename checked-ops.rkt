#lang rosette

; checked arithmetic on bitvectors using data/maybe and monads
; tried to make it work with Rosette

(require
  (only-in data/maybe
    just
    nothing
    [just? maybe:just?]
    [nothing? maybe:nothing?]
    [from-just maybe:from-just]
    [from-just! maybe:from-just!])
  (only-in data/monad
     [chain monad:chain])
  (only-in data/applicative
     pure)
  (for-syntax racket/base
                     racket/syntax
                     syntax/parse))
; NOTE we can't use do because it expands to code that uses monad:chain
; see https://stackoverflow.com/questions/57937588/in-racket-can-i-redefine-the-form-if-and-have-other-derived-forms-automatical

(provide
  (all-defined-out)
  just nothing)

; monad syntax (adapted from data/monad)

(define-syntax (<- stx)
  (raise-syntax-error '<- "cannot be used outside of a do block" stx))

(begin-for-syntax
  (define-syntax-class internal-definition
    #:attributes [expansion]
    #:description "internal definition"
    [pattern form
             #:with expansion
             (local-expand #'form (list (generate-temporary #'form))
                           (list #'define #'define-values #'define-syntax #'define-syntaxes))
             #:when (internal-definition? #'expansion)])

  (define internal-definition?
    (syntax-parser
      #:literals [begin define define-values define-syntax define-syntaxes]
      [(begin form ...)
       (ormap internal-definition? (attribute form))]
      [({~or define define-values define-syntax define-syntaxes} . _) #t]
      [_ #f])))

(define-syntax do
  (syntax-parser
    #:literals [<-]
    [(_ x:expr) #'x]
    [(_ [var {~and arrow <-} mx:expr] . rest)
     (with-disappeared-uses
      (begin
        (record-disappeared-uses (list #'arrow))
        #'(chain (lambda (var) (do . rest)) mx)))]
    [(_ def:internal-definition ...+ . rest)
     #'(let () def.expansion ... (do . rest))]
    [(_ mx:expr . rest)
     #'(chain (λ (_) (do . rest)) mx)]))

; we lift data/maybe and data/monad operations

(define (just? x)
  (for/all ([x x])
    (maybe:just? x)))

(define (nothing? x)
  (for/all ([x x])
    (maybe:nothing? x)))

(define (from-just! m)
  (for/all ([m m])
    (maybe:from-just! m)))

(define (from-just x m)
  (for/all ([m m])
    (maybe:from-just x m)))

(define (chain f x)
  (for/all ([x x])
    (monad:chain f x)))

(module+ test
  (require rackunit)

  (test-case
    "lifting of maybe"
    (before
      (clear-vc!)
      (define-symbolic b boolean?)
      (check-true
        (sat?
          (verify
            (assert
              (just?
                (if b (just #t) nothing))))))
      (check-false
        (sat?
          (verify
            (assert
              (just?
                (if b (just #t) (just #t))))))))))

(define (checked-add a b)
  (define sum
    (bvadd a b))
  (define overflow
    (bvult sum b))
  (if overflow nothing (just sum)))

(define (checked-sub a b)
  (define overflow
    (bvult a b))
  (if overflow nothing (just (bvsub a b))))

(define (checked-mult w a b)
  ; a and b must be bitvectors of width w
  (define prod
    (bvmul a b))
  (define ew
    (* 2 w))
  (define eprod
    (bvmul
      (zero-extend a (bitvector ew))
      (zero-extend b (bitvector ew))))
  (define overflow
    (not
      (bveq (zero-extend prod (bitvector ew)) eprod)))
  (cond
    [overflow nothing]
    [else (just prod)]))

(define (checked-div w a b)
  (cond
    [(bveq b (bv 0 w)) nothing]
    [else (just (bvudiv a b))]))

(module+ test
  (test-case
    "concrete checked ops"
    (check-true (just? (checked-add (bv 1 32) (bv 1 32))))
    (check-false (just? (checked-add (bv -1 32) (bv 1 32))))
    (check-true (just? (checked-add (bv -1 32) (bv 0 32))))
    (check-false (just? (checked-add (bv -1 32) (bv -1 32))))
    (check-true (nothing? (checked-sub (bv 1 32) (bv 2 32))))
    (check-true (just? (checked-sub (bv 2 32) (bv 2 32))))
    (check-true (nothing? (checked-mult 32 (bv -1 32) (bv 2 32))))
    (check-true (just? (checked-mult 32 (bv 1 32) (bv 2 32)))))
  (test-case
    "monad operations"
    (check-equal?
      (do
        [x <- (pure 1)]
        (+ 1 x))
      2)
    (check-equal?
      (chain (λ (x) (+ 1 x)) (pure 1))
       2)
    (check-equal?
      (do
        [x <- nothing]
        (+ 1 x))
       nothing)
    (check-equal?
      (chain (λ (x) (+ 1 x)) nothing)
       nothing))
  (test-case
    "monad operations on symolic data"
    (before
      (clear-vc!)
      (define-symbolic x (bitvector 32))
      (define-symbolic b boolean?)
      (check-false
        (sat?
          (verify
            (do
              [x <- (if b (pure x) nothing)]
              (bvadd (bv 1 32) x)))))))
  (test-case
    "symbolic tests"
    (before
      (clear-vc!)
      (define-symbolic x y (bitvector 32))
      (check-true
        (sat?
          (verify
            (begin
              (assume (just? (checked-add x y)))
              (assert #f)))))
      (define x33 (zero-extend x (bitvector 33)))
      (define y33 (zero-extend y (bitvector 33)))
      (check-true
        (unsat?
          (verify
            (begin
              (assume (just? (checked-add x y)))
              (assert (bveq
                        (zero-extend (from-just #f (checked-add x y)) (bitvector 33))
                        (bvadd x33 y33))))))))))
