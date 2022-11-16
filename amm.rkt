#lang rosette

(require
  "checked-ops.rkt")

; the state of the amm: we have the amounts of the two tokens (x and y) and the number of liquidity tokens
(struct amm (x y l) #:transparent)

; NOTE we use 32-bit words by default

; adding liquidity
; we specify how much of token x to provide
; however, to maintain a constay product x*y, we also need to provide y tokens; that amount is calculated as a function of delta-x and of the current state of the pool.
; no fee is taken
(define (add-liquidity pool delta-x)
  ; TODO how is this done in core?
  ; TODO monad notation
  ; assumes token quantities in the pool are not 0
  (define x-next
    (checked-add (amm-x pool) delta-x))
  (define (delta pool-amount)
    ; we double the bitwidth to avoid overflows and check in the end that the result fits in 32 bits
    (define delta-64
      (bvudiv ; 64 bits
        (bvmul
          (zero-extend delta-x (bitvector 64))
          (zero-extend pool-amount (bitvector 64)))
        (zero-extend (amm-x pool) (bitvector 64))))
    (cond
      [(bvugt ; can't fit in 32 bits
         delta-64
         (zero-extend (bv -1 32) (bitvector 64)))
       nothing]
      [else (just (extract 31 0 delta-64))]))
  (define delta-y
    (delta (amm-y pool)))
  (define y-next
    (chain
      (λ (r) (checked-add (bv 1 32) r))
      (chain
        (λ (dy) (checked-add (amm-y pool) dy))
        delta-y)))
  (define delta-l
    (delta (amm-l pool)))
  (define l-next
    (chain
      (λ (delta-l) (checked-add (amm-l pool) delta-l))
      delta-l))
  ; next, map/m would be useful
  (cond
    [(or
       (nothing? x-next)
       (nothing? y-next)
       (nothing? l-next))
     ; transaction fails; don't update the pool state
     pool]
    [else (amm (from-just! x-next) (from-just! y-next) (from-just! l-next))]))

(define (add-liquidity-2 pool delta-x)
  (define x-next
    (checked-add (amm-x pool) delta-x))
  (define y-next
    (chain
      (λ (r) (checked-add (bv 1 32) r))
      (chain
        (λ (delta-y) (checked-add (amm-y pool) delta-y))
        (chain
          (λ (n)
             (checked-div 32 n (amm-x pool)))
          (checked-mult 32 delta-x (amm-y pool))))))
  (define l-next
    (chain
      (λ (delta-l) (checked-add (amm-l pool) delta-l))
      (chain
        (λ (n)
           (checked-div 32 n (amm-x pool)))
        (checked-mult 32 delta-x (amm-l pool)))))
  ; next, map/m would be useful
  (cond
    [(or
       (nothing? x-next)
       (nothing? y-next)
       (nothing? l-next))
     ; transaction fails; don't update the pool state
     pool]
    [else (amm (from-just! x-next) (from-just! y-next) (from-just! l-next))]))

(module+ test
  (require rackunit)
  (define my-pool
    (amm (bv 1 32) (bv 4 32) (bv 2 32)))
  (test-case
    "add-liquidity"
    (check-equal?
      (add-liquidity my-pool (bv 1 32))
      (amm (bv #x00000002 32) (bv #x00000009 32) (bv #x00000004 32)))
    (check-equal?
      (add-liquidity my-pool (bv -1 32))
      my-pool)))

; TODO introduce a bug (e.g. don't add 1 to y-next) and see if Rosette finds an example where we make free money; for that we need to model withdrawing liquidity.
