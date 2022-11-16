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
  ; TODO monad notation
  ; token quantities in the pool must be non-zero
  (define x-next
    (checked-add (amm-x pool) delta-x))
  (define delta-y
    (delta (amm-x pool) delta-x (amm-y pool)))
  (define y-next
    (chain
      (λ (r) (checked-add (bv 1 32) r))
      (chain
        (λ (dy) (checked-add (amm-y pool) dy))
        delta-y)))
  (define delta-l
    (delta (amm-x pool) delta-x (amm-l pool)))
  (define l-next
    (chain
      (λ (delta-l) (checked-add (amm-l pool) delta-l))
      delta-l))
  ; TODO next, map/m would be useful
  (cond
    [(or
       (nothing? x-next)
       (nothing? y-next)
       (nothing? l-next))
     ; transaction fails; don't update the pool state
     pool]
    [else (amm (from-just! x-next) (from-just! y-next) (from-just! l-next))]))

(define (delta ref-token-reserve ref-token-delta reserve)
  ; we double the bitwidth to avoid overflows and check in the end that the result fits in 32 bits
  ; TODO could be a macro where we just give the field name
  (define delta-64
    (bvudiv ; 64 bits
      (bvmul
        (zero-extend ref-token-delta (bitvector 64))
        (zero-extend reserve (bitvector 64)))
      (zero-extend ref-token-reserve (bitvector 64))))
  (cond
    [(bvugt ; can't fit in 32 bits
       delta-64
       (zero-extend (bv -1 32) (bitvector 64)))
     nothing]
    [else (just (extract 31 0 delta-64))]))

(module+ test
  (require rackunit)
  (test-case
    "add-liquidity"
    (define my-pool
      (amm (bv 1 32) (bv 4 32) (bv 2 32)))
    (check-equal?
      (add-liquidity my-pool (bv 1 32))
      (amm (bv #x00000002 32) (bv #x00000009 32) (bv #x00000004 32)))
    (check-equal?
      (add-liquidity my-pool (bv -1 32))
      my-pool)))

(define (remove-liquidity pool delta-l)
  (define l-next
    (checked-sub (amm-l pool) delta-l))
  (define delta-x
    (delta (amm-l pool) delta-l (amm-x pool)))
  (define x-next
    (chain
      (λ (delta-x) (checked-sub (amm-x pool) delta-x))
      delta-x))
  (define delta-y
    (delta (amm-l pool) delta-l (amm-y pool)))
  (define y-next
    (chain
      (λ (delta-y) (checked-sub (amm-y pool) delta-y))
      delta-y))
  ; TODO next, map/m would be useful
  (cond
    [(or
       (nothing? x-next)
       (nothing? y-next)
       (nothing? l-next))
     ; transaction fails; don't update the pool state
     pool]
    [else (amm (from-just! x-next) (from-just! y-next) (from-just! l-next))]))

(module+ test
  (test-case
    "remove-liquidity"
    (define my-pool
      (amm (bv 1 32) (bv 4 32) (bv 2 32)))
    (check-equal?
      (remove-liquidity my-pool (bv 1 32))
      (amm (bv #x00000001 32) (bv #x00000002 32) (bv 1 32)))
    (check-equal?
      (remove-liquidity my-pool (bv -1 32))
      my-pool)))

; TODO introduce a bug (e.g. don't add 1 to y-next) and see if Rosette finds an example where we make free money; for that we need to model withdrawing liquidity.

(module+ test
  (test-case
    "monad operations on symolic data"
    (before
      (clear-vc!)
      (define-symbolic x y l delta-x (bitvector 32))
      (check-false
        (sat?
          (verify
            (begin
              (define my-pool
                (amm x y l))
              (define my-pool-2
                (add-liquidity my-pool delta-x))
              (define delta-l
                (bvsub (amm-l my-pool-2) (amm-l my-pool)))
              (define my-pool-3
                (remove-liquidity my-pool-2 delta-l))
              (assert (bveq (amm-l my-pool-3) (amm-l my-pool))))))))))

