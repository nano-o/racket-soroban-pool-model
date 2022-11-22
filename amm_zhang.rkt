#lang rosette

(require
  "checked-ops.rkt")

; the state of the amm: we have the amounts of the two tokens (x and y) and the number of liquidity tokens
(struct amm (x y l) #:transparent)

(define w 4) ; bit width
(define dw (* 2 w)) ; double the bit width

; adding liquidity
; we specify how much of token x to provide
; however, to maintain a constant product x*y, we also need to provide y tokens; that amount is calculated as a function of delta-x and of the current state of the pool.
; no fee is taken
(define (add-liquidity pool delta-x)
  ; token quantities in the pool must be non-zero
  (define x-next
    (checked-add (amm-x pool) delta-x))
  (define delta-y
    (delta (amm-x pool) delta-x (amm-y pool)))
  (define y-next
    (do
      [dy <- delta-y]
      [y+dy <- (checked-add (amm-y pool) dy)]
      (checked-add (bv 1 w) y+dy)))
  (define delta-l
    (delta (amm-x pool) delta-x (amm-l pool)))
  (define l-next
    (do
      [dl <- delta-l]
      (checked-add (amm-l pool) dl)))
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
  ; we double the bitwidth to avoid overflows and check in the end that the result fits in word-width bits
  (define delta-ext
    (bvudiv ; (* 2 word-width) bits
      (bvmul
        (zero-extend ref-token-delta (bitvector dw))
        (zero-extend reserve (bitvector dw)))
      (zero-extend ref-token-reserve (bitvector dw))))
  (cond
    [(bvugt ; can't fit in word-width bits
       delta-ext
       (zero-extend (bv -1 w) (bitvector dw)))
     nothing]
    [else (just (extract (- w 1) 0 delta-ext))]))

(module+ test
  (require rackunit)
  (test-case
    "add-liquidity"
    (define my-pool
      (amm (bv 1 w) (bv 4 w) (bv 2 w)))
    (check-equal?
      (add-liquidity my-pool (bv 1 w))
      (amm (bv 2 w) (bv 9 w) (bv 4 w)))
    (check-equal?
      (add-liquidity my-pool (bv -1 w))
      my-pool)))

(define (remove-liquidity pool delta-l)
  (define l-next
    (checked-sub (amm-l pool) delta-l))
  (define delta-x
    (delta (amm-l pool) delta-l (amm-x pool)))
  (define x-next
    (do
      [dx <- delta-x]
      (checked-sub (amm-x pool) dx)))
  (define delta-y
    (delta (amm-l pool) delta-l (amm-y pool)))
  (define y-next
    (do
      [dy <- delta-y]
      (checked-sub (amm-y pool) dy)))
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
      (amm (bv 1 w) (bv 4 w) (bv 2 w)))
    (check-equal?
      (remove-liquidity my-pool (bv 1 w))
      (amm (bv 1 w) (bv 2 w) (bv 1 w)))
    (check-equal?
      (remove-liquidity my-pool (bv -1 w))
      my-pool)))

(module+ test
  (test-case
    "trying to accumulate errors"
    (before
      (clear-vc!)
      (check-false
        (sat?
          (verify
            (begin
              (define-symbolic x y l delta-x-1 delta-x-2 (bitvector w))
              (define my-pool
                (amm x y l))
              (define dxs
                (list delta-x-1 delta-x-2))
              (define pool-2
                ; we deposit more than once and then withdraw all our liquidity; if we omit the +1 in the computation of y then the LP makes money for free.
                (foldr (λ (d p) (add-liquidity p d)) my-pool dxs))
              (define delta-l
                (bvsub (amm-l pool-2) (amm-l my-pool)))
              (define pool-3
                (remove-liquidity pool-2 delta-l))
              (assert
                (bvuge (amm-y pool-3) (amm-y my-pool))))))))))
