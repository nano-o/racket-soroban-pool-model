#lang rosette

(require
  "checked-ops.rkt")

; the state of the amm: we have the amounts of the two tokens (x and y) and the number of liquidity tokens
(struct amm (x y l) #:transparent)

(define w 4) ; bit width
(define dw (* 2 w)) ; double the bit width

; ab/c without overflow in intermediate computation
(define (ab-div-c a b c)
  (define res
    (bvudiv
      (bvmul
        (zero-extend a (bitvector dw))
        (zero-extend b (bitvector dw)))
      (zero-extend c (bitvector dw))))
  (cond
    [(bvugt
       res
       (zero-extend (bv -1 w) (bitvector dw)))  ; doesn't fit in a word
     nothing]
    [else
      (just (extract (- w 1) 0 res))]))

; we send delta-x and delta-y to the pool and get liquidity shares in exchange
(define (add-liquidity pool delta-x delta-y)
  ; token quantities in the pool must be non-zero
  (define maybe-shares-x
    (ab-div-c delta-x (amm-l pool) (amm-x pool)))
  (define maybe-shares-y
    (ab-div-c delta-y (amm-l pool) (amm-y pool)))
  (define maybe-l
    (do
      [sx <- maybe-shares-x]
      [sy <- maybe-shares-y]
      (define delta-l (bvumin sx sy))
      (checked-add (amm-l pool) delta-l)))
  (do
    [x <- (checked-add (amm-x pool) delta-x)] [y <- (checked-add (amm-y pool) delta-y)]
    [l <- maybe-l] ; here it'd be nice to use map and apply (Haskell <*> and <$>), but we'd need to curry bvumin, which Rosette does not support
    (just (amm x y l))))

; buggy version of the Soroban pool contract
(define (add-liquidity-buggy pool delta-x delta-y)
  ; token quantities in the pool must be non-zero
  (define maybe-shares-x
    (do
      [x <- (checked-add (amm-x pool) delta-x)]
      (ab-div-c x (amm-l pool) (amm-x pool))))
  (define maybe-shares-y
    (do
      [y <- (checked-add (amm-y pool) delta-y)]
      (ab-div-c y (amm-l pool) (amm-y pool))))
  (define maybe-l
    (do
      [sx <- maybe-shares-x]
      [sy <- maybe-shares-y]
      (define delta-l (bvumin sx sy))
      (checked-add (amm-l pool) delta-l)))
  (do
    [x <- (checked-add (amm-x pool) delta-x)]
    [y <- (checked-add (amm-y pool) delta-y)]
    [l <- maybe-l] ; here it'd be nice to use map and apply (Haskell <*> and <$>), but we'd need to curry bvumin, which Rosette does not support
    (just (amm x y l))))


(module+ test
  (require rackunit)
  (test-case
    "add-liquidity"
    (define my-pool
      (amm (bv 1 w) (bv 4 w) (bv 2 w)))
    (check-equal?
      (add-liquidity my-pool (bv 1 w) (bv 5 w))
      (just (amm (bv 2 w) (bv 9 w) (bv 4 w))))
    (check-equal?
      (add-liquidity my-pool (bv 1 w) (bv 4 w))
      (just (amm (bv 2 w) (bv 8 w) (bv 4 w))))
    (check-equal?
      (add-liquidity my-pool (bv -1 w) (bv 1 w))
      nothing)))

(define (withdraw pool delta-l)
  (define maybe-x
    (do
      [delta-x <- (ab-div-c delta-l (amm-x pool) (amm-l pool))]
      (checked-sub (amm-x pool) delta-x)))
  (define maybe-y
    (do
      [delta-y <- (ab-div-c delta-l (amm-y pool) (amm-l pool))]
      (checked-sub (amm-y pool) delta-y)))
  (do
    [x <- maybe-x]
    [y <- maybe-y]
    [l <- (checked-sub (amm-l pool) delta-l)]
    (just (amm x y l))))

(module+ test
  (test-case
    "remove-liquidity"
    (define my-pool
      (amm (bv 1 w) (bv 4 w) (bv 2 w)))
    (check-equal?
      (withdraw my-pool (bv 1 w))
      (just (amm (bv 1 w) (bv 2 w) (bv 1 w))))
    (check-equal?
      (withdraw my-pool (bv -1 w))
      nothing)))

(define (add-liquidity* f p xys)
  ; f is the add-liquidity function
  (foldl
    (λ (xy maybe-p)
       (do
         [p <- maybe-p]
         (f p (car xy) (cdr xy))))
    (just p) ; init
    xys))

(module+ test
  (define (add-liquidity*-then-remove f p xys)
    (define maybe-p-2
      (add-liquidity* f p xys)) ; list
    (do
      [p-2 <- maybe-p-2]
      (define delta-l (bvsub (amm-l p-2) (amm-l p)))
      (withdraw p-2 delta-l)))

  (test-case
    "add-liquidity*"
    (define my-pool
      (amm (bv 1 w) (bv 4 w) (bv 2 w)))
    (check-equal?
      (add-liquidity* add-liquidity my-pool (list (cons (bv 2 w) (bv 2 w)) (cons (bv 3 w) (bv 4 w))))
      (just (amm (bv 6 w) (bv 10 w) (bv 5 w))))
    (check-equal?
      (add-liquidity*-then-remove add-liquidity my-pool (list (cons (bv 2 w) (bv 2 w)) (cons (bv 3 w) (bv 4 w))))
      (just (amm (bv 3 w) (bv 4 w) (bv 2 w)))))

  (define-symbolic x y l delta-x-1 delta-x-2 delta-y-1 delta-y-2 (bitvector w))
  (define my-pool
    (amm x y l))
  (define xys
    (list (cons delta-x-1 delta-y-1) (cons delta-x-2 delta-y-2))) ; we're adding liquidity twice

  ; now we're going to check that, after adding liquidity multiple times, if we remove all the liquidity we added then the pool has at least as much funds as before.

  (test-case
    "trying to accumulate errors"
    (before
      (clear-vc!)
      (check-false
        (sat?
          (verify
            (begin
              (define p (add-liquidity*-then-remove add-liquidity my-pool xys))
              (assert
                (or
                  (nothing? p)
                  (and
                    (bvuge (amm-x (from-just! p)) (amm-x my-pool))
                    (bvuge (amm-y (from-just! p)) (amm-y my-pool)))))))))))
  (test-case
    "trying to accumulate errors; buggy version"
    (before
      (clear-vc!)
      (check-true
        (sat?
          (verify
            (begin
              (define p (add-liquidity*-then-remove add-liquidity-buggy my-pool xys))
              (assert
                (or
                  (nothing? p)
                  (and
                    (bvuge (amm-x (from-just! p)) (amm-x my-pool))
                    (bvuge (amm-y (from-just! p)) (amm-y my-pool))))))))))))
