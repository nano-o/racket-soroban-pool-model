; #lang errortrace rosette
; #lang rosette
#lang racket
; #lang errortrace racket

(require
  (only-in rosette
           bv
           bitvector
           bveq
           bvudiv
           bvmul
           bvadd
           bvsub
           zero-extend
           bvlshr
           extract
           bvumin))

; This is a model of the Soroban liquidity pool.
; The goal is exhibit evidence that money cannot be stolen from the pool.

(require
  "checked-ops.rkt"
  struct-update)

(define w 4) ; bit width
(define dw (* 2 w)) ; double the bit width

; State of the pool
; We have the pool address, reserve amounts and the number of pool shares
(struct pool (addr reserve-a reserve-b total-shares) #:transparent)
(define-struct-updaters pool)
(define (pool/kw #:addr a #:reserve-a ra #:reserve-b rb #:total-shares ts)
  (pool a ra rb ts))
; Token-contract state: map from address to balance
(struct token (balance) #:transparent)
; Model state: consists of the state of the pool and of the three tokens involved
(struct state (pool ta tb ts) #:transparent)
(define-struct-updaters state)
(define (state/kw #:pool p #:token-a ta #:token-b tb #:token-s ts)
  (state p ta tb ts))

(define (burn t addr amount)
  (do
    [new-amount <- (checked-sub ((token-balance t) addr) amount)]
    (just
      (λ (a)
         (cond
           [(bveq a addr)
            new-amount]
           [else
            ((token-balance t) a)])))))

(define (mint t addr amount)
  (do
    [new-amount <- (checked-add ((token-balance t) addr) amount)]
    (just
      (token
        (λ (a)
           (cond
             [(bveq a addr)
              new-amount]
             [else
               ((token-balance t) a)]))))))

(define (transfer t from to amount)
  (do
    [new-amount-from <- (checked-sub ((token-balance t) from) amount)]
    [new-amount-to <- (checked-add ((token-balance t) to) amount)]
    (just
      (token
        (λ (a)
           (cond
             [(bveq a from)
              new-amount-from]
             [(bveq a to)
              new-amount-to]
             [else
               ((token-balance t) a)]))))))

; x*y/z without overflow in intermediate computation
; Returns `nothing` if the result does not fit in a word
; NOTE This uses double-width multiplication
(define (xy/z x y z)
  (define res
    (bvudiv
      (bvmul
        (zero-extend x (bitvector dw))
        (zero-extend y (bitvector dw)))
      (zero-extend z (bitvector dw))))
  (cond
    [(not ; doesn't fit in a word
       (bveq
         (bvlshr res (bv w dw))
         (bv 0 dw)))
     nothing]
    [else
      (just (extract (- w 1) 0 res))]))

(define (deposit s from)
  (define p (state-pool s))
  (define ta (state-ta s))
  (define tb (state-tb s))
  (define ts (state-ts s))
  (define addr
    (pool-addr p))
  (define balance-a
    ((token-balance ta) addr))
  (define balance-b
    ((token-balance tb) addr))
  (define total-shares
    (pool-total-shares p))
  (define new-total-shares
    (do
      [shares-a <- (xy/z balance-a total-shares (pool-reserve-a p))]
      [shares-b <- (xy/z balance-b total-shares (pool-reserve-b p))]
      (just
        (bvumin shares-a shares-b))))
  (define new-pool
    (do
      [new-total-shares <- new-total-shares]
      (just
        (pool
          addr
          balance-a
          balance-b
          new-total-shares))))
  (define shares-to-mint
    (do
      [new-total-shares <- new-total-shares]
      (just (bvsub new-total-shares total-shares)))) ; NOTE there's no need for checked-sub here
  (do
    [new-pool <- new-pool]
    [shares-to-mint <- shares-to-mint]
    [new-ts <- (mint ts from shares-to-mint)]
    (just (state new-pool ta tb new-ts))))

(define (total-supply t addrs)
  (for/fold
    ([sum (just (bv 0 w))])
    ([a addrs])
    (do
      [sum <- sum]
      (checked-add sum ((token-balance t) a)))))

(define (pool-invariant s users)
  (define addrs (cons (pool-addr (state-pool s)) users))
  (define ta (state-ta s))
  (define tb (state-tb s))
  (define ts (state-ts s))
  (and
    (or
      (just? (total-supply ta addrs))
      (begin0
        #f
        (displayln "total token-a supply overflow")))
    (or
      (just? (total-supply tb addrs))
      (begin0
        #f
        (displayln "total token-b supply overflow")))
    (and
      (or
        (just? (total-supply ts addrs))
        (begin0
          #f
          (displayln "total shares supply overflow")))
      (or
        (bveq
          (pool-total-shares (state-pool s))
          (from-just! (total-supply ts addrs)))
        (begin0
          #f
          (displayln "total shares not equal to total supply"))))
    (or
      (bveq
        (pool-reserve-a (state-pool s))
        ((token-balance ta) (pool-addr (state-pool s))))
      (begin0
        #f
        (displayln "reserve of token a not equal to balance")))
    (or
      (bveq
        (pool-reserve-b (state-pool s))
        ((token-balance tb) (pool-addr (state-pool s))))
      (begin0
        #f
        (displayln "reserve of token b not equal to balance")))))

  ; (define my-pool-addr
    ; (bv 0 w))
  ; (define user1-addr
    ; (bv 1 w))
  ; (define user2-addr
    ; (bv 2 w))
  ; (define s0
    ; (state/kw
      ; #:pool
      ; (pool/kw
        ; #:addr my-pool-addr
        ; #:reserve-a (bv 2 w)
        ; #:reserve-b (bv 4 w)
        ; #:total-shares (bv 2 w))
      ; ; user1 has 100 of each token a and b
      ; #:token-a
      ; (token
        ; (λ (addr)
           ; (cond
             ; [(equal? addr user1-addr) (bv 100 w)]
             ; [(equal? addr my-pool-addr) (bv 2 w)]
             ; [else (bv 0 w)])))
      ; #:token-b
      ; (token
        ; (λ (addr)
           ; (cond
             ; [(equal? addr user1-addr) (bv 100 w)]
             ; [(equal? addr my-pool-addr) (bv 4 w)]
             ; [else (bv 0 w)])))
      ; ; existing liquidity is owned by user2
      ; #:token-s (token (λ (addr) (if (equal? addr user2-addr) (bv 2 w) (bv 0 w))))))
  ; (define addrs (list my-pool-addr user1-addr user2-addr))

(module+ test
  (require rackunit)
  (define my-pool-addr
    (bv 0 w))
  (define user1-addr
    (bv 1 w))
  (define user2-addr
    (bv 2 w))
  (define s0
    (state/kw
      #:pool
      (pool/kw
        #:addr my-pool-addr
        #:reserve-a (bv 2 w)
        #:reserve-b (bv 4 w)
        #:total-shares (bv 2 w))
      ; user1 has 100 of each token a and b
      #:token-a
      (token
        (λ (addr)
           (cond
             [(equal? addr user1-addr) (bv 4 w)]
             [(equal? addr my-pool-addr) (bv 2 w)]
             [else (bv 0 w)])))
      #:token-b
      (token
        (λ (addr)
           (cond
             [(equal? addr user1-addr) (bv 4 w)]
             [(equal? addr my-pool-addr) (bv 4 w)]
             [else (bv 0 w)])))
      ; existing liquidity is owned by user2
      #:token-s (token (λ (addr) (if (equal? addr user2-addr) (bv 2 w) (bv 0 w))))))
  (define addrs (list my-pool-addr user1-addr user2-addr))
  (test-case
    "pool invariant test"
    (check-true (pool-invariant s0 addrs)))
  (test-case
    "deposit test"
    (do
      ; the user first transfers tokens to the pool
      [ta1 <- (transfer (state-ta s0) user1-addr my-pool-addr (bv 2 w))]
      (define s1 (state-ta-set s0 ta1))
      [tb2 <- (transfer (state-tb s1) user1-addr my-pool-addr (bv 4 w))]
      (define s2 (state-tb-set s1 tb2))
      ; then we call deposit
      [s3 <- (deposit s2 user1-addr)]
      [total-shares-supply <- (total-supply (state-ts s3) addrs)]
      (begin
        (check-equal?
          (pool-reserve-a (state-pool s3))
          (bv 4 w))
        (check-equal?
          (pool-reserve-b (state-pool s3))
          (bv 8 w))
        (check-equal?
          (pool-total-shares (state-pool s3))
          (bv 4 w))
        (check-true (pool-invariant s3 addrs))))))

(define (withdraw s to)
  (define p (state-pool s))
  (define ta (state-ta s))
  (define tb (state-tb s))
  (define ts (state-ts s))
  (define addr
    (pool-addr p))
  (define balance-a
    ((token-balance ta) addr))
  (define balance-b
    ((token-balance tb) addr))
  (define balance-shares
    ((token-balance tb) addr))
  (define out-a
    (xy/z balance-a balance-shares (pool-total-shares p)))
  (define out-b
    (xy/z balance-b balance-shares (pool-total-shares p)))
  (define new-total-shares
    (bvsub (pool-total-shares p) balance-shares)) ; NOTE no need for checked-sub here
  (define new-ts
    (burn ts addr balance-shares))
  (define new-ta
    (transfer ta addr to out-a))
  (define new-tb
    (transfer tb addr to out-b))
  (define new-pool
    (do
      [out-a <- out-a]
      [out-b <- out-b]
      (just
        (pool
          addr
          (bvsub balance-a out-a) ; NOTE no need for checked sub
          (bvsub balance-b out-b) ; NOTE no need for checked sub
          new-total-shares))))
  (do
    [new-pool <- new-pool]
    [new-ts <- new-ts]
    [new-ta <- new-ta]
    [new-tb <- new-tb]
    (just (state new-pool new-ta new-tb new-ts))))

; (module+ test
  ; (test-case
    ; "withdraw tests"
    ; ; TODO
    ; (define my-pool
      ; (amm (bv 1 w) (bv 4 w) (bv 2 w)))
    ; (check-equal?
      ; (withdraw my-pool (bv 1 w))
      ; (just (amm (bv 1 w) (bv 2 w) (bv 1 w))))
    ; (check-equal?
      ; (withdraw my-pool (bv -1 w))
      ; nothing)))

; ; TODO sequence of deposit and withdraws, not just deposits
; (define (deposit* p xys)
  ; (foldl
    ; (λ (xy maybe-p)
       ; (do
         ; [p <- maybe-p]
         ; (deposit p (car xy) (cdr xy))))
    ; (just p) ; init
    ; xys))

; (module+ test
  ; (define (add-liquidity*-then-remove f p xys)
    ; (define maybe-p-2
      ; (add-liquidity* f p xys)) ; list
    ; (do
      ; [p-2 <- maybe-p-2]
      ; (define delta-l (bvsub (amm-l p-2) (amm-l p)))
      ; (withdraw p-2 delta-l)))

  ; (test-case
    ; "add-liquidity*"
    ; (define my-pool
      ; (amm (bv 1 w) (bv 4 w) (bv 2 w)))
    ; (check-equal?
      ; (add-liquidity* add-liquidity my-pool (list (cons (bv 2 w) (bv 2 w)) (cons (bv 3 w) (bv 4 w))))
      ; (just (amm (bv 6 w) (bv 10 w) (bv 5 w))))
    ; (check-equal?
      ; (add-liquidity*-then-remove add-liquidity my-pool (list (cons (bv 2 w) (bv 2 w)) (cons (bv 3 w) (bv 4 w))))
      ; (just (amm (bv 3 w) (bv 4 w) (bv 2 w)))))

  ; (define-symbolic x y l delta-x-1 delta-x-2 delta-y-1 delta-y-2 (bitvector w))
  ; (define my-pool
    ; (amm x y l))
  ; (define xys
    ; (list (cons delta-x-1 delta-y-1) (cons delta-x-2 delta-y-2))) ; we're adding liquidity twice

  ; ; now we're going to check that, after adding liquidity multiple times, if we remove all the liquidity we added then the pool has at least as much funds as before.

  ; (test-case
    ; "trying to accumulate errors"
    ; (before
      ; (clear-vc!)
      ; (check-false
        ; (sat?
          ; (verify
            ; (begin
              ; (define p (add-liquidity*-then-remove add-liquidity my-pool xys))
              ; (assert
                ; (or
                  ; (nothing? p)
                  ; (and
                    ; (bvuge (amm-x (from-just! p)) (amm-x my-pool))
                    ; (bvuge (amm-y (from-just! p)) (amm-y my-pool)))))))))))
  ; (test-case
    ; "trying to accumulate errors; buggy version"
    ; (before
      ; (clear-vc!)
      ; (check-true
        ; (sat?
          ; (verify
            ; (begin
              ; (define p (add-liquidity*-then-remove add-liquidity-buggy my-pool xys))
              ; (assert
                ; (or
                  ; (nothing? p)
                  ; (and
                    ; (bvuge (amm-x (from-just! p)) (amm-x my-pool))
                    ; (bvuge (amm-y (from-just! p)) (amm-y my-pool))))))))))))
