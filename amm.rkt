; #lang errortrace rosette
; #lang rosette/safe
#lang rosette
; #lang racket
; #lang errortrace racket
; (require racket/trace)

(require
  #;(only-in rosette
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
           bvumin)
  (only-in rosette/lib/destruct
           destruct))

; This is a model of the Soroban liquidity pool.
; The goal is exhibit evidence that money cannot be stolen from the pool.

(require
  "checked-ops.rkt"
  struct-update)

(define w 6) ; bit width
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

(define (pool-invariant s users)
  (define addrs (cons (pool-addr (state-pool s)) users))
  (define ta (state-ta s))
  (define tb (state-tb s))
  (define ts (state-ts s))
  (define try-inv
    (do
      ; failre to compute the total supply (because of overflow) does not count as a failure of the invariant
      [total-supply-a <- (total-supply ta addrs)]
      [total-supply-b <- (total-supply tb addrs)]
      [total-supply-s <- (total-supply ts addrs)]
      (just
        (and
          (or
            (bveq
              (pool-total-shares (state-pool s))
              (from-just! (total-supply ts addrs)))
            (not (displayln "total shares not equal to total supply")))
          (or
            (bveq
              (pool-reserve-a (state-pool s))
              ((token-balance ta) (pool-addr (state-pool s))))
            (not (displayln "reserve of token a not equal to balance")))
          (or
            (bveq
              (pool-reserve-b (state-pool s))
              ((token-balance tb) (pool-addr (state-pool s))))
            (not (displayln "reserve of token b not equal to balance")))))))
  (or (nothing? try-inv) (from-just! try-inv)))

(define (burn t addr amount)
  (do
    [new-amount <- (checked-sub ((token-balance t) addr) amount)]
    (just
      (token
        (λ (a)
           (cond
             [(bveq a addr)
              new-amount]
             [else
               ((token-balance t) a)]))))))

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
; rounds the division down
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
  (foldl
    (λ (a sum)
       (do
         [sum <- sum]
         (checked-add sum ((token-balance t) a))))
    (just (bv 0 w))
    addrs))

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
    ((token-balance ts) addr))
  (define out-a
    (xy/z balance-a balance-shares (pool-total-shares p)))
  (define out-b
    (xy/z balance-b balance-shares (pool-total-shares p)))
  (define new-total-shares
    (bvsub (pool-total-shares p) balance-shares)) ; NOTE no need for checked-sub here
  (define new-ts
    (burn ts addr balance-shares))
  (define new-ta
    (do
      [out-a <- out-a]
      (transfer ta addr to out-a)))
  (define new-tb
    (do
      [out-b <- out-b]
      (transfer tb addr to out-b)))
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

  (define s3
    (do
      ; the user first transfers tokens to the pool
      [ta1 <- (transfer (state-ta s0) user1-addr my-pool-addr (bv 2 w))]
      (define s1 (state-ta-set s0 ta1))
      [tb2 <- (transfer (state-tb s1) user1-addr my-pool-addr (bv 4 w))]
      (define s2 (state-tb-set s1 tb2))
      ; then we call deposit
      (deposit s2 user1-addr)))

  (test-case
    "deposit test"
    (check-true (or (just? s3) (not (displayln "failed to compute s3"))))
    (do
      [s3 <- s3]
      (begin
        (check-true (pool-invariant s3 addrs))
        (check-equal?
          (pool-reserve-a (state-pool s3))
          (bv 4 w))
        (check-equal?
          (pool-reserve-b (state-pool s3))
          (bv 8 w))
        (check-equal?
          (pool-total-shares (state-pool s3))
          (bv 4 w))
        (check-equal?
          ((token-balance (state-ts s3)) user1-addr)
          (bv 2 w)))))

  (define s4
    (do
      [s3 <- s3]
      ; the user first transfers shares to the pool
      [ts1 <- (transfer (state-ts s3) user1-addr my-pool-addr (bv 1 w))]
      (define s4 (state-ts-set s3 ts1))
      ; then we call withdraw
      (withdraw s4 user1-addr)))

  (test-case
    "withdraw test"
    (check-true (or (just? s4) (not (displayln "failed to compute s4"))))
    (do
      [s4 <- s4]
      (begin
        (check-true (pool-invariant s4 addrs))
        (check-equal?
          (pool-reserve-a (state-pool s4))
          (bv 3 w))
        (check-equal?
          (pool-reserve-b (state-pool s4))
          (bv 6 w))
        (check-equal?
          (pool-total-shares (state-pool s4))
          (bv 3 w))))))

(struct deposit-op (amount-a amount-b))
(struct withdraw-op (amount))

(define (execute-op s user op)
  (destruct op
    [(deposit-op a b)
     (do
       [ta <- (transfer (state-ta s) user (pool-addr (state-pool s)) a)]
       [tb <- (transfer (state-tb s) user (pool-addr (state-pool s)) b)]
       (define s1 (state-tb-set (state-ta-set s ta) tb))
       (deposit s1 user))]
    [(withdraw-op shares)
     (do
       [ts <- (transfer (state-ts s) user (pool-addr (state-pool s)) shares)]
       (define s1 (state-ts-set s ts))
       (withdraw s1 user))]))

(define (execute-op* s user ops)
  (foldl
    (λ (op maybe-s)
       (do
         [s <- maybe-s]
         (execute-op s user op)))
    (just s) ; init
    ops))

(module+ test
  (test-case
    "execute-op* test"
    (define ops
      (list
        (deposit-op (bv 2 w) (bv 4 w))
        (withdraw-op (bv 1 w))))
    (do
      [s1 <- (execute-op* s0 user1-addr ops)]
      (check-true (pool-invariant s1 addrs)))))

(module+ test
  (define-symbolic u1a0 u1b0 ra0 rb0 ts0 a-1 b-1 a-2 b-2 s-1 (bitvector w))
  (define sym-state
    (state/kw
      #:pool
      (pool/kw
        #:addr my-pool-addr
        #:reserve-a ra0
        #:reserve-b rb0
        #:total-shares ts0)
      #:token-a
      (token
        (λ (addr)
           (cond
             [(equal? addr user1-addr)
              u1a0]
             [(equal? addr my-pool-addr)
              ra0]
             [else (bv 0 w)])))
      #:token-b
      (token
        (λ (addr)
           (cond
             [(equal? addr user1-addr)
              u1b0]
             [(equal? addr my-pool-addr)
              rb0]
             [else (bv 0 w)])))
      #:token-s
      (token
        (λ (addr)
           (cond
             [(equal? addr user2-addr) ; user2 has all the initial shares
              ts0]
             [else (bv 0 w)])))))
  ; symbolic operations:
  (define d-1
    (deposit-op a-1 b-1))
  (define d-2
    (deposit-op a-2 b-2))
  (define w-1
    (withdraw-op s-1))
  (define sym-ops
    ; NOTE it seems that including withdraw slows down z3 a lot
    (list d-1 w-1 d-2))

  (test-case
    "invariant preservation (symbolic test)"
    (before
      (clear-vc!)
      (check-true
        (unsat?
          (verify
            (begin
              #; ; does not seem to help
              (assume
                (and
                  (bvugt ((token-balance (state-ta sym-state)) my-pool-addr) (bv 0 w))
                  (bvugt ((token-balance (state-tb sym-state)) my-pool-addr) (bv 0 w))
                  (bvugt (pool-total-shares (state-pool sym-state)) (bv 0 w))))
              (do
                [s1 <- (execute-op* sym-state user1-addr sym-ops)]
                (assert
                  (pool-invariant s1 addrs)))))))))

  (test-case
    "no money lost (symbolic test)"
    ; takes 1 minutes with w=6
    (before
      (clear-vc!)
      (check-true
        (unsat?
          (verify
            (do
              [s1 <- (execute-op* sym-state user1-addr sym-ops)]
              (assert
                (and
                  (bvuge
                    ((token-balance (state-ta s1)) my-pool-addr)
                    ((token-balance (state-ta sym-state)) my-pool-addr))
                  (bvuge
                    ((token-balance (state-tb s1)) my-pool-addr)
                    ((token-balance (state-tb sym-state)) my-pool-addr))))))))))

  (test-case
    "invariant preservation; concrete version"
    (define-values (u1a0 u1b0 ra0 rb0 ts0 a-1 b-1)
      (values (bv 0 w) (bv 0 w) (bv #b11111 w) (bv #b10111 w) (bv 0 w) (bv 0 w) (bv 0 w)))
    (define d-1
      (deposit-op a-1 b-1))
    (define conc-ops
      (list d-1))
    (define conc-state
      (state/kw
        #:pool
        (pool/kw
          #:addr my-pool-addr
          #:reserve-a ra0
          #:reserve-b rb0
          #:total-shares ts0)
        #:token-a
        (token
          (λ (addr)
             (cond
               [(equal? addr user1-addr)
                u1a0]
               [(equal? addr my-pool-addr)
                ra0]
               [else (bv 0 w)])))
        #:token-b
        (token
          (λ (addr)
             (cond
               [(equal? addr user1-addr)
                u1b0]
               [(equal? addr my-pool-addr)
                rb0]
               [else (bv 0 w)])))
        #:token-s
        (token
          (λ (addr)
             (cond
               [(equal? addr user2-addr) ; user2 has all the initial shares
                ts0]
               [else (bv 0 w)])))))
    (do
      [s1 <- (execute-op* conc-state user1-addr conc-ops)]
      (check-true
        (pool-invariant s1 addrs))))

  (test-case
    "no money lost; concrete version"
    (define-values (u1a0 u1b0 ra0 rb0 ts0 a-1 b-1)
      (values (bv 0 w) (bv 0 w) (bv #b11111 w) (bv #b00011 w) (bv #b00010 w) (bv 0 w) (bv 0 w)))
    (define d-1
      (deposit-op a-1 b-1))
    (define conc-ops
      (list d-1))
    (define conc-state
      (state/kw
        #:pool
        (pool/kw
          #:addr my-pool-addr
          #:reserve-a ra0
          #:reserve-b rb0
          #:total-shares ts0)
        #:token-a
        (token
          (λ (addr)
             (cond
               [(equal? addr user1-addr)
                u1a0]
               [(equal? addr my-pool-addr)
                ra0]
               [else (bv 0 w)])))
        #:token-b
        (token
          (λ (addr)
             (cond
               [(equal? addr user1-addr)
                u1b0]
               [(equal? addr my-pool-addr)
                rb0]
               [else (bv 0 w)])))
        #:token-s
        (token
          (λ (addr)
             (cond
               [(equal? addr user2-addr) ; user2 has all the initial shares
                ts0]
               [else (bv 0 w)])))))
    (do
      [s1 <- (execute-op* conc-state user1-addr conc-ops)]
      (check-true
        (and
          (bvuge
            ((token-balance (state-ta s1)) my-pool-addr)
            ((token-balance (state-ta conc-state)) my-pool-addr))
          (bvuge
            ((token-balance (state-tb s1)) my-pool-addr)
            ((token-balance (state-tb conc-state)) my-pool-addr)))))))
