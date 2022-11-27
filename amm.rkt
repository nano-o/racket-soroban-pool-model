#lang rosette

; This is a model of the Soroban liquidity pool.
; The goal is exhibit evidence that money cannot be stolen from the pool.

; Checking the "no money lost" property is too slow for a word width of more than 6 bits.
; TODO what about an inductive invariant?

(require
  "checked-ops.rkt"
  rosette/lib/destruct
  rosette/solver/smt/boolector
  rosette/solver/smt/cvc4
  rosette/solver/smt/z3
  struct-update)

(define w (make-parameter 8)) ; bit width
(define (dw) (+ (w) (w))) ; double the bit width; has to be a function in order to depend on the dynamic value of the parameter w

(define debug (make-parameter #f))

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
      ; failure to compute the total supply (because of overflow) does not count as a failure of the invariant
      [total-supply-a <- (total-supply ta addrs)]
      [total-supply-b <- (total-supply tb addrs)]
      [total-supply-s <- (total-supply ts addrs)]
      (just
        (and
          (or
            (bveq
              (pool-total-shares (state-pool s))
              (from-just! (total-supply ts addrs)))
            (and (debug) (not (displayln "~a total shares not equal to total supply" debug))))
          (or
            (bveq
              (pool-reserve-a (state-pool s))
              ((token-balance ta) (pool-addr (state-pool s))))
            (and (debug) (not (displayln "reserve of token a not equal to balance"))))
          (or
            (bveq
              (pool-reserve-b (state-pool s))
              ((token-balance tb) (pool-addr (state-pool s))))
            (and (debug) (not (displayln "reserve of token b not equal to balance"))))))))
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
        (zero-extend x (bitvector (dw)))
        (zero-extend y (bitvector (dw))))
      (zero-extend z (bitvector (dw)))))
  (cond
    [(not ; doesn't fit in a word
       (bveq
         (bvlshr res (bv (w) (dw)))
         (bv 0 (dw))))
     nothing]
    [else
      (just (extract (- (w) 1) 0 res))]))

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
  (do
    [shares-a <- (xy/z balance-a total-shares (pool-reserve-a p))]
    [shares-b <- (xy/z balance-b total-shares (pool-reserve-b p))]
    (define new-total-shares
      (bvumin shares-a shares-b))
    (define new-pool
      (pool
        addr
        balance-a
        balance-b
        new-total-shares))
    (define shares-to-mint
      (bvsub new-total-shares total-shares))
    [new-ts <- (mint ts from shares-to-mint)]
    (just (state new-pool ta tb new-ts))))

(define (total-supply t addrs)
  (define (proc a maybe-sum)
    (do
      [sum <- maybe-sum]
      (checked-add sum ((token-balance t) a))))
  (foldl proc (just (bv 0 (w))) addrs))

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
  (define new-total-shares
    (bvsub (pool-total-shares p) balance-shares)) ; NOTE no need for checked-sub here
  (do
    [out-a <- (xy/z balance-a balance-shares (pool-total-shares p))]
    [out-b <- (xy/z balance-b balance-shares (pool-total-shares p))]
    [new-ta <- (transfer ta addr to out-a)]
    [new-tb <- (transfer tb addr to out-b)]
    [new-ts <- (burn ts addr balance-shares)]
    (define new-pool
      (pool
        addr
        (bvsub balance-a out-a) ; NOTE no need for checked sub
        (bvsub balance-b out-b) ; NOTE no need for checked sub
        new-total-shares))
    (just (state new-pool new-ta new-tb new-ts))))

; user pool operations

(struct deposit-op (user amount-a amount-b))
(struct withdraw-op (user amount))

(define (execute-op s op)
  (destruct op
    [(deposit-op user a b)
     (do
       [ta <- (transfer (state-ta s) user (pool-addr (state-pool s)) a)]
       [tb <- (transfer (state-tb s) user (pool-addr (state-pool s)) b)]
       (define s1 (state-tb-set (state-ta-set s ta) tb))
       (deposit s1 user))]
    [(withdraw-op user shares)
     (do
       [ts <- (transfer (state-ts s) user (pool-addr (state-pool s)) shares)]
       (define s1 (state-ts-set s ts))
       (withdraw s1 user))]))

(define (execute-op* s ops)
  (define (proc op maybe-s)
    (do
      [s <- maybe-s]
      (execute-op s op)))
  (foldl proc (just s) ops))

(module+ test
  (require rackunit)

  ; we will run tests with two users user-1 and user-2
  (define my-pool-addr ; pool has address 0
    (bv 0 (w)))
  (define user-1-addr
    (bv 1 (w)))
  (define user-2-addr
    (bv 2 (w)))

  (define (make-initial-state
            #:reserve-a ra
            #:reserve-b rb
            #:total-shares ts
            #:user-1-a u1a
            #:user-1-b u1b)
    (state/kw
      #:pool
      (pool/kw
        #:addr my-pool-addr
        #:reserve-a ra
        #:reserve-b rb
        #:total-shares ts)
      ; user-1 has 2 of each token a and b
      #:token-a
      (token
        (λ (addr)
           (cond
             [(equal? addr user-1-addr) u1a]
             [(equal? addr my-pool-addr) ra]
             [else (bv 0 (w))])))
      #:token-b
      (token
        (λ (addr)
           (cond
             [(equal? addr user-1-addr) u1b]
             [(equal? addr my-pool-addr) rb]
             [else (bv 0 (w))])))
      ; existing liquidity is owned by user-2
      #:token-s (token (λ (addr) (if (equal? addr user-2-addr) ts (bv 0 (w)))))))

  (define s0
    (make-initial-state
      #:reserve-a (bv 1 (w))
      #:reserve-b (bv 2 (w))
      #:total-shares (bv 1 (w))
      #:user-1-a (bv 2 (w))
      #:user-1-b (bv 2 (w))))

  (define addrs (list my-pool-addr user-1-addr user-2-addr))

  (test-case
    "s0 satisfies the pool invariant"
    (check-true (pool-invariant s0 addrs)))

  (test-case
    "basic operation-execution scenario"
    (define ops
      (list
        (deposit-op user-1-addr (bv 2 (w)) (bv 2 (w)))
        (withdraw-op user-1-addr (bv 1 (w)))))
    (do
      [s1 <- (execute-op* s0 ops)]
      (begin
        (check-equal? ((token-balance (state-ts s1)) user-1-addr) (bv 0 (w)))
        (check-equal? ((token-balance (state-ta s1)) user-1-addr) (bv 1 (w)))
        (check-equal? ((token-balance (state-tb s1)) user-1-addr) (bv 2 (w)))
        (check-equal? ((token-balance (state-ta s1)) my-pool-addr) (bv 2 (w)))
        (check-equal? (pool-total-shares (state-pool s1)) (bv 1 (w)))
        (check-equal? ((token-balance (state-ts s1)) user-2-addr) (bv 1 (w)))
        (check-true (pool-invariant s1 addrs)))))

  ; deposit, deposit, and withdraw:
  (define (make-d-d-w a-1 b-1 a-2 b-2 s-1)
    (list
      (deposit-op user-1-addr a-1 b-1)
      (deposit-op user-1-addr a-2 b-2)
      (withdraw-op user-1-addr s-1)))

  (test-case
    "invariant preservation (symbolic test)"
    (before
      (clear-vc!)
      (parameterize
        [(w 64)
         (debug #f)
         (current-solver
           (boolector
             #:logic "QF_BV"))]
        (define-symbolic ra rb ts u1a u1b (bitvector (w)))
        (define sym-state
          (make-initial-state
            #:reserve-a ra
            #:reserve-b rb
            #:total-shares ts
            #:user-1-a u1a
            #:user-1-b u1b))
        (define-symbolic a-1 b-1 a-2 b-2 s-1 (bitvector (w)))
        (define sym-ops
          (make-d-d-w a-1 b-1 a-2 b-2 s-1))
        (define result
          (verify
            (do
              [s1 <- (execute-op* sym-state sym-ops)]
              (assert
                (pool-invariant s1 addrs)))))
        #;
        (displayln
          (pretty-format (model (complete-solution result (list ra rb ts u1a u1b a-1 b-1 a-2 b-2 s-1)))))
        (check-true
          (unsat? result)))))

  (test-case
    "no money lost (symbolic test)"
    (before
      (clear-vc!)
      (parameterize
        [(w 4) ; this test takes too long for more than 4 bits...
         (current-solver
           (boolector
             #:logic "QF_BV"))]
        (define-symbolic ra rb ts u1a u1b (bitvector (w)))
        (define sym-state
          (make-initial-state
            #:reserve-a ra
            #:reserve-b rb
            #:total-shares ts
            #:user-1-a u1a
            #:user-1-b u1b))
        (define-symbolic a-1 b-1 a-2 b-2 s-1 (bitvector (w)))
        (define sym-ops
          (make-d-d-w a-1 b-1 a-2 b-2 s-1))
        (check-true
          (unsat?
            (verify
              (do
                [s1 <- (execute-op* sym-state sym-ops)]
                (assert
                  (and
                    (bvuge
                      ((token-balance (state-ta s1)) my-pool-addr)
                      ((token-balance (state-ta sym-state)) my-pool-addr))
                    (bvuge
                      ((token-balance (state-tb s1)) my-pool-addr)
                      ((token-balance (state-tb sym-state)) my-pool-addr))))))))))))
