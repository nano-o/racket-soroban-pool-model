#include "seahorn/seahorn.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "sys/param.h"

/*
 * We implement a simple model of an AMM and try verifying some properties with Seahorn.
 */

// to set something to a non-deterministic value:
extern uint32_t nd();

// state of the liquidity pool:
typedef struct {
    uint32_t ra; // reserve of a
    uint32_t rb; // reserve of b
    uint32_t s; // total number of shares
} pool_t;

// token struct tracking the balances of a user and the pool
typedef struct {
    uint32_t pool;
    uint32_t user;
} token_t;

// the state of the system:
pool_t pool;
token_t ta;
token_t tb;
token_t ts;

uint32_t xy_over_z(uint32_t x, uint32_t y, uint32_t z) {
    uint64_t result = ((uint64_t)x * (uint64_t)y)/((uint64_t) z);
    if ((result>>32) != 0) { // overflow
        exit(1);
    }
    else {
        return (uint32_t)result;
    }
}

// the deposit function of the pool contract
void deposit() {
    // the user has already sent funds to the pool (in the token contracts ta and tb)
    printf("user sent %x token a\n", ta.pool - pool.ra);
    printf("user sent %x token b\n", tb.pool - pool.rb);
    uint32_t shares_a = xy_over_z(ta.pool, pool.s, pool.ra);
    printf("shares_a is %x\n", shares_a);
    uint32_t shares_b = xy_over_z(tb.pool, pool.s, pool.rb);
    printf("shares_b is %x\n", shares_b);
    uint32_t new_total_shares = MIN(shares_a, shares_b);
    printf("new_total_shares is %x\n", new_total_shares);
    uint32_t new_user_shares = new_total_shares - pool.s;
    printf("new_user_shares is %x\n", new_user_shares);
    // update pool reserves:
    pool.ra = ta.pool;
    pool.rb = tb.pool;
    // send shares to user:
    uint32_t shares_to_mint = new_total_shares - pool.s; // no overflow possible
    printf("shares_to_mint is %x\n", shares_to_mint);
    uint32_t total_user_shares = ts.user + shares_to_mint;
    if (total_user_shares < ts.user) {
        exit(1); // overflow
    };
    ts.user = total_user_shares;
    // update total pool shares:
    pool.s = new_total_shares;
}

void withdraw() {
    // the user has already sent shares to the pool
    uint32_t new_total_shares = pool.s - ts.pool;
    uint32_t out_a = xy_over_z(pool.ra, ts.pool, pool.s);
    uint32_t out_b = xy_over_z(pool.rb, ts.pool, pool.s);
    // sent tokens to user (we only deduct from the pool balance for now):
    ta.pool = ta.pool - out_a;
    tb.pool = tb.pool - out_b;
    // compute new reserves:
    pool.ra = pool.ra - out_a;
    pool.rb = pool.rb - out_b;
    pool.s = pool.s - ts.pool;
    // burn the shares:
    ts.pool = 0;
}

int main(void) {
    pool = (pool_t){.ra = nd(), .rb = nd(), .s = nd()};
    printf("pool.ra is %x\n", pool.ra);
    printf("pool.rb is %x\n", pool.rb);
    printf("pool.s is %x\n", pool.s);
    assume (pool.ra > 0);
    assume (pool.rb > 0);
    assume (pool.s > 0);
    ta = (token_t){.pool = nd(), .user = 0}; // we don't care about how much a tokens the user has
    printf("initial ta.pool is %x\n", ta.pool);
    tb = (token_t){.pool = nd(), .user = 0}; // we don't care about how much b tokens the user has
    printf("initial tb.pool is %x\n", tb.pool);
    ts = (token_t){.pool = 0, .user = 0};
    // the user has sent non-zero amounts of each token to the pool:
    assume (ta.pool > pool.ra);
    assume (tb.pool > pool.rb);
    // now call deposit:
    deposit();
    printf("pool.ra is %x\n", pool.ra);
    printf("pool.rb is %x\n", pool.rb);
    printf("pool.s is %x\n", pool.s);
    printf("user has %x shares\n", ts.user);
    sassert(ts.user <= pool.s);
    // user can still end up with no shares; why? rounding.
    // sassert(ts.user > 0);
    //
    // now deposit again:
    // ta.pool = nd();
    // tb.pool = nd();
    // assume (ta.pool > pool.ra);
    // assume (tb.pool > pool.rb);
    // deposit();
    // then withdraw some amount of shares held by the user:
    // ts.pool = nd();
    // assume(ts.pool <= ts.user);
    // withdraw();
    // sassert(ta.pool > 0);
}
