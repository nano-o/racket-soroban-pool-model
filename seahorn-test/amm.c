#include "seahorn/seahorn.h"
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "sys/param.h"
#include "setjmp.h"

/*
 * Here we want to simulate withdraw and deposit operations in a simple AMM and try verifying some properties with Seahorn.
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

// global variable holding an environment to lonjump to on overflow:
jmp_buf env; // upon overflow we jump env, but we do not undo anything.

uint32_t xy_over_z(uint32_t x, uint32_t y, uint32_t z) {
    uint64_t result = ((uint64_t)x * (uint64_t)y)/((uint64_t) z);
    if ((result>>32) != 0) { // overflow
        longjmp(env, 1);
    }
    else {
        return (uint32_t)result;
    }
}

// the deposit function of the pool contract
void deposit() {
    // the user has already sent funds to the pool (in the token contracts ta and tb)
    uint32_t shares_a = xy_over_z(ta.pool, pool.s, pool.ra);
    uint32_t shares_b = xy_over_z(tb.pool, pool.s, pool.rb);
    uint32_t new_total_shares = MIN(shares_a, shares_b);
    uint32_t new_user_shares = new_total_shares - pool.s;
    // update pool:
    pool.ra = ta.pool;
    pool.rb = tb.pool;
    pool.s = new_total_shares;
    // send shares to user:
    uint32_t total_user_shares = ts.user + new_total_shares;
    if (total_user_shares < ts.user) {
        longjmp(env, 1); // overflow
    };
    ts.user = total_user_shares;
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
    int i;
    i = setjmp(env);
    if (i == 0) {
        pool = (pool_t){.ra = nd(), .rb = nd(), .s = nd()};
        assume (pool.ra > 0);
        assume (pool.rb > 0);
        assume (pool.s > 0);
        ta = (token_t){.pool = nd(), .user = 0}; // we don't care about how much a tokens the user has
        tb = (token_t){.pool = nd(), .user = 0}; // we don't care about how much b tokens the user has
        ts = (token_t){.pool = 0, .user = 0};
        // the user has sent non-zero amounts of each token to the pool:
        assume (ta.pool > pool.ra);
        assume (tb.pool > pool.rb);
        // now call deposit:
        deposit();
        // user can still end up with no shares; why? rounding.
        // sassert(ts.user > 0);
        // now deposit again:
        // ta.pool = nd();
        // tb.pool = nd();
        // assume (ta.pool > pool.ra);
        // assume (tb.pool > pool.rb);
        deposit();
        // then withdraw some amount of shares held by the user:
        ts.pool = nd();
        assume(ts.pool <= ts.user);
        withdraw();
        sassert(ta.pool > 0);
    }
}
