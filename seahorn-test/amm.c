#include "seahorn/seahorn.h"
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "sys/param.h"

/*
 * Here we want to simulate withdraw and deposit operations in a simple AMM and try verifying some properties with Seahorn.
 */

// to set something to a non-deterministic value:
extern uint32_t nd();

// optional types:
#define make_opt_s(valtype, name) \
    typedef struct { \
        valtype val; \
        bool present; \
    } name##_opt;

make_opt_s(uint32_t, uint32)

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

// the world consists of a liquidity pool and one user that holds pool shares:
typedef struct {
    pool_t pool;
    token_t ta;
    token_t tb;
    token_t ts;
} world_t;

make_opt_s(world_t, world)

uint32_opt xy_over_z(uint32_t x, uint32_t y, uint32_t z) {
    uint64_t res = ((uint64_t)x * (uint64_t)y)/((uint64_t) z);
    if ((res>>32) != 0) {
        // overflow
        return (uint32_opt){.present=false};
    }
    else {
        return (uint32_opt){.val=(uint32_t)res, .present=true};
    }
}

// the deposit function of the pool contract
world_opt deposit(world_t w) {
    pool_t p = w.pool;
    uint32_opt shares_a = xy_over_z(w.ta.pool, p.s, p.ra);
    uint32_opt shares_b = xy_over_z(w.tb.pool, p.s, p.rb);
    if (!(shares_a.present || shares_b.present)) {
        return (world_opt){.present = false}; // we abort the transation (and the user looses their funds!)
    };
    uint32_t new_total_shares = MIN(shares_a.val, shares_b.val);
    uint32_t new_user_shares = new_total_shares - p.s;
    pool_t new_pool = {.ra = w.ta.pool, .rb = w.tb.pool, .s = new_total_shares};
    token_t new_ts = {.pool = w.ts.pool, .user = new_user_shares};
    world_t new_world = {.pool = new_pool, .ta = w.ta, .tb = w.tb, .ts = new_ts};
    return (world_opt){.val = new_world, .present = true};
}

int main(void) {
    pool_t pool = {.ra = nd(), .rb = nd(), .s = nd()};
    assume (pool.ra > 0);
    assume (pool.rb > 0);
    assume (pool.s > 0);
    token_t ta = {.pool = nd(), .user = 0};
    token_t tb = {.pool = nd(), .user = 0};
    // the user has sent non-zero amounts of each token to the pool:
    assume (ta.pool > pool.ra);
    assume (tb.pool > pool.rb);
    token_t ts = {.pool = 0, .user = 0};
    world_t w = {.pool = pool, .ta = ta, .tb = tb, .ts = ts};
    // now call deposit:
    world_opt result = deposit(w);
    if (result.present) {
        sassert(result.val.ta.pool == result.val.pool.ra);
        /* sassert(result.val.ts.user > 0); // user can still end up with no shares; why? rounding. */
    }
}
