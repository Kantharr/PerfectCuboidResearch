/*
 * Route F mechanism check: for every product-only (y^2 != xz) primitive
 * all-odd triple with R a perfect square, up to x<=N, find every prime p
 * dividing exactly two of x,y,z (a "two-variable prime"), and check the
 * parity of v_p(Q), Q = x^2z^2+y^2z^2-x^2y^2.
 *
 * The claim being tested: v_p(Q) is always EVEN for two-variable primes,
 * except possibly at the delicate e1=e2=delta boundary case already flagged
 * in Remark 3.10 (the (723,559,507) example). This script finds every
 * two-variable prime with e1=e2 (the only case where v_p(Q) could plausibly
 * be odd) and reports v_p(Q)'s actual parity directly, across as many real
 * triples as x<=N allows.
 *
 *   gcc -O2 -o route_f_check route_f_check.c -lm
 *   ./route_f_check 7000
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

typedef __int128 i128;

static int t64[64], t63[63], t65[65], t11[11];

static void init_tables(void)
{
    for (int i = 0; i < 64; i++) t64[i] = 0;
    for (int i = 0; i < 64; i++) t64[(i * i) % 64] = 1;
    for (int i = 0; i < 63; i++) t63[i] = 0;
    for (int i = 0; i < 63; i++) t63[(i * i) % 63] = 1;
    for (int i = 0; i < 65; i++) t65[i] = 0;
    for (int i = 0; i < 65; i++) t65[(i * i) % 65] = 1;
    for (int i = 0; i < 11; i++) t11[i] = 0;
    for (int i = 0; i < 11; i++) t11[(i * i) % 11] = 1;
}

static long long isqrt128(i128 n)
{
    long long r = (long long) sqrtl((long double) n);
    while ((i128) r * r > n) r--;
    while ((i128)(r + 1) * (r + 1) <= n) r++;
    return r;
}

static long long gcd_ll(long long a, long long b)
{
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static int vp_ll(long long n, long long p)
{
    int v = 0;
    if (n < 0) n = -n;
    while (n % p == 0) { n /= p; v++; }
    return v;
}

/* find all prime factors of n via trial division (n small, <= ~5e7 here) */
#define MAXF 12
static int factor_list(long long n, long long *out)
{
    int cnt = 0;
    for (long long p = 2; p * p <= n; p++) {
        if (n % p == 0) {
            out[cnt++] = p;
            while (n % p == 0) n /= p;
        }
    }
    if (n > 1) out[cnt++] = n;
    return cnt;
}

int main(int argc, char **argv)
{
    init_tables();
    long long N = (argc > 1) ? atoll(argv[1]) : 7000;

    long long total_2var = 0, even_count = 0, odd_count = 0;
    long long e1eqe2_total = 0, e1eqe2_even = 0, e1eqe2_odd = 0;

    for (long long x = 3; x <= N; x += 2) {
        i128 xx = (i128) x * x;
        for (long long y = 3; y < x; y += 2) {
            i128 yy = (i128) y * y, f1 = xx + yy;
            for (long long z = 1; z < y; z += 2) {
                i128 zz = (i128) z * z;
                i128 R = f1 * (xx - zz) * (yy - zz);

                if (!t64[(uint64_t) R & 63]) continue;
                uint64_t r = (uint64_t)(R % 45045);
                if (!t63[r % 63] || !t65[r % 65] || !t11[r % 11]) continue;

                long long k = isqrt128(R);
                if ((i128) k * k != R) continue;
                if (gcd_ll(gcd_ll(x, y), z) != 1) continue;
                if ((i128) y * y == (i128) x * z) continue; /* family A */

                long long Q = (long long)((i128) x * x * z * z + (i128) y * y * z * z - (i128) x * x * y * y);
                if (Q == 0) continue;

                long long fx[MAXF], fy[MAXF], fz[MAXF];
                int nfx = factor_list(x, fx), nfy = factor_list(y, fy), nfz = factor_list(z, fz);

                /* two-variable primes: appear in exactly two of the three factor lists */
                for (int i = 0; i < nfx; i++) {
                    long long p = fx[i];
                    int in_y = 0, in_z = 0;
                    for (int j = 0; j < nfy; j++) if (fy[j] == p) in_y = 1;
                    for (int j = 0; j < nfz; j++) if (fz[j] == p) in_z = 1;
                    if (in_y + in_z != 1) continue; /* need exactly two of three total (x + one other) */
                    int e1 = vp_ll(x, p);
                    int e2 = in_y ? vp_ll(y, p) : vp_ll(z, p);
                    int vpq = vp_ll(Q, p);
                    total_2var++;
                    if (vpq % 2 == 0) even_count++; else odd_count++;
                    if (e1 == e2) {
                        e1eqe2_total++;
                        if (vpq % 2 == 0) e1eqe2_even++; else {
                            e1eqe2_odd++;
                            printf("  ODD at boundary: (x,y,z)=(%lld,%lld,%lld) p=%lld e1=e2=%d v_p(Q)=%d\n",
                                   x, y, z, p, e1, vpq);
                        }
                    }
                }
                /* also need y-only-paired-with-z primes not sharing with x */
                for (int i = 0; i < nfy; i++) {
                    long long p = fy[i];
                    int in_x = 0, in_z = 0;
                    for (int j = 0; j < nfx; j++) if (fx[j] == p) in_x = 1;
                    for (int j = 0; j < nfz; j++) if (fz[j] == p) in_z = 1;
                    if (in_x || !in_z) continue; /* already counted above if in_x; skip if not paired with z */
                    int e1 = vp_ll(y, p), e2 = vp_ll(z, p);
                    int vpq = vp_ll(Q, p);
                    total_2var++;
                    if (vpq % 2 == 0) even_count++; else odd_count++;
                    if (e1 == e2) {
                        e1eqe2_total++;
                        if (vpq % 2 == 0) e1eqe2_even++; else {
                            e1eqe2_odd++;
                            printf("  ODD at boundary: (x,y,z)=(%lld,%lld,%lld) p=%lld e1=e2=%d v_p(Q)=%d\n",
                                   x, y, z, p, e1, vpq);
                        }
                    }
                }
            }
        }
    }

    fprintf(stderr, "\nx<=%lld: two-variable-prime instances checked: %lld\n", N, total_2var);
    fprintf(stderr, "  v_p(Q) even: %lld   odd: %lld\n", even_count, odd_count);
    fprintf(stderr, "  of these, e1=e2 (boundary-eligible): %lld\n", e1eqe2_total);
    fprintf(stderr, "    v_p(Q) even at boundary: %lld   ODD at boundary: %lld\n", e1eqe2_even, e1eqe2_odd);
    return 0;
}
