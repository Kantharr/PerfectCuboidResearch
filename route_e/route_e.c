/*
 * Route E (referee_notes.md, Part 2): "Attack through Theorem 3.9's criterion".
 *
 * Theorem 3.9 (thm:converse-full) says: given a primitive all-odd triple
 * x>y>z>0 with R a perfect square, Q>0 and A^2=mS/(m-k) the square of an
 * integer, (A,B,C) is a perfect cuboid iff no odd prime p divides two of
 * x,y,z to the same exponent e with p | N, where (Lemma 3.8 / lem:twovar)
 *
 *   N = x0^2 + y0^2   if p | x, p | y
 *   N = x0^2 - z0^2   if p | x, p | z
 *   N = y0^2 - z0^2   if p | y, p | z
 *
 * with x0,y0,z0 the variables divided by p^e.
 *
 * This script asks the question Route E poses: among product-only (y^2 != xz)
 * primitive all-odd triples with R a perfect square (independent of whether
 * A^2 even works out to an integer or a square -- that is a separate, already
 * -tested necessary condition), does the "no bad prime" criterion tend to
 * hold or tend to fail? If it fails systematically, that is close to a proof
 * that Case 2 is empty. If it usually holds, this route does not close the
 * case on its own.
 *
 *   gcc -O2 -o route_e route_e.c -lm
 *   ./route_e 7000
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

typedef struct { long long p; int e; } Factor;
#define MAXFACT 8

/* trial division suffices: x,y,z <= N <= a few 10^4 */
static int factorize(long long n, Factor *f)
{
    int nf = 0;
    for (long long p = 3; p * p <= n; p += 2) {
        if (n % p == 0) {
            int e = 0;
            while (n % p == 0) { n /= p; e++; }
            f[nf].p = p; f[nf].e = e; nf++;
        }
    }
    if (n > 1) { f[nf].p = n; f[nf].e = 1; nf++; }
    return nf;
}

/* if x,y share prime p to equal exponent e, check p | N = x0^2 (+/-) y0^2 */
static int check_pair(long long a, long long b, long long p, int e,
                       int sign, long long *out_delta)
{
    long long pe = 1;
    for (int t = 0; t < e; t++) pe *= p;
    long long a0 = a / pe, b0 = b / pe;
    i128 Nval = (i128) a0 * a0 + (i128) sign * (i128) b0 * b0;
    if (Nval < 0) Nval = -Nval;
    if (Nval == 0) { *out_delta = -1; return 1; } /* p | N trivially (N=0) */
    i128 tmp = Nval;
    int vp = 0;
    while (tmp % p == 0) { tmp /= p; vp++; }
    *out_delta = vp / 2;
    return vp > 0;
}

int main(int argc, char **argv)
{
    init_tables();
    long long N = (argc > 1) ? atoll(argv[1]) : 2000;

    long long prodOnly = 0, havePair = 0, violated = 0, holds = 0, vacuous = 0;
    long long qpos = 0, havePairQ = 0, violatedQ = 0, holdsQ = 0, vacuousQ = 0;
    long long next_report = 1000;

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
                if ((i128) y * y == (i128) x * z) continue; /* skip family A */

                prodOnly++;
                i128 m = (i128) x * y * z;
                int is_qpos = (m > k);
                if (is_qpos) qpos++;

                Factor fx[MAXFACT], fy[MAXFACT], fz[MAXFACT];
                int nfx = factorize(x, fx), nfy = factorize(y, fy), nfz = factorize(z, fz);

                int found_pair = 0, found_bad = 0;
                long long bad_p = 0; int bad_e = 0; long long bad_delta = 0;

                for (int i = 0; i < nfx; i++)
                    for (int j = 0; j < nfy; j++)
                        if (fx[i].p == fy[j].p && fx[i].e == fy[j].e) {
                            found_pair = 1;
                            long long delta;
                            if (check_pair(x, y, fx[i].p, fx[i].e, +1, &delta)) {
                                found_bad = 1; bad_p = fx[i].p; bad_e = fx[i].e; bad_delta = delta;
                            }
                        }
                for (int i = 0; i < nfx; i++)
                    for (int j = 0; j < nfz; j++)
                        if (fx[i].p == fz[j].p && fx[i].e == fz[j].e) {
                            found_pair = 1;
                            long long delta;
                            if (check_pair(x, z, fx[i].p, fx[i].e, -1, &delta)) {
                                found_bad = 1; bad_p = fx[i].p; bad_e = fx[i].e; bad_delta = delta;
                            }
                        }
                for (int i = 0; i < nfy; i++)
                    for (int j = 0; j < nfz; j++)
                        if (fy[i].p == fz[j].p && fy[i].e == fz[j].e) {
                            found_pair = 1;
                            long long delta;
                            if (check_pair(y, z, fy[i].p, fy[i].e, -1, &delta)) {
                                found_bad = 1; bad_p = fy[i].p; bad_e = fy[i].e; bad_delta = delta;
                            }
                        }

                if (found_bad) {
                    violated++;
                    if (is_qpos) violatedQ++;
                    printf("  VIOLATED: (%lld,%lld,%lld)  p=%lld e=%d delta=%lld  Q>0:%d\n",
                           x, y, z, bad_p, bad_e, bad_delta, is_qpos);
                } else if (found_pair) {
                    holds++;
                    if (is_qpos) holdsQ++;
                } else {
                    vacuous++;
                    if (is_qpos) vacuousQ++;
                }
                if (found_pair) { havePair++; if (is_qpos) havePairQ++; }
            }
        }
        if (x >= next_report) {
            printf("x<=%6lld : product-only %5lld (Q>0 %4lld) | equal-exp pair %4lld | "
                   "violated %3lld | holds %4lld | vacuous %4lld\n",
                   x, prodOnly, qpos, havePair, violated, holds, vacuous);
            fflush(stdout);
            next_report += 1000;
        }
    }

    printf("\nRoute E summary, x<=%lld:\n", N);
    printf("  product-only (y^2 != xz) triples examined : %lld\n", prodOnly);
    printf("  with >=1 equal-exponent shared prime       : %lld\n", havePair);
    printf("    criterion VIOLATED (some such p | N)     : %lld\n", violated);
    printf("    criterion holds (no such p | N)          : %lld\n", holds);
    printf("  no equal-exponent shared prime at all      : %lld\n", vacuous);
    printf("\n  restricted to Q>0 (the actually-relevant candidate pool):\n");
    printf("  product-only with Q>0                      : %lld\n", qpos);
    printf("    with >=1 equal-exponent shared prime      : %lld\n", havePairQ);
    printf("      criterion VIOLATED (some such p | N)    : %lld\n", violatedQ);
    printf("      criterion holds (no such p | N)         : %lld\n", holdsQ);
    printf("    no equal-exponent shared prime at all      : %lld\n", vacuousQ);
    return 0;
}
