/*
 * Verification program for "A Three-Parameter Reduction of the Perfect Cuboid
 * Problem, and the Resolution of a Distinguished Family".
 *
 * Same computation as verify.py, fast enough for the x <= 7000 range quoted in
 * Section 6.  Uses __int128 because the radicand R exceeds 64 bits.
 *
 *   gcc -O2 -o verify verify.c -lm
 *   ./verify 7000
 *
 * Runtime: a few seconds at N=2000, about two minutes at N=7000.
 *
 * Expected output at N=7000 (final line):
 *   famA 719 (m1 square 719) | product-only 492 (m1 square 0)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

typedef __int128 i128;

/* quick non-residue filters: a square must be a square modulo each of these */
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

static int is_square_ll(long long n)
{
    if (n < 0) return 0;
    long long r = isqrt128((i128) n);
    return r * r == n;
}

static long long gcd_ll(long long a, long long b)
{
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

int main(int argc, char **argv)
{
    init_tables();
    long long N = (argc > 1) ? atoll(argv[1]) : 2000;

    long long famA = 0, prod = 0, qpos = 0, integral = 0, square = 0;
    long long m1sqA = 0, m1sqC = 0, next_report = 1000;

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

                i128 m = (i128) x * y * z, S = xx + yy - zz;
                long long h = gcd_ll((long long) m, k);
                long long m1 = (long long)(m / h);

                if ((i128) y * y == (i128) x * z) {          /* family A */
                    famA++;
                    if (is_square_ll(m1)) m1sqA++;
                    continue;
                }
                prod++;
                if (is_square_ll(m1)) m1sqC++;

                if (m <= k) continue;                        /* Q <= 0 */
                qpos++;

                long long d = m1 - k / h;
                if (S % d) continue;                         /* A^2 not integral */
                integral++;
                i128 A2 = (i128) m1 * (S / d);
                long long a2 = (long long) A2;
                if (is_square_ll(a2)) square++;
                printf("   integral A^2: (%lld,%lld,%lld)  m1=%lld  e=%lld  "
                       "A^2=%lld  square=%d\n",
                       x, y, z, m1, (long long)(S / d), a2, is_square_ll(a2));
            }
        }
        if (x >= next_report) {
            printf("x<=%6lld : famA %4lld (m1 sq %4lld) | product-only %4lld "
                   "(m1 sq %4lld) | Q>0 %4lld | d|S %2lld | A^2 square %lld\n",
                   x, famA, m1sqA, prod, m1sqC, qpos, integral, square);
            fflush(stdout);
            next_report += 1000;
        }
    }

    printf("\nFINAL N=%lld: famA %lld (m1 square %lld) | "
           "product-only %lld (m1 square %lld)\n",
           N, famA, m1sqA, prod, m1sqC);
    printf("            Q>0 %lld | d|S %lld | A^2 a perfect square %lld\n",
           qpos, integral, square);
    return 0;
}
