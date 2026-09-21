/*
 * Kernel decomposition tool for referee_notes.md Routes A and H.
 *
 * For every product-only (y^2 != xz) primitive all-odd triple with R a
 * perfect square and Q>0, up to x<=N, computes the squarefree-kernel
 * decomposition (alpha,beta,gamma,u1,u2,u3) of Theorem 4.1:
 *
 *   x^2+y^2 = alpha*beta*u1^2
 *   x^2-z^2 = alpha*gamma*u2^2
 *   y^2-z^2 = beta*gamma*u3^2
 *
 * with alpha,beta,gamma pairwise coprime squarefree positive integers,
 * exactly as constructed in the proof of Theorem 4.1 (kernel of each
 * factor, then alpha=gcd(d1,d2), beta=gcd(d1,d3), gamma=gcd(d2,d3)).
 *
 * Prints one CSV row per qualifying triple to stdout; sanity-checks the
 * decomposition against the theorem's own claims (d1=alpha*beta, etc.,
 * and that the u_i are exact integers) and reports to stderr if any of
 * that fails -- it shouldn't, since Theorem 4.1 is a proved theorem, but
 * this is a real check on the implementation, not a hope.
 *
 *   gcc -O2 -o kernel_decomp kernel_decomp.c -lm
 *   ./kernel_decomp 7000 > kernel_table.csv
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

static long long isqrt_ll(long long n)
{
    long long r = (long long) sqrtl((long double) n);
    while (r * r > n) r--;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

static long long gcd_ll(long long a, long long b)
{
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

/* squarefree kernel of n: product of primes dividing n to an odd power */
static long long squarefree_kernel(long long n)
{
    long long k = 1;
    for (long long p = 2; p * p <= n; p++) {
        if (n % p == 0) {
            int e = 0;
            while (n % p == 0) { n /= p; e++; }
            if (e % 2) k *= p;
        }
    }
    if (n > 1) k *= n;
    return k;
}

int main(int argc, char **argv)
{
    init_tables();
    long long N = (argc > 1) ? atoll(argv[1]) : 7000;

    long long count = 0, warn = 0;

    printf("x,y,z,alpha,beta,gamma,u1,u2,u3,Q,d1,d2,d3\n");

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

                i128 m = (i128) x * y * z;
                if (m <= k) continue; /* Q <= 0 */

                long long Q = (long long)((i128) x * x * z * z + (i128) y * y * z * z - (i128) x * x * y * y);

                long long f1v = x * x + y * y;
                long long f2v = x * x - z * z;
                long long f3v = y * y - z * z;

                long long d1 = squarefree_kernel(f1v);
                long long d2 = squarefree_kernel(f2v);
                long long d3 = squarefree_kernel(f3v);

                long long alpha = gcd_ll(d1, d2);
                long long beta  = gcd_ll(d1, d3);
                long long gamma = gcd_ll(d2, d3);

                if (alpha * beta != d1 || alpha * gamma != d2 || beta * gamma != d3) {
                    fprintf(stderr, "WARN kernel mismatch at (%lld,%lld,%lld): "
                            "d1=%lld d2=%lld d3=%lld alpha=%lld beta=%lld gamma=%lld\n",
                            x, y, z, d1, d2, d3, alpha, beta, gamma);
                    warn++;
                    continue;
                }

                long long u1 = isqrt_ll(f1v / d1);
                long long u2 = isqrt_ll(f2v / d2);
                long long u3 = isqrt_ll(f3v / d3);

                if (u1 * u1 != f1v / d1 || u2 * u2 != f2v / d2 || u3 * u3 != f3v / d3) {
                    fprintf(stderr, "WARN u_i not exact at (%lld,%lld,%lld)\n", x, y, z);
                    warn++;
                    continue;
                }

                printf("%lld,%lld,%lld,%lld,%lld,%lld,%lld,%lld,%lld,%lld,%lld,%lld,%lld\n",
                       x, y, z, alpha, beta, gamma, u1, u2, u3, Q, d1, d2, d3);
                count++;
            }
        }
    }

    fprintf(stderr, "\nkernel_decomp: %lld qualifying triples (Q>0, product-only, R square), "
            "%lld warnings, x<=%lld\n", count, warn, N);
    return 0;
}
