/*
 * Targeted line search: fix x=p*t, y=q*t for a given coprime odd (p,q)
 * (e.g. p=39,q=37, found recurring in kernel (5,2,19)), vary t and z, and
 * look for triples with R a perfect square, y^2 != xz, Q>0, gcd(x,y,z)=1.
 *
 * This is a 2-variable search (t,z) instead of the full 3-variable (x,y,z)
 * enumeration, so it can reach much larger x for the same cost -- a direct
 * test of whether fixing this ratio produces a genuine, richer family
 * (Route A's parametrization hope) or just a couple of sporadic hits.
 *
 *   gcc -O2 -o kernel_line_search kernel_line_search.c -lm
 *   ./kernel_line_search 39 37 5000
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

/* Integer-only isqrt for __int128: a long-double initial guess loses
 * precision (and, worse, k=sqrt(R) can itself overflow a 64-bit long long
 * once x exceeds ~2.1 million, since k ~ x^3) once R needs more than about
 * 64 significant bits, which happens well within the ranges this tool is
 * meant to explore. Newton's method with a bit-length-based integer initial
 * guess avoids both problems entirely -- everything stays in i128. */
static i128 isqrt128(i128 n)
{
    if (n <= 0) return 0;
    int bits = 0;
    for (i128 t = n; t > 0; t >>= 1) bits++;
    i128 r = (i128) 1 << ((bits + 1) / 2);
    for (int iter = 0; iter < 200; iter++) {
        i128 r2 = (r + n / r) / 2;
        if (r2 >= r) break;
        r = r2;
    }
    while (r * r > n) r--;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

static long long gcd_ll(long long a, long long b)
{
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

int main(int argc, char **argv)
{
    if (argc < 3) { fprintf(stderr, "usage: %s p q [Tmax]\n", argv[0]); return 1; }
    init_tables();
    long long p = atoll(argv[1]);
    long long q = atoll(argv[2]);
    long long Tmax = (argc > 3) ? atoll(argv[3]) : 5000;

    long long hits = 0, checked_t = 0;

    for (long long t = 1; t <= Tmax; t += 2) {
        long long x = p * t, y = q * t;
        if (x <= y) continue; /* need x>y */
        checked_t++;
        i128 xx = (i128) x * x, yy = (i128) y * y, f1 = xx + yy;
        for (long long z = 1; z < y; z += 2) {
            i128 zz = (i128) z * z;
            i128 R = f1 * (xx - zz) * (yy - zz);

            if (!t64[(uint64_t) R & 63]) continue;
            uint64_t r = (uint64_t)(R % 45045);
            if (!t63[r % 63] || !t65[r % 65] || !t11[r % 11]) continue;

            i128 k = isqrt128(R);
            if (k * k != R) continue;
            if (gcd_ll(gcd_ll(x, y), z) != 1) continue;
            if ((i128) y * y == (i128) x * z) continue; /* family A */

            i128 m = (i128) x * y * z;
            int qpos = (m > k);

            printf("  HIT: t=%lld  (x,y,z)=(%lld,%lld,%lld)  Q>0:%d\n", t, x, y, z, qpos);
            hits++;
        }
    }

    fprintf(stderr, "\nkernel_line_search p=%lld q=%lld: checked %lld odd t up to %lld, "
            "%lld hits (R square, y^2!=xz)\n", p, q, checked_t, Tmax, hits);
    return 0;
}
