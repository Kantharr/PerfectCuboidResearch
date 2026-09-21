/*
 * Generalized line search: fix ONE coordinate pair to a ratio p:q (scaled by
 * t) and search over the third (free) coordinate. Which pair is fixed is
 * given by argv[1]: "xy" (x=pt,y=qt, search z), "xz" (x=pt,z=qt, search y),
 * or "yz" (y=pt,z=qt, search x).
 *
 *   gcc -O2 -o kernel_line_search2 kernel_line_search2.c -lm
 *   ./kernel_line_search2 yz 53 49 3000
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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

/* Integer-only isqrt for __int128 -- see kernel_line_search.c for why the
 * long-double + long-long version breaks once k=sqrt(R) exceeds ~9.2e18
 * (which happens once x exceeds ~2.1 million, well within this tool's
 * intended reach). Newton's method with an integer initial guess. */
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

static int check_and_report(long long x, long long y, long long z, long long t, long long *hits)
{
    if (x <= y || y <= z || z <= 0) return 0;
    i128 xx = (i128) x * x, yy = (i128) y * y, zz = (i128) z * z;
    i128 R = (xx + yy) * (xx - zz) * (yy - zz);

    if (!t64[(uint64_t) R & 63]) return 0;
    uint64_t r = (uint64_t)(R % 45045);
    if (!t63[r % 63] || !t65[r % 65] || !t11[r % 11]) return 0;

    i128 k = isqrt128(R);
    if (k * k != R) return 0;
    if (gcd_ll(gcd_ll(x, y), z) != 1) return 0;
    if ((i128) y * y == (i128) x * z) return 0; /* family A */

    i128 m = (i128) x * y * z;
    int qpos = (m > k);
    printf("  HIT: t=%lld  (x,y,z)=(%lld,%lld,%lld)  Q>0:%d\n", t, x, y, z, qpos);
    (*hits)++;
    return 1;
}

int main(int argc, char **argv)
{
    if (argc < 5) { fprintf(stderr, "usage: %s xy|xz|yz p q Tmax\n", argv[0]); return 1; }
    init_tables();
    const char *mode = argv[1];
    long long p = atoll(argv[2]);
    long long q = atoll(argv[3]);
    long long Tmax = atoll(argv[4]);

    long long hits = 0;

    for (long long t = 1; t <= Tmax; t += 2) {
        long long a = p * t, b = q * t; /* the two fixed coords, a>b */
        if (a <= b) continue;
        if (strcmp(mode, "xy") == 0) {
            long long x = a, y = b;
            for (long long z = 1; z < y; z += 2) check_and_report(x, y, z, t, &hits);
        } else if (strcmp(mode, "xz") == 0) {
            long long x = a, z = b;
            for (long long y = z + 2; y < x; y += 2) check_and_report(x, y, z, t, &hits);
        } else if (strcmp(mode, "yz") == 0) {
            long long y = a, z = b;
            for (long long x = y + 2; ; x += 2) {
                if (x > y * 40) break; /* cap search width per t */
                check_and_report(x, y, z, t, &hits);
            }
        } else {
            fprintf(stderr, "unknown mode %s\n", mode);
            return 1;
        }
    }

    fprintf(stderr, "\nkernel_line_search2 mode=%s p=%lld q=%lld: Tmax=%lld, %lld hits\n",
            mode, p, q, Tmax, hits);
    return 0;
}
