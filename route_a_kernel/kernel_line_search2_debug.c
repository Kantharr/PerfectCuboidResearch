/*
 * Debug instrumented copy of kernel_line_search2.c, adding progress logging
 * (t value + elapsed time + call counts) to diagnose the 287:109 anomalous
 * slowdown (2.5+ hours vs the ~15s expected at t<=10000, alone, no
 * concurrency) -- 2026-09-20. Not for general use; delete once diagnosed.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef __int128 i128;

static int t64[64], t63[63], t65[65], t11[11];
static long long calls = 0, isqrt_calls = 0;

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

static i128 isqrt128(i128 n)
{
    if (n <= 0) return 0;
    int bits = 0;
    for (i128 t = n; t > 0; t >>= 1) bits++;
    i128 r = (i128) 1 << ((bits + 1) / 2);
    int iter;
    for (iter = 0; iter < 200; iter++) {
        i128 r2 = (r + n / r) / 2;
        if (r2 >= r) break;
        r = r2;
    }
    if (iter >= 199) {
        fprintf(stderr, "  [WARN] isqrt128 Newton loop hit 200-iteration cap!\n");
    }
    long long corr = 0;
    while (r * r > n) { r--; corr++; if (corr > 1000000) { fprintf(stderr, "  [WARN] isqrt128 downward correction >1e6 steps!\n"); break; } }
    corr = 0;
    while ((r + 1) * (r + 1) <= n) { r++; corr++; if (corr > 1000000) { fprintf(stderr, "  [WARN] isqrt128 upward correction >1e6 steps!\n"); break; } }
    return r;
}

static long long gcd_ll(long long a, long long b)
{
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static int check_and_report(long long x, long long y, long long z, long long t, long long *hits)
{
    calls++;
    if (x <= y || y <= z || z <= 0) return 0;
    i128 xx = (i128) x * x, yy = (i128) y * y, zz = (i128) z * z;
    i128 R = (xx + yy) * (xx - zz) * (yy - zz);

    if (!t64[(uint64_t) R & 63]) return 0;
    uint64_t r = (uint64_t)(R % 45045);
    if (!t63[r % 63] || !t65[r % 65] || !t11[r % 11]) return 0;

    isqrt_calls++;
    i128 k = isqrt128(R);
    if (k * k != R) return 0;
    if (gcd_ll(gcd_ll(x, y), z) != 1) return 0;
    if ((i128) y * y == (i128) x * z) return 0;

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
    time_t t0 = time(NULL);
    time_t last_report = t0;

    for (long long t = 1; t <= Tmax; t += 2) {
        long long a = p * t, b = q * t;
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
                if (x > y * 40) break;
                check_and_report(x, y, z, t, &hits);
            }
        } else {
            fprintf(stderr, "unknown mode %s\n", mode);
            return 1;
        }
        time_t now = time(NULL);
        if (difftime(now, last_report) >= 2.0) {
            fprintf(stderr, "  progress: t=%lld/%lld  elapsed=%.0fs  calls=%lld  isqrt_calls=%lld\n",
                    t, Tmax, difftime(now, t0), calls, isqrt_calls);
            last_report = now;
        }
    }

    fprintf(stderr, "\nkernel_line_search2 mode=%s p=%lld q=%lld: Tmax=%lld, %lld hits, %lld calls, %lld isqrt_calls\n",
            mode, p, q, Tmax, hits, calls, isqrt_calls);
    return 0;
}
