/*
 * Route F extended survivor scan: find every d|S survivor (Q>0, product-only,
 * R a perfect square, A^2 an integer) up to x<=N, and for each, classify
 * every odd-power prime of m1 as one-variable (unconditional obstruction,
 * Lemma 3.6) or two-variable (possible escape only at delta=e, per the
 * 2026-09-18 derivation). Reports whether the survivor has ANY one-variable
 * obstruction, or is a genuine "escape risk" candidate (all odd-power primes
 * of m1 are two-variable).
 *
 *   gcc -O2 -o route_f_scan route_f_scan.c -lm
 *   ./route_f_scan 30000
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

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

/* Fast float-based isqrt (long-double initial guess + correction). This is
 * the version with a known overflow risk once k=sqrt(R) exceeds ~9.2e18,
 * i.e. once x exceeds ~2.1 million (see kernel_line_search.c's fixed history
 * for why) -- but this scan targets x in the tens of thousands, x^3 nowhere
 * near that ceiling, so it's safe here and ~2x faster than the integer-only
 * Newton's-method version, which matters at this loop's O(N^3) cost. */
static i128 isqrt128(i128 n)
{
    i128 r = (i128) sqrtl((long double) n);
    while (r * r > n) r--;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

static i128 gcd_i128(i128 a, i128 b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { i128 t = a % b; a = b; b = t; }
    return a;
}

static long long gcd_ll(long long a, long long b)
{
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

/* factor n (fits in i128, but values here stay well under 1e15) via trial
 * division; returns count, fills primes[] and exps[] */
#define MAXF 20
static int factor_i128(i128 n, long long *primes, int *exps)
{
    int cnt = 0;
    for (long long p = 3; (i128) p * p <= n; p += 2) {
        if (n % p == 0) {
            int e = 0;
            while (n % p == 0) { n /= p; e++; }
            primes[cnt] = p; exps[cnt] = e; cnt++;
        }
    }
    if (n > 1) { primes[cnt] = (long long) n; exps[cnt] = 1; cnt++; }
    return cnt;
}

int main(int argc, char **argv)
{
    init_tables();
    long long N = (argc > 1) ? atoll(argv[1]) : 20000;

    long long checked = 0, survivors = 0, escape_risk = 0;
    long long next_report = N / 10;
    if (next_report < 1000) next_report = 1000;
    time_t t0 = time(NULL);

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

                i128 k = isqrt128(R);
                if (k * k != R) continue;
                if (gcd_ll(gcd_ll(x, y), z) != 1) continue;
                if ((i128) y * y == (i128) x * z) continue; /* family A */

                i128 m = (i128) x * y * z;
                if (m <= k) continue; /* Q <= 0 */
                checked++;

                i128 h = gcd_i128(m, k);
                i128 m1 = m / h, k1 = k / h;
                i128 S = xx + yy - zz;
                i128 d = m1 - k1;
                if (d <= 0 || S % d != 0) continue; /* not a d|S survivor */
                i128 e_val = S / d;

                survivors++;
                long long primes[MAXF]; int exps[MAXF];
                int nf = factor_i128(m1, primes, exps);

                int has_onevar_odd = 0;
                for (int i = 0; i < nf; i++) {
                    if (exps[i] % 2 == 0) continue; /* even contribution, skip */
                    long long p = primes[i];
                    int divs = (x % p == 0) + (y % p == 0) + (z % p == 0);
                    if (divs == 1) { has_onevar_odd = 1; break; }
                }

                /* Per the 2026-09-18 collapse: sf(m1)=sf(e) iff BOTH m1 and e
                 * are individually perfect squares. Check that directly. */
                i128 sq_m1 = isqrt128(m1);
                int m1_is_square = (sq_m1 * sq_m1 == m1);
                i128 sq_e = isqrt128(e_val);
                int e_is_square = (sq_e * sq_e == e_val);

                printf("SURVIVOR: (%lld,%lld,%lld)  m1=", x, y, z);
                /* print m1/e (may exceed long long precision at high N; print via repeated division) */
                {
                    char buf[64]; int len = 0; i128 tmp = m1;
                    if (tmp == 0) { buf[len++] = '0'; }
                    while (tmp > 0) { buf[len++] = '0' + (int)(tmp % 10); tmp /= 10; }
                    for (int i = len - 1; i >= 0; i--) putchar(buf[i]);
                }
                printf(" (square:%s)  e=", m1_is_square ? "YES" : "no");
                {
                    char buf[64]; int len = 0; i128 tmp = e_val;
                    if (tmp == 0) { buf[len++] = '0'; }
                    while (tmp > 0) { buf[len++] = '0' + (int)(tmp % 10); tmp /= 10; }
                    for (int i = len - 1; i >= 0; i--) putchar(buf[i]);
                }
                printf(" (square:%s)  one-variable obstruction: %s",
                       e_is_square ? "YES" : "no", has_onevar_odd ? "YES" : "NO (ESCAPE RISK)");
                if (!has_onevar_odd) escape_risk++;
                if (m1_is_square && e_is_square) {
                    printf("  <<< COUNTEREXAMPLE CANDIDATE: both m1 and e are perfect squares! >>>");
                }
                printf("\n");
            }
        }
        /* Progress checkpoint: fires once per x-decile regardless of whether
         * any survivor was found at this x -- previously this fprintf was
         * nested inside the survivor-found block above, so with survivors as
         * rare as they are, most deciles silently passed with no log output
         * at all. Fixed 2026-09-18. */
        if (x >= next_report) {
            time_t now = time(NULL);
            fprintf(stderr, "  progress: x<=%lld  (%.0f sec elapsed)  checked=%lld survivors=%lld escape_risk=%lld\n",
                    x, difftime(now, t0), checked, survivors, escape_risk);
            fflush(stderr); /* stderr can be block-buffered once redirected to a file */
            next_report += (N / 10 > 1000 ? N / 10 : 1000);
        }
    }

    time_t t1 = time(NULL);
    fprintf(stderr, "\nx<=%lld done in %.0f sec: checked=%lld (Q>0 product-only) survivors=%lld (d|S) escape_risk=%lld\n",
            N, difftime(t1, t0), checked, survivors, escape_risk);
    return 0;
}
