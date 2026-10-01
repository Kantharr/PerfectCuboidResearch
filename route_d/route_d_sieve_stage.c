/* One streamed lift-and-filter stage of the Route D Mordell-Weil sieve (route_d_mwsieve.py), in C.

   Given the surviving classes mod N (each m = r + nt integers: r generator coordinates mod N, nt
   torsion bits), lift every class to the k^r classes mod N*k (generator coordinates only) and keep
   a lifted class iff, at every prime of this stage, its reduction lies in the allowed set:
       bits[ ((sum c_i cb_i) mod c2) * c1 + (sum c_i ca_i) mod c1 ] == '1'.
   Primes are applied in the given order, with early exit, exactly as the Python streamed path, so
   the per-prime counts (classes reaching prime j, classes passing it) agree with it.

   Usage:  route_d_sieve_stage  primes.txt  classes_in.bin  classes_out.bin  counts.txt  r nt N k
     primes.txt : one prime per line:  l c1 c2 ca_1..ca_m cb_1..cb_m bits   (m = r + nt)
     classes    : raw int32, m per class
     counts.txt : one line per prime:  l nb na ;  last line: total_lifted survivors
   Build:  gcc -O2 -o route_d_sieve_stage route_d_sieve_stage.c                                  */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { int64_t l, c1, c2; int64_t *ca, *cb; char *bits; int64_t nbits; } prime_t;

int main(int argc, char **argv)
{
    if (argc != 9) { fprintf(stderr, "usage: %s primes classes_in classes_out counts r nt N k\n", argv[0]); return 2; }
    int r = atoi(argv[5]), nt = atoi(argv[6]), m = r + nt;
    int64_t N = atoll(argv[7]), k = atoll(argv[8]);
    if (r < 1 || r > 8 || m > 16 || N < 1 || k < 1) { fprintf(stderr, "bad parameters\n"); return 2; }

    /* primes */
    FILE *fp = fopen(argv[1], "r");
    if (!fp) { perror(argv[1]); return 1; }
    int np = 0, cap = 64;
    prime_t *P = malloc(cap * sizeof(prime_t));
    for (;;) {
        prime_t q;
        if (fscanf(fp, "%lld %lld %lld", &q.l, &q.c1, &q.c2) != 3) break;
        q.ca = malloc(m * sizeof(int64_t)); q.cb = malloc(m * sizeof(int64_t));
        for (int i = 0; i < m; i++) if (fscanf(fp, "%lld", &q.ca[i]) != 1) { fprintf(stderr, "bad ca\n"); return 1; }
        for (int i = 0; i < m; i++) if (fscanf(fp, "%lld", &q.cb[i]) != 1) { fprintf(stderr, "bad cb\n"); return 1; }
        q.nbits = q.c1 * q.c2;
        q.bits = malloc(q.nbits + 2);
        if (fscanf(fp, " %s", q.bits) != 1 || (int64_t)strlen(q.bits) != q.nbits) { fprintf(stderr, "bad bits for l=%lld\n", q.l); return 1; }
        if (np == cap) { cap *= 2; P = realloc(P, cap * sizeof(prime_t)); }
        P[np++] = q;
    }
    fclose(fp);

    /* per-prime step for each lifted coordinate: adding N to coordinate i changes the indices by */
    int64_t *sa = malloc((size_t)np * r * sizeof(int64_t)), *sb = malloc((size_t)np * r * sizeof(int64_t));
    for (int j = 0; j < np; j++)
        for (int i = 0; i < r; i++) {
            sa[j * r + i] = ((N % P[j].c1) * (((P[j].ca[i] % P[j].c1) + P[j].c1) % P[j].c1)) % P[j].c1;
            sb[j * r + i] = ((N % P[j].c2) * (((P[j].cb[i] % P[j].c2) + P[j].c2) % P[j].c2)) % P[j].c2;
        }
    uint64_t *nb = calloc(np ? np : 1, sizeof(uint64_t)), *na = calloc(np ? np : 1, sizeof(uint64_t));

    FILE *fin = fopen(argv[2], "rb"), *fout = fopen(argv[3], "wb");
    if (!fin || !fout) { perror("classes"); return 1; }
    int32_t c[16], cc[16];
    int64_t A[4096], B[4096];                          /* per-prime current indices */
    if (np > 4096) { fprintf(stderr, "too many primes in one stage\n"); return 1; }
    int64_t L[8];
    uint64_t total = 0, kept = 0;
    while (fread(c, sizeof(int32_t), m, fin) == (size_t)m) {
        for (int j = 0; j < np; j++) {
            int64_t a = 0, b = 0;
            for (int i = 0; i < m; i++) {
                a = (a + (int64_t)c[i] % P[j].c1 * ((P[j].ca[i] % P[j].c1 + P[j].c1) % P[j].c1)) % P[j].c1;
                b = (b + (int64_t)c[i] % P[j].c2 * ((P[j].cb[i] % P[j].c2 + P[j].c2) % P[j].c2)) % P[j].c2;
            }
            A[j] = a; B[j] = b;
        }
        memset(L, 0, sizeof(L));
        for (;;) {                                   /* odometer over L in [0,k)^r */
            total++;
            int ok = 1;
            for (int j = 0; j < np; j++) {
                nb[j]++;
                if (P[j].bits[B[j] * P[j].c1 + A[j]] != '1') { ok = 0; break; }
                na[j]++;
            }
            if (ok) {
                for (int i = 0; i < m; i++) cc[i] = c[i];
                for (int i = 0; i < r; i++) cc[i] = (int32_t)(c[i] + L[i] * N);
                fwrite(cc, sizeof(int32_t), m, fout); kept++;
            }
            /* advance the odometer, updating every prime's indices incrementally */
            int i = 0;
            for (; i < r; i++) {
                if (L[i] + 1 < k) {
                    L[i]++;
                    for (int j = 0; j < np; j++) { A[j] = (A[j] + sa[j * r + i]) % P[j].c1; B[j] = (B[j] + sb[j * r + i]) % P[j].c2; }
                    break;
                }
                /* wrap coordinate i back to 0: subtract (k-1) steps */
                for (int j = 0; j < np; j++) {
                    A[j] = ((A[j] - (k - 1) % P[j].c1 * sa[j * r + i]) % P[j].c1 + P[j].c1) % P[j].c1;
                    B[j] = ((B[j] - (k - 1) % P[j].c2 * sb[j * r + i]) % P[j].c2 + P[j].c2) % P[j].c2;
                }
                L[i] = 0;
            }
            if (i == r) break;
        }
    }
    fclose(fin); fclose(fout);
    FILE *fc = fopen(argv[4], "w");
    for (int j = 0; j < np; j++) fprintf(fc, "%lld %llu %llu\n", P[j].l, (unsigned long long)nb[j], (unsigned long long)na[j]);
    fprintf(fc, "%llu %llu\n", (unsigned long long)total, (unsigned long long)kept);
    fclose(fc);
    return 0;
}
