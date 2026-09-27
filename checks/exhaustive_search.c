/* Exhaustive search without a SAT solver (Remark 3.3 of the paper).

   Usage: exhaustive_search L S Q   (S <= 62)

   Counts the sequences of L positive integers with sum at most S whose block
   sums are covered by Q sumfree sets (x + y = z with x = y also forbidden),
   and prints the first 20 of them.  The search extends a sequence one entry
   at a time and drops a prefix whose block sums have no such cover; this is
   sound because the block sums of a prefix are block sums of every
   extension.  The cover test assigns the block sums in increasing order to
   the Q classes by backtracking, so each sum x + y = z is tested when its
   largest element z is placed. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int L, S, Q;
static int elems[64];
static int nel;
static uint64_t cls[8];

static int conflict(uint64_t m, int d) {
    for (int a = 1; 2 * a <= d; a++)
        if (((m >> a) & 1) && ((m >> (d - a)) & 1)) return 1;
    return 0;
}

static int colour(int i, int used) {
    if (i == nel) return 1;
    int d = elems[i];
    int lim = used < Q ? used + 1 : Q;
    for (int k = 0; k < lim; k++) {
        if (conflict(cls[k] | (1ULL << d), d)) continue;
        cls[k] |= 1ULL << d;
        int ok = colour(i + 1, k + 1 > used ? k + 1 : used);
        cls[k] &= ~(1ULL << d);
        if (ok) return 1;
    }
    return 0;
}

static int colourable(uint64_t B) {
    nel = 0;
    for (int d = 1; d < 64; d++) if ((B >> d) & 1) elems[nel++] = d;
    for (int k = 0; k < Q; k++) cls[k] = 0;
    return colour(0, 0);
}

static int pre[64];
static long long found = 0, nodes = 0;
static int seq[64];

static void dfs(int k, uint64_t B) {
    nodes++;
    if (k == L) {
        found++;
        if (found <= 20) {
            printf("  sol (sum %d):", pre[k]);
            for (int i = 0; i < L; i++) printf(" %d", seq[i]);
            printf("\n");
        }
        return;
    }
    for (int a = 1; pre[k] + a + (L - k - 1) <= S; a++) {
        pre[k + 1] = pre[k] + a;
        seq[k] = a;
        uint64_t B2 = B;
        for (int j = 0; j <= k; j++) B2 |= 1ULL << (pre[k + 1] - pre[j]);
        if (B2 != B && !colourable(B2)) continue;
        dfs(k + 1, B2);
    }
}

int main(int argc, char **argv) {
    if (argc != 4) { fprintf(stderr, "usage: %s L S Q\n", argv[0]); return 2; }
    L = atoi(argv[1]); S = atoi(argv[2]); Q = atoi(argv[3]);
    if (Q < 1 || Q > 8) { fprintf(stderr, "Q must be 1..8\n"); return 1; }
    if (S > 62) { fprintf(stderr, "S too large\n"); return 1; }
    pre[0] = 0;
    dfs(0, 0);
    printf("L=%d S=%d Q=%d: %lld sequences, %lld nodes\n", L, S, Q, found, nodes);
    return 0;
}
