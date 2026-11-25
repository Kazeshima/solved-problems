/* Exhaust all one-coordinate Pareto witnesses in connected graph6 records of
   order 2..10 (10 is available for the submitted positive control).
   Usage: scan-spikes graph2c.g6 ... graph9c.g6 > scan.tsv
   Each row gives the original code, exact expansion numerator/denominator,
   and the support/mass of every violating spike, if any. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { MAX_N = 10, MAX_MASK = 1 << MAX_N };
static int size[MAX_MASK], lowest[MAX_MASK];

static int gcd(int a, int b) {
    while (b) {
        int r = a % b;
        a = b;
        b = r;
    }
    return a;
}

static int scan(const char *code) {
    int n = (unsigned char)code[0] - 63;
    if (n < 2 || n > MAX_N) return 0;
    int bits = n * (n - 1) / 2;
    if (strlen(code) != (size_t)(1 + (bits + 5) / 6)) return 0;
    for (size_t i = 1; code[i]; ++i)
        if (code[i] < 63 || code[i] > 126) return 0;
    int pad = (6 - bits % 6) % 6;
    if ((code[strlen(code) - 1] - 63) & ((1 << pad) - 1)) return 0;

    int adj[MAX_N] = {0}, position = 0;
    for (int v = 1; v < n; ++v) {
        for (int u = 0; u < v; ++u, ++position) {
            int word = code[1 + position / 6] - 63;
            if ((word >> (5 - position % 6)) & 1) {
                adj[u] |= 1 << v;
                adj[v] |= 1 << u;
            }
        }
    }
    int cut[MAX_MASK] = {0}, minimum[MAX_N], cover[MAX_N] = {0};
    int full = (1 << n) - 1, k = n / 2;
    int numerator = n, denominator = 1;
    for (int v = 0; v < n; ++v) minimum[v] = n;
    for (int s = 1; s <= full; ++s) {
        int count = size[s];
        if (count > k) continue;
        int v = lowest[s], rest = s & (s - 1);
        /* Adding v turns its edges to rest from crossing to internal. */
        cut[s] = cut[rest] + size[adj[v]] - 2 * size[adj[v] & rest];
        if (cut[s] * denominator < numerator * count) {
            numerator = cut[s];
            denominator = count;
        }
        for (int t = s; t; t &= t - 1) {
            int u = lowest[t];
            if (cut[s] < minimum[u]) {
                minimum[u] = cut[s];
                cover[u] = 0;
            }
            if (cut[s] == minimum[u]) cover[u] |= s;
        }
    }
    if (numerator == 0) return 0;  /* the requested input catalog is connected */
    int common = gcd(numerator, denominator);
    printf("%s\t%d/%d\t", code, numerator/common, denominator/common);
    int matches = 0;
    for (int v = 0; v < n; ++v)
        if (cover[v] == full && minimum[v] * denominator < k * numerator) {
            printf("%s%d=%d", matches ? "," : "", v, minimum[v]);
            ++matches;
        }
    puts(matches ? "" : "-");
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fputs("usage: scan-spikes FILE.g6 ...\n", stderr);
        return EXIT_FAILURE;
    }
    for (int s = 1; s < MAX_MASK; ++s) {
        size[s] = size[s >> 1] + (s & 1);
        lowest[s] = (s & 1) ? 0 : 1 + lowest[s >> 1];
    }
    puts("graph6\th\tviolating_support=mass");
    for (int i = 1; i < argc; ++i) {
        FILE *file = fopen(argv[i], "r");
        if (!file) { perror(argv[i]); return EXIT_FAILURE; }
        char line[32];
        while (fgets(line, sizeof line, file)) {
            line[strcspn(line, "\r\n")] = 0;
            if (!scan(line)) {
                fprintf(stderr, "invalid or disconnected record in %s: %s\n", argv[i], line);
                fclose(file);
                return EXIT_FAILURE;
            }
        }
        if (ferror(file)) { perror(argv[i]); fclose(file); return EXIT_FAILURE; }
        fclose(file);
    }
    return ferror(stdout) ? EXIT_FAILURE : EXIT_SUCCESS;
}
