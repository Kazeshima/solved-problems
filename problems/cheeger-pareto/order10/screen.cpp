// Exact necessary conditions for a counterexample over arbitrary real vectors.
// Build with c++ -O3 -std=c++17 [-fopenmp] screen.cpp -o screen.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
constexpr int n = 10, full = (1 << n) - 1;
std::array<int, 1024> size{}, lowest{};
std::vector<int> blocks;

struct Graph {
    std::array<int, n> adj{};
    std::array<int, 1024> cut{};
    int edges = 0, threshold = 0, minimizing_cut = 0;  // threshold is exactly 12 * 5 * h

    explicit Graph(const std::string& record) {
        if (record.size() != 9 || record[0] != 'I') throw std::runtime_error("bad graph6 record");
        for (char ch : record) if (ch < 63 || ch > 126) throw std::runtime_error("bad graph6 byte");
        if ((record.back() - 63) & 7) throw std::runtime_error("bad graph6 padding");
        int pos = 0;
        for (int v = 1; v < n; ++v) {
            for (int u = 0; u < v; ++u, ++pos) {
                if (((record[1 + pos / 6] - 63) >> (5 - pos % 6)) & 1) {
                    adj[u] |= 1 << v;
                    adj[v] |= 1 << u;
                    ++edges;
                }
            }
        }
    }

    void boundaries() {
        threshold = 60 * n;
        for (int s = 1; s < 512; ++s) {
            int v = lowest[s], rest = s & (s - 1);
            int c = cut[rest] + size[adj[v]] - 2 * size[adj[v] & rest];
            cut[s] = cut[full ^ s] = c;
            int small = std::min(size[s], n - size[s]);
            int value = (60 / small) * c;
            if (value < threshold) {
                threshold = value;
                minimizing_cut = size[s] <= 5 ? s : full ^ s;
            }
        }
    }

    bool compatible(int a, int b) const {
        int common = a & b;
        return common != 0 && size[a | b] > 5
            && 12 * (cut[a] + cut[b] - cut[common]) < threshold;
    }

    bool cover(int remaining, const std::vector<int>& pool,
               std::vector<unsigned char>& proof) const {
        if (!remaining) return true;
        int available = 0;
        for (int b : pool) available |= b;
        int missing = remaining & ~available;
        int pivot = lowest[missing ? missing : remaining];
        proof.push_back(static_cast<unsigned char>(pivot));
        if (missing) return false;
        int lead = 1 << pivot;
        for (int a : pool) if (a & lead) {
            int rest = remaining & ~a;
            if (!rest) return true;
            std::vector<int> next;
            for (int b : pool) if ((rest & b) && compatible(a, b)) {
                next.push_back(b);
            }
            if (cover(rest, next, proof)) return true;
        }
        return false;
    }

    int screen(std::vector<unsigned char>& proof) const {
        std::vector<int> pool;
        int union_mask = 0;
        for (int s : blocks) if (12 * cut[s] < threshold) {
            pool.push_back(s);
            union_mask |= s;
        }
        if (union_mask != full) {
            proof.push_back(static_cast<unsigned char>(lowest[full ^ union_mask]));
            return 0;
        }
        if (!cover(full, pool, proof)) return 1;
        proof.clear();
        return 2;
    }
};
}  // namespace

int main(int argc, char** argv) {
    if (argc != 5) {
        std::cerr << "usage: screen INPUT.g6 CUT_CERTIFICATES.bin CANDIDATES.tsv COVER_PROOFS.bin\n";
        return 1;
    }
    for (int s = 1; s <= full; ++s) {
        size[s] = size[s >> 1] + (s & 1);
        lowest[s] = (s & 1) ? 0 : 1 + lowest[s >> 1];
        if (size[s] == 3 || size[s] == 4) blocks.push_back(s);
    }
    std::ifstream src(argv[1]);
    std::ofstream statuses(argv[2], std::ios::binary), candidates(argv[3]);
    std::ofstream trees(argv[4], std::ios::binary);
    if (!src || !statuses || !candidates || !trees) return 2;
    std::array<std::array<uint64_t, 3>, 46> counts{};
    std::vector<std::string> batch(8192);
    std::array<unsigned char, 8192> verdict{};
    std::array<int, 8192> edges{}, target{}, minimizer{};
    std::array<unsigned char, 16384> records{};
    std::vector<std::vector<unsigned char>> proof(batch.size());
    uint64_t total = 0;
    candidates << "index\tgraph6\tedges\t12kh\n";
    while (src) {
        int count = 0;
        while (count < int(batch.size()) && std::getline(src, batch[count])) {
            if (!batch[count].empty() && batch[count].back() == '\r') batch[count].pop_back();
            ++count;
        }
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
        for (int i = 0; i < count; ++i) {
            try {
                Graph g(batch[i]);
                edges[i] = g.edges;
                g.boundaries();
                target[i] = g.threshold;
                minimizer[i] = g.minimizing_cut;
                proof[i].clear();
                verdict[i] = static_cast<unsigned char>(g.screen(proof[i]));
            } catch (const std::exception&) {
                verdict[i] = 255;
            }
        }
        for (int i = 0; i < count; ++i) {
            int code = verdict[i];
            if (code > 2) { std::cerr << "invalid graph at index " << total+i << '\n'; return 4; }
            int entry = minimizer[i] + 1024 * code;
            records[2*i] = static_cast<unsigned char>(entry & 255);
            records[2*i+1] = static_cast<unsigned char>(entry >> 8);
            std::size_t length = proof[i].size();
            while (length >= 128) {
                trees.put(static_cast<char>(128 | (length & 127)));
                length >>= 7;
            }
            trees.put(static_cast<char>(length));
            if (!proof[i].empty()) trees.write(reinterpret_cast<const char*>(proof[i].data()),
                                               static_cast<std::streamsize>(proof[i].size()));
            ++counts[edges[i]][code];
            if (code == 2) candidates << total + i << '\t' << batch[i] << '\t'
                                      << edges[i] << '\t' << target[i] << '\n';
        }
        statuses.write(reinterpret_cast<const char*>(records.data()), 2 * count);
        total += count;
    }
    if (src.bad() || !statuses.flush() || !candidates.flush() || !trees.flush()) return 3;
    std::cout << "edges\tno_union\tno_compatible_cover\tcandidate\n";
    for (int m = 0; m <= 45; ++m) {
        const auto& row = counts[m];
        if (row[0] || row[1] || row[2]) {
            std::cout << m;
            for (auto v : row) std::cout << '\t' << v;
            std::cout << '\n';
        }
    }
    std::cerr << total << " records\n";
}
