// Independent order-ten replay. Build with c++ -O3 -std=c++17 [-fopenmp].
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
constexpr int N = 10, ALL = 1023;
using Mask = int;
using Key = std::uint64_t;
static unsigned char card[1024], first_vertex[1024];
alignas(64) static unsigned char contribution[8][64][1024];
static std::array<std::vector<int>, 6> by_size;

void initialize() {
    for (int s = 1; s <= ALL; ++s) {
        card[s] = static_cast<unsigned char>(card[s / 2] + s % 2);
        first_vertex[s] = static_cast<unsigned char>(s % 2 ? 0 : first_vertex[s / 2] + 1);
        if (card[s] <= 5) by_size[card[s]].push_back(s);
    }
    // graph6 payload chunk j spans the six edge positions 6j,...,6j+5.
    int pos = 0;
    for (int v = 1; v < N; ++v) for (int u = 0; u < v; ++u, ++pos) {
        int column = pos / 6, bit = 32 >> (pos % 6);
        for (int word = 0; word < 64; ++word) if (word & bit)
            for (int s = 0; s <= ALL; ++s)
                contribution[column][word][s] += ((s >> v) ^ (s >> u)) & 1;
    }
}

struct Graph {
    std::array<Mask, N> adj{};
    std::array<unsigned char, 1024> boundary{};
    int edges = 0, L = 0;  // L / 12 is the conjectured total

    explicit Graph(const std::string& code) {
        if (code.size() != 9 || code.front() != 'I') throw std::runtime_error("order/header");
        std::array<int, 8> words{};
        for (int i = 0; i < 8; ++i) {
            words[i] = int(code[i + 1]) - 63;
            if (words[i] < 0 || words[i] > 63) throw std::runtime_error("graph6 byte");
        }
        if (words[7] % 8) throw std::runtime_error("graph6 padding");
        for (int j = 0; j < 8; ++j) {
            const auto& part = contribution[j][words[j]];
            for (int m = 0; m <= ALL; ++m) boundary[m] += part[m];
        }
        for (int v = 1; v < N; ++v) for (int u = 0; u < v; ++u) {
            int t = v * (v - 1) / 2 + u;
            if (words[t / 6] & (32 >> (t % 6))) {
                adj[u] |= 1 << v;
                adj[v] |= 1 << u;
                ++edges;
            }
        }
        L = 600;
        for (int r = 1; r <= 5; ++r) {
            int least = 46;
            for (int s : by_size[r]) least = std::min(least, int(boundary[s]));
            L = std::min(L, 60 * least / r);
        }
        if (!L) throw std::runtime_error("disconnected input");
    }

    bool can_coexist(int a, int b) const {
        if (!(a & b) || card[a | b] <= 5) return false;
        // Direct edge form of the submodular difference, independent of screen.cpp.
        int crossing = 0, right = b & ~a;
        for (int t = a & ~b; t; t &= t - 1) crossing += card[adj[first_vertex[t]] & right];
        return 12 * (boundary[a | b] + 2 * crossing) < L;
    }

    bool search(int uncovered, const std::vector<int>& blocks) const {
        if (!uncovered) return true;
        std::array<int, N> incidence{};
        for (int b : blocks)
            for (int t = b & uncovered; t; t &= t - 1) ++incidence[first_vertex[t]];
        int pivot = first_vertex[uncovered];
        for (int t = uncovered; t; t &= t - 1) {
            int v = first_vertex[t];
            if (incidence[v] < incidence[pivot]) pivot = v;
        }
        if (!incidence[pivot]) return false;
        for (int a : blocks) if (a & (1 << pivot)) {
            int rest = uncovered & ~a;
            if (!rest) return true;
            std::vector<int> children;
            for (int b : blocks)
                if ((b & rest) && can_coexist(a, b)) children.push_back(b);
            if (search(rest, children)) return true;
        }
        return false;
    }

    unsigned char status() const {
        int covered = 0;
        std::vector<int> blocks;
        for (int r : {4, 3}) for (int s : by_size[r])
            if (12 * boundary[s] < L) { covered |= s; blocks.push_back(s); }
        if (covered != ALL) return 0;
        return search(ALL, blocks) ? 2 : 1;
    }

    // Verify every branch of the supplied negative proof. A node gives a vertex
    // still needing coverage. Its children exhaust the possible sets through it.
    bool verify_tree(int remaining, const std::vector<int>& pool,
                     const std::vector<unsigned char>& proof, std::size_t& cursor) const {
        if (!remaining || cursor == proof.size()) return false;
        unsigned v = proof[cursor++];
        if (v >= N || !(remaining & (1 << v))) return false;
        for (int a : pool) if (a & (1 << v)) {
            int rest = remaining & ~a;
            std::vector<int> next;
            for (int b : pool) if ((b & rest) && can_coexist(a, b)) next.push_back(b);
            if (!verify_tree(rest, next, proof, cursor)) return false;
        }
        return true;
    }

    bool certified(unsigned char result, const std::vector<unsigned char>& proof) const {
        if (result == 2) return proof.empty();
        std::vector<int> pool;
        for (int a = 1; a < ALL; ++a)
            if ((card[a] == 3 || card[a] == 4) && 12 * boundary[a] < L) pool.push_back(a);
        std::size_t cursor = 0;
        return verify_tree(ALL, pool, proof, cursor) && cursor == proof.size();
    }
};

// An ordered partition is refined only by isomorphism-invariant counts.
// The ordered children of a cell are always contiguous and never exchange places.
struct Partition {
    std::array<Mask, N> cells{};
    int length = 0;
    void append(Mask s) { cells[length++] = s; }
};

Partition refine(const Graph& g, Partition p) {
    for (;;) {
        int previous = p.length;
        Partition splitters = p;
        for (int i = 0; i < previous && p.length < N; ++i) {
            int splitter = splitters.cells[i];
            Partition next;
            for (int j = 0; j < p.length; ++j) {
                int cell = p.cells[j];
                if (!(cell & (cell - 1))) { next.append(cell); continue; }
                std::array<Mask, N + 1> buckets{};
                int used = 0;
                for (int t = cell; t; t &= t - 1) {
                    int v = first_vertex[t], count = card[g.adj[v] & splitter];
                    buckets[count] |= 1 << v;
                    used |= 1 << count;
                }
                // In a simple ten-vertex graph the count is always at most nine.
                for (int t = used; t; t &= t - 1) next.append(buckets[first_vertex[t]]);
            }
            p = next;
        }
        if (p.length == previous || p.length == N) return p;
    }
}

struct Orbit { Key key; int automorphisms; };

Orbit canonical(const Graph& g, Partition p) {
    p = refine(g, p);
    if (p.length == N) {
        Key code = 0;
        for (int j = 1; j < N; ++j) {
            int neighbors = g.adj[first_vertex[p.cells[j]]];
            for (int i = 0; i < j; ++i) code = 2 * code + bool(neighbors & p.cells[i]);
        }
        return {code, 1};
    }
    int cell_index = -1;
    for (int i = 0; i < p.length; ++i) {
        if (card[p.cells[i]] > 1 &&
            (cell_index == -1 || card[p.cells[i]] < card[p.cells[cell_index]])) cell_index = i;
    }
    int cell = p.cells[cell_index];
    Orbit best{UINT64_MAX, 0};
    for (int untried = cell; untried;) {
        int v = first_vertex[untried], bit = 1 << v, twins = bit;
        // Swapping indistinguishable twins in this cell is an automorphism fixing the rest.
        for (int t = untried & ~bit; t; t &= t - 1) {
            int w = first_vertex[t];
            if (!((g.adj[v] ^ g.adj[w]) & ~(bit | (1 << w)))) twins |= 1 << w;
        }
        untried &= ~twins;
        Partition child;
        for (int j = 0; j < p.length; ++j) {
            if (j == cell_index) { child.append(bit); child.append(cell ^ bit); }
            else child.append(p.cells[j]);
        }
        Orbit result = canonical(g, child);
        result.automorphisms *= card[twins];
        if (result.key < best.key) best = result;
        else if (result.key == best.key) best.automorphisms += result.automorphisms;
    }
    return best;
}

Key connected_labeled() {
    std::array<Key, N + 1> connected{};
    for (int n = 1; n <= N; ++n) {
        connected[n] = Key(1) << (n * (n - 1) / 2);
        Key choose = 1;
        for (int k = 1; k < n; ++k) {
            int rest = n - k;
            connected[n] -= choose * connected[k] * (Key(1) << (rest * (rest - 1) / 2));
            choose = choose * (n - k) / k;
        }
    }
    return connected[N];
}

void write_order(std::ostream& out, unsigned value) {
    while (value >= 128) { out.put(char(128 | (value & 127))); value >>= 7; }
    out.put(char(value));
}

bool read_tree(std::istream& in, std::vector<unsigned char>& proof) {
    std::uint64_t length = 0;
    for (unsigned shift = 0; shift < 32; shift += 7) {
        int value = in.get();
        if (value < 0) return false;
        length |= std::uint64_t(value & 127) << shift;
        if (!(value & 128)) {
            if (length > UINT32_MAX) return false;
            proof.resize(static_cast<std::size_t>(length));
            return !length || bool(in.read(reinterpret_cast<char*>(proof.data()),
                                           static_cast<std::streamsize>(length)));
        }
    }
    return false;
}
}  // namespace

int main(int argc, char** argv) {
    if (argc != 5) {
        std::cerr << "usage: audit INPUT.g6 CUT_CERTIFICATES.bin COVER_PROOFS.bin AUT_ORDERS.bin\n";
        return 1;
    }
    initialize();
    std::ifstream src(argv[1]), statuses(argv[2], std::ios::binary);
    std::ifstream trees(argv[3], std::ios::binary);
    std::ofstream orders(argv[4], std::ios::binary);
    if (!src || !statuses || !orders || !trees) return 2;
    std::vector<Key> keys;
    keys.reserve(11716571);
    std::vector<std::string> batch(4096);
    std::array<unsigned char, 8192> expected{};
    std::array<unsigned char, 4096> result{};
    std::array<int, 4096> edge{}, level{};
    std::array<Orbit, 4096> orbit{};
    std::vector<std::vector<unsigned char>> proof(batch.size());
    Key labeled = 0, proof_nodes = 0;
    std::size_t longest_proof = 0;
    std::array<Key, 3> totals{};
    while (src) {
        int count = 0;
        while (count < int(batch.size()) && std::getline(src, batch[count])) {
            if (!batch[count].empty() && batch[count].back() == '\r') batch[count].pop_back();
            ++count;
        }
        if (!statuses.read(reinterpret_cast<char*>(expected.data()), 2 * count)) return 3;
        for (int i = 0; i < count; ++i) if (!read_tree(trees, proof[i])) return 3;
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
        for (int i = 0; i < count; ++i) {
            try {
                Graph g(batch[i]);
                int entry = expected[2*i] + 256 * expected[2*i+1], t = entry & ALL;
                if (!t || card[t] > 5 || 60 * g.boundary[t] != g.L * card[t])
                    throw std::runtime_error("incorrect minimizing cut");
                result[i] = g.status();
                if (!g.certified(result[i], proof[i])) throw std::runtime_error("bad cover proof");
                edge[i] = g.edges;
                level[i] = g.L;
                Partition start; start.append(ALL);
                orbit[i] = canonical(g, start);
            } catch (const std::exception&) {
                result[i] = 255;
            }
        }
        for (int i = 0; i < count; ++i) {
            int entry = expected[2*i] + 256 * expected[2*i+1];
            if (result[i] > 2 || result[i] != (entry >> 10)) {
                std::cerr << "bad input, minimizing cut, status or cover proof for " << batch[i] << '\n'; return 4;
            }
            if (orbit[i].automorphisms <= 0 || 3628800 % orbit[i].automorphisms) return 5;
            if (result[i] == 2)
                std::cout << "candidate " << keys.size() << ' ' << batch[i] << " edges=" << edge[i]
                          << " 12kh=" << level[i] << " key=" << orbit[i].key
                          << " aut=" << orbit[i].automorphisms << '\n';
            keys.push_back(orbit[i].key);
            write_order(orders, unsigned(orbit[i].automorphisms));
            labeled += 3628800 / orbit[i].automorphisms;
            proof_nodes += proof[i].size();
            longest_proof = std::max(longest_proof, proof[i].size());
            ++totals[result[i]];
        }
    }
    if (src.bad() || statuses.peek() != std::char_traits<char>::eof() || statuses.bad() ||
        trees.peek() != std::char_traits<char>::eof() || trees.bad() || !orders.flush()) return 6;
    std::sort(keys.begin(), keys.end());
    if (std::adjacent_find(keys.begin(), keys.end()) != keys.end()) {
        std::cerr << "duplicate isomorphism class\n"; return 7;
    }
    std::cout << "distinct connected classes=" << keys.size() << " labeled orbit sum=" << labeled
              << " recurrence=" << connected_labeled() << '\n';
    if (labeled != connected_labeled() || keys.size() != 11716571) return 8;
    std::cout << "verified refutation trees=" << (totals[0] + totals[1])
              << " pivot nodes=" << proof_nodes << " largest tree=" << longest_proof << '\n';
    std::cout << "no union=" << totals[0] << " no compatible cover=" << totals[1]
              << " candidates=" << totals[2] << "\nPASS\n";
    return 0;
}
