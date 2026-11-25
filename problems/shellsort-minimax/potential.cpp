// Full Boolean lattice, descending topological order, no first-pass compression.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Mask = std::uint32_t;
struct Pass {
    int gap;
    std::vector<Mask> residues, predecessors;
    std::vector<std::vector<Mask>> prefixes;
    std::vector<unsigned> counts;
    Mask input{};
    Pass(unsigned n, int h) : gap(h), residues(h), predecessors(n), prefixes(h), counts(h) {
        for (int r = 0; r < h; ++r) {
            prefixes[r].push_back(0);
            for (unsigned i = r; i < n; i += h) {
                predecessors[i] = residues[r];
                residues[r] |= Mask{1} << i;
                prefixes[r].push_back(residues[r]);
            }
        }
    }
    Mask project(Mask s) {
        input = s;
        Mask out = 0;
        for (int r = 0; r < gap; ++r) {
            counts[r] = std::popcount(s & residues[r]);
            out |= prefixes[r][counts[r]];
        }
        return out;
    }
};

int main(int argc, char** argv) {
    if (argc < 3) throw std::invalid_argument("potential n gaps... [--save output]");
    const unsigned n = std::stoul(argv[1]);
    if (n < 2 || n > 30) throw std::invalid_argument("supported sizes 2..30");
    std::vector<Pass> passes;
    std::string output;
    for (int i = 2; i < argc; ++i) {
        if (std::string(argv[i]) == "--save" && i + 2 == argc) {
            output = argv[++i]; break;
        }
        int h = std::stoi(argv[i]);
        if (h < 1 || h >= (passes.empty() ? int(n) : passes.back().gap))
            throw std::invalid_argument("illegal gap");
        passes.emplace_back(n,h);
    }
    if (passes.empty() || passes.back().gap != 1) throw std::invalid_argument("missing final 1");
    const Mask full = (Mask{1} << n)-1;
    std::vector<std::uint16_t> budget(full+1,0);
    std::uint64_t edges = 0;
    for (Mask s = full; s-- > 0;) {
        Mask a = s;
        for (Pass& p : passes) a = p.project(a);
        unsigned high = 0;
        for (Mask rest = full ^ s; rest; rest &= rest-1) {
            Mask bit = rest & -rest;
            unsigned x = std::countr_zero(bit);
            unsigned cost = 0;
            for (const Pass& p : passes) {
                unsigned small = std::popcount(p.input & p.predecessors[x]);
                cost += x / p.gap - small + (small != 0);
                unsigned r = x % p.gap;
                x = r + p.gap * p.counts[r];
            }
            high = std::max(high, cost + budget[s | bit]);
            ++edges;
        }
        // At most (n-1)*binom(n,2) comparisons, below 65536 for every supported n.
        budget[s] = static_cast<std::uint16_t>(high);
    }
    if (!output.empty()) {
        std::ofstream f(output,std::ios::binary);
        for (unsigned v : budget) { f.put(char(v & 255)); f.put(char(v >> 8)); }
        f.close();
        if (!f) throw std::runtime_error("cannot write potential");
    }
    std::cout << "n=" << n << " gaps=";
    for (const Pass& p : passes) std::cout << p.gap << ",";
    std::cout << " states=" << budget.size() << " edges=" << edges << " max=" << budget[0] << "\n";
}
