// Exhaustive search for fan-in-two monotone circuits on one-hot pairs.
// Compile with c++ -O3 -std=c++17. Run with order, gate budget, and seconds.
// An optional "baseline" omits the antichain and rectangle cuts.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

using Word = std::uint64_t;
using Pool = std::vector<Word>;
using Clock = std::chrono::steady_clock;
using ByteMap = std::array<Word, 256>;
using Operation = std::array<Word, 3>;

int bits(Word w) { return __builtin_popcountll(w); }

struct Hash {
    size_t operator()(const Pool& pool) const {
        size_t h = 0;
        for (Word w : pool) h ^= w + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
        return h;
    }
};

struct Slice {
    Word domain;
    int lower;
    unsigned removed;
};

struct Search {
    int order, budget, seconds;
    bool baseline, limited = false;
    Clock::time_point start = Clock::now();
    unsigned visits = 0, states = 0;
    Word positives = 0, negatives = 0;
    Pool raw;
    std::vector<std::vector<ByteMap>> maps;
    std::vector<std::array<int, 6>> permutations;
    std::vector<Slice> slices;
    std::vector<std::unordered_set<Pool, Hash>> seen;
    std::vector<Operation> prefix;

    Search(int n, int k, int time, bool basic)
        : order(n), budget(k), seconds(time), baseline(basic), raw(2*n), seen(k+1) {
        for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) {
            Word bit = Word(1) << (i*n+j);
            (i == j ? negatives : positives) |= bit;
            raw[i] |= bit;
            raw[n+j] |= bit;
        }
        makeSlices();
        makeMaps();
    }

    void makeSlices() {
        // Only smaller orders may be used. Check them in ascending order.
        const int lower[] = {0, 0, 3, 7, 11, 15};
        int all = (1 << order) - 1;
        for (int left = 1; left <= all; ++left) for (int right = 1; right <= all; ++right) {
            if (left == all && right == all) continue;
            int shared = bits(left & right), extra = bits(left ^ right);
            if (shared < 2 || shared < order-2 || extra > 2) continue;
            Word domain = 0;
            for (int i = 0; i < order; ++i) if (left & (1 << i)) {
                for (int j = 0; j < order; ++j) if (right & (1 << j))
                    domain |= Word(1) << (i*order+j);
            }
            unsigned removed = (all^left) | ((all^right) << order);
            slices.push_back({domain, lower[shared]+extra, removed});
        }
        std::stable_sort(slices.begin(), slices.end(), [](auto a, auto b) { return a.lower > b.lower; });
    }

    void makeMaps() {
        std::vector<int> perm(order);
        for (int i = 0; i < order; ++i) perm[i] = i;
        do {
            for (bool transpose : {false, true}) {
                std::vector<ByteMap> table((order*order+7)/8);
                for (unsigned group = 0; group < table.size(); ++group) {
                    for (unsigned byte = 1; byte < 256; ++byte) {
                        int bit = 8*group+__builtin_ctz(byte);
                        Word mapped = 0;
                        if (bit < order*order) {
                            int i = perm[bit/order], j = perm[bit%order];
                            if (transpose) std::swap(i, j);
                            mapped = Word(1) << (i*order+j);
                        }
                        table[group][byte] = table[group][byte & (byte-1)] | mapped;
                    }
                }
                std::array<int, 6> p{};
                std::copy(perm.begin(), perm.end(), p.begin());
                permutations.push_back(p);
                maps.push_back(std::move(table));
            }
        } while (std::next_permutation(perm.begin(), perm.end()));
    }

    Pool representative(const Pool& pool) const {
        // A permutation may only map a vertex into its sorted signature class.
        // This still considers all ties, independently for each orientation.
        std::array<std::array<std::vector<unsigned>, 6>, 2> signature;
        for (int i = 0; i < order; ++i) for (Word w : pool) {
            unsigned row = bits(w & raw[i]), col = bits(w & raw[order+i]);
            unsigned diagonal = (w >> (i*(order+1))) & 1;
            signature[0][i].push_back((diagonal*8+row)*8+col);
            signature[1][i].push_back((diagonal*8+col)*8+row);
        }
        std::array<std::array<int, 6>, 2> rank{}, width{};
        for (int side = 0; side < 2; ++side) {
            for (int i = 0; i < order; ++i) {
                auto& v = signature[side][i];
                std::sort(v.begin(), v.end());
            }
            for (int i = 0; i < order; ++i) for (int j = 0; j < order; ++j) {
                rank[side][i] += signature[side][j] < signature[side][i];
                width[side][i] += signature[side][j] == signature[side][i];
            }
        }
        Pool best;
        for (unsigned h = 0; h < maps.size(); ++h) {
            int side = h%2;
            bool allowed = true;
            for (int i = 0; i < order; ++i) {
                int j = permutations[h][i], lo = rank[side][i];
                if (j < lo || j >= lo+width[side][i]) { allowed = false; break; }
            }
            if (!allowed) continue;
            Pool image;
            for (Word w : pool) {
                Word mapped = 0;
                for (const auto& chunk : maps[h]) { mapped |= chunk[w & 255]; w >>= 8; }
                image.push_back(mapped);
            }
            std::sort(image.begin(), image.end());
            if (best.empty() || image < best) best = std::move(image);
        }
        if (best.empty()) throw std::logic_error("missing representative");
        return best;
    }

    bool separates(const Pool& pool) const {
        for (int i = 0; i < order; ++i) {
            Word missing = positives, negative = Word(1) << (i*(order+1));
            for (Word w : pool) if (!(w & negative)) missing &= ~w;
            if (missing) return false;
        }
        return true;
    }

    bool treePossible(const Pool& pool) const {
        // Each unique separator forces a cell into its wire's leaf rectangle.
        std::array<Word, 32> rows{}, cols{};
        for (int j = 0; j < order; ++j) {
            Word negative = Word(1) << (j*(order+1)), one = 0, two = 0;
            for (Word w : pool) if (!(w & negative)) { two |= one & w; one |= w; }
            Word unique = one & ~two & positives;
            for (unsigned i = 0; i < pool.size(); ++i) if (!(pool[i] & negative)) {
                Word forced = unique & pool[i];
                if (forced) { rows[i] |= forced; cols[i] |= 1u << j; }
            }
        }
        for (unsigned i = 0; i < pool.size(); ++i) for (unsigned j = 0; j < i; ++j)
            if ((rows[i] & rows[j]) && (cols[i] & cols[j])) return false;
        return true;
    }

    static bool dominates(Word a, Word b, Word plus, Word minus) {
        return !(b & plus & ~a) && !(a & minus & ~b);
    }

    static Word output(Operation g) { return g[2] ? g[0]|g[1] : g[0]&g[1]; }

    bool slicePossible(const Pool& pool, int remaining) const {
        std::array<int, 12> uses{};
        for (int i = 0; i < 2*order; ++i) {
            uses[i] = std::find(pool.begin(), pool.end(), raw[i]) != pool.end();
            for (auto g : prefix) uses[i] += int(g[0] == raw[i]) + int(g[1] == raw[i]);
        }
        for (const auto& slice : slices) {
            int saved = 0;
            for (unsigned v = slice.removed; v; v &= v-1) saved += uses[__builtin_ctz(v)];
            if (budget-saved < slice.lower) return false;
            Word domain = slice.domain, plus = positives & domain, minus = negatives & domain;
            int constants = 0;
            Pool required;
            for (Word value : pool) {
                Word w = value & domain;
                if (!(w & plus) || (w & minus) == minus) { ++constants; continue; }
                bool free = false;
                for (Word z : raw) if (dominates(z, w, plus, minus)) { free = true; break; }
                if (!free) required.push_back(w);
            }
            int wanted = slice.lower+constants-remaining;
            if (wanted <= 0) continue;
            if (required.empty() || wanted > int(prefix.size())) return false;

            // Record one valid implementation for each distinct projected prefix wire.
            std::array<Word, 64> known{};
            std::array<unsigned, 64> dependencies{};
            int count = 0;
            known[count++] = 0;
            known[count++] = domain;
            for (Word w : raw) known[count++] = w & domain;
            auto index = [&](Word w) {
                return int(std::find(known.begin(), known.begin()+count, w)-known.begin());
            };
            for (unsigned i = 0; i < prefix.size(); ++i) {
                auto g = prefix[i];
                Word w = output(g) & domain;
                if (index(w) != count) continue;
                int a = index(g[0] & domain), b = index(g[1] & domain);
                if (a == count || b == count) throw std::logic_error("missing projected operand");
                known[count] = w;
                dependencies[count++] = dependencies[a] | dependencies[b] | (1u << i);
            }
            unsigned keep = 0;
            for (Word w : required) {
                bool found = false;
                unsigned best = 0;
                for (int i = 0; i < count; ++i) if (dominates(known[i], w, plus, minus)) {
                    unsigned candidate = keep | dependencies[i];
                    if (!found || bits(candidate) < bits(best)) { found = true; best = candidate; }
                }
                if (!found) throw std::logic_error("missing live projection");
                keep = best;
            }
            if (bits(keep) < wanted) return false;
        }
        return true;
    }

    bool search(const Pool& pool, int remaining) {
        if (++visits%8192 == 0 && Clock::now()-start >= std::chrono::seconds(seconds)) limited = true;
        if (limited) return false;
        if (std::find(pool.begin(), pool.end(), positives) != pool.end()) return true;
        if (!remaining || int(pool.size()) > remaining+1 || !separates(pool)) return false;
        if (!baseline && int(pool.size()) == remaining+1 && !treePossible(pool)) return false;
        if (!slicePossible(pool, remaining)) return false;
        if (!seen[remaining].insert(representative(pool)).second) return false;
        if (++states > 400000) { limited = true; return false; }

        for (unsigned i = 0; i < pool.size(); ++i) for (unsigned j = i+1; j < pool.size(); ++j) {
            for (bool join : {false, true}) {
                Word a = pool[i], b = pool[j], w = join ? a|b : a&b;
                if (!(w & positives) || (w & negatives) == negatives) continue;
                auto better = [&](Word v) { return dominates(v, w, positives, negatives); };
                if (std::any_of(raw.begin(), raw.end(), better) ||
                    std::any_of(pool.begin(), pool.end(), better)) continue;
                if (!baseline && std::any_of(prefix.begin(), prefix.end(),
                    [&](Operation old) { return better(output(old)); })) continue;
                prefix.push_back({a, b, join});
                if (w == positives) return true;
                Pool rest{w};
                for (unsigned x = 0; x < pool.size(); ++x) if (x != i && x != j) rest.push_back(pool[x]);
                auto supersedes = [&](Word old) { return dominates(w, old, positives, negatives); };
                unsigned forbid = baseline ? 0 : unsigned(supersedes(a)) + 2*unsigned(supersedes(b));
                bool clash = !baseline && std::any_of(rest.begin()+1, rest.end(), supersedes);
                for (unsigned keep = 0; !clash && keep < 4; ++keep) {
                    if (keep & forbid) continue;
                    Pool next = rest;
                    if (keep & 1) next.push_back(a);
                    if (keep & 2) next.push_back(b);
                    if (int(next.size()) <= remaining && search(next, remaining-1)) return true;
                    if (limited) { prefix.pop_back(); return false; }
                }
                prefix.pop_back();
            }
        }
        return false;
    }
};

int main(int argc, char** argv) {
    if (argc < 4 || argc > 5) return 2;
    int n = std::stoi(argv[1]), k = std::stoi(argv[2]), time = std::stoi(argv[3]);
    if (n < 2 || n > 6 || k < 1 || k > 24 || time < 1) return 2;
    bool baseline = argc == 5 && std::string(argv[4]) == "baseline";
    if (argc == 5 && !baseline) return 2;
    Search s(n, k, time, baseline);
    bool sat = s.search(s.raw, k);
    std::cout << "n " << n << " budget " << k << " " << (sat ? "SAT" : s.limited ? "LIMIT" : "UNSAT")
              << " states " << s.states << " visits " << s.visits << std::endl;
    if (sat) for (auto g : s.prefix) std::cout << g[0] << " " << g[1] << " " << g[2] << "\n";
    return s.limited ? 3 : 0;
}
