// Exact synthesis for the cube and one vertex deletion. C++17.
#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <iostream>

template<int N>
class Search {
    static constexpr int rows = 1 << N;
    using Table = std::bitset<rows>;
    using Needs = std::array<Table, N>;
    using Loss = std::array<int, N>;
    std::array<Table, N + 13> wires{}, correct{};
    std::array<Table, N> zeroSlices{};
    Table target, boundary;
    Needs initial{};
    int limit, cofactor;
    std::uint64_t visits = 0;

    static int vertex(int i) { return N == 7 ? i + 1 : i; }
    static bool adjacent(int a, int b) {
        int delta = vertex(a) ^ vertex(b);
        return delta && !(delta & (delta-1));
    }

    bool visit(int depth, int minB, int minA, unsigned pending,
               const Needs& needs, const Loss& lost) {
        ++visits;
        int wire = N + depth, after = limit - depth - 1;
        for (int b = minB; b < wire; ++b) {
            for (int a = b == minB ? minA : 0; a < b; ++a) {
                unsigned leaves = (pending & ~(1u << a) & ~(1u << b)) | (1u << wire);
                if (__builtin_popcount(leaves) > after + 1) continue;
                for (int isOr = 0; isOr <= 1; ++isOr) {
                    if (depth == 0 && N == 8) {
                        // One pair per possible Hamming distance in the cube.
                        if (a || (b != 1 && b != 3 && b != 7)) continue;
                    }
                    auto val = isOr ? (wires[a] | wires[b]) : (wires[a] & wires[b]);
                    if (!after && val != target) continue;
                    auto right = ~(val ^ target);
                    // A constant or an earlier wire can replace any gate it
                    // dominates on the minimal positives and maximal negatives.
                    if ((right & boundary & target).none() || (right & boundary & ~target).none()) continue;
                    bool discard = false;
                    for (int h = 0; h < wire && !discard; ++h)
                        discard = (right & boundary & ~correct[h]).none();
                    if (discard) continue;
                    Needs next;
                    int required = __builtin_popcount(leaves);
                    for (int v = 0; v < N; ++v) {
                        next[v] = needs[v] & ~(val ^ (val >> (1 << v)));
                        required += next[v].any();
                    }
                    if (required > after + 1) continue;
                    Loss dropped = lost;
                    if (cofactor) {
                        for (int v = 0; v < N; ++v) {
                            auto on = right & zeroSlices[v];
                            bool removable = (on & target).none() || (on & ~target).none();
                            for (int h = 0; h < wire && !removable; ++h)
                                removable = (on & ~correct[h]).none();
                            dropped[v] += removable;
                            if (limit - dropped[v] - int(next[v].any()) < cofactor) {
                                discard = true;
                                break;
                            }
                        }
                    }
                    if (discard) continue;
                    wires[wire] = val;
                    correct[wire] = right;
                    if (!after || visit(depth+1, b, a, leaves, next, dropped)) return true;
                }
            }
        }
        return false;
    }

public:
    Search(int budget, int pinnedLower) : limit(budget), cofactor(pinnedLower) {
        for (int x = 0; x < rows; ++x)
            for (int i = 0; i < N; ++i) {
                wires[i][x] = (x >> i) & 1;
                for (int j = 0; j < i; ++j)
                    if ((x >> i & x >> j & 1) && adjacent(i,j)) target.set(x);
            }
        for (int x = 0; x < rows; ++x) {
            for (int v = 0; v < N; ++v)
                if (!(x >> v & 1) && !target[x] && target[x | (1 << v)]) initial[v].set(x);
            for (int pin = -1; pin < N; ++pin) {
                if (pin >= 0 && (x >> pin & 1)) continue;
                bool extreme = true;
                for (int v = 0; v < N; ++v)
                    if (v != pin && bool(x >> v & 1) == target[x] &&
                        target[x ^ (1 << v)] == target[x]) extreme = false;
                if (extreme) (pin < 0 ? boundary : zeroSlices[pin]).set(x);
            }
        }
        for (int v = 0; v < N; ++v) correct[v] = ~(wires[v] ^ target);
    }
    bool run() {
        bool found = visit(0, 1, 0, 0, initial, Loss{});
        std::cout << N << " inputs, " << limit << " gates: "
                  << (found ? "SAT" : "UNSAT") << " (" << visits << " nodes)" << std::endl;
        return found;
    }
};

int main() {
    // A binary output depending on all N inputs needs at least N-1 gates.
    for (int size = 6; size <= 9; ++size)
        if (Search<7>(size, 0).run()) return 1;
    if (!Search<7>(10, 0).run()) return 1;
    for (int size = 7; size <= 12; ++size)
        if (Search<8>(size, 10).run()) return 1;
}
