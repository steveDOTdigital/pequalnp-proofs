// Count optimal base circuits for two induced subgraphs of the cube, then
// test every eligible way to restore the missing input. Compile with C++17 -O3.
#include <array>
#include <bitset>
#include <cstdint>
#include <iostream>

template<int N>
class Lifts {
    using Table = std::bitset<(1 << N)>;
    using Sensitive = std::array<Table, N>;
    struct Gate { int left, right; bool isOr; };
    static constexpr int maxGates = 10;
    std::array<Table, N + maxGates> values{};
    std::array<Gate, maxGates> gates{};
    Table target, restored;
    Sensitive initial{};
    int budget, insertions;

    void test(unsigned ports) {
        // A restored OR is the identity at zero and is constant true at one.
        // Only the truth table with the restored input equal to one can differ.
        auto high = values;
        Table ones;
        ones.set();
        for (int i = 0; i < budget; ++i) {
            auto gate = gates[i];
            auto left = ports & (1u << (2*i)) ? ones : high[gate.left];
            auto right = ports & (2u << (2*i)) ? ones : high[gate.right];
            high[N+i] = gate.isOr ? (left | right) : (left & right);
        }
        ++lifts;
        matches += high[N+budget-1] == restored;
    }

    void record() {
        ++bases;
        if (!insertions) return;
        std::array<unsigned, N + maxGates> uses{};
        for (int i = 0; i < budget; ++i) {
            uses[gates[i].left] |= 1u << (2*i);
            uses[gates[i].right] |= 2u << (2*i);
        }
        for (int a = 0; a < (insertions == 1 ? N+budget-1 : N); ++a)
            for (unsigned u = uses[a]; u; u = (u-1) & uses[a]) {
                if (insertions == 1) {
                    test(u);
                    continue;
                }
                // At least one restored OR takes a raw input. Include each
                // unordered pair of distinct sources exactly once.
                for (int b = a+1; b < N+budget-1; ++b)
                    for (unsigned v = uses[b]; v; v = (v-1) & uses[b])
                        test(u | v);
            }
    }

    void enumerate(int depth, int minRight, int minLeft, unsigned unread,
                   const Sensitive& sensitive) {
        const int next = N + depth;
        const int leftAfter = budget - depth - 1;
        for (int b = minRight; b < next; ++b)
            for (int a = b == minRight ? minLeft : 0; a < b; ++a) {
                const unsigned pending = (unread & ~(1u<<a) & ~(1u<<b)) | (1u<<next);
                const int outputs = static_cast<int>(std::bitset<32>(pending).count());
                if (outputs > leftAfter+1) continue;
                for (int op = 0; op < 2; ++op) {
                    auto value = op ? (values[a] | values[b]) : (values[a] & values[b]);
                    gates[depth] = {a,b,op != 0};
                    if (leftAfter == 0) {
                        if (value == target) record();
                        continue;
                    }
                    // Each sensitive assignment still distinguishes an input
                    // that a later gate must read directly. These raw inputs
                    // and the unread gate outputs all need to reach the root.
                    Sensitive remaining;
                    int sources = outputs;
                    for (int i = 0; i < N; ++i) {
                        remaining[i] = sensitive[i] & ~(value ^ (value >> (1 << i)));
                        sources += remaining[i].any();
                    }
                    if (sources > leftAfter+1) continue;
                    values[next] = value;
                    enumerate(depth+1, b, a, pending, remaining);
                }
            }
    }

    static bool adjacent(int u, int v) {
        const int delta = u ^ v;
        return delta != 0 && (delta & (delta-1)) == 0;
    }

public:
    std::uint64_t bases = 0, lifts = 0, matches = 0;
    Lifts(int size, int restoreCount) : budget(size), insertions(restoreCount) {
        // Base vertices are 1..N. Restore vertex 7 to the six-cycle, or
        // vertex 0 to the seven-vertex cube with a corner removed.
        const int missing = N == 6 ? 7 : 0;
        for (int x = 0; x < (1 << N); ++x) {
            for (int i = 0; i < N; ++i) {
                values[i][x] = (x >> i) & 1;
                if (!values[i][x]) continue;
                if (adjacent(i+1,missing)) restored.set(x);
                for (int j = 0; j < i; ++j)
                    if ((x >> j & 1) && adjacent(i+1,j+1)) target.set(x);
            }
        }
        restored |= target;
        for (int i = 0; i < N; ++i)
            for (int x = 0; x < (1 << N); ++x)
                if (!(x >> i & 1) && !target[x] && target[x | (1<<i)]) initial[i].set(x);
    }

    void run() {
        enumerate(0, 1, 0, 0, initial);
        std::cout << N << " inputs, " << budget << " gates: " << bases
                  << " base sequences, " << lifts << " lifts, " << matches
                  << " matches" << std::endl;
    }
};

int main() {
    for (int s = 5; s < 8; ++s) {
        Lifts<6> small(s,0);
        small.run();
        if (small.bases) return 1;
    }
    Lifts<6> cycle(8,1);
    cycle.run();
    if (cycle.bases != 6 || cycle.lifts != 114 || cycle.matches) return 1;
    Lifts<7> deletion(10,2);
    deletion.run();
    if (deletion.bases != 48 || deletion.lifts != 10140 || deletion.matches) return 1;
}
