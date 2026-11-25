// Enumerate one bypass and one freely rewired binary gate in either order.
// Input is a stream of 24-gate templates from degenerate-pencil-search.py.
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Bits = std::uint64_t;
constexpr int sources = 20;
constexpr Bits goal = (Bits{1} << 20) - 1;
struct Gate { int op, a, b; };
using Values = std::array<Bits, 48>;

Bits eval(const Gate &g, const Values &w) {
    return g.op ? w[g.a] | w[g.b] : w[g.a] & w[g.b];
}

struct Search {
    const std::vector<Gate> &gates;
    int end;
    const Values &raw;
    std::uint64_t windows = 0;
    int bypass = -1, source = -1, edit = -1;
    Gate replacement{};

    Bits finish(Values &w, int start) const {
        for (int i = start; i < end; ++i)
            w[i] = i == bypass ? w[source] : eval(gates[i - sources], w);
        return w[end - 1];
    }

    bool run() {
        for (bypass = sources; bypass < end; ++bypass) {
            for (source = 0; source < bypass; ++source) {
                Values base = raw;
                if (finish(base, sources) == goal) {
                    edit = -1;
                    return true;
                }
                for (edit = sources; edit < end; ++edit) {
                    if (edit == bypass) continue;
                    // Clamp one wire at both extremes. Correlated repeated uses
                    // are recomputed together, including uses by the bypass.
                    Values changed = base;
                    changed[edit] = 0;
                    Bits low = finish(changed, edit + 1);
                    if ((low & ~goal) != 0) continue;
                    changed[edit] = ~Bits{0};
                    Bits high = finish(changed, edit + 1);
                    if ((goal & ~high) != 0) continue;
                    ++windows;
                    Bits care = low ^ high, on = goal & care;
                    for (int a = 0; a < edit; ++a) {
                        for (int b = a; b < edit; ++b) {
                            for (int op = 0; op < 2; ++op) {
                                Gate candidate{op, a, b};
                                if ((eval(candidate, base) & care) == on) {
                                    replacement = candidate;
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    void print_witness() const {
        auto remap = [&](int w) { return w == bypass ? source : w - (w > bypass); };
        std::cout << "Witness\n";
        for (int i = sources; i < end; ++i) {
            if (i == bypass) continue;
            Gate g = i == edit ? replacement : gates[i - sources];
            std::cout << g.op << " " << remap(g.a) << " " << remap(g.b) << "\n";
        }
        std::cout << "Output " << remap(end - 1) << "\n";
    }
};

int main() {
    Values raw{};
    for (int i = 0; i < sources; ++i)
        if (!(std::cin >> raw[i])) return 2;
    int count = 0;
    std::uint64_t windows = 0;
    for (int n; std::cin >> n;) {
        if (n != 24) throw std::runtime_error("unexpected template length");
        std::vector<Gate> gates(n);
        for (int i = 0; i < n; ++i) {
            auto &g = gates[i];
            if (!(std::cin >> g.op >> g.a >> g.b) || g.op < 0 || g.op > 1 ||
                g.a < 0 || g.b < 0 || g.a >= sources + i || g.b >= sources + i)
                throw std::runtime_error("invalid gate");
        }
        Search s{gates, sources + n, raw};
        Values initial = raw;
        if (s.finish(initial, sources) != goal) throw std::runtime_error("template fails");
        if (count == 0) {
            auto control = gates;
            control[2].op = 1 - control[2].op;
            control.push_back({0, sources + n - 1, 0});
            Search positive{control, sources + n + 1, raw};
            if (!positive.run()) throw std::runtime_error("repair control failed");
        }
        if (s.run()) {
            s.print_witness();
            return 0;
        }
        ++count;
        windows += s.windows;
    }
    std::cout << "Templates exhausted " << count << ", feasible windows " << windows << "\n";
}
