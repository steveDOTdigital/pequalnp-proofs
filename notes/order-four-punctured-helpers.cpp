// Retained flag graphs for the sole shared helper in case 9834.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstdio>
#include <vector>

using Mask = std::uint32_t;
using Neighbors = std::array<Mask, 19>;
using LinePoints = std::array<int, 5>;

const std::array<LinePoints, 19> lines = {{
    {2, 3, 6, 16, 18},
    {3, 4, 7, 17, 19},
    {4, 5, 8, 18, 20},
    {0, 5, 6, 9, 19},
    {1, 6, 7, 10, 20},
    {0, 2, 7, 8, 11},
    {1, 3, 8, 9, 12},
    {2, 4, 9, 10, 13},
    {3, 5, 10, 11, 14},
    {4, 6, 11, 12, 15},
    {5, 7, 12, 13, 16},
    {6, 8, 13, 14, 17},
    {7, 9, 14, 15, 18},
    {8, 10, 15, 16, 19},
    {9, 11, 16, 17, 20},
    {0, 10, 12, 17, 18},
    {1, 11, 13, 18, 19},
    {2, 12, 14, 19, 20},
    {0, 3, 13, 15, 20}
}};

int first(Mask x) { return __builtin_ctz(x); }
int count(Mask x) { return __builtin_popcount(x); }

int matching(const Neighbors& neighbors) {
    std::array<int, 21> mate;
    mate.fill(-1);
    auto augment = [&](auto& self, int line, Mask& seen) -> bool {
        for (Mask rest = neighbors[line]; rest; rest &= rest - 1) {
            int point = first(rest);
            Mask bit = Mask(1) << point;
            if (seen & bit) continue;
            seen |= bit;
            if (mate[point] < 0 || self(self, mate[point], seen)) {
                mate[point] = line;
                return true;
            }
        }
        return false;
    };
    int size = 0;
    for (int line = 0; line < 19; ++line) {
        Mask seen = 0;
        size += augment(augment, line, seen);
    }
    return size;
}

struct RankBound {
    Neighbors retained{};
    Mask points = 0, lines = 0;
    int edges = 0;

    void add(int point, int line) {
        retained[line] |= Mask(1) << point;
        points |= Mask(1) << point;
        lines |= Mask(1) << line;
        ++edges;
    }

    int isolated() const { return 40 - count(points) - count(lines); }
    int quick() const { return edges + (edges + 4) / 5 + isolated(); }
    int exact() const { return edges + matching(retained) + isolated(); }
};

void examine(bool lineSide) {
    int n = lineSide ? 19 : 21;
    std::array<Mask, 21> neighbors{}, nearby{};
    std::array<std::array<Mask, 21>, 21> through{};
    for (int line = 0; line < 19; ++line)
        for (int point : lines[line]) {
            int v = lineSide ? line : point, w = lineSide ? point : line;
            neighbors[v] |= Mask(1) << w;
        }
    for (int v = 0; v < n; ++v)
        for (int u = 0; u < n; ++u) {
            if (u == v) continue;
            Mask common = neighbors[v] & neighbors[u];
            if (!common) continue;
            if (count(common) != 1) std::abort();
            through[v][first(common)] |= Mask(1) << u;
            nearby[v] |= Mask(1) << u;
        }

    std::vector<int> minimum(n + 1, 200), surviving(n + 1, 0);
    for (Mask selected = 1; selected < (Mask(1) << n); ++selected) {
        int k = count(selected);
        if (k < 2) continue;
        std::array<RankBound, 3> bounds{};
        std::array<Mask, 21> omissions{};
        for (int v = 0; v < n; ++v) {
            Mask hit = 0;
            for (Mask a = neighbors[v]; a; a &= a - 1) {
                int w = first(a);
                if (through[v][w] & selected) hit |= Mask(1) << w;
            }
            // The first test retains flags whose ordinary cross contains a
            // selected input. The second can omit one flag to improve the
            // negatives for all the other flags of this center.
            Mask exchange = neighbors[v], alternative = neighbors[v];
            Mask distant = selected & ~(nearby[v] | (Mask(1) << v));
            if (!distant && hit != neighbors[v]) {
                if (!hit) std::abort();
                omissions[v] = hit;
                if (count(hit) + 1 == count(neighbors[v])) omissions[v] = neighbors[v];
                alternative &= ~(hit & -hit);
                if (count(hit) + 1 == count(neighbors[v])) exchange = hit;
                else exchange &= ~(hit & -hit);
            }
            std::array<Mask, 3> keep = {hit, exchange, alternative};
            for (int method = 0; method < 3; ++method)
                for (Mask a = keep[method]; a; a &= a - 1) {
                    int w = first(a);
                    bounds[method].add(lineSide ? w : v, lineSide ? v : w);
                }
        }
        int leaves = std::max({bounds[0].quick(), bounds[1].quick(), bounds[2].quick()});
        if (leaves < minimum[k] || leaves <= 112 - k)
            leaves = std::max({bounds[0].exact(), bounds[1].exact(), bounds[2].exact()});
        if (k >= 8 && leaves <= 112 - k) {
            // Favor the same omitted opposite vertex at several centers. Such
            // an isolated vertex still needs a leaf in the residual formula.
            int opposite = lineSide ? 21 : 19;
            for (int firstDrop = 0; firstDrop < opposite && leaves <= 112 - k; ++firstDrop) {
                for (int secondDrop = firstDrop; secondDrop < opposite && leaves <= 112 - k; ++secondDrop) {
                    RankBound candidate;
                    Mask preferred = (Mask(1) << firstDrop) | (Mask(1) << secondDrop);
                    for (int v = 0; v < n; ++v) {
                        Mask keep = neighbors[v];
                        if (omissions[v]) {
                            Mask choice = preferred & omissions[v];
                            if (!choice) choice = omissions[v];
                            keep &= ~(choice & -choice);
                        }
                        for (Mask a = keep; a; a &= a - 1) {
                            int w = first(a);
                            candidate.add(lineSide ? w : v, lineSide ? v : w);
                        }
                    }
                    leaves = std::max(leaves, candidate.exact());
                }
            }
        }
        minimum[k] = std::min(minimum[k], leaves);
        if (leaves <= 112 - k) ++surviving[k];
    }
    for (int k = 2; k <= n; ++k)
        std::printf("%s %d %d %d\n", lineSide ? "lines" : "points",
                    k, minimum[k], surviving[k]);
}

int main() {
    examine(false);
    examine(true);
}
