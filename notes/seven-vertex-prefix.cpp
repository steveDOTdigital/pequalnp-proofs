// Exact depth-first synthesis for a seven-variable monotone graph function.
// Input contains a budget, the edge bit masks, and the permitted first gates.
// The driver supplies the checked lower bounds for every one-bit cofactor.
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using Table = unsigned __int128;
constexpr int n = 7, maxWires = 25, domains = 14;
using Bounds = std::array<int, domains>;
using Needs = std::array<Table, n>;

class Search {
    std::array<Table, maxWires> wires{}, good{};
    std::array<Table, domains> boundary{};
    std::array<std::array<std::array<bool,n>,n>,2> first{};
    std::array<int, maxWires> lhs{}, rhs{}, op{};
    Table target = 0, global = 0;
    Bounds cap{};
    std::vector<std::array<int,3>> fixed;
    int budget, seconds;
    uint64_t nodes = 0;
    std::chrono::steady_clock::time_point start;
    bool expired = false;

    static Table bit(int row) { return Table(1) << row; }
    bool visit(int depth, int minA, int minB, const Bounds& lost, const Needs& needs, unsigned pending) {
        if ((++nodes & 4095) == 0 &&
            std::chrono::steady_clock::now() - start > std::chrono::seconds(seconds)) {
            expired = true;
            return false;
        }
        const int wire = n + depth, after = budget - depth - 1;
        for (int b = minB; b < wire; ++b) {
            for (int a = (b == minB ? minA : 0); a < b; ++a) {
                unsigned nextPending = (pending & ~(1u<<a) & ~(1u<<b)) | (1u<<wire);
                if (__builtin_popcount(nextPending) > after + 1) continue;
                for (int isOr = 0; isOr < 2; ++isOr) {
                    if (depth < int(fixed.size()) && fixed[depth] != std::array<int,3>{isOr,a,b}) continue;
                    if (!depth && !first[isOr][a][b]) continue;
                    Table val = isOr ? wires[a] | wires[b] : wires[a] & wires[b];
                    if (after == 0 && val != target) continue;
                    Table correct = ~(val ^ target);
                    // The constants are also available by propagation for free.
                    if (!(correct & global & target) || !(correct & global & ~target)) continue;
                    std::array<Table,maxWires> difference{};
                    bool admissible = true;
                    for (int h = 0; h < wire; ++h) {
                        difference[h] = correct & ~good[h];
                        if (!(difference[h] & global)) { admissible = false; break; }
                    }
                    if (!admissible) continue;
                    Needs remaining{};
                    int mustRead = __builtin_popcount(nextPending);
                    for (int v = 0; v < n; ++v) {
                        remaining[v] = needs[v] & ~(val ^ (val >> (1<<v)));
                        mustRead += remaining[v] != 0;
                    }
                    if (mustRead > after+1) continue;
                    Bounds dropped = lost;
                    for (int d = 0; d < domains; ++d) {
                        bool redundant = !(correct & boundary[d] & target) || !(correct & boundary[d] & ~target);
                        for (int h = 0; h < wire && !redundant; ++h)
                            redundant = !(difference[h] & boundary[d]);
                        dropped[d] += redundant;
                        // The same raw bit still required in the suffix ensures
                        // another gate can be folded after this restriction.
                        if (dropped[d] + (remaining[d/2] != 0) > cap[d]) {
                            admissible = false;
                            break;
                        }
                    }
                    if (!admissible) continue;
                    lhs[depth] = a; rhs[depth] = b; op[depth] = isOr;
                    wires[wire] = val; good[wire] = correct;
                    if (!after || visit(depth+1,a,b,dropped,remaining,nextPending)) return true;
                    if (expired) return false;
                }
            }
        }
        return false;
    }

public:
    void run() {
        int edges, choices;
        std::cin >> budget >> seconds >> edges;
        if (!std::cin || budget < 1 || n+budget > maxWires) std::exit(2);
        for (int i=0; i<edges; ++i) {
            int e; std::cin >> e;
            for (int row=0; row<128; ++row) if ((e&row)==e) target |= bit(row);
        }
        for (int& c: cap) { int lower; std::cin >> lower; c=budget-lower; }
        std::cin >> choices;
        while (choices--) {
            int o,a,b; std::cin >> o >> a >> b;
            first.at(o).at(a).at(b)=true;
        }
        int fixedSize;
        std::cin >> fixedSize;
        if (fixedSize < 0 || fixedSize > budget) std::exit(2);
        fixed.resize(fixedSize);
        for (auto& gate: fixed) std::cin >> gate[0] >> gate[1] >> gate[2];
        if (!std::cin) std::exit(2);
        Needs needs{};
        for (int r=0; r<128; ++r) {
            bool positive = (target & bit(r)) != 0;
            for (int v=0; v<n; ++v) {
                if (r & (1<<v)) wires[v] |= bit(r);
                else if (!positive && (target & bit(r|(1<<v)))) needs[v] |= bit(r);
            }
            for (int fixed=-1; fixed<n; ++fixed) {
                bool keep=true;
                for (int i=0; i<n; ++i) if (i!=fixed && bool(r&(1<<i))==positive) {
                    if (bool(target & bit(r^(1<<i)))==positive) { keep=false; break; }
                }
                if (keep) {
                    if (fixed<0) global |= bit(r);
                    else boundary[2*fixed+bool(r&(1<<fixed))] |= bit(r);
                }
            }
        }
        for (int i=0;i<n;++i) good[i]=~(wires[i]^target);
        start=std::chrono::steady_clock::now();
        bool found=visit(0,0,1,Bounds{},needs,0);
        if (found) {
            // Re-evaluate every truth row independently from the decoded gates.
            for (int r=0;r<128;++r) {
                std::array<bool,maxWires> values{};
                for (int i=0;i<n;++i) values[i]=r&(1<<i);
                for (int g=0;g<budget;++g) values[n+g]=op[g] ? values[lhs[g]]||values[rhs[g]] :
                                                               values[lhs[g]]&&values[rhs[g]];
                if (values[n+budget-1]!=bool(target & bit(r))) std::exit(3);
            }
            for (int g=0;g<budget;++g)
                std::cout << (op[g]?"OR ":"AND ") << lhs[g] << " " << rhs[g] << "\n";
        }
        std::cout << (found?"SAT":expired?"UNKNOWN":"UNSAT") << " " << nodes << "\n";
    }
};

int main() { Search search; search.run(); }
