// Exhaustive minimum-circuit search on all rows, with signed or monotone binary gates.
// Input contains a budget, the edge bit masks, and the permitted first gates.
// The driver supplies established lower bounds for every one-bit cofactor.
// Signed wires are normalized to false on the empty input: a NOR is stored as OR.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

#include <bitset>
using Table = std::bitset<(1u << WIDTH)>;
constexpr int n = WIDTH, maxWires = 26, domains = 2 * n + (SIGNED_MODE && n == 9 ? 9 : 0);
using Bounds = std::array<int, domains>;
using Needs = std::array<Table, n>;
using Readers = std::array<std::array<unsigned char, 2>, n>;

class Search {
    std::array<Table, maxWires> wires{}, good{};
    std::array<Table, domains> boundary{};
    std::array<std::array<std::array<bool,n>,n>,4> first{}, rawAllowed{};
    std::array<int, maxWires> lhs{}, rhs{}, op{};
    Table target = 0, global = 0;
    Bounds cap{};
    std::array<int,domains> pinA{}, pinB{};
    std::array<bool,domains> commonReader{};
    std::vector<std::array<int,3>> fixed;
    int budget, seconds;
    uint64_t nodes = 0;
    std::chrono::steady_clock::time_point start;
    bool expired = false;

    static Table bit(int row) { return Table(1) << row; }
    bool visit(int depth, int minA, int minB, const Bounds& lost, const Needs& needs, unsigned pending, const Readers& seen) {
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
                for (int isOr = 0; isOr < (SIGNED_MODE?4:2); ++isOr) {
                    if (depth < int(fixed.size()) && fixed[depth] != std::array<int,3>{isOr,a,b}) continue;
                    if (!depth && !first[isOr][a][b]) continue;
                    // Each gate on raw pins could be put first in a legal ordering.
                    if (b<n && !rawAllowed[isOr][a][b]) continue;
                    if (SIGNED_MODE && b >= n && (lhs[b-n] == a || rhs[b-n] == a)) continue;
                    Table val = isOr ? wires[a] | wires[b] : wires[a] & wires[b];
                    if (SIGNED_MODE) {
                        Table left = (isOr & 1) ? ~wires[a] : wires[a];
                        Table right = (isOr & 2) ? ~wires[b] : wires[b];
                        val = left & right;
                        if (val.test(0)) val.flip();
                    }
                    if (after == 0 && val != target && (!SIGNED_MODE || ~val != target)) continue;
                    Table correct = ~(val ^ target);
                    // The constants are also available by propagation for free.
                    if (SIGNED_MODE ? (val.none() || val.all()) :
                        ((correct & global & target).none() || (correct & global & ~target).none())) continue;
                    std::array<Table,maxWires> difference{};
                    bool admissible = true;
                    for (int h = 0; h < wire; ++h) {
                        difference[h] = SIGNED_MODE ? (val ^ wires[h]) : (correct & ~good[h]);
                        if (SIGNED_MODE ? (difference[h].none() || difference[h].all()) : (difference[h] & global).none()) { admissible = false; break; }
                    }
                    if (!admissible) continue;
                    Needs remaining{};
                    int mustRead = __builtin_popcount(nextPending);
                    for (int v = 0; v < n; ++v) {
                        remaining[v] = needs[v] & ~(val ^ (val >> (1<<v)));
                        mustRead += remaining[v].any();
                    }
                    if (mustRead > after+1) continue;
                    Readers readers = seen;
                    if (SIGNED_MODE) {
                        if (a < n) ++readers[a][isOr & 1];
                        if (b < n) ++readers[b][(isOr >> 1) & 1];
                        for (int v=0; v<n; ++v) {
                            int total=readers[v][0]+readers[v][1]+int(remaining[v].any());
                            for (int t=0; t<2; ++t) {
                                // Each forced reader needs a separate consumer from the
                                // direct readers. Two solely co-consumed forced signals
                                // would replace three gates by at most two.
                                int consumers=std::min(2,int(readers[v][t]));
                                if (total+consumers>cap[2*v+t]) admissible=false;
                            }
                        }
                        if (!admissible) continue;
                    }
                    Bounds dropped = lost;
                    for (int d = 0; d < domains; ++d) {
                        bool redundant = SIGNED_MODE ?
                            ((val & boundary[d]).none() || (~val & boundary[d]).none()) :
                            ((correct & boundary[d] & target).none() || (correct & boundary[d] & ~target).none());
                        for (int h = 0; h < wire && !redundant; ++h)
                            redundant = (difference[h] & boundary[d]).none() || (SIGNED_MODE && (~difference[h] & boundary[d]).none());
                        dropped[d] += redundant;
                        // The same raw bit still required in the suffix ensures
                        // another gate can be folded after this restriction.
                        int extra=remaining[pinA[d]].any();
                        if (pinB[d]>=0 && remaining[pinB[d]].any()
                            && (!extra || !commonReader[d])) ++extra;
                        if (dropped[d] + extra > cap[d]) {
                            admissible = false;
                            break;
                        }
                    }
                    if (!admissible) continue;
                    lhs[depth] = a; rhs[depth] = b; op[depth] = isOr;
                    wires[wire] = val; good[wire] = correct;
                    if (!after || visit(depth+1,a,b,dropped,remaining,nextPending,readers)) return true;
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
            for (int row=0; row<(1<<n); ++row) if ((e&row)==e) target |= bit(row);
        }
        for (int d=0; d<domains; ++d) {
            pinA[d]=d/2; pinB[d]=-1;
            if (d>=2*n) std::cin >> pinA[d] >> pinB[d];
            int lower; std::cin >> lower; cap[d]=budget-lower;
        }
        std::cin >> choices;
        while (choices--) {
            int o,a,b; std::cin >> o >> a >> b;
            first.at(o).at(a).at(b)=true;
        }
        std::cin >> choices;
        while (choices--) {
            int o,a,b; std::cin >> o >> a >> b;
            rawAllowed.at(o).at(a).at(b)=true;
        }
        for (int d=2*n; d<domains; ++d) {
            int a=pinA[d],b=pinB[d];
            if (a<0 || a>=b || b>=n) std::exit(2);
            for (int o=0; o<4; ++o) commonReader[d] |= rawAllowed[o][a][b];
            for (int r=0; r<(1<<n); ++r)
                if (!(r & ((1<<a)|(1<<b)))) boundary[d] |= bit(r);
        }
        int fixedSize;
        std::cin >> fixedSize;
        if (fixedSize < 0 || fixedSize > budget) std::exit(2);
        fixed.resize(fixedSize);
        for (auto& gate: fixed) std::cin >> gate[0] >> gate[1] >> gate[2];
        if (!std::cin) std::exit(2);
        Needs needs{};
        for (int r=0; r<(1<<n); ++r) {
            bool positive = (target & bit(r)) != 0;
            for (int v=0; v<n; ++v) {
                if (r & (1<<v)) wires[v] |= bit(r);
                else if (!positive && (target & bit(r|(1<<v))).any()) needs[v] |= bit(r);
            }
            for (int fixed=-1; fixed<n; ++fixed) {
                bool keep=true;
                for (int i=0; i<n; ++i) if (i!=fixed && bool(r&(1<<i))==positive) {
                    if ((target & bit(r^(1<<i))).any()==positive) { keep=false; break; }
                }
                if (keep || SIGNED_MODE) {
                    if (fixed<0) global |= bit(r);
                    else boundary[2*fixed+bool(r&(1<<fixed))] |= bit(r);
                }
            }
        }
        for (int i=0;i<n;++i) good[i]=~(wires[i]^target);
        start=std::chrono::steady_clock::now();
        bool found=visit(0,0,1,Bounds{},needs,0,Readers{});
        if (found) {
            // Re-evaluate every truth row independently from the decoded gates.
            for (int r=0;r<(1<<n);++r) {
                std::array<bool,maxWires> values{};
                for (int i=0;i<n;++i) values[i]=r&(1<<i);
                for (int g=0;g<budget;++g) {
                    bool a=values[lhs[g]], b=values[rhs[g]];
                    if (SIGNED_MODE) {
                        a ^= bool(op[g]&1); b ^= bool(op[g]&2);
                        values[n+g]=(a && b) ^ (op[g]==3);
                    } else values[n+g]=op[g] ? (a || b) : (a && b);
                }
                if (values[n+budget-1]!=target.test(r)) std::exit(3);
            }
            for (int g=0;g<budget;++g)
                std::cout << op[g] << " " << lhs[g] << " " << rhs[g] << "\n";
        }
        std::cout << (found?"SAT":expired?"UNKNOWN":"UNSAT") << " " << nodes << "\n";
    }
};

int main() { Search search; search.run(); }
