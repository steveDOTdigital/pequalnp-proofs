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
#ifndef PETERSEN_PAIR_MODE
#define PETERSEN_PAIR_MODE 0
#endif
constexpr int n = WIDTH, maxWires = PETERSEN_PAIR_MODE ? 32 : 26;
constexpr int domains = 2*n + (PETERSEN_PAIR_MODE ? 45 : (SIGNED_MODE && n==9 ? 9 : 0));
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
    unsigned repeatedRaw = 0;
    int rawQuota(int v) const { return 1 + ((repeatedRaw>>v)&1u); }
    uint64_t nodes = 0;
    std::chrono::steady_clock::time_point start;
    bool expired = false;

    static Table bit(int row) { return Table(1) << row; }
    std::array<signed char,maxWires> shareOk{};
    std::array<int,PETERSEN_PAIR_MODE && !SIGNED_MODE ? (1<<n) : 1> formulaFloor{};

    // Seven twice-read inputs leave precisely one extra internal use in a
    // 17-gate raw circuit. Its shared wire has two uses and its cone is a tree.
    bool canBeOnlySharedWire(int h) {
        if (shareOk[h] >= 0) return shareOk[h];
        shareOk[h] = 0;
        for (int v = 0; v < n; ++v) {
            if (rawQuota(v) != 2) continue;
            Table mask = ~wires[v];
            // The 9-input cofactor needs 16 binary gates as a formula.
            // Two direct readers vanish, leaving at most 15 gates. If h
            // becomes an input or a constant the cofactor has no sharing.
            if ((wires[h] & mask).none() || (~wires[h] & mask).none()) return false;
            for (int j = 0; j < n; ++j)
                if (((wires[j] ^ wires[h]) & mask).none()) return false;
        }
        std::array<int,n> leaves{};
        std::vector<int> stack{h};
        while (!stack.empty()) {
            const int j = stack.back();
            stack.pop_back();
            if (j < n) ++leaves[j];
            else {
                stack.push_back(lhs[j-n]);
                stack.push_back(rhs[j-n]);
            }
        }
        for (int mask = 1; mask < (1<<n); ++mask) {
            int outside = 0;
            for (int j = 0; j < n; ++j)
                if ((mask >> j) & 1) outside += rawQuota(j) - leaves[j];
            if (outside >= formulaFloor[mask]) continue;
            std::array<int,maxWires> weight{};
            for (int j = 0; j < n; ++j) weight[j] = (mask >> j) & 1;
            // Zero pins discard the other branch of an AND. For an OR all
            // surviving leaves are a valid upper bound after simplification.
            for (int j = n; j <= h; ++j) {
                const int a = weight[lhs[j-n]], b = weight[rhs[j-n]];
                weight[j] = op[j-n] || (a && b) ? a+b : 0;
            }
            if (outside + 2*weight[h] < formulaFloor[mask]) return false;
        }
        shareOk[h] = 1;
        return true;
    }

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
                if (PETERSEN_PAIR_MODE && !SIGNED_MODE && __builtin_popcount(repeatedRaw) == 7) {
                    if (a >= n && !(pending & (1u<<a)) && !canBeOnlySharedWire(a)) continue;
                    if (b >= n && !(pending & (1u<<b)) && !canBeOnlySharedWire(b)) continue;
                }
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
                    if (SIGNED_MODE || PETERSEN_PAIR_MODE) {
                        if (a < n) ++readers[a][isOr & 1];
                        if (b < n) ++readers[b][SIGNED_MODE ? ((isOr >> 1) & 1) : isOr];
                        for (int v=0; v<n; ++v) {
                            int total=readers[v][0]+readers[v][1]+int(remaining[v].any());
                            for (int t=0; t<2; ++t) {
                                // Each forced reader needs a separate consumer from the
                                // direct readers. Two solely co-consumed forced signals
                                // would replace three gates by at most two.
                                int consumers=SIGNED_MODE ? std::min(2,int(readers[v][t])) : int(readers[v][t]>0);
                                if (total+consumers>cap[2*v+t]) admissible=false;
                            }
                        }
                        if (PETERSEN_PAIR_MODE) {
                            int futureSlots=0;
                            for (int v=0; v<n; ++v) {
                                const int used=readers[v][0]+readers[v][1];
                                if (used+int(remaining[v].any())>rawQuota(v)) admissible=false;
                                if (rawQuota(v)==2 && readers[v][0]) admissible=false;
                                futureSlots+=rawQuota(v)-used;
                            }
                            if (futureSlots+__builtin_popcount(nextPending)>after+1) admissible=false;
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
                        if (PETERSEN_PAIR_MODE) {
                            int v=pinA[d], w=pinB[d];
                            extra=rawQuota(v)-readers[v][0]-readers[v][1];
                            if (w>=0) {
                                int more=rawQuota(w)-readers[w][0]-readers[w][1];
                                // At most one future gate can read both pinned sources.
                                // All raw-pair gates are ORs, and duplicates are redundant.
                                bool mayCombine=commonReader[d] && extra>0 && more>0;
                                if (mayCombine) {
                                    if ((a==v && b==w) || (a==w && b==v)) mayCombine=false;
                                    for(int j=0;j<depth && mayCombine;++j)
                                        if ((lhs[j]==v && rhs[j]==w) || (lhs[j]==w && rhs[j]==v)) mayCombine=false;
                                }
                                extra+=more-int(mayCombine);
                            }
                        }
                        if (dropped[d] + extra > cap[d]) {
                            admissible = false;
                            break;
                        }
                    }
                    if (!admissible) continue;
                    lhs[depth] = a; rhs[depth] = b; op[depth] = isOr;
                    shareOk[wire] = -1;
                    wires[wire] = val; good[wire] = correct;
                    bool restartOrder=PETERSEN_PAIR_MODE && depth+1==int(fixed.size());
                    if (!after || visit(depth+1,restartOrder ? 0 : a,restartOrder ? 1 : b,dropped,remaining,nextPending,readers)) return true;
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
        if(PETERSEN_PAIR_MODE) std::cin >> repeatedRaw;
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
        if (PETERSEN_PAIR_MODE && !SIGNED_MODE)
            for (int &floor : formulaFloor) std::cin >> floor;
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
