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
constexpr int domains = 2*n + (PETERSEN_PAIR_MODE ? n*(n-1)/2 : (SIGNED_MODE && n==9 ? 9 : 0));
using Bounds = std::array<int, domains>;
using Needs = std::array<Table, n>;
using Readers = std::array<std::array<unsigned char, 2>, n>;

#if PETERSEN_PAIR_MODE >= 2
#include "petersen-profile-cuts.hpp"
#endif

class Search {
#if PETERSEN_PAIR_MODE >= 2
    PetersenProfileCuts cuts{PETERSEN_PAIR_MODE == 3};
    std::array<int,1<<n> circuitFloor{};
    std::array<unsigned,domains> constantWires{};
    Table minimalPos{}, maximalNeg{};
#endif
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
    int quotaTotal = 0;
    int rawQuota(int v) const {
        if (PETERSEN_PAIR_MODE >= 2) return 1 + ((repeatedRaw>>(2*v))&3u);
        return 1 + ((repeatedRaw>>v)&1u);
    }
#if PETERSEN_PAIR_MODE == 4
    // Bit z means this physical polarity is available when raw z has both signs.
    std::array<std::array<unsigned,2>,maxWires> polarities{};
    std::array<unsigned,maxWires> compatible{};
    std::array<Table,n> slicePos{}, sliceNeg{}, sensitiveLow{};
    std::array<unsigned,maxWires> usedPositive{}, usedNegative{};
    // The circuit remains monotone on each fixed-z slice. Replacing a gate
    // by an earlier physical wire can only help on these two boundaries.
    unsigned undominated(int wire, const Table& v, unsigned eligible) const {
        unsigned result = eligible;
        for (unsigned m = eligible; m; m &= m-1) {
            int z = __builtin_ctz(m);
            unsigned bitZ = 1u << z;
            bool inverted = (polarities[wire][0] & bitZ) == 0;
            const Table actual = inverted ? ~v : v;
            const Table need = actual & slicePos[z], avoid = ~actual & sliceNeg[z];
            bool replace = need.none() || avoid.none();
            for (int j = 0; j < wire && !replace; ++j) {
                if (polarities[j][0] & bitZ)
                    replace = ((need & ~wires[j]) | (avoid & wires[j])).none();
                if (!replace && (polarities[j][1] & bitZ))
                    replace = ((need & wires[j]) | (avoid & ~wires[j])).none();
            }
            if (replace) result &= ~bitZ;
        }
        return result;
    }
#endif
#if PETERSEN_PAIR_MODE == 3 || PETERSEN_PAIR_MODE == 4
    // When all deletion savings are already owed by direct readers, every
    // other gate must be indispensable on this vertex-deleted graph.
    std::array<std::array<Table,n>,n> pinnedPos{}, pinnedNeg{};
    bool neededAfterPin(int z, int wire, int a, int b, const Table& val) const {
        for (int v = 0; v < n; ++v) {
            if (v==a || v==b || rawQuota(v)!=cap[2*v]) continue;
            const auto& pos = pinnedPos[v][z];
            const auto& neg = pinnedNeg[v][z];
#if PETERSEN_PAIR_MODE == 4
            const unsigned bitZ=1u<<z;
            const bool inverted=(polarities[wire][0] & bitZ)==0;
            const Table value=inverted ? ~val : val;
#else
            const Table& value=val;
#endif
            const Table need=value & pos, avoid=~value & neg;
            if (need.none() || avoid.none()) return false;
            for (int j=0; j<wire; ++j) {
#if PETERSEN_PAIR_MODE == 4
                if ((polarities[j][1] & bitZ) &&
                    ((need & wires[j]) | (avoid & ~wires[j])).none()) return false;
                if (!(polarities[j][0] & bitZ)) continue;
#endif
                if (((need & ~wires[j]) | (avoid & wires[j])).none()) return false;
            }
        }
        return true;
    }
    void buildPinnedBoundaries() {
        for (int v=0; v<n; ++v) for (int z=0; z<n; ++z) {
            if (PETERSEN_PAIR_MODE==3 && z!=0) continue;
            for (int row=0; row<(1<<n); ++row) {
                if (row & (1<<v)) continue;
                bool on=target.test(row), boundaryRow=true;
                for (int i=0; i<n; ++i) {
                    if (i==v || (PETERSEN_PAIR_MODE==4 && i==z) ||
                        bool(row & (1<<i))!=on) continue;
                    if (target.test(row^(1<<i))==on) { boundaryRow=false; break; }
                }
                if (boundaryRow) (on ? pinnedPos[v][z] : pinnedNeg[v][z]).set(row);
            }
        }
    }
#endif
    uint64_t nodes = 0;
    std::chrono::steady_clock::time_point start;
    bool expired = false;

    static Table bit(int row) { return Table(1) << row; }
    std::array<signed char,maxWires> shareOk{};
    std::array<int,PETERSEN_PAIR_MODE >= 2 || (PETERSEN_PAIR_MODE && !SIGNED_MODE) ? (1<<n) : 1> formulaFloor{};

    // Seven twice-read inputs leave precisely one extra internal use in a
    // 17-gate raw circuit. Its shared wire has two uses and its cone is a tree.
    bool canBeOnlySharedWire(int h) {
        if (shareOk[h] >= 0) return shareOk[h];
        shareOk[h] = 0;
        for (int v = 0; v < n; ++v) {
            const int without = ((1<<n)-1) ^ (1<<v);
            if (budget - rawQuota(v) >= formulaFloor[without] - 1) continue;
            Table mask = ~wires[v];
            // A cofactor below its formula minimum must retain genuine sharing.
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
                if (SIGNED_MODE) {
                    const bool killed = (!a && !(op[j-n]&1)) || (!b && !(op[j-n]&2));
                    weight[j] = killed ? 0 : a+b;
                } else weight[j] = op[j-n] || (a && b) ? a+b : 0;
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
                if (PETERSEN_PAIR_MODE && quotaTotal == budget && (!SIGNED_MODE || PETERSEN_PAIR_MODE >= 2)) {
                    if (a >= n && !(pending & (1u<<a)) && !canBeOnlySharedWire(a)) continue;
                    if (b >= n && !(pending & (1u<<b)) && !canBeOnlySharedWire(b)) continue;
                }
                for (int isOr = 0; isOr < (SIGNED_MODE?4:2); ++isOr) {
                    if (PETERSEN_PAIR_MODE == 3 && isOr != 0 && isOr != 3) continue;
                    if (depth < int(fixed.size()) && fixed[depth] != std::array<int,3>{isOr,a,b}) continue;
                    if (!depth && !first[isOr][a][b]) continue;
                    // Each gate on raw pins could be put first in a legal ordering.
                    if (b<n && !rawAllowed[isOr][a][b]) continue;
                    if (SIGNED_MODE && b >= n && (lhs[b-n] == a || rhs[b-n] == a)) continue;
#if PETERSEN_PAIR_MODE == 4
                    const int sa = isOr & 1, sb = isOr >> 1, flip = isOr == 3;
                    polarities[wire][flip] = polarities[a][sa] & polarities[b][sb];
                    polarities[wire][!flip] = polarities[a][!sa] & polarities[b][!sb];
                    const unsigned viable = compatible[depth] &
                        (polarities[wire][0] | polarities[wire][1]);
                    if (!viable || (!after && !(viable & polarities[wire][0]))) continue;
                    compatible[depth+1] = viable;
#if FREE_RAW_REQUIRED
                    usedPositive[depth+1] = usedPositive[depth];
                    usedNegative[depth+1] = usedNegative[depth];
                    for (int v : {a,b}) {
                        if (v >= n || !(viable & (1u<<v))) continue;
                        bool inputSign = (v==a ? sa : sb) ^ flip ^
                            bool(polarities[wire][1] & (1u<<v));
                        (inputSign ? usedNegative : usedPositive)[depth+1] |= 1u<<v;
                        if (seen[v][0]+seen[v][1]+1 == rawQuota(v) &&
                            !((usedPositive[depth+1] & usedNegative[depth+1]) & (1u<<v)))
                            compatible[depth+1] &= ~(1u<<v);
                    }
                    if (!compatible[depth+1]) continue;
#endif
#endif
                    Table val = isOr ? wires[a] | wires[b] : wires[a] & wires[b];
                    if (SIGNED_MODE) {
                        Table left = (isOr & 1) ? ~wires[a] : wires[a];
                        Table right = (isOr & 2) ? ~wires[b] : wires[b];
                        val = left & right;
                        if (val.test(0)) val.flip();
                    }
#if PETERSEN_PAIR_MODE == 4
#if FREE_RAW_REQUIRED
                    // There is exactly one positive reader of the exceptional
                    // variable. On every rising target pair its physical output
                    // must rise: after cutting it, the other raw occurrence falls.
                    for (int v : {a,b}) {
                        if (v>=n || rawQuota(v)!=2 || !(compatible[depth+1] & (1u<<v))) continue;
                        bool outputSign=(polarities[wire][1] & (1u<<v)) != 0;
                        bool inputSign=(v==a ? sa : sb) ^ flip ^ outputSign;
                        if (!inputSign) {
                            const Table physical=outputSign ? ~val : val;
                            if ((sensitiveLow[v] & (physical | ~(physical >> (1<<v)))).any())
                                compatible[depth+1] &= ~(1u<<v);
                        } else {
                            // Replacing this sole negative literal by either
                            // constant eliminates its reader. Some minimal
                            // positive at v=0 and maximal negative at v=1 must
                            // therefore be lost by the two respective replacements.
                            const int other=v==a ? b : a;
                            const bool otherSign=(v==a ? sb : sa) ^ flip ^ outputSign;
                            const Table companion=otherSign ? ~wires[other] : wires[other];
                            const Table neutral=(outputSign ^ flip) ? ~companion : companion;
                            if ((neutral & slicePos[v] & ~wires[v]).none() ||
                                (neutral & sliceNeg[v] & wires[v]).none())
                                compatible[depth+1] &= ~(1u<<v);
                        }
                    }
#endif
                    compatible[depth+1] = undominated(wire,val,compatible[depth+1]);
                    if (__builtin_popcount(compatible[depth+1])<=3) {
                        for (unsigned m=compatible[depth+1]; m; m &= m-1) {
                            const int z=__builtin_ctz(m);
                            if (!neededAfterPin(z,wire,a,b,val)) compatible[depth+1] &= ~(1u<<z);
                        }
                    }
                    if (!compatible[depth+1]) continue;
#elif PETERSEN_PAIR_MODE == 3
                    if (!neededAfterPin(0,wire,a,b,val)) continue;
#endif
                    if (after == 0 && val != target && (!SIGNED_MODE || ~val != target)) continue;
#if PETERSEN_PAIR_MODE == 3
                    bool dominated = (val & minimalPos).none() || (~val & maximalNeg).none();
                    for (int j = 0; j < wire && !dominated; ++j)
                        dominated = ((val & ~wires[j] & minimalPos) | (~val & wires[j] & maximalNeg)).none();
                    if (dominated) continue;
#endif
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
                    if constexpr (SIGNED_MODE != 0 || PETERSEN_PAIR_MODE != 0) {
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
                                if (PETERSEN_PAIR_MODE >= 2) {
                                    if (rawQuota(v) + std::min(2,int(readers[v][0])) > cap[2*v]) admissible=false;
                                } else if (rawQuota(v)==2 && readers[v][0]) admissible=false;
                                futureSlots+=rawQuota(v)-used;
                            }
                            if (futureSlots+__builtin_popcount(nextPending)>after+1) admissible=false;
                        }
                        if (!admissible) continue;
                    }
                    Bounds dropped = lost;
                    for (int d = 0; d < domains; ++d) {
#if PETERSEN_PAIR_MODE >= 2
                        // All zero restrictions are handled together below.
                        if (d >= 2*n || !(d&1)) continue;
                        const bool constant = (val & boundary[d]).none() || (~val & boundary[d]).none();
                        if (constant) constantWires[d] |= 1u<<wire;
                        else constantWires[d] &= ~(1u<<wire);
#endif
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
#if PETERSEN_PAIR_MODE >= 2
                        extra += __builtin_popcount(nextPending & constantWires[d]);
#endif
                        if (dropped[d] + extra > cap[d]) {
                            admissible = false;
                            break;
                        }
                    }
                    if (!admissible) continue;
#if PETERSEN_PAIR_MODE >= 2
                    if (!cuts.canSeparate(wire,a,b,isOr,nextPending,readers,after)) continue;
#if PETERSEN_PAIR_MODE == 4
                    if (__builtin_popcount(compatible[depth+1])<=3) {
                        for (unsigned m=compatible[depth+1]; m; m &= m-1) {
                            int z=__builtin_ctz(m);
                            if (!cuts.physicalSuffix(z,wire,nextPending,readers,after,polarities,
                                                     usedPositive[depth+1],usedNegative[depth+1]))
                                compatible[depth+1] &= ~(1u<<z);
                        }
                        if (!compatible[depth+1]) continue;
                    }
#endif
                    if (!cuts.withinZeroBudgets(wire,a,b,val,pending,wires)) continue;
#endif
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
        if (PETERSEN_PAIR_MODE) {
            std::cin >> repeatedRaw;
            for (int v = 0; v < n; ++v) quotaTotal += rawQuota(v);
        }
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
        if (PETERSEN_PAIR_MODE >= 2 || (PETERSEN_PAIR_MODE && !SIGNED_MODE))
            for (int &floor : formulaFloor) std::cin >> floor;
#if PETERSEN_PAIR_MODE >= 2
        for (int &floor : circuitFloor) std::cin >> floor;
#endif
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
#if PETERSEN_PAIR_MODE >= 2
        std::array<int,n> counts{};
        for (int v = 0; v < n; ++v) counts[v] = rawQuota(v);
        if (!cuts.initialize(budget,counts,target,wires,circuitFloor)) {
            std::cout << "UNSAT 0" << std::endl;
            return;
        }
        if (PETERSEN_PAIR_MODE == 3) {
            for (int row = 0; row < (1<<n); ++row) {
                if (target.test(row) && __builtin_popcount(row)==2) minimalPos.set(row);
                if (target.test(row)) continue;
                bool maximal = true;
                for (int v = 0; v < n; ++v)
                    if (!(row & (1<<v)) && !target.test(row|(1<<v))) maximal=false;
                if (maximal) maximalNeg.set(row);
            }
        }
#endif
#if PETERSEN_PAIR_MODE == 4
        compatible[0] = (1u<<n)-1;
        for (int v = 0; v < n; ++v) {
            polarities[v] = {(1u<<n)-1,1u<<v};
#if FREE_RAW_REQUIRED
            if (rawQuota(v) < 2) compatible[0] &= ~(1u<<v);
#endif
            sensitiveLow[v]=~wires[v] & ~target & (target >> (1<<v));
            for (int row=0; row<(1<<n); ++row) {
                bool on=target.test(row), minimal=true;
                for (int i=0; i<n; ++i) {
                    if (i==v || bool(row & (1<<i))!=on) continue;
                    if (target.test(row^(1<<i))==on) { minimal=false; break; }
                }
                if (minimal) (on ? slicePos[v] : sliceNeg[v]).set(row);
            }
        }
#endif
#if PETERSEN_PAIR_MODE == 3 || PETERSEN_PAIR_MODE == 4
        buildPinnedBoundaries();
#endif
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
