// Additional necessary conditions for a minimum circuit with fixed raw read counts.
// Included only by the 10-input Petersen profile search.
#pragma once

class PetersenProfileCuts {
    using RowPairs = std::bitset<3072>;
    std::array<Table,n> raw{};
    Table target{};
    std::array<int,n> quota{};
    std::array<Table,maxWires> zeroOn{};
    std::array<std::array<Table,5>,maxWires> slackBits{};
    std::array<RowPairs,maxWires> positive{}, negative{}, separates{};
    RowPairs selected{};
    bool monotone;

    // Bit A of this result says the function vanishes when only the vertices
    // in A may be selected. The upward closure visits all subsets in parallel.
    Table zeroRestrictions(Table v) const {
        for (int i = 0; i < n; ++i) v |= (v << (1<<i)) & raw[i];
        return ~v;
    }

    RowPairs distinction(int i) const {
        return monotone ? positive[i] & ~negative[i] : positive[i] ^ negative[i];
    }

    static RowPairs combine(int op, const RowPairs& a, const RowPairs& b) {
        // Consistent with signed wire normalization at the empty input.
        if (op == 3) return a | b;
        if (op == 2) return a & ~b;
        if (op == 1) return ~a & b;
        return a & b;
    }

public:
    explicit PetersenProfileCuts(bool monotoneOnly) : monotone(monotoneOnly) {}

    bool initialize(int budget, const std::array<int,n>& counts, const Table& goal,
                    const std::array<Table,maxWires>& wires, const std::array<int,1<<n>& lower) {
        target = goal;
        quota = counts;
        for (int v = 0; v < n; ++v) raw[v] = wires[v];
        for (int active = 0; active < (1<<n); ++active) {
            // The constant target on an edgeless induced graph has no output
            // path that needs to absorb pending constants.
            if (!target.test(active)) continue;
            int slack = budget - lower[active];
            for (int v = 0; v < n; ++v)
                if (!(active & (1<<v))) slack -= quota[v];
            if (slack < 0) return false;
            for (int j = 0; j < 5; ++j) slackBits[0][j].set(active, (slack>>j)&1);
        }

        int k = 0;
        for (int y = 0; y < (1<<n); ++y) if (!target.test(y)) {
            bool maximal = true;
            for (int v = 0; v < n; ++v)
                if (!(y & (1<<v)) && !target.test(y|(1<<v))) maximal = false;
            for (int x = 0; x < (1<<n); ++x) if (target.test(x)) {
                const int distance = __builtin_popcount(x^y);
                if (__builtin_popcount(x) != 2 && distance != 1 && !(maximal && distance == 2))
                    continue;
                if (k >= int(selected.size())) std::exit(19);
                selected.set(k);
                for (int v = 0; v < n; ++v) {
                    positive[v].set(k, (x>>v)&1);
                    negative[v].set(k, (y>>v)&1);
                }
                ++k;
            }
        }
        for (int v = 0; v < n; ++v) separates[v] = distinction(v);
        return true;
    }

    // A suffix can access the raw inputs still owed reads and each pending
    // gate once. Every other earlier gate it accesses spends an extra use.
    bool canSeparate(int wire, int a, int b, int op, unsigned pending,
                     const Readers& read, int remainingGates) {
        positive[wire] = combine(op, positive[a], positive[b]);
        negative[wire] = combine(op, negative[a], negative[b]);
        separates[wire] = distinction(wire);
        RowPairs missing = selected;
        int spare = remainingGates + 1 - __builtin_popcount(pending);
        for (int v = 0; v < n; ++v) {
            const int left = quota[v] - read[v][0] - read[v][1];
            spare -= left;
            if (left) missing &= ~separates[v];
        }
        for (unsigned m = pending; m; m &= m-1) missing &= ~separates[__builtin_ctz(m)];
        if (missing.none()) return true;
        if (spare <= 0) return false;
        RowPairs available{};
        for (int i = n; i < wire; ++i) if (!(pending & (1u<<i))) {
            const RowPairs other = missing & ~separates[i];
            if (other.none()) return true;
            if (spare == 2) for (int j = n; j < i; ++j)
                if (!(pending & (1u<<j)) && (other & ~separates[j]).none()) return true;
            available |= separates[i];
        }
        return spare > 2 && (missing & ~available).none();
    }

#if PETERSEN_PAIR_MODE == 4
    bool physicalSuffix(int z, int wire, unsigned pending, const Readers& read, int after,
                        const std::array<std::array<unsigned,2>,maxWires>& polarity,
                        unsigned usedPos, unsigned usedNeg) const {
        const unsigned bitZ=1u<<z;
        RowPairs missing=selected;
        int spare=after+1-__builtin_popcount(pending);
        auto covers = [&](int j, bool pos, bool neg) -> RowPairs {
            if (pos && neg) return positive[j] ^ negative[j];
            if (pos) return positive[j] & ~negative[j];
            if (neg) return negative[j] & ~positive[j];
            return RowPairs{};
        };
        for (int j=0; j<n; ++j) {
            const int left=quota[j]-read[j][0]-read[j][1];
            spare-=left;
            if (!left) continue;
            bool pos=true,neg=j==z;
#if FREE_RAW_REQUIRED
            if (j==z && quota[j]==2) {
                pos=!(usedPos & bitZ);
                neg=!(usedNeg & bitZ);
            }
#endif
            missing &= ~covers(j,pos,neg);
        }
        auto signal = [&](int j) {
            return covers(j,polarity[j][0]&bitZ,polarity[j][1]&bitZ);
        };
        for (unsigned m=pending; m; m &= m-1) missing &= ~signal(__builtin_ctz(m));
        if (missing.none()) return true;
        if (spare<=0) return false;
        RowPairs available{};
        for (int i=n; i<wire; ++i) if (!(pending & (1u<<i))) {
            RowPairs rest=missing & ~signal(i);
            if (rest.none()) return true;
            if (spare==2) for (int j=n; j<i; ++j) {
                if (!(pending & (1u<<j)) && (rest & ~signal(j)).none()) return true;
            }
            available |= signal(i);
        }
        return spare>2 && (missing & ~available).none();
    }
#endif

    // For each induced graph, charge each folded prefix gate, each future
    // pinned raw read and each still-unconsumed constant prefix signal.
    bool withinZeroBudgets(int wire, int a, int b, const Table& value, unsigned pendingBefore,
                           const std::array<Table,maxWires>& wires) {
        const int depth = wire - n;
        const Table zero = zeroRestrictions(value);
        zeroOn[wire] = zero;
        auto resource = [&](int i) -> Table {
            if (i < n) return ~raw[i];
            return (pendingBefore & (1u<<i)) ? zeroOn[i] : Table{};
        };
        const Table left = resource(a), right = resource(b);
        const Table any = left | right, both = left & right;
        const Table forced = zero & ~both & target;
        const Table twice = zero & ~any & target;
        const auto& slack = slackBits[depth];
        auto& next = slackBits[depth+1];
        const Table atMostOne = ~(slack[1] | slack[2] | slack[3] | slack[4]);
        const Table noneLeft = atMostOne & ~slack[0];
        if ((noneLeft & forced).any() || (atMostOne & twice).any()) return false;
        Table dropped = zero;
        for (int h = 0; h < wire; ++h) {
            dropped |= zeroRestrictions(value ^ wires[h]);
            if ((noneLeft & dropped & ~any & target).any()) return false;
        }
        // One or two units of slack may disappear. All 1,024 arithmetic
        // operations are performed in parallel on the five binary digits.
        Table borrow = ((dropped & ~any) | forced) & target;
        for (int i = 0; i < 5; ++i) {
            next[i] = slack[i] ^ borrow;
            borrow &= ~slack[i];
        }
        borrow = twice;
        for (int i = 0; i < 5; ++i) {
            const Table old = next[i];
            next[i] = old ^ borrow;
            borrow &= ~old;
        }
        return true;
    }
};
