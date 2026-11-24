// Formula exclusions for the last OR of the nine-input Petersen circuit.
// With the first OR supplied as an input, a circuit with no further sharing
// unfolds to a formula. A formula with k binary gates has at most k+1 leaves.
// Test all twelve edge rows and all twelve maximal independent rows. A formula
// that works everywhere must separate these rows, as well as each additional
// independent row used below. The rectangle recurrence gives the minimum
// number of signed leaves that can separate the specified rows.
// Compile with c++ -O3 -std=c++20 notes/petersen-terminal-formulas.cpp.
#define PETERSEN_RECTANGLES_LIBRARY
#include "petersen-mixed-rectangles.cpp"

std::vector<Mask> maximalIndependentRows() {
    std::vector<Mask> rows;
    for (Mask x = 0; x < helper; ++x) {
        if (graph(x)) continue;
        bool maximal = true;
        for (int i = 0; i < variables; ++i)
            if (!(x & (1u << i)) && !graph(x | (1u << i))) maximal = false;
        if (maximal) rows.push_back(x);
    }
    return rows;
}

bool pin(Mask row, int index) {
    return index == 9 ? bool(row & 9u) : bool(row & (1u << index));
}

int main() {
    const auto boundary = maximalIndependentRows();
    if (boundary.size() != 12 || graph(100) || graph(386)) return 1;
    auto augmented = boundary;
    augmented.push_back(100);
    augmented.push_back(386);
    const Literals pos(positive, 9);
    const Literals neg(boundary, 9);
    if (boundaryMinimum(pos, neg, helper, 1023) != 16) return 2;
    for (int i = 0; i < 9; ++i) {
        unsigned signs = helper | (1u << i);
        int initial = boundaryMinimum(pos, neg, signs, 1023);
        int strengthened = i == 4 ? boundaryMinimum(pos, Literals(augmented,9), signs,1023) : initial;
        std::cout << "raw inversion " << i << ": " << initial << " -> " << strengthened << std::endl;
        if (strengthened != 16) return 3;
    }
    // Give a binary gate and its complement for free. Only twelve other
    // binary gates remain after paying for the prescribed OR, this gate and
    // the NOT. An unshared remaining circuit has at most thirteen leaves.
    int excluded = 0, unresolved = 0;
    for (int a = 0; a < 10; ++a) {
        for (int b = a+1; b < 10; ++b) {
            for (int isOr = 0; isOr < 2; ++isOr) {
                std::string cut(512, '0');
                for (Mask r = 0; r < 512; ++r) {
                    bool x = pin(r,a), y = pin(r,b);
                    cut[r] = (isOr ? x || y : x && y) ? '1' : '0';
                }
                const Literals cutPos(positive,9,cut);
                int bound = boundaryMinimum(cutPos, Literals(boundary,9,cut), 3*helper);
                if (bound <= 13)
                    bound = boundaryMinimum(cutPos, Literals(augmented,9,cut), 3*helper);
                if (bound <= 13 && isOr) {
                    // These four pairs form one orbit under the graph symmetries
                    // preserving the first OR. Each extra row is independent.
                    const std::vector<std::pair<Mask,Mask>> witnesses = {
                        {66,40},{132,257},{160,10},{320,5}
                    };
                    for (auto [pair,row] : witnesses) {
                        if (pair != ((1u<<a) | (1u<<b))) continue;
                        if (graph(row)) return 4;
                        auto extra = boundary;
                        extra.push_back(row);
                        bound = boundaryMinimum(cutPos, Literals(extra,9,cut), 3*helper);
                    }
                }
                if (bound > 13) ++excluded;
                else {
                    ++unresolved;
                    std::cout << "unresolved " << a << ' ' << b << ' ' << (isOr ? "OR" : "AND")
                              << " boundary cost " << bound << std::endl;
                }
            }
        }
    }
    std::cout << "binary cuts excluded " << excluded << " unresolved " << unresolved << std::endl;
    return excluded == 90 && unresolved == 0 ? 0 : 5;
}
