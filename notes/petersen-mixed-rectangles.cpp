// Lower bounds for signed formulas with one free OR on Petersen minus one vertex.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

using Mask = unsigned;
constexpr int variables = 9;
constexpr Mask helper = 1u << variables;
constexpr Mask allSignals = 4 * helper - 1;
const std::vector<Mask> positive = {3,6,12,24,17,33,66,132,264,160,320,288};

bool graph(Mask row) {
    return std::any_of(positive.begin(), positive.end(),
                       [row](Mask edge) { return (row & edge) == edge; });
}

struct Literals {
    std::vector<Mask> allOn, allOff;
    Literals(const std::vector<Mask>& rows, Mask pair, const std::string& cut = "")
        : allOn(1u << rows.size(), allSignals), allOff(allOn) {
        for (Mask set = 1; set < allOn.size(); ++set) {
            Mask row = rows[std::countr_zero(set)];
            if (!cut.empty() && cut[row] == '1') row |= 2 * helper;
            if (row & pair) row |= helper;
            const Mask rest = set & (set - 1);
            allOn[set] = allOn[rest] & row;
            allOff[set] = allOff[rest] & ~row;
        }
    }
};

// At an OR, partition the required positive rows. At an AND, partition
// the required negative rows. Both children must pass the opposite shore.
int boundaryMinimum(const Literals& pos, const Literals& neg, Mask signs, Mask allowed = allSignals) {
    const Mask h = pos.allOn.size(), w = neg.allOn.size();
    std::vector<uint8_t> cost(h * w, 18);
    for (Mask p = 1; p < h; ++p) {
        auto row = cost.data() + p * w;
        for (Mask n = 1; n < w; ++n)
            if ((allowed & pos.allOn[p] & neg.allOff[n]) || (signs & pos.allOff[p] & neg.allOn[n]))
                row[n] = 1;
        for (Mask a = (p - 1) & p; a > (p ^ a); a = (a - 1) & p) {
            auto l = cost.data() + a * w, r = cost.data() + (p ^ a) * w;
            for (Mask n = 1; n < w; ++n)
                row[n] = std::min(row[n], static_cast<uint8_t>(l[n] + r[n]));
        }
        for (Mask n = 1; n < w; ++n) {
            if (row[n] <= 2) continue;
            for (Mask b = (n - 1) & n; b > (n ^ b); b = (b - 1) & n)
                row[n] = std::min(row[n], static_cast<uint8_t>(row[b] + row[n ^ b]));
        }
    }
    return cost.back();
}

int main(int argc, char** argv) {
    std::vector<Mask> negative;
    constexpr int reflect[] = {0,5,8,3,4,1,7,6,2};
    for (Mask row = 0; row < helper; ++row) {
        Mask reflected = 0;
        for (int i = 0; i < variables; ++i)
            if (row & (1u << i)) reflected |= 1u << reflect[i];
        if (graph(row) != graph(reflected)) return 1;
        if (graph(row)) continue;
        bool maximal = true;
        for (int i = 0; i < variables; ++i)
            if (!(row & (1u << i)) && !graph(row | (1u << i))) maximal = false;
        if (maximal) negative.push_back(row);
    }
    if (negative.size() != 12 || positive.size() != 12) return 2;
    // Optional single-cut subproblem. The caller supplies one bit for each
    // of the 512 original rows, both raw polarity masks and the prescribed OR.
    if (argc == 5) {
        Mask pair = std::stoul(argv[1]), raws = std::stoul(argv[2]), signedRaws = std::stoul(argv[3]);
        std::string cut = argv[4];
        if (cut.size() != 512 || cut.find_first_not_of("01") != std::string::npos) return 8;
        std::cout << boundaryMinimum(Literals(positive,pair,cut), Literals(negative,pair,cut),
                                     signedRaws | 3*helper, raws | 3*helper) << std::endl;
        return 0;
    }
    if (argc != 1) return 10;
    for (int q : {2, 3, 8}) {
        const Mask pair = 2u | (1u << q);
        Mask eligible = pair;
        int covers = 0;
        for (Mask subset = 0; subset < helper; ++subset) {
            if (subset & pair || std::popcount(subset) > 3) continue;
            if (std::any_of(positive.begin(), positive.end(),
                            [=](Mask edge) { return !(edge & (pair | subset)); })) continue;
            if (std::popcount(subset) != 3) return 3;
            eligible |= subset;
            ++covers;
            std::cout << "pair 1 " << q << " minimum cover mask " << subset << '\n';
        }
        if (covers != (q == 8 ? 2 : 1)) return 4;
        for (Mask row = 0; row < helper; ++row) {
            auto x = [row](int i) { return bool(row & (1u << i)); };
            const bool u = row & pair;
            const bool star2 = x(2) && ((q == 3 ? u : (x(1) || x(3))) || x(7));
            const bool star6 = x(6) && (q == 8 ? u : (x(1) || x(8)));
            const bool result = (x(0) && (x(1)||x(4)||x(5))) || star2 ||
                (x(3) && (x(4)||x(8))) || (x(5) && (x(7)||x(8))) || star6;
            if (result != graph(row)) return 5;
        }
        Literals pos(positive, pair), neg(negative, pair);
        for (int extra = -1; extra < variables; ++extra) {
            if (extra >= 0 && !(eligible & (1u << extra))) continue;
            Mask signs = helper | (extra < 0 ? 0u : 1u << extra);
            int result = boundaryMinimum(pos, neg, signs);
            std::cout << "pair 1 " << q << " negative raw " << extra << " minimum " << result << std::endl;
            if (q == 3 && extra == 7) {
                if (result != 15 || graph(73) || std::find(negative.begin(),negative.end(),73) != negative.end()) return 6;
                auto augmented = negative;
                augmented.push_back(73);
                result = boundaryMinimum(pos, Literals(augmented,pair), signs);
                std::cout << "with negative row 73: " << result << std::endl;
            }
            if (result < 16) return 7;
        }
    }
}
