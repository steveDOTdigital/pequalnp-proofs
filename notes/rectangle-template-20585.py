"""Replay the fixed-template bounds and the 1,489-gate witness; standard library."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
import json
import re
from urllib.request import Request, urlopen

ROOT = "https://raw.githubusercontent.com/open-goat/pequalnp-proofs"
REV = "3b47ace034724a2b2d0294334d51c3e6aae1c63a"
CATALOGUE = "https://data.pequalnp.com/data/lemma/L-meta-20585.d22fa7045cab.json"
# Indexes in the sorted list of all sharable masks in the published template.
SELECTED = [43,76,84,88,93,95,96,98,102,170,188,198,257,299,308,310,316,339,375,378,380,428,435,447,452,465,470,471,476,479,491,493,524,527,529,554,587,600,602,618,625,647,706,714,721,730,733,741,753,758,762,770,773,785,792,798,802,804,818,826,835,838,862,863,872,873,880,886,896,911,917,918,932,933,937,939,946,956,957,959,965,1008,1009,1021,1026,1040,1043,1052,1055,1064,1078,1089,1090,1099,1110,1120,1141,1147,1159,1161,1170,1195,1207,1236,1242,1246,1263,1264,1270,1277,1304,1332,1334,1344,1348,1363,1368,1396,1403,1405,1440,1441,1446,1450,1467,1487,1495,1510,1520,1530,1532,1545,1548,1551,1563,1587,1611,1622,1623,1633,1649,1653,1655,1669,1686,1687,1708,1717,1724,1729,1745,1753,1762,1793,1794,1818,1828,1833,1835,1862,1872,1883,1894,1906,1908,1910,1923,1925,1926,1927,1951,1967,1969,1970,1972,1979,1998,2029,2038,2040,2042,2048,2052,2061,2063,2083,2090,2111,2120,2125,2141,2145,2191,2193,2212,2238,2240,2265,2290,2301,2302,2303,2307,2316,2344,2345,2351,2365,2366,2372,2373,2385,2391,2393,2394,2431,2456,2473,2475,2497,2515,2517,2520,2524,2537,2538,2542,2591,2595,2600,2617,2620,2637,2639,2652,2666,2685,2687,2689,2700,2712,2726,2730,2756,2767,2771,2792,2806,2807,2810,2819,2824,2839,2863,2865,2871,2894,2895,2897,2907,2930,2937,2957,2984,2989,2993,3008,3010,3014,3015,3021,3027,3031,3042,3045,3046,3048,3054,3056,3058,3060,3062,3079,3089,3108,3133,3137,3149,3156,3162,3165,3170,3184,3201,3209,3215,3226,3227,3238,3246,3251,3262,3270,3274,3293,3301,3320,3332,3341,3354,3359,3384,3392,3397,3403,3421,3447,3454,3456,3459,3467,3468,3472,3487,3495,3506,3509,3519,3534,3539,3541,3590,3605,3640,3645,3656,3664,3674,3679,3683,3704,3718,3725,3742,3757,3760,3765,3767,3773,3783,3788,3794,3805,3871,3901,3902,3909,3911,3918,3919,3921,3924,3936,3962,3963,3970,3989,4000,4019,4030,4035,4038,4052,4078,4080,4086,4089,4099,4128,4134,4139,4152,4175,4186,4194,4198,4208,4213,4216,4234,4240,4244,4254,4256,4267,4273]


def read_instance():
    with urlopen(Request(CATALOGUE, headers={"User-Agent": "steveDOTdigital proof replay/1.0"}), timeout=30) as response:
        statement = json.load(response)["formal_statement"]
    rows = [int(x, 16) for x in re.findall(r"0x[0-9a-fA-F]+", statement)]
    with urlopen(f"{ROOT}/{REV}/lean/PEqualNP/Outside/L_meta_19358.lean", timeout=30) as response:
        source = response.read().decode()
    section = source.split("def codes", 1)[1].split("def circuit", 1)[0]
    gates = re.findall(r"\((true|false),\s*(\d+),\s*(\d+)\)", section)
    support = [1 << i for i in range(256)]
    targets = []
    for op, left, right in gates:
        a, b = support[int(left)], support[int(right)]
        if op == "true":
            support.append(a | b if a and b else 0)
        else:
            assert a and b
            targets.extend([a, b])
            support.append(0)
    assert len(gates) == 1500 and len(targets) == len(set(targets)) == 128
    assert len(rows) == 128 and sum(r.bit_count() for r in rows) == 6485
    return rows, targets


def minimum_cover(mask, pool):
    # Single raw indicators are always available. Inclusion-maximal options suffice.
    atoms = [1 << i for i in range(mask.bit_length()) if (mask >> i) & 1]
    options = {x for x in pool if x != mask and x & ~mask == 0} | set(atoms)
    maximal = {x for x in options if not any(x != y and x & ~y == 0 for y in options)}
    by_bit = {b: sorted(x for x in maximal if b & x) for b in atoms}

    @lru_cache(None)
    def solve(rem):
        if not rem:
            return 0, ()
        bit = min((b for b in atoms if b & rem), key=lambda b: len(by_bit[b]))
        return min((1 + size, (s,) + tail) for s in by_bit[bit]
                   for size, tail in [solve(rem & ~s)])

    return solve(mask)


def all_shared(targets):
    options = set()
    for a, b in combinations(targets, 2):
        common = a & b
        subset = common
        while subset:
            if subset.bit_count() >= 2:
                options.add(subset)
            subset = (subset - 1) & common
    return sorted(options)


def template_lower(targets, options):
    cover = []
    for i, target in enumerate(targets):
        others = (target & x for j,x in enumerate(targets) if j != i)
        cover.append(minimum_cover(target, others)[0])
    assert Counter(cover) == {5: 7, 6: 65, 7: 49, 8: 6, 9: 1}
    private = sum(cover) - len(targets)
    capacity = sorted((sum(s & ~t == 0 for t in targets) for s in options), reverse=True)
    demand = sum(t.bit_count() - 1 for t in targets)
    # A shared mask can be counted at most once per cone containing it.
    total = reach = private
    while reach < demand:
        reach += capacity[total-private]
        total += 1
    assert (private, demand, total, total + 127) == (697, 1919, 1055, 1182)


def make_circuit(targets, options):
    shared = {options[i] for i in SELECTED}
    index = {1 << i:i for i in range(256)}
    gates = []

    def add(op, a, b):
        gates.append((op, a, b))
        return 255 + len(gates)

    for mask in sorted(shared | set(targets), key=lambda x:(x.bit_count(), x)):
        _, parts = minimum_cover(mask, shared)
        w = index[parts[0]]
        for part in parts[1:]:
            w = add("or", w, index[part])
        index[mask] = w
    terms = [add("and", index[targets[i]], index[targets[i+1]]) for i in range(0,128,2)]
    out = terms[0]
    for term in terms[1:]:
        out = add("or", out, term)
    return gates, out


def determinant(rows):
    p = 1009
    matrix = [[(row >> j) & 1 for j in range(128)] for row in rows]
    det = 1
    for j in range(128):
        pivot = next((i for i in range(j,128) if matrix[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[pivot], matrix[j] = matrix[j], matrix[pivot]
            det = -det
        value = matrix[j][j]
        det = det * value % p
        for i in range(j+1,128):
            coeff = matrix[i][j] * pow(value,-1,p) % p
            if coeff:
                for k in range(j,128):
                    matrix[i][k] = (matrix[i][k] - coeff * matrix[j][k]) % p
    return det


def main():
    rows, targets = read_instance()
    options = all_shared(targets)
    template_lower(targets, options)
    gates, out = make_circuit(targets, options)
    first_col = sum(1 << (128*i) for i in range(128))
    wires = [((1 << 128) - 1) << (128*i) for i in range(128)] + [first_col << j for j in range(128)]
    for op, a, b in gates:
        wires.append(wires[a] | wires[b] if op == "or" else wires[a] & wires[b])
    assert wires[out] == sum(row << (128*i) for i,row in enumerate(rows))
    assert len(gates) == 1489 and determinant(rows) == 675
    print("1,489 gates verified on 16,384 inputs. Fixed-template lower bound 1,182. Rank 128.")


if __name__ == "__main__":
    main()
