"""Enumerate first-gate and direct-reader orbits in the raw Petersen lower bounds."""
import argparse
import runpy
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

NOTES = Path(__file__).resolve().parent
graph = runpy.run_path(str(NOTES / 'petersen-free-or-certificate.py'))
EDGES, PAIRS = graph['EDGES'], graph['PAIRS']


def population(mask):
    return bin(mask).count('1')


def formula_floors():
    # On each induced graph the monotone formula leaf minimum is m + tau.
    floors = []
    for active in range(1024):
        edges = [(i, j) for i, j in EDGES if (active >> i) & (active >> j) & 1]
        cover = min(population(mask) for mask in range(1024)
                    if mask & ~active == 0
                    and all((mask >> i | mask >> j) & 1 for i, j in edges))
        floors.append(len(edges) + cover)
    return floors


def profiles(pair):
    stabilizer = [p for p in graph['automorphisms']()
                  if {p[pair[0]], p[pair[1]]} == set(pair)]
    required = (1 << pair[0]) | (1 << pair[1])
    seen = set()
    for mask in range(1024):
        if mask in seen or mask & required != required or population(mask) > 7:
            continue
        orbit = {sum(1 << p[i] for i in range(10) if mask >> i & 1)
                 for p in stabilizer}
        seen.update(orbit)
        yield mask, len(orbit)
    assert len(seen) == 219


def instance(signed, pair, mask, floors, seconds):
    budget = 16 if signed else 17
    or_code = 3 if signed else 1
    first = (or_code, *pair)
    data = [budget, seconds, len(EDGES), mask]
    data.extend((1 << i) | (1 << j) for i, j in sorted(EDGES))
    for _ in range(10):
        data.extend((14, 8) if signed else (15, 11))
    for i, j in PAIRS:
        data.extend((i, j, 13 if (i, j) in EDGES else 12))
    allowed = [(or_code, i, j) for i, j in PAIRS if (mask >> i) & (mask >> j) & 1]
    data.extend((1, *first, len(allowed)))
    for gate in allowed:
        data.extend(gate)
    data.extend(floors)
    data.extend((1, *first))
    return ' '.join(map(str, data)) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--signed', action='store_true', help='exclude 16 signed gates')
    parser.add_argument('--seconds', type=int, default=120, help='time limit for each orbit')
    args = parser.parse_args()
    graph['check_target']()
    if args.signed:
        floors = []
        cases = [((0, 2), mask, size) for mask, size in graph['repeated_profiles']()]
    else:
        floors = formula_floors()
        cases = [(pair, mask, size) for pair in ((0, 1), (0, 2))
                 for mask, size in profiles(pair)]
        assert len(cases) == 122
    with tempfile.TemporaryDirectory(prefix='pnp-petersen-profiles-') as tmp:
        exe = Path(tmp) / 'search'
        subprocess.run(['c++', '-O3', '-std=c++17', '-DWIDTH=10',
                        '-DSIGNED_MODE=' + str(int(args.signed)), '-DPETERSEN_PAIR_MODE=1',
                        str(NOTES / 'petersen-raw-prefix.cpp'), '-o', str(exe)], check=True)

        def check(case):
            pair, mask, size = case
            result = subprocess.run([str(exe)], input=instance(args.signed, pair, mask, floors, args.seconds),
                                    capture_output=True, text=True, check=True, timeout=args.seconds + 30)
            fields = result.stdout.strip().split()
            print(pair, mask, size, result.stdout.strip(), flush=True)
            return fields[0]

        with ThreadPoolExecutor(max_workers=3) as pool:
            verdicts = list(pool.map(check, cases))
    assert not Path(tmp).exists()
    if any(verdict != 'UNSAT' for verdict in verdicts):
        raise SystemExit('Incomplete exclusion: inspect the individual verdicts.')
    print('Excluded every one of', len(cases), 'orbits.')


if __name__ == '__main__':
    main()
