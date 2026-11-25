"""Run the exact 23-gate local repair search using a temporary C++17 binary."""
from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path
import runpy
import subprocess
import tempfile

folder = Path(__file__).resolve().parent
original = runpy.run_path(str(folder / "shared-pencil-search.py"))


@lru_cache(None)
def trees(leaves):
    if len(leaves) == 1:
        return (leaves[0],)
    result = []
    for size in range(len(leaves) - 1):
        for subset in combinations(leaves[1:], size):
            left = (leaves[0],) + subset
            right = tuple(x for x in leaves if x not in left)
            result.extend((a, b) for a in trees(left) for b in trees(right))
    return tuple(result)


def layouts():
    for pattern in product(range(3), repeat=5):
        yield original["baseline"](pattern)[:20]
    # Each possible unbalanced four-leaf tree at one star, with the other
    # four in their canonical balanced forms. An unordered bottom pair has
    # two possible orders for the third and fourth leaves.
    baseline = original["baseline"]((0,) * 5)[:20]
    for p in range(5):
        i = 4 * p
        ls = baseline[i][1:] + baseline[i + 1][1:]
        for a, b, c, d in permutations(ls):
            if a > b:
                continue
            result = baseline.copy()
            result[i:i+3] = [("or", a, b), ("or", 20+i, c), ("or", 21+i, d)]
            yield result


def templates():
    branches = trees((23, 27, 31, 35, 39))
    assert len(branches) == len(set(branches)) == 105
    for prefix in layouts():
        for tree in branches:
            gates = prefix.copy()

            def emit(node):
                if isinstance(node, int):
                    return node
                a, b = map(emit, node)
                gates.append(("or", a, b))
                return 19 + len(gates)

            assert emit(tree) == 43
            yield gates


def main():
    pos, neg = original["samples"]()
    rows = pos + neg
    raw = [sum(((row >> i) & 1) << j for j, row in enumerate(rows)) for i in range(20)]
    with tempfile.TemporaryDirectory(prefix="desk-pencil-repairs-") as temp:
        binary = Path(temp) / "search"
        subprocess.run(["c++", "-O3", "-std=c++17", str(folder / "degenerate-pencil-repairs.cpp"),
                        "-o", str(binary)], check=True)
        with subprocess.Popen([str(binary)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              text=True) as search:
            try:
                search.stdin.write(" ".join(map(str, raw)) + "\n")
                for gates in templates():
                    text = " ".join(f"{int(op == 'or')} {a} {b}" for op, a, b in gates)
                    search.stdin.write(f"{len(gates)} {text}\n")
                search.stdin.close()
            except BrokenPipeError:
                pass
            report = search.stdout.read()
            if search.wait():
                raise RuntimeError("repair search did not finish")
        print(report, end="")
        if report.startswith("Witness"):
            wires = raw.copy()
            lines = report.splitlines()
            assert len(lines[1:-1]) == 23
            for gate in lines[1:-1]:
                op, a, b = map(int, gate.split())
                wires.append((wires[a] | wires[b]) if op else (wires[a] & wires[b]))
            output = int(lines[-1].split()[1])
            assert wires[output] == (1 << 20) - 1
        else:
            assert report.startswith("Templates exhausted 31815,")
    assert not Path(temp).exists()


if __name__ == "__main__":
    main()
