"""Classify minimum three-line cores, or search for a double directional miss.

The bounded search uses private-pair disjunctions in a triangle and private
triples in a pencil. Core classification checks the bare six-cycle or pencil.
"""
import argparse
from itertools import combinations
from pathlib import Path
import subprocess


EDGES = [(0, 6), (1, 6), (3, 6), (1, 7), (2, 7), (4, 7),
         (2, 8), (0, 8), (5, 8)]


PENCIL = [(0, 4), (1, 4), (0, 5), (2, 5), (0, 6), (3, 6)]


def target(row, edges):
    return any(row >> p & row >> line & 1 for p, line in edges)


def evaluate(gates, row, direction, count):
    values = [bool(row >> i & 1) for i in range(count)]
    slopes = [bool(direction >> i & 1) for i in range(count)]
    for is_or, a, b in gates:
        if is_or:
            value = values[a] or values[b]
            slope = slopes[a] or slopes[b]
        else:
            value = values[a] and values[b]
            slope = (values[a] and slopes[b]) or (slopes[a] and values[b])
        values.append(value)
        slopes.append(slope)
    return values[-1], slopes[-1]


class Formula:
    def __init__(self):
        self.count = 0
        self.clauses = []

    def var(self):
        self.count += 1
        return self.count

    def selectors(self, n):
        choices = [self.var() for _ in range(n)]
        self.clauses.append(choices)
        self.clauses.extend([-a, -b] for a, b in combinations(choices, 2))
        return choices

    def port(self, select, wires):
        v = self.var()
        for use, x in zip(select, wires):
            self.clauses.extend(([-use, -v, x], [-use, v, -x]))
        return v

    def gate(self, op, a, b):
        v = self.var()
        self.clauses.extend(([-op, -a, v], [-op, -b, v], [-op, a, b, -v],
                             [op, a, -v], [op, b, -v], [op, -a, -b, v]))
        return v

    def text(self):
        return f"p cnf {self.count} {len(self.clauses)}\n" + "".join(
            " ".join(map(str, clause)) + " 0\n" for clause in self.clauses)


def positive_control(pencil):
    count = 7 if pencil else 9
    gates = []
    def add(is_or, a, b):
        gates.append((is_or, a, b))
        return count - 1 + len(gates)
    stars = []
    if pencil:
        for private, line in [(1, 4), (2, 5), (3, 6)]:
            stars.append(add(False, line, add(True, 0, private)))
    else:
        for a, b, private, line in [(0,1,3,6), (1,2,4,7), (2,0,5,8)]:
            stars.append(add(False, line, add(True, private, add(True,a,b))))
    pair = add(True, stars[0], stars[1])
    root = add(True, pair, stars[2])
    duplicate = add(True, pair, stars[2])
    add(False,root,duplicate)
    # Renumber in the same topological order used by the SAT clauses.
    ids = {i:i for i in range(count)}
    ordered = []
    while len(ordered) < len(gates):
        candidates = []
        for index, (op, a, b) in enumerate(gates,count):
            if index in ids or a not in ids or b not in ids:
                continue
            lo, hi = sorted([ids[a],ids[b]])
            candidates.append((hi,lo,index,op))
        hi, lo, index, op = min(candidates)
        ids[index] = count + len(ordered)
        ordered.append((op,lo,hi))
    return ordered


def search(size, p, seconds, pencil, fixed=None, missing_stars=None):
    count, line, edges = (7, 4, PENCIL) if pencil else (9, 6, EDGES)
    if missing_stars is not None and not pencil:
        count, line = 6, 3
        edges = [(0,3),(1,3),(1,4),(2,4),(2,5),(0,5)]
    f = Formula()
    one = f.var()
    f.clauses.append([one])
    negative = [r for r in range(1 << count) if not target(r, edges) and
                all(r >> i & 1 or target(r | 1 << i, edges) for i in range(count))]
    rows = [1 << a | 1 << b for a, b in edges] + negative
    # The last four columns are two primal values and their formal directions.
    raw = rows if missing_stars is not None else rows + [1 << p, 1 << line, 1 << line, 1 << p]
    cols = [[one if r >> i & 1 else -one for i in range(count)] for r in raw]
    choices = []
    readers = [[] for _ in range(count + size)]
    for g in range(size):
        n = count + g
        op = f.var()
        ls, rs = f.selectors(n), f.selectors(n)
        for i in range(n):
            f.clauses.extend([-ls[i], -rs[j]] for j in range(i+1))
            readers[i].extend([ls[i], rs[i]])
        # Take the ready gate with least larger operand, then least smaller.
        # A newly ready gate reads the preceding output, a larger index.
        if choices:
            _, last_left, last_right = choices[-1]
            for j, old in enumerate(last_right):
                f.clauses.extend([-old, -now] for now in rs[:j])
                for i, small in enumerate(last_left):
                    f.clauses.extend([-old, -rs[j], -small, -now] for now in ls[:i])
        choices.append((op, ls, rs))
        ports = [(f.port(ls, ws), f.port(rs, ws)) for ws in cols]
        for k, (a, b) in enumerate(ports):
            if k in [len(rows)+1, len(rows)+3]:
                left_base, right_base = ports[k-1]
                first = f.gate(-one, left_base, b)
                second = f.gate(-one, a, right_base)
                product = f.gate(one, first, second)
                union = f.gate(one, a, b)
                v = f.var()
                f.clauses.extend(([-op, -v, union], [-op, v, -union],
                                  [op, -v, product], [op, v, -product]))
            else:
                v = f.gate(op, a, b)
            cols[k].append(v)
    if fixed is not None:
        for (want, a, b), (op, ls, rs) in zip(fixed, choices):
            f.clauses.extend(([op if want else -op], [ls[a]], [rs[b]]))
    for row, col in zip(rows, cols):
        f.clauses.append([col[-1] if target(row, edges) else -col[-1]])
    if missing_stars is None:
        f.clauses.extend(([-cols[-1][-1]], [-cols[-3][-1]]))
    else:
        for center in missing_stars:
            a, b = sorted(v for e in edges if center in e for v in e if v != center)
            for g, (op1, left, right) in enumerate(choices):
                for op2, left2, right2 in choices[g+1:]:
                    f.clauses.append([-op1,-left[a],-right[b],op2,-left2[center],-right2[count+g]])
    # Remove dead gates before choosing a size. Every raw variable is essential.
    f.clauses.extend(readers[:-1])
    exe = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin/cadical"
    result = subprocess.run([exe, "-q", "--check", "--checkproof=2", "-t", str(seconds)],
                            input=f.text(), capture_output=True, text=True, timeout=seconds+20)
    if result.returncode == 20:
        assert "s UNSATISFIABLE" in result.stdout
        return "UNSAT"
    if result.returncode == 0:
        return "time limit"
    if result.returncode != 10 or "s SATISFIABLE" not in result.stdout:
        raise RuntimeError(result.stderr[-400:])
    model = {int(v) for line in result.stdout.splitlines() if line.startswith("v ")
             for v in line.split()[1:] if int(v) > 0}
    def operand(select):
        return next(i for i, bit in enumerate(select) if bit in model)
    gates = [(op in model, operand(ls), operand(rs)) for op, ls, rs in choices]
    assert all(evaluate(gates, row, 0, count)[0] == target(row, edges) for row in range(1 << count))
    if missing_stars is None:
        assert not evaluate(gates, 1 << p, 1 << line, count)[1]
        assert not evaluate(gates, 1 << line, 1 << p, count)[1]
    else:
        for center in missing_stars:
            neighbors = sorted(v for e in edges if center in e for v in e if v != center)
            for g, (op, a, b) in enumerate(gates):
                if op and [a,b] == neighbors:
                    assert (False, center, count+g) not in gates
    return gates


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=int, default=40)
    parser.add_argument("--sizes", nargs="+", type=int, default=None)
    parser.add_argument("--control-only", action="store_true")
    parser.add_argument("--pencil", action="store_true", help="use the three concurrent lines")
    parser.add_argument("--classify-core", action="store_true", help="check minimum cost and all missing-star orbits for the selected core")
    args = parser.parse_args()
    if args.classify_core:
        for size in (range(6, 8) if args.pencil else range(5, 8)):
            verdict = search(size, 0, args.seconds, args.pencil, missing_stars=())
            print("unrestricted core size",size,verdict,flush=True)
            assert verdict == "UNSAT"
        for centers in ([(), (4,)] if args.pencil else [(), (0, 3), (0, 4)]):
            verdict = search(8, 0, args.seconds, args.pencil, missing_stars=centers)
            print("eight-gate core, missing centers", centers, verdict, flush=True)
            assert (verdict == "UNSAT") if centers else isinstance(verdict,list)
        raise SystemExit
    control = positive_control(args.pencil)
    vertices = (0, 1) if args.pencil else (0, 3)
    sizes = args.sizes or ([6, 7, 8] if args.pencil else [8, 9, 10, 11])
    for vertex in vertices:
        assert search(len(control),vertex,10,args.pencil,fixed=control) == control
    print(f"Both fixed {len(control)}-gate controls passed.",flush=True)
    for size in ([] if args.control_only else sizes):
        for vertex in vertices:
            print(size,vertex,search(size,vertex,args.seconds,args.pencil),flush=True)
