"""Encode the L-meta-908 defined inputs for circuits with a fixed number of internal ANDs."""

import argparse
import hashlib
import subprocess
import sys


EDGES = [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5),
         (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)]
EDGE_MASKS = [(1 << a) | (1 << b) for a, b in EDGES]


def defined_points():
    def independent(point):
        return all(point & edge != edge for edge in EDGE_MASKS)

    negatives = [point for point in range(512) if independent(point) and
                 all(not independent(point | (1 << i)) for i in range(9) if not point & (1 << i))]
    positives = sorted({point | (1 << i) for point in negatives for i in range(9)
                        if not point & (1 << i)})
    assert (len(negatives), len(positives)) == (16, 67)
    return negatives, positives


class Formula:
    def __init__(self):
        self.size = 0
        self.clauses = []

    def fresh(self):
        self.size += 1
        return self.size

    def both(self, left, right):
        result = self.fresh()
        self.clauses.extend(([-result, left], [-result, right], [result, -left, -right]))
        return result

    def any_of(self, values):
        result = self.fresh()
        self.clauses.append([-result] + values)
        self.clauses.extend([result, -value] for value in values)
        return result

    def lex_order(self, left, right):
        # A prefix remains equal as long as the next two bits agree. While it
        # is equal, a one on the left and zero on the right is forbidden.
        equal = self.fresh()
        self.clauses.append([equal])
        for a, b in zip(left, right):
            self.clauses.append([-equal, -a, b])
            following = self.fresh()
            self.clauses.extend(([-equal, a, b, following], [-equal, -a, -b, following]))
            equal = following

    def dimacs(self):
        lines = [" ".join(map(str, clause)) + " 0" for clause in self.clauses]
        return f"p cnf {self.size} {len(lines)}\n" + "\n".join(lines) + "\n"


def encode(internal, gates=5, fixed=None):
    negatives, positives = defined_points()
    formula = Formula()
    sides = []
    for gate in range(gates):
        arity = 9 + min(gate, internal)
        left, right = [[formula.fresh() for _ in range(arity)] for _ in range(2)]
        sides.append((left, right))
        formula.lex_order(left, right)
        formula.clauses.extend((left, right))
        if gate < internal:
            formula.clauses.extend([-a, -b] for a, b in zip(left, right))
        if gate > internal:
            previous_left, previous_right = sides[gate - 1]
            formula.lex_order(previous_left + previous_right, left + right)
    for gate in range(internal):
        formula.clauses.append([sides[later][side][9 + gate] for later in range(gate + 1, gates)
                                for side in range(2)])
    if fixed is not None:
        for wires, masks in zip(sides, fixed):
            for side, mask in zip(wires, masks):
                formula.clauses.extend([v if mask & (1 << i) else -v] for i, v in enumerate(side))

    for point in negatives + positives:
        values = []
        for left, right in sides:
            inputs = []
            for side in (left, right):
                active = [wire for i, wire in enumerate(side[:9]) if point & (1 << i)]
                active.extend(formula.both(wire, v) for wire, v in zip(side[9:], values))
                inputs.append(formula.any_of(active))
            values.append(formula.both(*inputs))
        if point in negatives:
            formula.clauses.extend([-value] for value in values[internal:])
        else:
            formula.clauses.append(values[internal:])
    return formula.dimacs()


def six_star_control(internal):
    # Duplicate the edge signal x0 AND x1. Using these copies on the x0 side
    # of the 0-star does not change that star, and exercises internal wiring.
    def bits(mask):
        return tuple((mask >> i) & 1 for i in range(9 + internal))

    def ordered(a, b):
        return tuple(sorted((a, b), key=bits))

    terminals = []
    for v in (0, 2, 3, 4, 6, 7):
        neighbors = sum(1 << (a if v == b else b) for a, b in EDGES if v in (a, b))
        left = 1 << v
        if v == 0:
            left |= ((1 << internal) - 1) << 9
        terminals.append(ordered(left, neighbors))
    terminals.sort(key=lambda pair: bits(pair[0]) + bits(pair[1]))
    return [ordered(1, 2)] * internal + terminals


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver", help="path to CaDiCaL")
    parser.add_argument("internal", type=int, choices=range(5), nargs="+")
    parser.add_argument("--seconds", type=int, default=120)
    args = parser.parse_args()
    for count in args.internal:
        control = six_star_control(count)
        command = [args.solver, "-q", "--check", "--checkproof=2", "-t", str(args.seconds)]
        trial = subprocess.run(command, input=encode(count, len(control), control),
                               text=True, capture_output=True)
        if trial.returncode != 10 or "s SATISFIABLE" not in trial.stdout:
            sys.exit("The fixed six-star positive control failed.")
        problem = encode(count)
        print(count, problem.splitlines()[0], hashlib.sha256(problem.encode()).hexdigest(), flush=True)
        run = subprocess.run(command, input=problem, text=True, capture_output=True)
        if run.returncode == 20 and "s UNSATISFIABLE" in run.stdout:
            print("UNSAT", flush=True)
        elif run.returncode == 10 and "s SATISFIABLE" in run.stdout:
            print(run.stdout, flush=True)
        else:
            print("Inconclusive", run.returncode, flush=True)


if __name__ == "__main__":
    main()
