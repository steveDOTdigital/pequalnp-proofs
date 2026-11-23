"""Exact six-input synthesis for L-meta-652, using a CaDiCaL executable.

All 64 truth-table rows are imposed. The optional fixed prefix consists of
zero, one or two five-gate matching circuits. A bounded solver timeout is
reported as UNKNOWN. No CNF, model or solver trace is left on disk.
"""

import argparse
import subprocess
from itertools import combinations


MASK = (1 << 64) - 1
INPUTS = [sum(((row >> i) & 1) << row for row in range(64)) for i in range(6)]


def gate(op, a, b):
    if op == "AND":
        return a & b
    if op == "OR":
        return a | b
    return MASK ^ a


def targets():
    return [(INPUTS[0] & INPUTS[3 + k]) | (INPUTS[1] & INPUTS[3 + (1 + k) % 3])
            | (INPUTS[2] & INPUTS[3 + (2 + k) % 3]) for k in range(3)]


class Formula:
    def __init__(self):
        self.clauses = []
        self.count = 0

    def vars(self, n):
        first = self.count + 1
        self.count += n
        return list(range(first, self.count + 1))

    def one_of(self, n):
        choices = self.vars(n)
        self.clauses.append(choices)
        self.clauses.extend([-a, -b] for a, b in combinations(choices, 2))
        return choices

    def dimacs(self):
        header = f"p cnf {self.count} {len(self.clauses)}\n"
        return header + "".join(" ".join(map(str, c)) + " 0\n" for c in self.clauses)


def synthesize(executable, fixed, total, seconds, check=False):
    f = Formula()
    prefix = INPUTS.copy()
    for k in range(fixed):
        products = [INPUTS[i] & INPUTS[3 + (i + k) % 3] for i in range(3)]
        prefix.extend(products + [products[0] | products[1], targets()[k]])
    tables = []
    for bits in prefix:
        # Six extra rows track structural dependence. An unreached input
        # cannot affect an output. This also applies to the fixed prefix.
        dependencies = sum(1 << i for i in range(6) if any(
            ((bits >> r) ^ (bits >> (r ^ (1 << i)))) & 1 for r in range(64)))
        encoded = bits | (dependencies << 64)
        table = f.vars(70)
        tables.append(table)
        f.clauses.extend([v if encoded & (1 << row) else -v] for row, v in enumerate(table))
    choices = []
    for _ in range(total - 5 * fixed):
        ports = []
        selectors = []
        for _ in range(2):
            sel = f.one_of(len(tables))
            selectors.append(sel)
            values = f.vars(70)
            ports.append(values)
            for choice, table in zip(sel, tables):
                for v, src in zip(values, table):
                    f.clauses.extend(([-choice, -v, src], [-choice, v, -src]))
        ops = f.one_of(3)
        if not fixed and not choices:
            # Independent cyclic shifts of the two triples, simultaneous
            # reversal and exchanging the triples permute the three outputs.
            # Give priority to a literal NOT, then a same-side pair, then
            # a cross pair. Each can become the least ready pair of its kind.
            f.clauses.append([selectors[0][0]])
            f.clauses.append([selectors[1][0], selectors[1][1], selectors[1][3]])
            f.clauses.append([-selectors[1][0], ops[2]])
        for i, left in enumerate(selectors[0]):
            for j, right in enumerate(selectors[1]):
                if i > j:
                    f.clauses.append([-left, -right])
                if i != j:
                    f.clauses.append([-ops[2], -left, -right])
        # Order independent gates by their larger operand, then the smaller.
        # Greedily taking the least ready pair gives this topological order:
        # any newly enabled gate uses the wire that was just appended.
        if choices:
            _, prev_left, prev_right = choices[-1]
            equal_right = f.vars(1)[0]
            for i, previous in enumerate(prev_right):
                for smaller in selectors[1][:i]:
                    f.clauses.append([-previous, -smaller])
                f.clauses.append([-previous, -selectors[1][i], equal_right])
            for i, previous in enumerate(prev_left):
                for smaller in selectors[0][:i]:
                    f.clauses.append([-equal_right, -previous, -smaller])
        output = f.vars(70)
        for row, (a, b, y) in enumerate(zip(*ports, output)):
            if row < 64:
                f.clauses.extend(([-ops[0], -y, a], [-ops[0], -y, b], [-ops[0], y, -a, -b],
                                  [-ops[1], y, -a], [-ops[1], y, -b], [-ops[1], -y, a, b],
                                  [-ops[2], y, a], [-ops[2], -y, -a]))
            else:
                f.clauses.extend(([y, -a], [y, -b], [-y, a, b]))
        tables.append(output)
        choices.append((ops, *selectors))
    outputs = []
    for wanted in targets()[fixed:]:
        # Free choice of output wire, with fanout allowed between outputs.
        out = f.one_of(len(tables) - len(prefix))
        outputs.append(out)
        for selector, table in zip(out, tables[len(prefix):]):
            f.clauses.extend([-selector, v if row >= 64 or wanted & (1 << row) else -v]
                             for row, v in enumerate(table))
    # Remove dead logic in a smallest solution, then pad with copies of an
    # output if needed. Thus every appended gate can have a reader.
    for i in range(len(choices)):
        wire = len(prefix) + i
        readers = [out[i] for out in outputs]
        for _, left, right in choices[i + 1:]:
            readers.extend((left[wire], right[wire]))
        f.clauses.append(readers)
    print(f"{fixed} fixed outputs, {total} gate budget, {f.count} variables, "
          f"{len(f.clauses)} clauses", flush=True)
    command = [executable, "-q", "-t", str(seconds)]
    if check:
        command.extend(("--check", "--checkproof=2"))
    result = subprocess.run(command, input=f.dimacs(),
                            capture_output=True, text=True, timeout=seconds + 15)
    if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
        print("UNSAT")
    elif result.returncode == 10 and "s SATISFIABLE" in result.stdout:
        model = {int(tok) for line in result.stdout.splitlines() if line.startswith("v ")
                 for tok in line.split()[1:]}
        wires = prefix.copy()
        for ops, left, right in choices:
            op, a, b = [next(i for i, x in enumerate(opts) if x in model)
                        for opts in (ops, left, right)]
            name = ("AND", "OR", "NOT")[op]
            wires.append(gate(name, wires[a], wires[b]))
            print(f"wire {len(wires)-1}: {name} {a} {b}")
        assert all(wanted in wires for wanted in targets())
        print("SAT, all output truth tables independently verified")
    elif result.returncode == 0 and ("s UNKNOWN" in result.stdout or "UNKNOWN" in result.stdout):
        print("UNKNOWN")
    else:
        raise RuntimeError((result.returncode, result.stdout[-300:], result.stderr[-300:]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver")
    parser.add_argument("--fixed", type=int, choices=(0, 1, 2), default=0)
    parser.add_argument("--gates", type=int, default=14)
    parser.add_argument("--seconds", type=int, default=60)
    parser.add_argument("--check", action="store_true", help="enable CaDiCaL's internal proof checker")
    args = parser.parse_args()
    synthesize(args.solver, args.fixed, args.gates, args.seconds, args.check)
