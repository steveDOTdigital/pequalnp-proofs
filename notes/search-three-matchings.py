"""Exact six-input synthesis for L-meta-652, using a CaDiCaL executable.

All 64 truth-table rows are imposed. The optional fixed prefix consists of
zero, one or two five-gate matching circuits. A bounded solver timeout is
reported as UNKNOWN. No CNF, model or solver trace is left on disk.
"""

import argparse
import subprocess
from itertools import combinations, permutations


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


def restricted_instance(pins):
    free = [i for i in range(6) if i not in pins]
    rows = 1 << len(free)
    inputs = [sum(((row >> j) & 1) << row for row in range(rows)) for j in range(len(free))]
    base = sum(value << i for i, value in pins.items())
    full = [base + sum(((row >> j) & 1) << i for j, i in enumerate(free)) for row in range(rows)]
    trivial = {0, (1 << rows)-1, *inputs}
    wanted = [sum(((t >> x) & 1) << row for row, x in enumerate(full)) for t in targets()]
    return inputs, list(dict.fromkeys(t for t in wanted if t not in trivial))


def canonical_pairs(n, wanted):
    autos = []
    for p in permutations(range(n)):
        action = [sum(((x >> j) & 1) << p[j] for j in range(n)) for x in range(1 << n)]
        permuted = {sum(((v >> x) & 1) << y for x, y in enumerate(action)) for v in wanted}
        if permuted == set(wanted):
            autos.append(p)
    return {(a, b) for a in range(n) for b in range(a, n)
            if all((b,a) <= (max(p[a],p[b]),min(p[a],p[b])) for p in autos)}


def require_cofactor_sizes(formula, tables, choices, inputs, lower_bounds):
    """Count gates that still supply distinct nonconstant functions after pinning."""
    n = len(inputs)
    rows = 1 << n
    differences = {}
    for (i, value), minimum in lower_bounds.items():
        selected = [x for x in range(rows) if ((x >> i) & 1) == value]
        novel = formula.vars(len(choices))
        # Every set of budget - minimum + 1 gates contains a surviving gate.
        formula.clauses.extend(list(group) for group in combinations(novel, len(choices)-minimum+1))
        for k, (_, left, right) in enumerate(choices):
            new, wire = novel[k], tables[n+k]
            formula.clauses.extend(([-new, -left[i]], [-new, -right[i]],
                                    [-new, *[wire[x] for x in selected]],
                                    [-new, *[-wire[x] for x in selected]]))
            for source, truth in enumerate(inputs):
                if source != i:
                    formula.clauses.append([-new, *[-wire[x] if (truth >> x) & 1 else wire[x]
                                                    for x in selected]])
            for prior in range(k):
                key = (prior, k)
                if key not in differences:
                    xor = formula.vars(rows)
                    differences[key] = xor
                    for d, a, b in zip(xor, tables[n+prior], wire):
                        # A claimed difference requires opposite truth values.
                        formula.clauses.extend(([-d, a, b], [-d, -a, -b]))
                formula.clauses.append([-new, *[differences[key][x] for x in selected]])


def synthesize(executable, fixed, total, seconds, check=False, supplied=None,
               first_input_one=False, first_gate=None, pins=None, cofactor_bounds=False,
               six_input_outputs=None):
    f = Formula()
    if first_input_one and pins is not None:
        raise ValueError("use only one type of restriction")
    pins = {0: 1} if first_input_one else pins
    if six_input_outputs is not None:
        if fixed or supplied is not None or pins or cofactor_bounds:
            raise ValueError("explicit outputs require the six raw inputs")
        n, inputs, wanted_tables = 6, INPUTS, six_input_outputs
        allowed = canonical_pairs(n, wanted_tables)
    elif pins:
        if fixed or supplied is not None:
            raise ValueError("restricted instances start with raw inputs")
        inputs, wanted_tables = restricted_instance(pins)
        n = len(inputs)
        allowed = canonical_pairs(n, wanted_tables)
    else:
        n, inputs, wanted_tables = 6, INPUTS, targets()
    rows = 1 << n
    prefix = inputs.copy()
    for k in range(fixed):
        products = [INPUTS[i] & INPUTS[3 + (i + k) % 3] for i in range(3)]
        prefix.extend(products + [products[0] | products[1], targets()[k]])
    if supplied is not None:
        assert fixed == 1 and targets()[0] in supplied
        prefix = INPUTS + list(supplied)
    # Mark raw inputs whose flip can change an output while every supplied
    # wire stays fixed. The suffix must read these actual inputs. Structural
    # rows propagate reachability through the suffix, treating helpers as leaves.
    required = []
    for target in wanted_tables[fixed:]:
        required.append([any(
            ((target >> x) ^ (target >> (x ^ (1 << i)))) & 1 and
            all(not (((helper >> x) ^ (helper >> (x ^ (1 << i)))) & 1)
                for helper in prefix[n:])
            for x in range(rows)) for i in range(n)])
    tables = []
    for j, bits in enumerate(prefix):
        encoded = bits | (((1 << j) if j < n else 0) << rows)
        table = f.vars(rows + n)
        tables.append(table)
        f.clauses.extend([v if encoded & (1 << row) else -v] for row, v in enumerate(table))
    choices = []
    for _ in range(total - (len(prefix) - n)):
        ports = []
        selectors = []
        for _ in range(2):
            sel = f.one_of(len(tables))
            selectors.append(sel)
            values = f.vars(rows + n)
            ports.append(values)
            for choice, table in zip(sel, tables):
                for v, src in zip(values, table):
                    f.clauses.extend(([-choice, -v, src], [-choice, v, -src]))
        ops = f.one_of(3)
        if (pins or six_input_outputs is not None) and not choices:
            for a in range(n):
                for b in range(a, n):
                    if (a, b) not in allowed:
                        f.clauses.append([-selectors[0][a], -selectors[1][b]])
                    elif a == b:
                        f.clauses.append([-selectors[0][a], -selectors[1][b], ops[2]])
        elif not fixed and not choices:
            # Independent cyclic shifts of the two triples, simultaneous
            # reversal and exchanging the triples permute the three outputs.
            # Give priority to a literal NOT, then a same-side pair, then
            # a cross pair. Each can become the least ready pair of its kind.
            f.clauses.append([selectors[0][0]])
            f.clauses.append([selectors[1][0], selectors[1][1], selectors[1][3]])
            f.clauses.append([-selectors[1][0], ops[2]])
        if first_gate is not None and not choices:
            op, a, b = first_gate
            f.clauses.extend(([ops[("AND", "OR", "NOT").index(op)]],
                              [selectors[0][a]], [selectors[1][b]]))
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
        output = f.vars(rows + n)
        for row, (a, b, y) in enumerate(zip(*ports, output)):
            if row < rows:
                f.clauses.extend(([-ops[0], -y, a], [-ops[0], -y, b], [-ops[0], y, -a, -b],
                                  [-ops[1], y, -a], [-ops[1], y, -b], [-ops[1], -y, a, b],
                                  [-ops[2], y, a], [-ops[2], -y, -a]))
            else:
                f.clauses.extend(([y, -a], [y, -b], [-y, a, b]))
        tables.append(output)
        choices.append((ops, *selectors))
    outputs = []
    for wanted, needs in zip(wanted_tables[fixed:], required):
        # Free choice of output wire, with fanout allowed between outputs.
        out = f.one_of(len(tables) - len(prefix))
        outputs.append(out)
        for selector, table in zip(out, tables[len(prefix):]):
            f.clauses.extend([-selector, v if row >= rows or wanted & (1 << row) else -v]
                             for row, v in enumerate(table) if row < rows or needs[row - rows])
        for i, essential in enumerate(needs):
            if essential:
                f.clauses.append([port[i] for _, left, right in choices for port in (left, right)])
        for k in range(min(max(0, sum(needs)-2), len(out))):
            f.clauses.append([-out[k]])
    # Remove dead logic in a smallest solution, then pad with copies of an
    # output if needed. Thus every appended gate can have a reader.
    for i in range(len(choices)):
        wire = len(prefix) + i
        readers = [out[i] for out in outputs]
        for _, left, right in choices[i + 1:]:
            readers.extend((left[wire], right[wire]))
        f.clauses.append(readers)
    if cofactor_bounds:
        if fixed or pins not in (None, {0: 1}):
            raise ValueError("these bounds apply to the raw problem or its first-input true restriction")
        # For either remaining point bit, the zero/one cofactors need 6/7
        # gates. For any line bit the corresponding lower bounds are 7/6.
        lower = ({(i, v): (6 + v if i < 2 else 7 - v) for i in range(5) for v in (0, 1)}
                 if pins else {(i, 1): 11 for i in range(6)})
        require_cofactor_sizes(f, tables, choices, inputs, lower)
    print(f"{fixed} fixed outputs, {total} gate budget, {f.count} variables, "
          f"{len(f.clauses)} clauses", flush=True)
    command = [executable, "-q", "-t", str(seconds)]
    if check:
        command.extend(("--check", "--checkproof=2"))
    result = subprocess.run(command, input=f.dimacs(),
                            capture_output=True, text=True, timeout=seconds + 15)
    if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
        print("UNSAT", flush=True)
        return "UNSAT"
    elif result.returncode == 10 and "s SATISFIABLE" in result.stdout:
        model = {int(tok) for line in result.stdout.splitlines() if line.startswith("v ")
                 for tok in line.split()[1:]}
        wires = prefix.copy()
        for ops, left, right in choices:
            op, a, b = [next(i for i, x in enumerate(opts) if x in model)
                        for opts in (ops, left, right)]
            name = ("AND", "OR", "NOT")[op]
            wires.append(gate(name, wires[a], wires[b]) & ((1 << rows) - 1))
            print(f"wire {len(wires)-1}: {name} {a} {b}")
        assert all(wanted in wires for wanted in wanted_tables)
        print("SAT, all output truth tables independently verified", flush=True)
        return "SAT"
    elif result.returncode == 0 and ("s UNKNOWN" in result.stdout or "UNKNOWN" in result.stdout):
        print("UNKNOWN", flush=True)
        return "UNKNOWN"
    else:
        raise RuntimeError((result.returncode, result.stdout[-300:], result.stderr[-300:]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver")
    parser.add_argument("--fixed", type=int, choices=(0, 1, 2), default=0)
    parser.add_argument("--gates", type=int, default=14)
    parser.add_argument("--seconds", type=int, default=60)
    parser.add_argument("--check", action="store_true", help="enable CaDiCaL's internal proof checker")
    parser.add_argument("--first-input-one", action="store_true", help="fix the first raw input to true")
    parser.add_argument("--cofactor-bounds", action="store_true")
    parser.add_argument("--first", nargs=3, metavar=("OP","A","B"),
                        help="restrict the first gate to a canonical instruction")
    args = parser.parse_args()
    first = None
    if args.first:
        op, a, b = args.first
        first = (op, int(a), int(b))
        pairs = {(0,0), (0,1), (0,2), (2,2), (2,3)} if args.first_input_one else {(0,0),(0,1),(0,3)}
        if (first[1:] not in pairs or op not in ("AND","OR","NOT") or
                (op == "NOT") != (a == b) or args.fixed):
            parser.error("choose a canonical first gate for the selected raw-input problem")
    synthesize(args.solver, args.fixed, args.gates, args.seconds, args.check, first_input_one=args.first_input_one, first_gate=first, cofactor_bounds=args.cofactor_bounds)
