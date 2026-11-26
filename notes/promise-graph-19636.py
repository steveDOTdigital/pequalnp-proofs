"""Exact synthesis on the 25 promised inputs of L-meta-19636. Requires python-sat."""
import argparse
from itertools import combinations

MASK = 8130428
UPPER = [(1,5,6),(1,8,9),(1,4,10),(1,2,12),(1,0,11),
         (1,3,14),(0,13,15),(2,16,16),(1,12,14),(0,17,18)]


def inputs(row):
    i, j = divmod(row, 5)
    return [q == i for q in range(5)] + [q == j for q in range(5)]


def evaluate(gates):
    mask = 0
    for row in range(25):
        wires = inputs(row)
        for op, a, b in gates:
            x, y = wires[a], wires[b]
            wires.append((x and y) if op == 0 else (x or y) if op == 1 else not x)
        mask |= int(wires[-1]) << row
    return mask


class Encoding:
    def __init__(self, size):
        self.clauses = []
        self.count = 0
        self.ports = []
        self.uses = [[] for _ in range(10 + size)]
        wires = [list(bits) for bits in zip(*(inputs(row) for row in range(25)))]
        for _ in range(size):
            wires.append(self.gate(wires))
        for row, out in enumerate(wires[-1]):
            self.clauses.append([out if MASK >> row & 1 else -out])
        # A least circuit can be trimmed to its output cone and ordered with its output last.
        self.clauses.extend(self.uses[10:-1])
        self.used = [self.new() for _ in range(10)]
        for flag, reads in zip(self.used, self.uses):
            self.clauses.extend([[-read, flag] for read in reads])
            self.clauses.append([-flag, *reads])

    def new(self):
        self.count += 1
        return self.count

    def choice(self, n):
        ids = [self.new() for _ in range(n)]
        self.clauses.append(ids)
        self.clauses.extend([[-a, -b] for a,b in combinations(ids, 2)])
        return ids

    def select_value(self, selectors, values):
        result = self.new()
        for s, value in zip(selectors, values):
            if type(value) is bool:
                self.clauses.append([-s, result if value else -result])
            else:
                self.clauses.extend([[-s,-value,result],[-s,value,-result]])
        return result

    def gate(self, wires):
        n = len(wires)
        left, right, ops = self.choice(n), self.choice(n), self.choice(3)
        for i in range(n):
            self.uses[i].extend((left[i],right[i]))
            # Commutative operands ascend strictly; NOT selects the same input twice.
            self.clauses.extend([[-left[i],-right[j]] for j in range(i)])
            self.clauses.extend([[-ops[2],-left[i],right[i]],[-left[i],-right[i],ops[2]]])
        if self.ports:
            # The lexicographically least topological order has no independent
            # adjacent descent in its smaller input index.
            previous = self.ports[-1][0]
            for i, sel in enumerate(previous):
                self.clauses.extend([[-sel,-left[j],right[-1]] for j in range(i)])
        out, ab, ba = [], [], []
        for bits in zip(*wires):
            a, b = self.select_value(left,bits), self.select_value(right,bits)
            y, witness_ab, witness_ba = self.new(), self.new(), self.new()
            out.append(y)
            ab.append(witness_ab)
            ba.append(witness_ba)
            self.clauses.extend([[-ops[0],-a,-b,y],[-ops[0],a,-y],[-ops[0],b,-y],
                                 [-ops[1],a,b,-y],[-ops[1],-a,y],[-ops[1],-b,y],
                                 [-ops[2],a,y],[-ops[2],-a,-y],
                                 [-witness_ab,a],[-witness_ab,-b],[-witness_ba,-a],[-witness_ba,b]])
        # A constant gate or a gate equal to one of its inputs can be folded on the promise.
        self.clauses.extend([out,[-v for v in out],[ops[2],*ab],[ops[2],*ba]])
        self.ports.append((left,right,ops))
        return out

    def decode(self, model):
        true = {v for v in model if v > 0}
        def index(choice):
            return next(i for i, flag in enumerate(choice) if flag in true)
        return [(index(ops),index(left),index(right)) for left,right,ops in self.ports]


def has_small_formula(budget):
    """Test a formula budget using its smaller root subtree and partial truth tables."""
    from functools import lru_cache
    full = (1 << 25) - 1
    raw = [sum(int(bit) << row for row, bit in enumerate(bits))
           for bits in zip(*(inputs(row) for row in range(25)))]
    levels, seen = [set(raw)], set(raw)
    for cost in range(1, (budget - 1) // 2 + 1):
        new = {full ^ w for w in levels[-1]}
        for i in range((cost - 1) // 2 + 1):
            for a in levels[i]:
                for b in levels[cost - 1 - i]:
                    new.update((a & b, a | b))
        levels.append(new - seen)
        seen.update(new)

    @lru_cache(maxsize=None)
    def fits(ones, zeros, k, allow_not):
        for layer in levels[:k+1]:
            if any((w & ones) == ones and not (w & zeros) for w in layer):
                return True
        if k < len(levels):
            return False
        if allow_not and fits(zeros, ones, k-1, False):
            return True
        for i in range((k-1)//2+1):
            for w in levels[i]:
                if not (w & zeros) and w & ones and fits(ones & ~w, zeros, k-i-1, True):
                    return True
                if w & ones == ones and zeros & ~w and fits(ones, zeros & w, k-i-1, True):
                    return True
        return False

    return fits(MASK, full ^ MASK, budget, True)


def supports():
    # Unread row indicators must all have the same row signature, and likewise for columns.
    target_rows = [(MASK >> (5*i)) & 31 for i in range(5)]
    target_cols = [sum(((MASK >> (5*i+j)) & 1) << i for i in range(5)) for j in range(5)]
    perms = []
    for swap in range(2):
        r = [4,1,3,2,0] if swap else list(range(5))
        for a in range(2):
            for b in range(2):
                c = [a,1-a,2,3+b,4-b]
                if swap:
                    c = [j+3 if j < 2 else j-3 if j > 2 else j for j in c]
                assert all(((MASK >> (5*i+j)) ^ (MASK >> (5*r[i]+c[j]))) & 1 == 0 for i in range(5) for j in range(5))
                perms.append(r+[5+j for j in c])
    found = set()
    for m in range(1024):
        if len({v for i,v in enumerate(target_rows) if not m & 1<<i})>1:continue
        if len({v for j,v in enumerate(target_cols) if not m & 1<<(5+j)})>1:continue
        orbit = [sum(1<<p[i] for i in range(10) if m & 1<<i) for p in perms]
        found.add(min(orbit))
    return sorted(found,key=lambda m:(m.bit_count(),m))


def search(size,backend,one_case):
    from pysat.solvers import Solver
    e = Encoding(size)
    cases = [m for m in supports() if m.bit_count() <= size+1]
    if one_case is not None:
        if one_case not in cases:raise ValueError("Support is not a feasible representative at this size.")
        cases = [one_case]
    with Solver(name=backend,bootstrap_with=e.clauses) as solver:
        for m in cases:
            assumptions = [v if m & 1<<i else -v for i,v in enumerate(e.used)]
            sat = solver.solve(assumptions=assumptions)
            print(f"size {size}, support {m}, {'SAT' if sat else 'UNSAT'}",flush=True)
            if sat:
                gates = e.decode(solver.get_model())
                assert evaluate(gates) == MASK
                print("GATES",gates,flush=True)
                return True
    return False


def search_nine(backend):
    """Use the checked monotone lower bound and the independent formula exclusion."""
    from pysat.solvers import Solver
    assert not has_small_formula(9)
    e = Encoding(9)
    negations = [ops[2] for _, _, ops in e.ports]
    for m in supports():
        for k in (1, 2):
            if m.bit_count() + k > 9:
                continue
            clauses = list(e.clauses)
            clauses.extend([[-v for v in subset] for subset in combinations(negations, k+1)])
            clauses.extend([list(subset) for subset in combinations(negations, 10-k)])
            for i, flag in enumerate(e.used):
                clauses.append([flag if m & (1 << i) else -flag])
            with Solver(name=backend, bootstrap_with=clauses) as solver:
                sat = solver.solve()
                print(f"size 9, support {m}, {k} NOTs: {'SAT' if sat else 'UNSAT'}", flush=True)
                if sat:
                    gates = e.decode(solver.get_model())
                    assert evaluate(gates) == MASK
                    print("GATES", gates, flush=True)
                    return True
    return False


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--nine-cases",action="store_true",help="check the nineteen remaining support and NOT-count cases")
    p.add_argument("--formulas",action="store_true",help="check whether nine gates suffice for a formula")
    p.add_argument("--size",type=int,choices=range(1,11))
    p.add_argument("--case",type=int)
    p.add_argument("--backend",default="cadical195")
    args=p.parse_args()
    assert evaluate(UPPER)==MASK
    if args.nine_cases:
        search_nine(args.backend)
        raise SystemExit(0)
    if args.formulas:
        print("Nine-gate formula exists:",has_small_formula(9))
        raise SystemExit(0)
    for size in ([args.size] if args.size is not None else range(6,10)):
        if search(size,args.backend,args.case):break
