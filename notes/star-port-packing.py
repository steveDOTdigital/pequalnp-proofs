"""Check simultaneous reader cuts and edge-star repairs on full truth tables."""
from itertools import combinations, product
from pathlib import Path
from runpy import run_path

frontier = run_path(str(Path(__file__).with_name("singleton-frontier.py")))
Circuit = frontier["Circuit"]
tables = frontier["tables"]
truth = frontier["truth"]
trim = frontier["rebuild"]


def subsets(items):
    items = tuple(items)
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def edge_row(edge):
    u, v = edge
    return 1 << ((1 << u) | (1 << v))


def saved_circuit(core, slots):
    """Set specified (gate index, input position) occurrences to zero and fold."""
    values = list(range(core.n))
    emitted = []
    for j, (op, a, b) in enumerate(core.gates):
        a = None if (j, 0) in slots else values[a]
        b = None if (j, 1) in slots else values[b]
        if a is None or b is None:
            new = None if op == "and" else (b if a is None else a)
        elif a == b:
            new = a
        else:
            new = core.n + len(emitted)
            emitted.append((op, a, b))
        values.append(new)
    root = values[core.output]
    return None if root is None else trim(Circuit(core.n, tuple(emitted), root))


def best_stars(edges):
    """A minimum vertex cover gives the least number of star centers."""
    if not edges:
        return []
    vertices = sorted(set().union(*edges))
    cover = next(s for s in subsets(vertices) if all(u in s or v in s for u, v in edges))
    groups = {v: [] for v in cover}
    for u, v in sorted(edges):
        center, neighbor = (u, v) if u in groups else (v, u)
        groups[center].append(neighbor)
    assert all(groups.values())
    return list(groups.items())


def reconstruct(n, core, protected):
    gates = [] if core is None else list(core.gates)
    root = None if core is None else core.output
    def gate(op, a, b):
        gates.append((op, a, b))
        return n + len(gates) - 1
    for center, neighbors in protected:
        alarm = neighbors[0]
        for y in neighbors[1:]:
            alarm = gate("or", alarm, y)
        star = gate("and", center, alarm)
        root = star if root is None else gate("or", root, star)
    assert root is not None
    return Circuit(n, tuple(gates), root)


def proof_masks(core, edge, ports):
    """Enumerate all sets of marked slots used by a successful proof on this edge."""
    proof = [{0} if x in edge else set() for x in range(core.n)]
    for j, (op, a, b) in enumerate(core.gates):
        left = {p | ports.get((j, 0), 0) for p in proof[a]}
        right = {p | ports.get((j, 1), 0) for p in proof[b]}
        proof.append(left | right if op == "or" else {p | q for p in left for q in right})
    return proof[core.output]


def matching(choices):
    owner = {}
    def place(i, visited):
        for edge in choices[i]:
            if edge in visited:
                continue
            visited.add(edge)
            if edge not in owner or place(owner[edge], visited):
                owner[edge] = i
                return True
        return False
    return all(place(i, set()) for i in range(len(choices)))


def star_tests(core, uncovered, x):
    tables_now = tables(core)
    away = sum(edge_row(e) for e in uncovered if x not in e)
    options = []
    for j, (_, a, b) in enumerate(core.gates):
        slots = [(j, p) for p, w in enumerate((a, b)) if not tables_now[w] & away]
        if slots:
            options.append(slots)
    for choice in product(*options):
        yield choice


def joint_price(protected, lost, remains):
    return len(lost) + len(best_stars(protected | lost)) - len(best_stars(protected)) - int(not remains)


def test_cuts(core, uncovered, x, slots, check_routes, protected):
    """Check joint loss against every routing; return the first affordable correction."""
    ports = {slot: 1 << j for j, slot in enumerate(slots)}
    incident = sorted(e for e in uncovered if x in e)
    proofs = [proof_masks(core, edge, ports) for edge in incident]
    assert all(proofs)
    expands = True
    repair = None
    for group in subsets(slots):
        if not group:
            continue
        mask = sum(ports[p] for p in group)
        after = saved_circuit(core, set(group))
        table = 0 if after is None else tables(after)[after.output]
        lost = {e for e in uncovered if not table & edge_row(e)}
        assert lost == {e for e, ways in zip(incident, proofs) if all(t & mask for t in ways)}
        saved = len(core.gates) - (0 if after is None else len(after.gates))
        assert saved >= len(group)
        expands &= len(group) <= len(lost)
        price = joint_price(protected, lost, after is not None)
        if repair is None and saved >= price:
            repair = (after, lost, saved, price)
    if check_routes:
        robust = True
        for routing in product(*proofs):
            choices = [[e for e, mask in zip(incident, routing) if mask & (1 << j)]
                       for j in range(len(slots))]
            if not matching(choices):
                robust = False
                break
        assert robust == expands
    return repair


def peel(c, edges):
    core = trim(c)
    protected = []
    uncovered = set(edges)
    expected = truth(c.n, edges)
    previous = len(core.gates)
    steps = []
    while core:
        change = None
        for x in range(c.n):
            for slots in star_tests(core, uncovered, x):
                change = test_cuts(core, uncovered, x, slots, True, set(edges) - uncovered)
                if change is not None:
                    break
            if change is not None:
                break
        if change is None:
            break
        core, lost, saved, price = change
        uncovered -= lost
        protected = best_stars(set(edges) - uncovered)
        rebuilt = reconstruct(c.n, core, protected)
        assert tables(rebuilt)[rebuilt.output] == expected
        assert len(rebuilt.gates) == previous - saved + price
        previous = len(rebuilt.gates)
        core_table = 0 if core is None else tables(core)[core.output]
        assert {e for e in edges if core_table & edge_row(e)} == uncovered
        steps.append((len(lost), saved, price))
    return len(c.gates), previous, len(uncovered), steps


def main():
    control = Circuit(4, (("or",0,1),("or",0,2),("and",4,5),("and",1,2),
                          ("or",3,7),("and",6,8),("or",4,5),("and",9,10)), 11)
    print("eight-gate matching:", peel(control, {(0,3),(1,2)}))
    # Lift the same overlapping singleton fork to two branching endpoints.
    inputs = 6
    lifted = []
    mapping = {0:0, 1:1, 2:2, 3:3}
    for x, y in [(0,4),(1,5)]:
        lifted.append(("or", x, y))
        mapping[x] = inputs + len(lifted) - 1
    for j, (op, a, b) in enumerate(control.gates):
        lifted.append((op, mapping[a], mapping[b]))
        mapping[4+j] = inputs + len(lifted) - 1
    c = Circuit(inputs, tuple(lifted), mapping[control.output])
    print("two three-vertex paths:", peel(c, {(0,3),(3,4),(1,2),(2,5)}))
    # A center available only after reorienting the already extracted edge.
    prior = {(0,1)}
    core = Circuit(4, (("or",1,3), ("and",4,2)), 5)
    residual = saved_circuit(core, {(0,0)})
    lost = {(1,2)}
    assert residual is not None and best_stars(prior)[0][0] == 0
    assert len(core.gates) - len(residual.gates) == joint_price(prior, lost, True) == 1
    before = reconstruct(4, core, best_stars(prior))
    after = reconstruct(4, residual, best_stars(prior | lost))
    assert len(before.gates) == len(after.gates) == 4 and best_stars(prior | lost)[0][0] == 1
    assert tables(before)[before.output] == tables(after)[after.output] == truth(4, prior | lost | {(2,3)})
    print("reoriented four-vertex path: one saved gate pays for the added edge")
    # Two contexts illustrate why edgewise unavoidable slots are a stronger demand:
    # the first edge requires both slots, the second permits either singleton slot.
    routes = [[3], [1, 2]]
    assert all(matching([[e for e, mask in enumerate(r) if mask & (1 << i)]
                         for i in range(2)]) for r in product(*routes))
    mandatory = [[e for e, ways in enumerate(routes) if all(mask & (1 << i) for mask in ways)]
                 for i in range(2)]
    assert not matching(mandatory)


if __name__ == "__main__":
    main()
