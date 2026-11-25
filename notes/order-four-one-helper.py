"""Find directly checkable cross certificates for a sole shared two-input OR gate."""
from itertools import combinations
from pathlib import Path
import runpy

geo = runpy.run_path(str(Path(__file__).with_name("order-four-alarm-rank.py")))
flags, keep, match = (geo[k] for k in ("flags","keep","match"))
N, ALL = 21,(1<<21)-1
def mask(indices):
    return sum(1<<i for i in indices)
near = list(map(mask,geo["near"].values()))
alarms = list(map(mask,geo["alarms"]))
special = mask(geo["special"])
edges = tuple(keep)
around = {(p,l):{(q,m) for q,m in edges if p==q or l==m} for p,l in edges}
raw = [(1<<p,0) for p in range(N)] + [(0,1<<l) for l in range(N)]
inputs = raw + [(0,s) for s in alarms]

def rotate(s):
    return [((a<<3)&ALL | a>>18, (b<<3)&ALL | b>>18) for a,b in s]

def fits(P,L,p,l,H,forbidP,forbidL):
    hp,hl = H
    needH = bool((hp>>p | hl>>l)&1)
    for add in [0]+[1<<q for q in range(N) if hp>>q&1]:
        S = P | add
        if S & forbidP:
            continue
        lines = ALL ^ forbidL
        for q in range(N):
            if S>>q&1:
                lines &= ~near[q]
        if L & ~lines:
            continue
        if needH and not (S&hp or lines&hl):
            continue
        if all(not(a>>l&1) or a&lines for a in alarms):
            return True
    return False

def failure(rows,H):
    for p,l in sorted(rows):
        adj = around[p,l] & rows
        P = mask(q for q,m in adj if m==l and q!=p)
        L = mask(m for q,m in adj if q==p and m!=l)
        if not fits(P,L,p,l,H,1<<p,1<<l):
            return adj
        if not P and not fits(1<<p,0,p,l,H,0,1<<l):
            return {(p,l)}
        if not L and not fits(0,1<<l,p,l,H,1<<p,0):
            return {(p,l)}
    return set()

def certify(H,floor):
    stack = [frozenset(edges)]
    seen = set()
    while stack:
        rows = stack.pop()
        if rows in seen:
            continue
        seen.add(rows)
        if len(rows)+21<floor or len(rows)+len(match(rows))<floor:
            continue
        issue = failure(rows,H)
        if not issue:
            return rows
        for bad in sorted(issue):
            stack.append(rows-{bad})
    return None

def near_covers():
    # Exactly one diagonal pair has both endpoints in a 22-vertex cover.
    # Among the other twenty, the pairs choosing their line form a closed
    # set in the directed graph obtained by deleting that double pair.
    covers = []
    for z in range(N):
        rest = set(range(N))-{z}
        reachable = {i:{i} for i in rest}
        for i in rest:
            for _ in rest:
                reachable[i] |= {l for p,l in edges if p in reachable[i] and l != z}
        closed = {frozenset()}
        for i in rest:
            closed |= {s | reachable[i] for s in closed}
        for s in closed:
            P,L = rest-set(s)|{z},set(s)|{z}
            assert len(P)+len(L)==22 and all(p in P or l in L for p,l in edges)
            covers.append((P,L))
    assert len(covers)==56
    return covers

def run():
    result = {}
    covers = near_covers()
    for i,j in combinations(range(42),2):
        p1,l1 = inputs[i]
        p2,l2 = inputs[j]
        H = p1|p2,l1|l2
        if H in result:
            continue
        if certify(H,101) is not None:
            reason = "rank 101"
        else:
            assert i < 21 <= j
            p,l = i,j-21
            assert any(fits(0,1<<m,q,m,H,1<<q,0) for q,m in flags if q==p)
            dp = sum(q==p for q,m in edges)
            dl = sum(m==l for q,m in edges)
            if min(dp,dl)==2:
                reason = "mixed pair with a degree-two endpoint"
            else:
                assert certify(H,100) is not None
                assert any(fits(1<<q,0,q,m,H,0,1<<m) for q,m in flags if m==l)
                for P,L in covers:
                    # A reporting vertex can miss only toward a reporting neighbor.
                    up = 1+sum(q==p and m in L for q,m in edges) if p in P else dp
                    ul = 1+sum(m==l and q in P for q,m in edges) if l in L else dl
                    assert min(up,ul)<4
                reason = "mixed pair with two private reports"
        current = [H]
        for _ in range(7):
            result[current[0]] = reason
            current = rotate(current)
    assert len(result)==861
    for reason in sorted(set(result.values())):
        print(reason,sum(v==reason for v in result.values()))
    print("All 861 distinct raw OR helpers excluded at every fanout.")

if __name__ == "__main__":
    run()
