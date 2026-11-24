"""Classify all monotone completions of the four-pencil quadrangle core."""
from itertools import permutations
from pathlib import Path
import runpy

geometry = runpy.run_path(str(Path(__file__).with_name("quadrangle-star-cores.py")))
bounds = runpy.run_path(str(Path(__file__).with_name("plane-small-core-bounds.py")))
MISSING=((15,23,27,90,120,150,180,210,270,300,330,390),
         (7,11,13,19,21,25,120,180,210,300,330,390))
def verify_four_frames():
    from itertools import product
    lines = geometry["LINES"]
    counts = dict.fromkeys(MISSING,0)
    permutations_of_rows = []
    for ordering in permutations(range(4)):
        mapping = [0,*[1+i for i in ordering],*[5+i for i in ordering]]
        permutations_of_rows.append([sum(1 << dest for i,dest in enumerate(mapping) if x & (1<<i))
                                     for x in range(512)])
    for c in range(13):
        arms = [i for i,line in enumerate(lines) if c in line]
        for reps in product(*(sorted(lines[i]-{c}) for i in arms)):
            _,negatives = geometry["project"](arms,[c,*reps])
            signature = min(tuple(sorted(mapping[x] for x in negatives))
                            for mapping in permutations_of_rows)
            counts[signature] += 1
            aligned = any(set(reps) <= line for line in lines)
            assert aligned == (signature == MISSING[1])
    assert tuple(counts.values()) == (936,117)
    return counts


def choices(unknown):
    supers={x:{y for y in unknown if x&y==x} for x in unknown}
    subs={x:{y for y in unknown if x&y==y} for x in unknown}
    def rec(left,selected):
        if not left:
            yield frozenset(selected)
            return
        x=min(left)
        yield from rec(left-subs[x],selected)
        up=left & supers[x]
        yield from rec(left-up,selected|up)
    yield from rec(set(unknown),set())

def completions(yes,no):
    xs=[x for x in range(512) if not any(x&e==e for e in yes) and not any(x&z==x for z in no)]
    def permute(x,p):
        return sum(1<<v for i,v in enumerate(p) if x&(1<<i))
    syms=[]
    for order in permutations(range(4)):
        p=[0,*[1+i for i in order],*[5+i for i in order]]
        if {permute(x,p) for x in no}==set(no):
            syms.append({x:permute(x,p) for x in xs})
    seen=set();reps=[]
    for hi in choices(xs):
        if hi not in seen:
            reps.append(hi)
            seen.update(frozenset(p[x] for x in hi) for p in syms)
    return len(xs),len(seen),reps

if __name__=="__main__":
    import sys
    print("Raw frames",list(verify_four_frames().values()),flush=True)
    yes,base=geometry["pencil_four"]()
    for no in (base,*MISSING):
        n,total,reps=completions(yes,no)
        print(n,total,len(reps),flush=True)
        if "--check" not in sys.argv:continue
        f=sum(1<<x for x in range(512) if any(x&e==e for e in yes))
        left=[]
        for hi in reps:
            if hi and not bounds["excludes_two_extra_reads"](9,f|sum(1<<x for x in hi)):
                left.append(sorted(hi))
            bounds["block"].cache_clear()
            bounds["read_once"].cache_clear()
        print("Noncanonical survivors",len(left),left[:8],flush=True)
        assert not left
