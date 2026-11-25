"""Integer rectangle prices for one free OR on the 234 quadrangle tests.

Run with NumPy and SciPy. The optimizer is only used to propose weights.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import argparse
import math
import runpy

library = runpy.run_path(str(Path(__file__).with_name('generic-helper-price.py')))
edges, perms, price = (library[k] for k in ('edges', 'perms', 'price'))
negative = library['previous']['neg']
columns = sorted(sum(1 << i for i in row) for row in negative)
assert len(set(columns)) == len(columns) == 234
assert all(not any((c >> a) & (c >> b) & 1 for a, b in edges) for c in columns)
members = [[i for i in range(26) if c >> i & 1] for c in columns]
geometry = (columns, {c:i for i,c in enumerate(columns)}, members,
            [sum(1 << t for t,c in enumerate(columns) if c >> i & 1) for i in range(26)])
pairs = sorted((1 << u) | (1 << v) for u,v in combinations(range(26), 2))
full = (1 << len(edges)) - 1

def variables(mask):
    return [v for v in range(26) if mask >> v & 1]

def investigate(key, stabilizer, budget=None, tight=False):
    hot = [sum(1 << i for i,(a,b) in enumerate(edges) if h & ((1 << a) | (1 << b))) for h in key]
    compulsory = []
    for column in columns:
        required = full
        for h, flags in zip(key, hot):
            if not column & h:
                required &= ~flags
        compulsory.append(required)
    arguments = dict(override=(stabilizer, set(), 0, compulsory), geometry=geometry)
    bound = price(0, **arguments)[0]
    if len(key) == 1 and bound < 64:
        bound = max(bound, price(0, refine=True, **arguments)[0])
    if bound <= (63 if len(key) == 1 else (64-3*len(key) if budget is None else budget)):
        bound = max(bound, price(0, pair_ref=key, **arguments)[0])
    target = 65-3*len(key)
    if tight and bound <= target:
        bound = max(bound, price(0, pair_ref=key, **arguments)[0])
    if tight and bound <= target:
        bound = max(bound, price(0, refine=True, **arguments)[0])
    if tight and bound <= target:
        bound = max(bound, price(0, refine=True, pair_ref=key, **arguments)[0])
    return bound

def check(count, tight=False):
    seen = set()
    histogram = Counter()
    for key in combinations(pairs, count):
        if key in seen:
            continue
        inputs = [variables(h) for h in key]
        images = [tuple(sorted(sum(1 << g[i] for i in v) for v in inputs)) for g in perms]
        stabilizer = [g for g,image in zip(perms,images) if image == key]
        orbit = set(images)
        assert not orbit & seen and all(h in pairs for h in key)
        seen.update(orbit)
        bound = investigate(key, stabilizer, tight=tight)
        histogram[bound] += 1
        print(count, 'OR inputs', inputs, 'raw leaves', bound, flush=True)
    assert len(seen) == math.comb(len(pairs), count)
    assert min(histogram) >= (63 if count == 1 else (60 if tight else 59))
    print('Histogram', count, sorted(histogram.items()), 'labeled cases', len(seen), flush=True)

def single_supports():
    reps=[0]
    for size in range(1,5):
        reps=library['previous']['orbit_reps'](size,reps)
        if size<3:continue
        results=Counter()
        for h in reps:
            vs=variables(h)
            fix=[g for g in perms if sum(1<<g[i] for i in vs)==h]
            results[investigate((h,),fix)]+=1
        assert min(results)>63-size
        print('Single disjunction size',size,sorted(results.items()),flush=True)

def relatives(nested=False,tight=False):
    result=Counter()
    for size in ((3,) if nested else range(3,5)):
        reps=[0]
        for n in range(1,size+1):reps=library['previous']['orbit_reps'](n,reps)
        for support in reps:
            raw=variables(support)
            local=[(1<<a)|(1<<b) for a,b in combinations(raw,2)]
            stab=[g for g in perms if sum(1<<g[v] for v in raw)==support]
            for count in ([2] if nested else range(3,len(local)+1)):
                choices=([(h,support) for h in local] if nested else combinations(local,count))
                seen=set()
                for key in choices:
                    key=tuple(sorted(key))
                    union=0
                    for h in key:union|=h
                    if union!=support or key in seen:continue
                    images=[tuple(sorted(sum(1<<g[v] for v in variables(h)) for h in key)) for g in stab]
                    seen.update(images)
                    subgroup=[g for g,image in zip(stab,images) if image==key]
                    budget=59 if nested else 64-3*count
                    bound=investigate(key,subgroup,budget,tight)
                    result[count,bound]+=1
                    if bound<=budget:print('Unresolved',key,bound,budget,flush=True)
                    if tight and bound<=65-3*count:
                        print('Equality case',key,bound,flush=True)
                possible=([(h,support) for h in local] if nested else combinations(local,count))
                expected={tuple(sorted(key)) for key in possible if all(any(h>>v&1 for h in key) for v in raw)}
                assert seen==expected
    if nested:
        assert sum(result.values()) == 18 and min(bound for count,bound in result) >= 60
    else:
        expected = {3:(176,56),4:(163,53),5:(74,52),6:(25,49)}
        for h,(number,minimum) in expected.items():
            assert sum(n for (k,_),n in result.items() if k==h)==number
            assert min(bound for k,bound in result if k==h)>=minimum
        if tight:
            assert result[3,56]==2 and min(bound for k,bound in result if k==4)>=54
    print('Nested' if nested else 'Pairs on four',sorted(result.items()),flush=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('count', nargs='?', type=int, choices=(1,2))
    parser.add_argument('--generic-control', action='store_true')
    parser.add_argument('--nested', action='store_true')
    parser.add_argument('--four', action='store_true')
    parser.add_argument('--tight', action='store_true')
    parser.add_argument('--disjunctions', action='store_true')
    args = parser.parse_args()
    if args.disjunctions:
        single_supports()
    elif args.nested or args.four:
        relatives(args.nested,args.tight)
    elif args.generic_control:
        library['raw_disjunctions']()
        print('Original 468-column bounds reproduced')
    else:
        for count in ([args.count] if args.count else [1,2]):
            check(count,args.tight)
