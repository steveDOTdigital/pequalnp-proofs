"""Count Petersen cuts that require two NOTs after hiding two raw coordinates."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import argparse
import runpy

data=runpy.run_path(str(Path(__file__).resolve().with_name('petersen-free-or-certificate.py')))
target=data['TARGET']
group=tuple(data['automorphisms']())
truth=[(target>>row)&1 for row in range(1024)]

def companion_pairs(a,b):
    """For each hidden input choose the OR of two visible coordinates."""
    return tuple(combinations((v for v in range(10) if v not in (a,b)),2))

def image(g,cut):
    return tuple(sorted((g[a],tuple(sorted(g[v] for v in pair))) for a,pair in cut))

def encode(row,cut):
    bits=row
    for i,(a,(b,c)) in enumerate(cut):
        bits &= ~(1<<a)
        h=(row>>a)&1
        t=((row>>b)|(row>>c))&1
        bits |= (h&t)<<(10+2*i)
        bits |= (h|t)<<(11+2*i)
    return bits

def maximum_drops(cut):
    hidden=sum(1<<a for a,_ in cut)
    visible=1023^hidden
    # Every transition increases the visible weight, or holds it fixed
    # and increases hidden weight. This order is therefore topological.
    order=sorted(range(1024),key=lambda x:((x&visible).bit_count(),(x&hidden).bit_count()))
    loss=[0]*1024
    parent=[-1]*1024
    companions=[(1<<a,(1<<b)|(1<<c)) for a,(b,c) in cut]
    def advance(x,y):
        new=loss[x]+int(truth[x]>truth[y])
        if parent[y]<0 or new>loss[y]:
            loss[y]=new
            parent[y]=x
    for x in order:
        unselected=1023^x
        while unselected:
            bit=unselected&-unselected
            unselected-=bit
            y=x|bit
            advance(x,y)
            if hidden&bit:continue
            can_fall=sum(h for h,comp in companions if x&h and not x&comp and bit&comp)
            subset=can_fall
            while subset:
                advance(x,y^subset)
                subset=(subset-1)&can_fall
    chain=[]
    row=1023
    while row!=-1:
        chain.append(row)
        row=parent[row]
    chain.reverse()
    pairs=[(x,y) for x,y in zip(chain,chain[1:]) if truth[x]>truth[y]]
    # Replay the order certificate in the original ten-variable truth table.
    assert all(encode(x,cut)&~encode(y,cut)==0 for x,y in zip(chain,chain[1:]))
    assert len(pairs)==loss[-1]<=2
    return loss[-1],pairs

def direct_drops(cut):
    # Independently search the full image poset for two successive drops.
    # A row's principal upper and lower sets are intersections of feature columns.
    all_rows=(1<<1024)-1
    raw=data['RAW']
    features=[bits for v,bits in enumerate(raw) if all(v!=a for a,pair in cut)]
    for a,(b,c) in cut:
        t=raw[b]|raw[c]
        features.extend((raw[a]&t,raw[a]|t))
    up_from_bad=0
    bad_predecessors=[]
    for n,value in enumerate(truth):
        if value:continue
        up=down=all_rows
        for col in features:
            if (col>>n)&1:up &= col
            else:down &= all_rows^col
        positive=down&target
        if positive:
            up_from_bad |= up
            bad_predecessors.append(positive)
    if any(p&up_from_bad for p in bad_predecessors):
        return 2
    return int(bool(bad_predecessors))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-certificates',action='store_true',
                        help='print the packed representatives and their four-row certificates')
    args=parser.parse_args()
    edges=data['EDGES']
    assert len(group)==len(set(group))==120
    assert all({tuple(sorted((g[a],g[b]))) for a,b in edges}==edges for g in group)
    example_cut=((0,(1,2)),(3,(1,4)))
    four_rows=(33,36,44,52)
    assert [truth[x] for x in four_rows]==[1,0,1,0]
    assert all(encode(x,example_cut)&~encode(y,example_cut)==0
               for x,y in zip(four_rows,four_rows[1:]))
    cuts={((a,u),(b,v)) for a,b in combinations(range(10),2)
          for u in companion_pairs(a,b) for v in companion_pairs(a,b)}
    assert len(cuts)==35280
    counts=Counter()
    orbits=Counter()
    example=None
    certificates=[]
    for cut in sorted(cuts):
        if cut not in cuts:continue
        orbit={image(g,cut) for g in group}
        assert orbit<=cuts
        cuts-=orbit
        n,witness=maximum_drops(cut)
        assert n==direct_drops(cut)
        counts[n]+=len(orbit)
        orbits[n]+=1
        if n==2 and example is None:
            example=cut,witness
        if n==2 and args.lean_certificates:
            variables=[v for a,pair in cut for v in (a,*pair)]
            code=sum(v<<(4*i) for i,v in enumerate(variables))
            points=[row for drop in witness for row in drop]
            evidence=sum(row<<(10*i) for i,row in enumerate(points))
            certificates.append((code,evidence))
    assert not cuts and counts=={1:3090,2:32190}
    assert orbits=={1:36,2:290}
    if args.lean_certificates:
        print(certificates)
        return
    print('Labeled configurations',dict(sorted(counts.items())))
    print('Automorphism orbits',dict(sorted(orbits.items())))
    print('Two-drop example',example)

if __name__=='__main__':
    main()
