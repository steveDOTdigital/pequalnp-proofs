"""Replay the Petersen 18-binary-gate search with one internal complemented wire.

The signed enumerator and the direct-reader profile generator are the ones used
for the 17-binary-gate exclusion. Gate counts refer to binary gates throughout.
"""
import argparse
import collections
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = Path(__file__).resolve().parent
driver = runpy.run_path(str(HERE / "petersen-unary-profiles.py"))
SOURCE = HERE / "petersen-raw-prefix.cpp"
HEADER = HERE / "petersen-profile-cuts.hpp"

STATE = r"""
    // Bit z tracks a circuit in which wire z may be read in both polarities.
    // Other wires use a single physical polarity relative to the truth table
    // normalized to zero on the all-zero input.
    std::array<std::array<unsigned,2>, maxWires> signs{};
    std::array<unsigned,maxWires> viableMarks{};
    std::array<Table,maxWires> slicePositive{}, sliceNegative{};
    Table graphEdges{}, independent{};

    void markBoundaries(int z, const Table& h) {
        // Inside either level of a monotone h, the physical suffix is monotone.
        Table pos=target, neg=~target;
        for (int v=0; v<n; ++v) {
            const int step=1<<v;
            const Table& raw=wires[v];
            pos &= ~(raw & (target<<step) & ~(h^(h<<step)));
            neg &= ~(~raw & ((~target)>>step) & ~(h^(h>>step)));
        }
        slicePositive[z]=pos;
        sliceNegative[z]=neg;
    }

    unsigned eligible(int wire, int opCode, int a, int b, const Table& value) {
        const int sa=opCode&1, sb=opCode>>1, flip=opCode==3;
        signs[wire][flip]=signs[a][sa]&signs[b][sb];
        signs[wire][!flip]=signs[a][!sa]&signs[b][!sb];
        const unsigned mark=1u<<wire;
        unsigned valid=viableMarks[wire-n] & (signs[wire][0]|signs[wire][1]);
        if (valid & mark) {
            if ((value & independent).none() || (~value & graphEdges).none())
                valid &= ~mark;
            else {
                markBoundaries(wire,value);
                signs[wire][1] |= mark;
            }
        }
        if (wire+1==n+budget) valid &= signs[wire][0];
        // A gate strictly after the marked wire can be replaced by any
        // available physical wire that dominates it on these slice boundaries.
        for (unsigned m=valid & (mark-1); m; m&=m-1) {
            const int z=__builtin_ctz(m);
            const unsigned bitZ=1u<<z;
            const Table actual=(signs[wire][0]&bitZ) ? value : ~value;
            const Table need=actual & slicePositive[z], avoid=~actual & sliceNegative[z];
            bool removable=need.none() || avoid.none();
            for (int j=0;j<wire && !removable;++j) {
                const Table& candidate=wires[j];
                if (signs[j][0]&bitZ)
                    removable=((need & ~candidate)|(avoid & candidate)).none();
                if (!removable && (signs[j][1]&bitZ))
                    removable=((need & candidate)|(avoid & ~candidate)).none();
            }
            if (removable) valid &= ~bitZ;
        }
        return valid;
    }
"""

def insert_once(s, needle, prefix):
    assert s.count(needle)==1
    return s.replace(needle,prefix+needle)

def build(temp):
    s=insert_once(SOURCE.read_text(), "    uint64_t nodes = 0;", STATE)
    # A reader can combine an operand with the complement of the gate that
    # used it. Normalizing such a reader in the unrestricted signed basis
    # could introduce another NOT. Keep it and use only one guaranteed
    # additional consumer when a pin forces one or more raw readers.
    guards={
        "if (SIGNED_MODE && b >= n && (lhs[b-n] == a || rhs[b-n] == a)) continue;": "",
        "std::min(2,int(readers[v][t]))": "int(readers[v][t]>0)",
        "std::min(2,int(readers[v][0]))": "int(readers[v][0]>0)",
    }
    for old,new in guards.items():
        assert s.count(old)==1
        s=s.replace(old,new)
    s=insert_once(s, "                    Table correct = ", """                    viableMarks[depth+1]=eligible(wire,isOr,a,b,val);
                    if (!viableMarks[depth+1]) continue;
""")
    s=insert_once(s, "        start=std::chrono", """        viableMarks[0]=((1u<<(n+budget))-1) & ~((1u<<n)-1);
        for (int v=0;v<n;++v) signs[v]={viableMarks[0],0};
        independent=~target;
        for (int r=0;r<(1<<n);++r) if (target.test(r) && __builtin_popcount(r)==2) graphEdges.set(r);
""")
    exe=temp/("search.exe" if os.name=="nt" else "search")
    source=temp/"search.cpp"
    macros=["WIDTH=10","SIGNED_MODE=1","PETERSEN_PAIR_MODE=2"]
    if os.environ.get("PETERSEN_ZIG"):
        compiler=[os.environ["PETERSEN_ZIG"],"c++"]
        if os.environ.get("PETERSEN_TARGET"):
            compiler.extend(["-target",os.environ["PETERSEN_TARGET"]])
    else:
        compiler=[os.environ.get("CXX","c++")]
    command=[*compiler,"-std=c++17","-O3",*["-D"+m for m in macros],str(source),"-o",str(exe)]
    source.write_text(s)
    shutil.copyfile(HEADER,temp/HEADER.name)
    subprocess.run(command,cwd=temp,check=True)
    return exe

def verify_slices():
    from itertools import combinations, product
    raw=driver['full']['RAW']
    target=driver['full']['TARGET']
    allrows=(1<<1024)-1
    def flip(x): return x^allrows
    # Cover raw ANDs, raw ORs and both three-input mixed gate shapes.
    markers=set()
    for mask in range(1,1<<10):
        conj,disj=allrows,0
        for v,x in enumerate(raw):
            if mask>>v&1:
                conj &= x
                disj |= x
        markers.update((conj,disj))
    for a,b in combinations(range(10),2):
        for c in range(10):
            if c not in (a,b):
                markers.update(((raw[a]&raw[b])|raw[c],(raw[a]|raw[b])&raw[c]))
    for h in markers:
        pos,neg=target,flip(target)
        for v,x in enumerate(raw):
            d=1<<v
            pos &= ~(x&(target<<d)&~(h^(h<<d)))
            neg &= ~(flip(x)&(flip(target)>>d)&~(h^(h>>d)))
        # Independently close upward/downward within each level of the marker.
        for level in (h,flip(h)):
            up,down=pos&level,neg&level
            for v,x in enumerate(raw):
                up |= (up<<(1<<v))&x&level
                down |= (down>>(1<<v))&flip(x)&level
            assert up==target&level and down==flip(target)&level
    # Check the two sign choices against physical AND/OR for all input bits.
    for a,b,sa,sb in product(range(2), repeat=4):
        flip_output=sa&sb
        canonical=((a^sa)&(b^sb))^flip_output
        assert canonical^flip_output==(a^sa)&(b^sb)
        assert canonical^(1^flip_output)==(a^sa^1)|(b^sb^1)
    print('Verified slice boundaries on all 1024 rows for',len(markers),'markers.',flush=True)

def omit_verified_raw_orbits(inp, tag, excluded):
    """Forbid raw pairs already excluded as first gates at this same profile."""
    mask,seed=tag
    excluded_here={gate for profile,gate in excluded if profile==mask}
    if not excluded_here:
        return inp
    if seed in excluded_here:
        raise ValueError('The case being tested cannot be an exclusion premise.')
    counts=[1+((mask>>(2*v))&3) for v in range(10)]
    stabilizer=[g for g in driver['GROUP'] if all(counts[g[v]]==counts[v] for v in range(10))]
    forbidden=set()
    for op,a,b in excluded_here:
        assert op in (0,3)
        for g in stabilizer:
            x,y=sorted((g[a],g[b]))
            forbidden.add((op,x,y))
    values=list(map(int,inp.split()))
    assert values[0]==18 and values[3]==mask
    pos=4+values[2]+2*10+3*45
    assert values[pos:pos+4]==[1,*seed]
    pos+=4
    end=pos+1+3*values[pos]
    raw=[tuple(values[i:i+3]) for i in range(pos+1,end,3)]
    keep=[gate for gate in raw if gate not in forbidden]
    assert seed in keep and len(keep)<len(raw)
    replacement=[len(keep)]+[v for gate in keep for v in gate]
    return ' '.join(map(str,values[:pos]+replacement+values[end:]))+'\n'

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--workers',type=int,default=4)
    p.add_argument('--seconds',type=int,default=45)
    p.add_argument('--slice',type=int,nargs=2)
    p.add_argument('--case',type=int,nargs=4,action='append',
                   metavar=('PROFILE','OP','A','B'),help='rerun a reported unresolved case')
    p.add_argument('--exclude-verified',type=int,nargs=4,action='append',default=[],
                   metavar=('PROFILE','OP','A','B'),help='use a previously completed first-gate exclusion')
    args=p.parse_args()
    verify_slices()
    f,l=driver['bounds'](10,False)
    cases=[(tag,inp) for tag,inp in driver['problems'](10,False,18,args.seconds,f,l) if tag[1][0] in (0,3)]
    excluded={(mask,(op,a,b)) for mask,op,a,b in args.exclude_verified}
    if not excluded.issubset(tag for tag,_ in cases): p.error('unknown first-gate exclusion')
    if excluded and not args.case: p.error('select the target cases when using previous exclusions')
    if args.slice: cases=cases[slice(*args.slice)]
    if args.case:
        requested={(mask,(op,a,b)) for mask,op,a,b in args.case}
        cases=[c for c in cases if c[0] in requested]
        if {c[0] for c in cases}!=requested: p.error('unknown case in selected range')
    print('Cases:',len(cases),flush=True)
    with tempfile.TemporaryDirectory(prefix='petersen-4727-') as td:
        exe=build(Path(td))
        def invoke(inp):
            return subprocess.check_output([str(exe)],input=inp,text=True,timeout=args.seconds+30).splitlines()
        control=invoke(driver['control'](10,args.seconds,f,l))
        assert control[-1].startswith('SAT '),control
        def check(case):
            tag,inp=case
            result=invoke(omit_verified_raw_orbits(inp,tag,excluded))
            return tag,result
        counts=collections.Counter()
        nodes=0
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            for i,(tag,result) in enumerate(pool.map(check,cases),1):
                verdict,num=result[-1].split()
                nodes+=int(num)
                counts[verdict]+=1
                if verdict!='UNSAT': print(tag,result,flush=True)
                if i%75==0: print(i,dict(counts),nodes,flush=True)
        print('Final:',dict(counts),nodes,flush=True)
    assert not Path(td).exists()
    if counts!={'UNSAT':len(cases)}: raise SystemExit('Incomplete exclusion.')

if __name__=='__main__':
    main()
