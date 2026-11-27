# Independently switchable endpoints at every block length

This is a written proof of [L-lib-540](https://data.pequalnp.com/data/lemma/L-lib-540.2a2f8c3e7d11.json). Write w=d+1, D=2^w and take L≥w. The same base table works for both directions, with a different choice of ports. The full desk theorem is awaiting Lean verification.

## Reversible rows and the effect of one port

Represent w-bit states as a vector space over the two-element field. A reversible row takes a state (a,z), consisting of its first bit and its tail, to (z,a XOR f_i(z)). Let P_i be the permutation taking an initial state to its state just before row i, and choose the L default rows so that P_L is the identity. The base table permits exactly the default appended bit at every row and state.

An optional port at row i with current state P_i(x) permits the opposite appended bit. Equivalently, first flip the first coordinate of P_i(x), then apply the default row. The resulting state is the default state of label y at row i+1, where y=P_i⁻¹(P_i(x)+e₀) and e₀ is the first coordinate vector. For an affine prefix the difference δ_i=y−x is independent of x. In that case δ_i is the inverse of the linear part of P_i applied to e₀.

Suppose J is a set of selected affine-prefix rows whose δ_i are distinct and a nonzero linear form λ is one on every δ_i in J. Let B₀ and B₁ be its zero and one banks. Each has D/2 states by translation by any vector with λ=1. Index the m=|J|D/2 pairs by (i,x) with i∈J, x∈B₀, and use the edge (x,x+δ_i). These edges are distinct because the displacement identifies the row and the source identifies x. Every source is in B₀ and every target in B₁.

For the forward direction take the optional port at P_i(x) and for reverse at P_i(x+δ_i), in each case with its nondefault bit. In either direction these ports are distinct: their row fixes the displacement and their current state fixes the starting label. The base entry is false by choice of appended bit. Following default rows keeps the current label; taking a port switches to the target label. There can be at most one switch, since all its possible targets are in the bank disjoint from the current direction's source bank. For any subset of the ports the default trajectory is the unique path from x to x. An off-diagonal pair has one path exactly when its port is enabled, since its edge identifies the unique switch. All other pairs have zero paths.

The allowed word of length L+w and its trajectory determine each other. Use its first w bits for the starting window, then append the chosen bit at each of the L rows. Conversely the successive states overlap in w−1 positions and determine those bits. The desk's addresses i+off and L+pos are less than L+w in their stated ranges, so the use of Fin.ofNat leaves the addresses unchanged. This proves the exact count in the assignment once the supply of rows J is established.

## Short lengths

For w≤L<10w apply the accepted [identity case of L-lib-471](https://data.pequalnp.com/data/lemma/L-lib-471.c24d6fde57d2.json) to obtain affine reversible rows with identity total. For i=0,…,w−1 the first w−i coordinates after i shifts are untouched original coordinates i,…,w−1. The inverse linear prefix applied to e₀ therefore gives a δ_i whose coordinate i is 1 and whose later coordinates are zero. Consequently these w displacements are a basis. There is a linear form equal to one on each of them. Taking all w rows gives 20m=10wD≥D min(L,D).

## Long lengths

For L≥10w put t=min(L−5w,D−1). There is a linear reversible shift T whose nonzero vectors each have orbit length D−1. Here is a construction. In the field F with 2^w elements take a generator α of its multiplicative group. Its first w powers form a basis over the two-element field, since the powers of α span the field and a power relation of degree below w would bound their span by that smaller degree. Identify a state with the values of a linear functional f on 1,α,…,α^(w−1). The action f↦(u↦f(αu)) shifts the first w−1 coordinates forward. In the last coordinate the coefficient of the dropped bit is one, because in the basis expression for α^w a zero constant coefficient would, after division by α, contradict independence of the basis. This gives the claimed reversible shift. If a nonzero functional were fixed by a kth power with 0<k<D−1, it would annihilate all (α^k−1)u. Multiplication by that nonzero scalar is surjective, a contradiction. Mathlib supplies [finite fields of the required cardinality](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Finite/GaloisField.html) and the cyclicity of their multiplicative groups.

Use T for the first t rows. Then use [L-lib-394](https://data.pequalnp.com/data/lemma/L-lib-394.0cabec908dfb.json) to implement the inverse of T^t in 4w rows, and L-lib-471 with zero translation to pad the remaining L−t−4w≥w rows. The undo can be nonlinear. Only the first t prefixes enter the port construction, and their displacements T^(-i)e₀ are all distinct since t≤D−1.

Each nonzero displacement has value one under exactly half of the linear forms. Averaging over linear forms therefore gives a form with value one on at least t/2 of the t displacements. It is nonzero since t≥1. Select those rows. As L−5w≥L/2 and D−1≥D/2, we have 2t≥min(L,D). Thus 4m≥Dt and 8m≥D min(L,D), which implies the claimed 20m bound.

## Finite controls

The replay uses actual reversible row permutations. At widths one through four it checks lengths from w through 12w+2, including the affine identity and maximal-period branches. It checks ports, the numerical bound and both direction counts, exhaustively over enable sets when there are at most eight ports and with deterministic sampled sets otherwise. At every enabled-set check it counts all state paths, including multiplicity, from every start.

```python
from random import Random
rng=Random(540)

def run_checks(w):
    D=1<<w
    I=tuple(range(D))
    parity=lambda n:n.bit_count()&1
    tables=[tuple((x>>1)|(((x&1)^parity((x>>1)&tap))<<(w-1)) for x in I)
            for tap in range(1<<(w-1))]
    def compose(a,b):return tuple(a[x] for x in b)
    def inv(a):return tuple(a.index(i) for i in I)
    def order(a):
        s=1
        for k in range(1,D):
            s=a[s]
            if s==1:return k
        raise AssertionError('bad permutation')
    step=next(k for k,a in enumerate(tables) if order(a)==D-1)
    # Finite witness search only. The general length resets are L-lib-471
    # and L-lib-394. These small tests happen to use linear resets.
    prev=[{I:None}]
    for L in range(1,12*w+3):
        nxt={}
        for state in prev[-1]:
            for j,a in enumerate(tables):
                nxt.setdefault(compose(a,state),(state,j))
        prev.append(nxt)
    def find(L,target):
        path=[]
        for i in range(L,0,-1):
            target,j=prev[i][target]
            path.append(j)
        assert target==I
        return list(reversed(path))
    total_cases=0
    for L in range(w,12*w+3):
        if L<10*w:
            base=find(L,I)
            usable=w
        else:
            usable=min(L-5*w,D-1)
            prefix=I
            for _ in range(usable):prefix=compose(tables[step],prefix)
            base=[step]*usable+find(4*w,inv(prefix))+find(L-usable-4*w,I)
        state=[I]
        for tap in base:state.append(compose(tables[tap],state[-1]))
        assert len(base)==L and state[-1]==I
        motion=[inv(a)[1] for a in state[:usable]]
        assert len(motion)==len(set(motion)) and 0 not in motion
        color=max(range(1,D),key=lambda n:sum(parity(n&v) for v in motion))
        if L<10*w:assert all(parity(color&v) for v in motion)
        edges=[(x,x^v,i) for i,v in enumerate(motion) if parity(color&v)
               for x in I if not parity(color&x)]
        assert D*min(L,D)<=20*len(edges)
        assert len(edges)==len({(x,y) for x,y,i in edges})
        assert all(parity(color&y) for x,y,i in edges)
        for reverse in (False,True):
            ordered=[(y,x,i) if reverse else (x,y,i) for x,y,i in edges]
            ports=[(i,state[i][x],tables[base[i]][state[i][x]]^(1<<(w-1))) for x,y,i in ordered]
            assert len(set(ports))==len(ports)
            assert all(t!=tables[base[i]][a] for i,a,t in ports)
            assert all(t==state[i+1][y] for (i,a,t),(x,y,_) in zip(ports,ordered))
            choices=(range(1<<len(edges)) if len(edges)<=8 else
                     [0,(1<<len(edges))-1,*[rng.getrandbits(len(edges)) for _ in range(24)]])
            for bits in choices:
                wanted={(x,x):1 for x in I}
                extras={}
                for j,(x,y,i) in enumerate(ordered):
                    if bits>>j&1:
                        wanted[x,y]=1
                        t,a,b=ports[j]
                        extras[t,a]=b
                reached={}
                for x in I:
                    paths={x:1}
                    for i,tap in enumerate(base):
                        nxt={}
                        for a,count in paths.items():
                            z=tables[tap][a]
                            for b in {z,extras.get((i,a),z)}:
                                nxt[b]=nxt.get(b,0)+count
                        paths=nxt
                    reached.update({(x,y):c for y,c in paths.items()})
                assert reached==wanted
                total_cases+=1
    print('width',w,'lengths',w,'to',12*w+2,':',total_cases,'direction/subset checks',flush=True)

for w in range(1,5):run_checks(w)
```
