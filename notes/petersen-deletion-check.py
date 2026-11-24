"""Check the isomorphisms, essential coordinates and numeric inputs to the signed-gate proof."""
from itertools import combinations, permutations, product
from pathlib import Path
import runpy

shared = runpy.run_path(str(Path(__file__).with_name("check-petersen-monotone.py")))
original = shared["original"]
elimination = shared["elimination"]


def edges(vertices):
    return {tuple(sorted((i,j))) for i,j in original if i in vertices and j in vertices}


def bijections(a,b):
    source, target = edges(a),edges(b)
    if len(source) != len(target):
        return
    for perm in permutations(b):
        renaming = dict(zip(a,perm))
        if {tuple(sorted((renaming[i],renaming[j]))) for i,j in source} == target:
            yield renaming


def first_gates(vertices, budget, zero):
    table,_,_ = shared["graph_data"](vertices)
    possible = []
    for i,j in combinations(range(len(vertices)),2):
        for a,b in product((0,1),repeat=2):
            cost = 0
            for p,q,forcing,other in ((i,j,a,b),(j,i,b,a)):
                slice_q = elimination["restrict"](table,q,other)
                v = p-int(q<p)
                assert elimination["restrict"](slice_q,v,0) != elimination["restrict"](slice_q,v,1)
                forced = elimination["lower"](elimination["restrict"](table,p,1))
                restricted = [zero[vertices[p]],forced]
                cost=max(cost,restricted[forcing]+3,restricted[1-forcing]+2)
            if cost <= budget:
                possible.append((vertices[i],vertices[j],a,b))
    return possible


def main():
    theta = [1,2,3,5,6,7,8]
    leaf_graph = [1,2,3,4,5,7,8]
    deletion = [0,1,2,3,4,5,7,8]
    six = (([2,3,5,6,7,8],8),([1,2,5,6,7,8],8),([1,3,5,6,7,8],7))
    for labels,lower in six:
        table,_,_=shared["graph_data"](labels)
        assert elimination["lower"](table) == lower-1
    assert elimination["lower"](shared["graph_data"](leaf_graph)[0]) == 7
    theta_bounds = {}
    for v in theta:
        subset = [i for i in theta if i != v]
        matched = [lb for labels,lb in six if next(bijections(subset,labels),None)]
        assert len(matched)==1
        theta_bounds[v] = matched[0]
    assert not first_gates(theta,8,theta_bounds)
    assert first_gates(theta,9,theta_bounds)==[(2,8,1,1)]
    bounds = {}
    for v in deletion:
        subset = [i for i in deletion if i!=v]
        cases = [cost for labels,cost in ((theta,10),(leaf_graph,9)) if next(bijections(subset,labels),None)]
        assert len(cases)==1
        bounds[v] = cases[0]
    assert not first_gates(deletion,10,bounds)
    seeds = first_gates(deletion,11,bounds)
    expected = {(i,j,1,1) for i,j in combinations((0,2,3,5),2)}
    assert set(seeds)==expected
    maps=list(bijections(deletion,deletion))
    orbit = lambda p,q: {tuple(sorted((d[p],d[q]))) for d in maps}
    assert orbit(0,2) | orbit(0,5) == {r[:2] for r in seeds}
    print("Theta zero-cofactor lower bounds:",theta_bounds)
    print("Eight-vertex zero-cofactor lower bounds:",bounds)
    print("Eight-vertex automorphisms:",len(maps),"seed orbit sizes:",len(orbit(0,2)),len(orbit(0,5)))

    # Each label sequence has a star upper bound from a minimum vertex cover.
    for vertices,limit in list(six)+[(leaf_graph,9),(theta,11),(deletion,13)]:
        es=edges(vertices)
        cover=next(c for k in range(1,len(vertices)+1) for c in combinations(vertices,k)
                   if all(i in c or j in c for i,j in es))
        stars={c:[] for c in cover}
        for i,j in es:
            center=i if i in cover else j
            stars[center].append(j if center==i else i)
        cost=sum(len(leaves) for leaves in stars.values()) + len(stars)-1
        assert cost<=limit
        for row in range(1<<len(vertices)):
            bit=lambda v: bool((row >> vertices.index(v)) & 1)
            assert any(bit(c) and any(bit(v) for v in leaves) for c,leaves in stars.items()) == any(bit(i) and bit(j) for i,j in es)
        print("Verified star control",vertices,cost,"gates")


if __name__=="__main__":
    main()
