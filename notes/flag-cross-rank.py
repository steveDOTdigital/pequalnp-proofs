"""Sparse negative tests and single-helper exclusions for projective-plane formulas."""
from fractions import Fraction
from itertools import product


def plane(q):
    # Representatives with first nonzero homogeneous coordinate equal to one.
    vectors = [(1,x,y) for x in range(q) for y in range(q)]
    vectors += [(0,1,y) for y in range(q)] + [(0,0,1)]
    return {(p,l) for p,a in enumerate(vectors) for l,b in enumerate(vectors)
            if sum(i*j for i,j in zip(a,b)) % q == 0}


def rank(matrix):
    a = [list(map(Fraction, row)) for row in matrix]
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r,len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        for i in range(r+1,len(a)):
            scale = a[i][j] / a[r][j]
            if scale:
                a[i] = [u-scale*v for u,v in zip(a[i],a[r])]
        r += 1
    return r


def verify(q):
    edges = plane(q)
    n, d = q*q+q+1, q+1
    points = [{p for p in range(n) if (p,l) in edges} for l in range(n)]
    lines = [{l for l in range(n) if (p,l) in edges} for p in range(n)]
    assert len(edges) == n*d
    for p,l in edges:
        a,b = points[l]-{p}, lines[p]-{l}
        assert len(a) == len(b) == q and not any((x,y) in edges for x in a for y in b)
        assert all(x in a or lines[x] & b for x in range(n))
        assert all(y in b or points[y] & a for y in range(n))
        assert all(y in b for y in lines[p]-{l}) and all(x in a for x in points[l]-{p})
    # Local pattern rank depends only on the number of missing diagonal entries.
    for pattern in product([0,1], repeat=d):
        matrix = [[int(i != j or pattern[i]) for j in range(d)] for i in range(d)]
        assert rank(matrix) == pattern.count(0) + int(any(pattern))
    print(f"q={q}: {len(edges)} negative crosses, {n*(q+2)} leaves, {n*(q+2)-1} gates")


def max_cold(q, a):
    n = q*q+q+1
    d = q+1
    first = a*q*d
    second = first + a*(a-1)*(q-1)
    return n*d - (first*first+second-1)//second


def excluded_from(q):
    n,d = q*q+q+1,q+1
    allowed = [a for a in range(q+2,n+1)
               if a + 2 <= max_cold(q,a) + max_cold(q,a)//d]
    return max(allowed,default=q+1)+1


if __name__ == "__main__":
    for prime in (2,3,5,7):
        verify(prime)
    print("point-singleton counts excluded for a sole shared wire")
    for q in (2,3,4,5,7,8,9,11,13,16,25,101):
        print(q, excluded_from(q))
