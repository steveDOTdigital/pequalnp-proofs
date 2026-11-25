"""Check local leaf families for the subquartic monotone formula bound."""
from itertools import combinations_with_replacement

def ones(x):return bin(x).count('1')

def dominated(rows):
    return sum(any(j!=i and (other & row)==other for j,other in enumerate(rows))
               for i,row in enumerate(rows))

def check():
    for degree in range(2,5):
        for leaves in range(1,degree):
            best=degree
            eligible=0
            for rows in combinations_with_replacement(range(1,1<<leaves),degree):
                if not any(all(ones(r&active)==1 for r in rows)
                           for active in range(1,1<<leaves)):continue
                best=min(best,dominated(rows));eligible+=1
            print(degree,leaves,eligible,best)
            assert best>=degree-leaves+1
    rows=(5,9,13,6,10)
    assert all(ones(r&3)==1 for r in rows)
    assert dominated(rows)==1

if __name__=='__main__':check()
