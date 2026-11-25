"""Check the five-seed boundary and ordinary-star controls on the 21-point plane."""
from array import array
from itertools import combinations
from collections import Counter
n=21
full=(1<<n)-1
offsets=(0,1,4,14,16)
lines=[sum(1<<((l+d)%n) for d in offsets) for l in range(n)]
pencils=[sum(1<<l for l in range(n) if lines[l]>>p&1) for p in range(n)]
def covers(rows):
    u=array('I',[0])*(1<<n)
    for mask in range(1,full+1):
        bit=mask & -mask
        u[mask]=u[mask^bit]|rows[bit.bit_length()-1]
    return u

def main():
    point_cover=covers(pencils)
    line_cover=covers(lines)
    seeds=[sum(1<<i for i in a) for k in range(6) for a in combinations(range(n),k)]
    generated=set(seeds)
    generated.update(full^line_cover[t] for t in seeds)
    minimum=min(b for b in (bin(line_cover[t]).count('1') for t in seeds if bin(t).count('1')==5))
    assert minimum==15
    seed4={t for t in seeds if bin(t).count('1')<=4}
    from4=seed4|{full^line_cover[t] for t in seed4}
    closed=[]
    hard=Counter()
    for x in range(full+1):
        y=full^point_cover[x]
        if x!=full^line_cover[y]:continue
        closed.append(x)
        assert x in generated
        if x not in from4:hard[bin(x).count('1'),bin(y).count('1')]+=1
    print('seeds',len(seeds),'distinct tested point masks',len(generated),'maximal negatives',len(closed))
    print('smallest five-line union',minimum,'closed point masks requiring the five-seed test',sorted(hard.items()))
    heavy=[p for p in range(n) if p%3==0]
    exterior=[p for p in range(n) if p%3]
    def stars(centers):
        gates=[]
        def gate(op,a,b):
            wire=42+len(gates);gates.append((op,a,b));return wire
        acc=None
        for p in centers:
            ls=[21+l for l in range(n) if pencils[p]>>l&1]
            disj=ls[0]
            for l in ls[1:]:disj=gate(0,disj,l)
            hit=gate(1,p,disj)
            acc=hit if acc is None else gate(0,acc,hit)
        return gates,acc
    # Bit-slice all tested inputs into one integer per wire.
    for centers,size in ((exterior,83),(exterior+heavy,125)):
        gates,out=stars(centers)
        assert len(gates)==size
        rows=[(1<<p,1<<l) for p in centers for l in range(n) if pencils[p]>>l&1]
        want=(1<<len(rows))-1
        rows.extend((x,full^point_cover[x]) for x in closed)
        data=[bytearray((len(rows)+7)//8) for i in range(42)]
        for j,(x,y) in enumerate(rows):
            mask=x|(y<<21)
            while mask:
                bit=mask & -mask
                data[bit.bit_length()-1][j//8]|=1<<(j%8)
                mask^=bit
        values=[int.from_bytes(t,'little') for t in data]
        for op,a,b in gates:values.append(values[a]&values[b] if op else values[a]|values[b])
        assert values[out]==want
        print('positive control',size,'gates',len(rows)-len(closed),'flags',len(closed),'maximal negatives')
if __name__=='__main__':main()
