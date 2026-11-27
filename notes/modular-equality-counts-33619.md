# Modular joint counts for optimal equality circuits

This is a written proof of the deterministic machine in L-meta-33619. It uses the desk's singleton-pair meaning of representation. The finite replay at the end checks the circuit classification, score decomposition, padding factor and modular hafnian arithmetic. This result has no complete Lean verification or upstream filing. [Desk unit](https://pequalnp.com/lemma#L-meta-33619) · [Representation definition](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Defs/Represents.lean)

## Equality functions are indexed by matchings

Write $X_i,Y_i$ for the two banks. Each raw bit is essential. For example the input with $X_i=Y_i=1$ alone must give true. If deleting $X_i$ preserved true, monotonicity would make the input with $X_j=Y_i=1$ true for $j\ne i$, which is forbidden. The other bank is symmetric. This argument also shows that any singleton input gives false.

Take the directed dependency cone of the output, with an arc only for a valid read of an earlier wire. All $2n$ raw bits are in the cone by essentiality. If there are $g$ gates in the cone, its underlying graph is connected on $2n+g$ vertices and has at most $2g$ arcs by fan-in. Hence $g\ge 2n-1$. The permitted size makes this an equality. Every gate has exactly two distinct valid reads and the dependency graph is a tree, so each leaf occurs once. In particular the all-zero input gives false at every subtree.

At an OR split both mates of every diagonal pair lie in the same child. If they split, each child sees at most a singleton and cannot make the output true. Recurse on the paired sets in the children. At an AND split the mates of each pair must separate, and every leaf alone must make its own child true. Each child function is therefore the OR of all its variables. Color an index by the child containing its left variable. Two indices of the same color would make a forbidden off-diagonal singleton pair true. There are only two colors, so this AND block is either one pair or a crossed two-index block.

Consequently the function is an OR of singleton blocks $X_i\land Y_i$ and crossed blocks $(X_i\lor Y_j)\land(X_j\lor Y_i)$. The crossed pairs form a matching $S$. Every matching gives such a formula with $2n$ leaves and $2n-1$ gates. Testing just $X_i,X_j$ with the right bank empty recovers exactly whether $\{i,j\}\in S$, so this is a bijection of functions. The desk's size field is $|S|$.

## Hard constraints and the signed score

On a pair of sets $(R,T)$, the function of $S$ is true precisely when either $R\cap T\ne\varnothing$ or some edge of $S$ lies wholly in $R$ or wholly in $T$. A hard record with nonempty intersection forces every count to zero. Otherwise the hard records simply delete the edges outside the desk's set $E$.

Let $B$ be the score of the empty matching. For a soft record $t=(R,T,b)$ set $\sigma(t)=1$ when $b$ is true and $\sigma(t)=-1$ otherwise. For $e\in E$ let $w_e$ be the sum of $\sigma(t)$ over disjoint soft records that contain $e$ wholly in one bank. A soft record with overlap has constant output across all matchings. For a disjoint record the change in score from the empty matching is $\sigma(t)$ times the indicator that at least one edge of $S$ lies wholly in a bank. Inclusion-exclusion expands that indicator over nonempty subsets of $S$. Each subset of size at least two is itself a disjoint matching in $E$ and its signed coefficient vanishes by the posted promise. Thus
$$
\operatorname{score}(S)=B+\sum_{e\in S}w_e.
$$
The range $-m\le w_e\le m$ lets us attach the nonnegative exponent $d_e=m+w_e$ to each edge.

## One bounded-degree generating polynomial

Attach weight $U V^{d_e}$ to an allowed original edge. Add a private copy $i'$ of each original vertex $i$ with its own edge $ii'$ of weight one. Join every pair of copy vertices by an edge of weight one. Let $A(U,V)$ be the symmetric zero-diagonal weighted adjacency matrix of this doubled graph.

Every perfect matching restricts to a matching $S$ of original vertices. Unmatched originals must use their own copies. Exactly $2|S|$ copies are then free, so there are $(2|S|-1)!!$ perfect completions with unchanged original weight. The empty product for $|S|=0$ is one. The coefficient of $U^s V^d$ in the hafnian therefore counts original matchings of size $s$ and shifted score $d$, times the odd factor $(2s-1)!!$. Divide by this unit modulo $2^k$. The desired score index $j$ uses the coefficient at $d=j-B+ms$, with zero for an exponent outside the degree range. The separate degree bounds are $\lfloor n/2\rfloor$ and $nm$.

## Hafnian calculation modulo the requested power of two

Work over a commutative ring $R$ reducing modulo two to a field. For a symmetric matrix and distinct indices $i,j$, add $c$ times row and column $j$ to row and column $i$ in the off-diagonal entries other than $ij$. Keep the $ij$ entry intact. The hafnian changes by
$$
2c\sum_{\{l,m\}\subseteq [N]\setminus\{i,j\}}
 a_{jl}a_{jm}\,\operatorname{haf} A[[N]\setminus\{i,j,l,m\}].
$$
To see this, first expand the difference by the mate $l$ of $i$, and then by the mate $m$ of $j$. Each unordered pair appears in both orders. This row and column calculation is the algebraic method used by Hirai and Namba. [Hirai and Namba, *Shortest (A+B)-path packing via hafnian*](https://arxiv.org/abs/1603.08073)

Choose an off-diagonal unit $a_{pq}$. For each $t\notin\{p,q\}$ add $-a_{tq}/a_{pq}$ times row and column $p$ to row and column $t$. This clears the other entries incident to $q$ while leaving the pivot intact. The modified hafnian is $a_{pq}$ times the minor with $p,q$ removed. Record the correction at each operation on the matrix before that operation. Each correction has a factor two so its minors need only precision $k-1$, and they have four fewer indices. The branch retaining precision $k$ removes two indices. If there is no unit, all matrix entries are divisible by two. For dimension $2r$, the hafnian is then divisible by $2^r$. It is zero modulo $2^k$ when $r\ge k$. Otherwise divide each matrix entry by two, evaluate modulo $2^{k-r}$ and multiply by $2^r$. The empty hafnian is one, and precision zero always returns zero.

A chain at one precision has at most the matrix dimension many steps. Each step produces at most a polynomial number of lower-precision calls. Lower-precision recursion depth is at most $k$, so the number of ring operations is bounded by $(N+2)^{O(k+1)}$ for dimension $N$. The recurrence works uniformly with $k$ supplied as input.

## Interpolation and the one machine

Choose an integer $e$ such that $2^e$ exceeds the larger degree bound. Take the least such positive $e$. Find a monic irreducible binary polynomial of degree $e$ by testing all monic polynomials of that degree for monic divisors of degree at most $e/2$. Both lists have polynomial length in the input size because $e=O(\log(nm+n+2))$. Lift the polynomial with coefficients zero or one and quotient $(\mathbb Z/2^k)[Z]$ by that lift. The quotient is free of rank $e$ over the base ring, and its residue modulo two is the finite field of size $2^e$.

Pairwise distinct binary representatives of residue classes have unit differences in this ring. An inverse is obtained first modulo two, then lifted by Newton iteration or by a finite geometric series. Thus a rectangular grid with one more point than the degree bound in each variable permits ordinary Vandermonde interpolation with unit denominators. Evaluate the hafnian by the recurrence at each grid point and interpolate the coefficient array. Its entries come from the constant copy of $\mathbb Z/2^k$, because the original polynomial had integer coefficients and the inclusion of constants in the quotient is injective. Divide by the odd completion factor, then output the requested $k$ bits from low to high in the desk's row order.

The unary counts and fixed-length membership banks can be parsed on finite tapes. All loop bounds, the irreducible polynomial search, modular ring operations, pivot choices and interpolation are deterministic and use the same algorithm for every input and every $k$. Every dimension, degree and bit length involved is polynomial in the encoded input length. The modular recursion contributes only the factor with exponent linear in $k$. Using finite tapes to store binary integers, polynomials and the recursion stack gives a deterministic finite-alphabet multitape implementation with polynomial overhead. This absorbs into a universal constant $c$ in $(|x|+2)^{c(k+1)}$, and yields the posted finite-alphabet TM2 claim.

## Finite controls

Run the following as a JavaScript file with Node.js. The formula check constructs all read-once AND/OR functions on four and six raw inputs and filters them by the exact singleton table. The score controls include overlapping hard rows and balance-preserving soft examples. The padding checks compare small perfect-matching sums and explicit matching completions. The modular recurrence is compared with the exact hafnian on small integer matrices, including even matrices. The interpolation argument is given above.

```js

const requireEqual=(a,b,w)=>{if(a!==b)throw new Error(w+': '+a+' <> '+b);};
function matchings(n,edges){
  function walk(i,used,acc) {
    if(i===n)return [acc];
    if((used>>i)&1)return walk(i+1,used,acc);
    const result=walk(i+1,used|(1<<i),acc);
    for(const [a,b] of edges){
      if(a===i&&!(used&(1<<b)))result.push(...walk(i+1,used|(1<<i)|(1<<b),[...acc,[a,b]]));
    }
    return result;
  }
  return walk(0,0,[]);
}
function graph(n){return Array.from({length:n},(_,a)=>Array.from({length:n-a-1},(_,j)=>[a,a+j+1])).flat();}
const hit=([a,b],r,t)=>Boolean(((r>>a)&1)&&((r>>b)&1)||((t>>a)&1)&&((t>>b)&1));
const value=(m,r,t)=>Boolean(r&t)||m.some(e=>hit(e,r,t));
function truthCols(width){
 const result=Array(width).fill(0n);
 for(let row=0;row<1<<width;row++)for(let i=0;i<width;i++)
   if(row&(1<<i))result[i]|=1n<<BigInt(row);
 return result;
}
function classification(n) {
  const width=2*n, cols=truthCols(width), levels=Array.from({length:1<<width},()=>new Set());
  for(let i=0;i<width;i++)levels[1<<i].add(cols[i]);
  for(let mask=1;mask<levels.length;mask++){
    const first=mask&-mask;
    if(first===mask)continue;
    for(let a=(mask-1)&mask;a;a=(a-1)&mask) {
      if(!(a&first))continue;
      const b=mask^a;
      for(const l of levels[a])for(const r of levels[b]) {
        levels[mask].add(l&r);
        levels[mask].add(l|r);
      }
    }
  }
  const fits=(word)=>{for(let i=0;i<n;i++)for(let j=0;j<n;j++){
    const row=(1<<i)|(1<<(n+j));
    if(Boolean(word&(1n<<BigInt(row)))!==(i===j))return false;
  }return true;};
  const real=new Set([...levels.at(-1)].filter(fits));
  const theoretical=new Set(matchings(n,graph(n)).map(m=>{
    let f=0n;for(let r=0;r<1<<n;r++)for(let t=0;t<1<<n;t++)if(value(m,r,t))f|=1n<<BigInt(r|(t<<n));return f;
  }));
  requireEqual(real.size,theoretical.size,'number of exact read-once functions');
  if([...real].some(w=>!theoretical.has(w)))throw Error('classification mismatch');
  return {width,nFunctions:real.size,allReadOnce:levels.at(-1).size};
}
function score(n,hard,soft){
 const usable=graph(n).filter(e=>hard.every(([r,t])=>!hit(e,r,t)));
 const base=soft.reduce((a,[r,t,b])=>a+Number(Boolean(r&t)===b),0);
 const total=new Map();
 const legal=hard.some(([r,t])=>r&t)?[]:matchings(n,usable);
 for(const m of legal){
   if(hard.some(([r,t])=>value(m,r,t)))throw Error('hard constraint logic');
   const direct=soft.reduce((a,[r,t,b])=>a+Number(value(m,r,t)===b),0);
   let predicted=base;
   for(const e of m)for(const [r,t,s] of soft) if(!(r&t)&&hit(e,r,t))predicted+=s?1:-1;
   requireEqual(direct,predicted,'balanced signed score');
   const key=m.length+','+direct;total.set(key,(total.get(key)??0)+1);
 }
 return total;
}
function hafExact(A) {
 if(A.length===0)return 1n;
 const rows=Array.from({length:A.length},(_,i)=>i);
 let out=0n;
 for(let j=1;j<A.length;j++)out+=A[0][j]*hafExact(submatrix(A,rows.filter(i=>i!==0&&i!==j)));
 return out;
}
function submatrix(A,p){return p.map(i=>p.map(j=>A[i][j]));}
function invOdd(x,mod) {
 let [a,b]=[x,mod], [u,v]=[1n,0n];
 while(b){let q=a/b;[a,b]=[b,a-q*b];[u,v]=[v,u-q*v];}
 if(a!==1n)throw Error('missing inverse');
 return (u%mod+mod)%mod;
}
function hafModulo(A,bits) {
 const n=A.length;if(bits<=0)return 0n; if(n===0)return 1n;
 const mod=1n<<BigInt(bits), modp=x=>(x%mod+mod)%mod;
 const B=A.map(r=>r.map(modp));
 const vertices=Array.from({length:n},(_,j)=>j);
 let p=-1,q=-1;
 outer: for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)if(B[i][j]&1n){p=i;q=j;break outer;}
 if(p<0){
  const m=BigInt(n/2);
  if(m>=BigInt(bits))return 0n;
  return modp((1n<<m)*hafModulo(B.map(r=>r.map(a=>a/2n)),bits-Number(m)));
 }
 let correction=0n;
 const inv=invOdd(B[p][q],mod);
 for(const t of vertices.filter(i=>i!==p&&i!==q)){
  const c=modp(-B[t][q]*inv);if(c===0n)continue;
  if(bits>1)for(const l of vertices.filter(i=>i!==t&&i!==p))
    for(const m of vertices.filter(i=>i>l&&i!==t&&i!==p)){
      if(!B[p][l]||!B[p][m])continue;
      const rest=vertices.filter(i=>i!==p&&i!==t&&i!==l&&i!==m);
      correction=modp(correction+2n*c*B[p][l]*B[p][m]*hafModulo(submatrix(B,rest),bits-1));
    }
  for(const i of vertices.filter(i=>i!==t&&i!==p))B[t][i]=B[i][t]=modp(B[t][i]+c*B[p][i]);
 }
 return modp(B[p][q]*hafModulo(submatrix(B,vertices.filter(i=>i!==p&&i!==q)),bits)-correction);
}
let randState=0x9524e1d3;
function pick(n){randState=(Math.imul(randState,1664525)+1013904223)>>>0;return (randState>>>12)%n;}
let moduloChecks=0;
for(const size of [0,2,4,6,8])for(let sample=0;sample<8;sample++){
 const A=Array.from({length:size},()=>Array(size).fill(0n));
 for(const [a,b] of graph(size)) A[a][b]=A[b][a]=BigInt(pick(14)-6)*(sample%3===0?2n:1n);
 const f=hafExact(A);
 for(let k=1;k<=4;k++){const m=1n<<BigInt(k);
  requireEqual(hafModulo(A,k),(f%m+m)%m,'hafnian modulo power of two');moduloChecks++;
 }
}
let scoreInputs=0,paddedChecks=0;
for(const n of [2,3,4,5]){
 const all=graph(n);
 for(let caseNo=0;caseNo<8;caseNo++){
  const hard=caseNo===7?[[1,1]]:caseNo%2===0?[[1<<(n-1),0]]:[[3,0]];
  const soft=[];
  // Equal-label pairs do not affect balance. A signed two-element row hits at most one edge.
  for(let j=0;j<4;j++){
    const r=pick(1<<n),t=pick(1<<n);soft.push([r,t,true],[r,t,false]);
  }
  for(let j=0;j<6;j++){
    const [a,b]=all[pick(all.length)];soft.push([(1<<a)|(1<<b),0,Boolean(pick(2))]);
  }
  soft.push([1,1,Boolean(pick(2))]);
  score(n,hard,soft);scoreInputs++;
 }
 const edgeSet=all.filter((_,i)=>i%3!==1), base=matchings(n,edgeSet);
 for(const u of [0n,2n,4n])for(const v of [0n,3n]){
  const A=Array.from({length:2*n},()=>Array(2*n).fill(0n));
  const w=(a,b)=>BigInt((a+b)%3);
  for(const [a,b] of edgeSet)A[a][b]=A[b][a]=u*v**w(a,b);
  for(let i=0;i<n;i++)A[i][n+i]=A[n+i][i]=1n;
  for(const [a,b] of all)A[n+a][n+b]=A[n+b][n+a]=1n;
  const odd=(s)=>Array.from({length:s},(_,i)=>BigInt(2*i+1)).reduce((x,y)=>x*y,1n);
  const expected=base.reduce((acc,m)=>acc+odd(m.length)*m.reduce((p,[a,b])=>p*u*v**w(a,b),1n),0n);
  requireEqual(hafExact(A),expected,'private-copy padding factor');paddedChecks++;
 }
}
console.log(JSON.stringify({formulas:[classification(2),classification(3)],moduloChecks,scoreInputs,paddedChecks}));
```
