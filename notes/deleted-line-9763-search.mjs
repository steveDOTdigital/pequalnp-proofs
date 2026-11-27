// Search one gate deletion and one further gate rewrite in a 59-gate star circuit.
// Every circuit is tested on all minimal positives and maximal negatives.
// These rows suffice to reject a circuit with a NOT, but a surviving signed
// candidate still needs full truth-table verification.
import assert from 'node:assert/strict';

const size = 13;
const points = Array.from({length: size}, (_, i) => i);
const edges = points.flatMap(p => [0,4,10,12].filter(d => (p+d)%size !== 0)
  .map(d => [p, (p+d)%size-1]));
const neighbors = points.map(p => edges.filter(([q]) => p === q)
  .reduce((mask,[,l]) => mask | 1<<l, 0));
const shore = (1<<size)-1;
const negatives = new Set();
for(let chosen=0;chosen<=shore;chosen++){
  let neighborhood=0;
  for(const p of points) if(chosen & 1<<p) neighborhood |= neighbors[p];
  const lines=4095 ^ neighborhood;
  const closure=points.reduce((mask,p) => neighbors[p]&lines ? mask : mask | 1<<p,0);
  negatives.add(closure | lines<<size);
}
assert.equal(negatives.size,553);
const positives=edges.map(([p,l])=>(1<<p)|(1<<(size+l)));
const rows=[...positives,...negatives];
const target=(1n<<BigInt(positives.length))-1n, all=(1n<<BigInt(rows.length))-1n;
const raw=Array.from({length:25},(_,v)=>rows.reduce((word,row,i)=>
  row & 1<<v ? word | 1n<<BigInt(i) : word,0n));
assert.equal(edges.length,48);
assert.ok([...negatives].every(row=>edges.every(([p,l])=>!(row & 1<<p) || !(row & 1<<(size+l)))));
function build(dual,balanced){
  const gates=[];
  function add(op,a,b){gates.push({op,a,b});return 24+gates.length}
  function join(words){
    if(!balanced)return words.slice(1).reduce((a,b)=>add('OR',a,b),words[0]);
    while(words.length>1){
      const next=[];
      for(let i=0;i<words.length;i+=2)next.push(i+1<words.length?add('OR',words[i],words[i+1]):words[i]);
      words=next;
    }
    return words[0];
  }
  join(points.slice(0,12).map(center=>{
    const ns=edges.filter(([p,l])=>center===(dual?l:p)).map(([p,l])=>dual?p:13+l).sort((a,b)=>a-b);
    return add('AND',dual?13+center:center,join(ns));
  }));
  assert.equal(gates.length,59);
  return gates;
}

const N = raw.length;
// A circuit is a DAG. An edit may use a wire that originally came later,
// provided the new dependencies still admit a topological ordering.
function search(balanced) {
  const original = build(true,balanced), last=N+original.length-1;
  const bit = i => 1n << BigInt(i);
  const initial = [];
  for (const {a,b} of original) {
    const i=N+initial.length;
    initial.push(bit(i) | (initial[a-N]??0n) | (initial[b-N]??0n));
  }
  let deletions=0,pivots=0, examined=0, admissible=0, hits=0;
  const candidates=[];
  function record(edit) { hits++; if(candidates.length<12)candidates.push(edit); }
  for(let d=N;d<=last;d++)for(let alias=0;alias<=last;alias++) {
    if((initial[alias-N]??0n)&bit(d))continue;
    deletions++;
    const sub=i=>i===d ? alias : i;
    const out=sub(last), gates=original.map(({op,a,b})=>({op,a:sub(a),b:sub(b)}));
    const order=[], ancestry=[];
    function visit(i) {
      if(i<N || ancestry[i]!==undefined)return;
      const {a,b}=gates[i-N];visit(a);visit(b);
      ancestry[i]=bit(i)|(ancestry[a]??0n)|(ancestry[b]??0n);
      order.push(i);
    }
    for(let i=N;i<=last;i++)if(i!==d)visit(i);
    function evaluate(pivot=-1,forced=0n) {
      const w=raw.slice();
      for(const i of order){const {a,b,op}=gates[i-N];w[i]=i===pivot?forced:op==='OR'?w[a]|w[b]:w[a]&w[b];}
      return w;
    }
    const w=evaluate();
    if(w[out]===target)record({d,alias});
    for(const pivot of order){
      if(!((ancestry[out]??0n)&bit(pivot)))continue;
      const avail=[];
      for(let i=0;i<=last;i++)if(i!==d && !((ancestry[i]??0n)&bit(pivot)))avail.push(i);
      const n=avail.length;
      pivots++;examined+=n*(n+1)+n+2;
      const lo=evaluate(pivot,0n)[out],hi=evaluate(pivot,all)[out];
      if((lo&(all^target)) || (target&(all^hi)))continue;
      admissible++;
      const sensitive=lo^hi,want=target&sensitive;
      if(want===0n || want===sensitive)record({d,alias,pivot,constant:want===sensitive});
      const values=avail.map(i=>w[i]&sensitive);
      for(let i=0;i<n;i++){
        const a=avail[i],x=values[i];
        if((x^sensitive)===want)record({d,alias,pivot,op:'NOT',a});
        for(let j=0;j<=i;j++){
          const b=avail[j],y=values[j];
          if((x&y)===want)record({d,alias,pivot,op:'AND',a,b});
          if((x|y)===want)record({d,alias,pivot,op:'OR',a,b});
        }
      }
    }
  }
  return {balanced,positives:positives.length,maximalNegatives:negatives.size,deletions,pivots,examined,admissible,hits,candidates};
}
for(const balanced of [false,true])console.log(JSON.stringify(search(balanced)));
