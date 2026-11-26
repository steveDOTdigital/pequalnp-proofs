// Search one gate deletion and one further gate rewrite in a 63-gate star circuit.
// Every circuit is tested on all minimal positives and maximal negatives.
// These rows suffice to reject a circuit with a NOT, but a surviving signed
// candidate still needs full truth-table verification.
import assert from 'node:assert/strict';

const size = 13;
const points = Array.from({length: size}, (_, i) => i);
const edges = points.flatMap(p => [0,4,10,12].filter(d => !(p === 0 && d === 0))
  .map(d => [p, (p+d)%size]));
const neighbors = points.map(p => edges.filter(([q]) => p === q)
  .reduce((mask,[,l]) => mask | 1<<l, 0));
const shore = (1<<size)-1;
const negatives = new Set();
for(let chosen=0;chosen<=shore;chosen++){
  let neighborhood=0;
  for(const p of points) if(chosen & 1<<p) neighborhood |= neighbors[p];
  const lines=shore ^ neighborhood;
  const closure=points.reduce((mask,p) => neighbors[p]&lines ? mask : mask | 1<<p,0);
  negatives.add(closure | lines<<size);
}
const positives=edges.map(([p,l])=>(1<<p)|(1<<(size+l)));
const rows=[...positives,...negatives];
const target=(1n<<BigInt(positives.length))-1n, all=(1n<<BigInt(rows.length))-1n;
const raw=Array.from({length:26},(_,v)=>rows.reduce((word,row,i)=>
  row & 1<<v ? word | 1n<<BigInt(i) : word,0n));
assert.equal(edges.length,51);
assert.ok([...negatives].every(row=>edges.every(([p,l])=>!(row & 1<<p) || !(row & 1<<(size+l)))));
function build(dual,balanced){
  const gates=[];
  function add(op,a,b){gates.push({op,a,b});return 25+gates.length}
  function join(words){
    if(!balanced)return words.slice(1).reduce((a,b)=>add('OR',a,b),words[0]);
    while(words.length>1){
      const next=[];
      for(let i=0;i<words.length;i+=2)next.push(i+1<words.length?add('OR',words[i],words[i+1]):words[i]);
      words=next;
    }
    return words[0];
  }
  join(points.map(center=>{
    const ns=edges.filter(([p,l])=>center===(dual?l:p)).map(([p,l])=>dual?p:13+l).sort((a,b)=>a-b);
    return add('AND',dual?13+center:center,join(ns));
  }));
  assert.equal(gates.length,63);
  return gates;
}
function evaluate(gates,deleted=-1,alias=-1,pivot=-1,forced=0n){
  const words=[...raw];
  for(let j=0;j<gates.length;j++){
    const {op,a,b}=gates[j];
    if(j===deleted) words.push(words[alias]);
    else if(j===pivot) words.push(forced);
    else words.push(op==='AND'?words[a]&words[b]:words[a]|words[b]);
  }
  return words;
}
function search(dual,balanced){
  const gates=build(dual,balanced);
  assert.equal(evaluate(gates).at(-1),target);
  let deletions=0,pivots=0,examined=0,admissible=0,hits=0;
  const candidates=[];
  function record(item){hits++;if(candidates.length<12)candidates.push(item)}
  for(let deleted=0;deleted<gates.length;deleted++) for(let alias=0;alias<26+deleted;alias++){
    deletions++;
    const words=evaluate(gates,deleted,alias);
    if(words.at(-1)===target) record({deleted,alias});
    for(let pivot=0;pivot<gates.length;pivot++){
      if(pivot===deleted)continue;
      const available=Array.from({length:26+pivot},(_,i)=>i).filter(i=>i!==26+deleted);
      const n=available.length;
      examined+=n*(n+1)+n; // unordered pairs incl. repeated inputs, two operations, and each NOT
      pivots++;
      const low=evaluate(gates,deleted,alias,pivot,0n).at(-1);
      const high=evaluate(gates,deleted,alias,pivot,all).at(-1);
      if((low & (all^target)) || (target & (all^high)))continue;
      admissible++;
      const sensitive=low^high, want=target&sensitive;
      for(let i=0;i<n;i++){
        const a=available[i],x=words[a]&sensitive;
        if((sensitive^x)===want)record({deleted,alias,pivot,op:'NOT',a});
        for(let k=0;k<=i;k++){
          const b=available[k],y=words[b]&sensitive;
          if((x&y)===want)record({deleted,alias,pivot,op:'AND',a,b});
          if((x|y)===want)record({deleted,alias,pivot,op:'OR',a,b});
        }
      }
    }
  }
  return {dual,balanced,positives:positives.length,maximalNegatives:negatives.size,deletions,pivots,examined,admissible,hits,candidates};
}
for(const dual of [false,true])for(const balanced of [false,true]){
  console.log(JSON.stringify(search(dual,balanced)));
}
