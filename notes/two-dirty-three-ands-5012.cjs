// Enumerate binary gate DAGs after cutting extra wire uses into reference leaves.
// Run with Node.js. Raw vertex names are immaterial; labeled targets include all permutations.
"use strict";
const assert = require("node:assert/strict");
const pop = x => { let n=0; while(x) {x &= x-1; n++;} return n; };
function permute(a, i, fn) {
  if(i === a.length) {fn(a);return;}
  for(let j=i;j<a.length;j++) {
    [a[i],a[j]]=[a[j],a[i]]; permute(a,i+1,fn); [a[i],a[j]]=[a[j],a[i]];
  }
}
const shapes = [["x"]];

function columns(rows, width) {
  return Array.from({length: width}, (_, j) =>
    rows.reduce((result, row, i) => result | (((row >> j) & 1) << i), 0));
}

function finiteTargets() {
  const graphs = new Map();
  function record(rows, width) {
    const forms = [];
    for (const [data, b] of [[rows, width], [columns(rows, width), rows.length]]) {
      if (data.length > b) continue;
      permute(Array.from({length: b}, (_, i) => i), 0, permutation => {
        const renamed = data.map(row => permutation.reduce(
          (mask, v, i) => mask | (((row >> v) & 1) << i), 0)).sort((x, y) => x-y);
        forms.push(JSON.stringify([data.length, b, renamed]));
      });
    }
    const key = forms.sort()[0];
    graphs.set(key, JSON.parse(key));
  }
  for (let b = 1; b <= 4; b++) {
    // Sorted distinct nonempty neighborhoods remove the left vertex permutations.
    for (let chosen = 1; chosen < (1 << ((1 << b)-1)); chosen++) {
      if (pop(chosen) > b) continue;
      const rows = [];
      for (let r = 1; r < (1 << b); r++) if ((chosen >> (r-1)) & 1) rows.push(r);
      const cols = columns(rows, b);
      if (cols.includes(0) || new Set(cols).size !== b) continue;
      if (rows.some((r,i) => rows.slice(0,i).some(s => pop(r&s) > 1))) continue;
      let unions = new Set([0]);
      for (const row of rows) unions = new Set([...unions, ...Array.from(unions,s => s|row)]);
      if (unions.size > 5) continue;
      record(rows, b);
      for (const row of rows) if (pop(row) === 1) record([...rows, row], b);
      for (const col of cols) if (pop(col) === 1) record([...cols, col], rows.length);
    }
  }
  const hard = [];
  for (const [a, b, rows] of graphs.values()) {
    let cover = a;
    for (let s = 0; s < (1 << b); s++) {
      cover = Math.min(cover, pop(s) + rows.filter(r => r & ~s).length);
    }
    const upper = rows.reduce((m,r) => m+pop(r), 0) + cover-1;
    if (upper > a+b) hard.push([a,b,rows,upper]);
  }
  console.log("Reduced graphs and graphs above the one-wire bound:",graphs.size,hard.length);
  return hard;
}

for(let g=1;g<=8;g++) {
  const list=[];
  for(let i=0;i<=g-1-i;i++) for(const a of shapes[i]) for(const b of shapes[g-1-i]){
    if(i !== g-1-i || a<=b) list.push("("+a+b+")");
  }
  shapes.push(list);
}
function search(n,g,records,stopOnWitness=false) {
  const L=g+1, total=L+g, root=total-1, r=L-n;
  const inputs=Array.from({length:n},(_,i)=>1<<i);
  const rows=[...inputs];
  for(let i=0;i<n;i++) for(let j=0;j<i;j++) rows.push(inputs[i]|inputs[j]);
  const rawSig=inputs.map(v=>rows.reduce((s,row,i)=>s|((row&v)?1<<i:0),0));
  const goal=new Map();
  for(const [a,b,adj,limit] of records){
    if(a+b!==n || limit<g)continue;
    permute(Array.from({length:n},(_,i)=>i),0,p=>{
      const edges=[];
      for(let i=0;i<a;i++)for(let j=0;j<b;j++)if(adj[i]>>j&1)edges.push((1<<p[i])|(1<<p[a+j]));
      const sig=rows.reduce((s,row,i)=>s|(edges.some(e=>(row&e)===e)?1<<i:0),0);
      if(goal.has(sig))return;
      const negative=[];
      for(let row=0;row<(1<<n);row++)if(edges.every(e=>(row&e)!==e))negative.push(row);
      goal.set(sig,negative);
    });
  }
  let acyclic=0,typed=0,exact=0,dirtyTwo=0;
  for(const shape of shapes[g]){
    if(stopOnWitness && dirtyTwo) break;
    const a=new Int16Array(total), b=new Int16Array(total), baseA=[], baseB=[];
    let pos=0,leaf=0,gate=L;
    function read(){
      if(shape[pos++]==="x")return leaf++;
      const i=read(),j=read();pos++;const w=gate++;baseA[w]=i;baseB[w]=j;return w;
    }
    assert.equal(read(),root);
    const alias=new Int16Array(L), rawId=new Int16Array(L), marked=[], choices=[];
    const deps=new Int16Array(g), order=new Int16Array(g), sig=new Int32Array(total), bit=new Int8Array(total);
    const rootBit=1<<(g-1); const colors=[];
    for(let i=0;i<g-1;i++)for(let j=0;j<i;j++)colors.push(rootBit|(1<<i)|(1<<j));
    function evaluate(){
      for(let w=L;w<total;w++){
        const i=baseA[w],j=baseB[w];a[w]=i<L?alias[i]:i;b[w]=j<L?alias[j]:j;
        if(a[w]===b[w])return;
        deps[w-L]=(a[w]>=L?1<<(a[w]-L):0)|(b[w]>=L?1<<(b[w]-L):0);
      }
      for(let w=L;w<total;w++){
        const i=a[w],j=b[w];
        if((i>=L&&(a[i]===j||b[i]===j))||(j>=L&&(a[j]===i||b[j]===i)))return;
      }
      let done=0,count=0;
      while(count<g){
        const old=done;
        for(let j=0;j<g;j++)if(!(done>>j&1)&&!(deps[j]&~done)){order[count++]=j+L;done|=1<<j;}
        if(old===done)return;
      }
      acyclic++;
      for(const ands of colors){
        typed++;
        for(let k=0;k<g;k++){const w=order[k];sig[w]=(ands>>(w-L)&1)?sig[a[w]]&sig[b[w]]:sig[a[w]]|sig[b[w]];}
        const neg=goal.get(sig[root]);if(neg===undefined)continue;
        let dirty=0,valid=true;
        for(const row of neg){
          for(let l=0;l<L;l++)if(rawId[l]>=0)bit[l]=(row>>rawId[l])&1;
          for(let k=0;k<g;k++){
            const w=order[k],flag=1<<(w-L);
            bit[w]=(ands&flag)?bit[a[w]]&bit[b[w]]:bit[a[w]]|bit[b[w]];
            if((ands&flag)&&bit[w])dirty|=flag;
          }
          if(bit[root]){valid=false;break;}
        }
        if(valid){exact++;if(pop(dirty)===2)dirtyTwo++;}
      }
    }
    function references(i){
      if(stopOnWitness && dirtyTwo) return;
      if(i===r){evaluate();return;}
      for(const dst of choices){alias[marked[i]]=dst;references(i+1);}
    }
    function select(start){
      if(marked.length===r){
        choices.length=0;let nr=0;
        for(let l=0;l<L;l++){rawId[l]=-1;alias[l]=l;if(!marked.includes(l)){
          rawId[l]=nr;sig[l]=rawSig[nr++];choices.push(l);
        }}
        for(let w=L;w<root;w++)choices.push(w);
        references(0);return;
      }
      for(let l=start;l<=L-(r-marked.length);l++){marked.push(l);select(l+1);marked.pop();}
    }
    select(0);
  }
  return {n,g,targetLabelings:goal.size,acyclic,typed,exact,dirtyTwo};
}
const targets=finiteTargets();
const control=search(4,7,[[2,2,[1,2],7]],true);
assert(control.dirtyTwo>0);
console.log("Recovered a two-dirty-AND circuit for the two-edge matching.");
for(const n of new Set(targets.map(([a,b])=>a+b))) {
  const upper=Math.max(...targets.filter(([a,b])=>a+b===n).map(t=>t[3]));
  for(let g=n+1;g<=upper;g++){
    const result=search(n,g,targets);
    console.log(JSON.stringify(result));
    assert.equal(result.dirtyTwo,0);
  }
}
