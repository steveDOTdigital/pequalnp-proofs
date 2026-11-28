"use strict";

const n=21, anchor=148193411399n;
const masks=[693637218693n,214750724172n,43100670213n,2201724715076n,429513539622n,10838245382n,214756769811n,412337856832n,154640061441n,1718003696225n,1387274437386n,3436007392450n,3436108316976n,1168315262978n];
const d=new Set([0,5,7,17,20]);
const ids=Array.from({length:n},(_,i)=>i);
const survives=(m,i)=>(m&(1n<<BigInt(i)))===0n;
const incident=(p,l)=>d.has((l+n-p)%n);
if(ids.some(p=>ids.some(q=>p<q&&ids.filter(l=>incident(p,l)&&incident(q,l)).length!==1)))
  throw Error("Wrong projective incidence");
function canonical(terms){
  const sorted=[...new Set(terms)].sort((a,b)=>a<b?-1:a>b?1:0);
  return sorted.filter(a=>!sorted.some(b=>a!==b&&(a&b)===b));
}
const equal=(a,b)=>a.length===b.length&&a.every((x,i)=>x===b[i]);
function starCircuit(){
  const gates=[];
  const put=(op,a,b)=>{gates.push({op,inputs:[a,b]});return 41+gates.length;};
  const stars=ids.map(p=>{
    const s=ids.filter(l=>incident(p,l)).map(l=>n+l);
    return put("and",p,s.reduce((a,b)=>put("or",a,b)));
  });
  return {gates,output:stars.reduce((a,b)=>put("or",a,b))};
}
// Each term is a bit mask of required raw inputs. Remove subsumed terms
// so equality of antichains is equality of the exact monotone functions.
function symbolic(c,restrict){
  const w=Array.from({length:42},(_,i)=>survives(restrict,i)?[1n<<BigInt(i)]:[]);
  for(const g of c.gates){
    const [a,b]=g.inputs.map(i=>w[i]);
    if(a===undefined||b===undefined)throw Error("Illegal wire in control");
    w.push(canonical(g.op==="and"?a.flatMap(x=>b.map(y=>x|y)):[...a,...b]));
  }
  return w;
}
function erase(c,m,p){
  if(m<0||m>=c.gates.length||p<0||p>=42+m)throw Error("Invalid erasure");
  const removed=42+m;
  const rd=i=>i===removed?p:i>removed?i-1:i;
  return {gates:[...c.gates.slice(0,m),...c.gates.slice(m+1).map(g=>({
    op:g.op,inputs:g.inputs.map(rd)
  }))],output:rd(c.output)};
}
function deadGate(c){
  const live=new Set();
  function visit(i){
    if(i<42||live.has(i))return;
    live.add(i);
    for(const j of c.gates[i-42].inputs)visit(j);
  }
  visit(c.output);
  return c.gates.findLastIndex((_,j)=>!live.has(42+j));
}
const control=starCircuit();
if(control.gates.length!==125)throw Error("Wrong star control size");
if(masks.length!==14)throw Error("Wrong posted mask count");
const result=masks.map((mask,i)=>{
  const zeroes=mask|anchor;
  const expected=canonical(ids.flatMap(p=>ids.filter(l=>incident(p,l)&&survives(zeroes,p)&&survives(zeroes,n+l))
    .map(l=>(1n<<BigInt(p))|(1n<<BigInt(n+l)))));
  if(!equal(symbolic(control,zeroes)[control.output],expected))throw Error("Wrong control function");
  const pins=Array.from({length:42},(_,j)=>j).filter(j=>!survives(zeroes,j));
  for(const j of pins){
    const liveNeighbors=j<21?ids.filter(l=>survives(zeroes,n+l)&&incident(j,l)):
      ids.filter(p=>survives(zeroes,p)&&incident(p,j-n));
    if(liveNeighbors.length<2)throw Error("Pinned coordinate lacks live neighbors");
  }
  const directReads=control.gates.filter(g=>g.inputs.some(j=>pins.includes(j))).length;
  let c=control;
  const ops=[];
  while(true){
    const t=symbolic(c,zeroes);
    let mark=null;
    for(let j=42;j<t.length&&!mark;j++){
      const p=t.findIndex((a,i)=>i<j&&equal(a,t[j]));
      if(p>=0)mark=[j-42,p];
    }
    if(!mark){
      const dead=deadGate(c);
      if(dead<0)break;
      mark=[dead,pins[0]];
    }
    c=erase(c,...mark);
    ops.push(mark);
  }
  const want=i<4?67:i<9?72:76;
  if(ops.length!==want||c.gates.length!==125-want||
     !equal(symbolic(c,zeroes)[c.output],expected))throw Error("Wrong residual trace in case "+i);
  return {case:i,pins:pins.length,directReads,erased:ops.length,residual:c.gates.length,ops};
});
console.log(JSON.stringify(result));

