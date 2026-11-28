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
function flagRows(zeroes){
  return ids.flatMap(p=>ids.filter(l=>incident(p,l)&&survives(zeroes,p)&&survives(zeroes,n+l))
    .map(l=>(1n<<BigInt(p))|(1n<<BigInt(n+l))));
}
function rowTape(c,row){
  const tape=Array.from({length:42},(_,j)=>!survives(row,j));
  for(const g of c.gates){
    const [a,b]=g.inputs.map(j=>tape[j]??false);
    tape.push(g.op==="and"?a&&b:a||b);
  }
  return tape;
}
const evalRow=(c,row)=>rowTape(c,row)[c.output]??false;

function forceAcceptingTree(c,row,mandatory){
  const tape=rowTape(c,row);
  function visit(w){
    if(!tape[w])throw Error("False accepting witness");
    if(w<42)return;
    const j=w-42;
    mandatory.add(j);
    const g=c.gates[j];
    if(g.op==="and"){
      g.inputs.forEach(visit);
    }else{
      const options=g.inputs.filter(i=>tape[i]);
      if(options.length!==1)throw Error("Nonunique witness in star control");
      visit(options[0]);
    }
  }
  visit(c.output);
}
const control=starCircuit();
const result=masks.map((mask,i)=>{
  const zeroes=mask|anchor;
  const q=Array.from({length:42},(_,j)=>j).find(j=>!survives(zeroes,j));
  const flags=flagRows(zeroes);
  const expected=canonical(flags);
  let c=control;
  const trace=[];
  for(let j=c.gates.length-1;j>=0;j--){
    const cut=erase(c,j,q);
    if(flags.every(row=>evalRow(cut,row))){
      c=cut;
      trace.push(j);
    }
  }
  const mandatory=new Set();
  flags.forEach(row=>forceAcceptingTree(control,row,mandatory));
  if(!equal(symbolic(c,zeroes)[c.output],expected)||mandatory.size!==c.gates.length||
       trace.some(j=>mandatory.has(j)||j>=control.gates.length))
    throw Error("Zero-only erasures differ from the exact witness union");
  // Put a nonincidence AND first and wire it into a redundant but reachable branch.
  const [u,v]=ids.filter(p=>survives(zeroes,p));
  const shift=x=>x>=42?x+1:x;
  const live=shift(control.output);
  const outer=42+control.gates.length+1;
  const contrast={gates:[
    {op:"and",inputs:[u,v]},
    ...control.gates.map(g=>({op:g.op,inputs:g.inputs.map(shift)})),
    {op:"and",inputs:[live,42]},
    {op:"or",inputs:[live,outer]}
  ],output:outer+1};
  const tape=symbolic(contrast,zeroes), junk=tape[42];
  if(junk.length!==1||tape.slice(0,42).some(x=>equal(x,junk))||
      !equal(tape[contrast.output],expected))throw Error("Weak control lacks live inequivalent gate");
  const cut=erase(contrast,0,q);
  if(!flags.every(row=>evalRow(cut,row))||!equal(symbolic(cut,zeroes)[cut.output],expected))
    throw Error("Flag-certified erasure failed");
  return {case:i,flags:flags.length,greedyErasures:trace.length,greedyResidual:c.gates.length,mandatory:mandatory.size,
    erasedLiveInequivalentGate:true,trace};
});
console.log(JSON.stringify(result));
