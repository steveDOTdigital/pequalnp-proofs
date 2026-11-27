const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");

const solverDirectory=process.argv[3];
const context=vm.createContext({});
vm.runInContext(fs.readFileSync(path.join(solverDirectory,"minisolvers.js"),"utf8"),context);
const Solver=context.minisolvers.MinisatSolver;
const shore=13, width=26, all=(1<<shore)-1;
const omitted=new Set([46,89,114,177,263,356,450,531,553,586,736,780,802,912,1046,1091,1220,1313,1360,1416,1541,1560,2076,2117,2186,2212,2321,2344,2566,2689,3081,3120,3648,4107,4133,4152,4242,4289,4372,4424,4688,4740,5132,5154,5888,6240,6402,7296]);
const offsets=[0,1,3,9];
const elements=Array.from({length:all+1},(_,m)=>
  Array.from({length:shore},(_,i)=>i).filter(i=>m&(1<<i)));
const incidence=Array.from({length:shore},(_,l)=>
  offsets.reduce((m,d)=>m|(1<<((l+d)%shore)),0));
const pencils=Array.from({length:shore},(_,p)=>
  incidence.reduce((m,line,l)=>m|(((line>>p)&1)<<l),0));
const cap=(m,sides)=>sides.every(s=>elements[m&s].length<=2);
const outside=b=>all^elements[b].reduce((m,l)=>m|incidence[l],0);
const positives=incidence.flatMap((m,l)=>elements[m].map(p=>(1<<p)|(1<<(shore+l))));
const negatives=elements.flatMap((set,b)=>
  set.length===4 && cap(b,pencils) && !omitted.has(b)?[outside(b)|(b<<shore)]:[]);
if(positives.length!==52||negatives.length!==186)throw Error("Unexpected test counts");

function starCircuit() {
  const gates=[];
  const add=(and,a,b)=>{const wire=width+gates.length;gates.push([and,a,b]);return wire;};
  const terms=incidence.map((line,l)=>{
    const points=elements[line];
    const any=points.slice(1).reduce((w,p)=>add(false,w,p),points[0]);
    return add(true,any,shore+l);
  });
  terms.slice(1).reduce((out,t)=>add(false,out,t),terms[0]);
  return gates;
}

function ordered(spec){
  const waiting=spec.map((gate,i)=>({gate,index:width+i}));
  const wires=new Map(Array.from({length:width},(_,i)=>[i,i]));
  const result=[];
  while(waiting.length){
    let best=null,bestMax=Infinity;
    for(const entry of waiting){
      const [,a,b]=entry.gate;
      if(!wires.has(a)||!wires.has(b))continue;
      const greatest=Math.max(wires.get(a),wires.get(b));
      if(greatest<bestMax){best=entry;bestMax=greatest;}
    }
    if(!best)throw Error("Cyclic control circuit");
    const [and,a,b]=best.gate, first=wires.get(a), second=wires.get(b);
    wires.set(best.index,width+result.length);
    result.push([and,Math.min(first,second),Math.max(first,second)]);
    waiting.splice(waiting.indexOf(best),1);
  }
  return result;
}

function solve(budget,points,lines,forced) {
  const S=new Solver();
  const fresh=()=>{S.new_var();return S.nvars();};
  const clause=(...input)=>S.add_clause(input);
  function one(lits){
    clause(...lits);
    let prev;
    for(let i=0;i+1<lits.length;i++){
      const next=fresh();
      clause(-lits[i],next);
      if(prev){clause(-prev,next);clause(-lits[i],-prev);}
      prev=next;
    }
    if(prev)clause(-lits.at(-1),-prev);
  }
  const active=Array.from({length:budget},fresh);
  clause(active.at(-1));
  const slots=[];
  for(let g=0;g<budget;g++){
    const lhs=Array.from({length:width+g},fresh), rhs=Array.from({length:width+g},fresh);
    const and=fresh();
    slots.push({lhs,rhs,and,degree:[]});
    one(lhs);one(rhs);
    clause(active[g],and);
    clause(active[g],lhs[0]);
    clause(active[g],rhs[shore]);
    if(g+1<budget)clause(-active[g],active[g+1]);
    for(let a=0;a<lhs.length;a++)for(let b=0;b<a;b++)clause(-lhs[a],-rhs[b]);
    for(let h=0;h<g;h++){
      clause(-lhs[width+h],active[h]);
      clause(-rhs[width+h],active[h]);
    }
    if(g) {
      const earlier=slots[g-1].rhs;
      for(let a=0;a<earlier.length;a++)for(let b=0;b<a;b++)
        clause(-active[g-1],-earlier[a],-rhs[b]);
    }

    for(const [kind,limit] of [points,lines].entries()){
      const a=Array.from({length:limit+1},fresh);
      const b=Array.from({length:limit+1},fresh);
      const result=Array.from({length:limit+1},fresh);
      one(a);one(b);one(result);
      slots[g].degree.push(result);
      for(const [selector,label] of [[lhs,a],[rhs,b]]){
        for(let i=0;i<selector.length;i++){
          if(i<width){
            const d=+(+(i>=shore)===kind);
            if(d<=limit)clause(-selector[i],label[d]);
            else clause(-selector[i]);
          }else{
            for(let k=0;k<=limit;k++)
              clause(-selector[i],-slots[i-width].degree[kind][k],label[k]);
          }
        }
      }
      for(let i=0;i<=limit;i++)for(let j=0;j<=limit;j++){
        clause(and,-a[i],-b[j],result[Math.max(i,j)]);
        if(i+j<=limit)clause(-and,-a[i],-b[j],result[i+j]);
        else clause(-and,-a[i],-b[j]);
      }
    }
  }
  for(let g=0;g+1<budget;g++){
    clause(-active[g],...slots.slice(g+1).flatMap(slot=>[slot.lhs[width+g],slot.rhs[width+g]]));
  }
  if(forced) ordered(forced).forEach(([and,a,b],i)=>{
    clause(active[i]);clause(and?slots[i].and:-slots[i].and);
    clause(slots[i].lhs[a]);clause(slots[i].rhs[b]);
  });

  const requested=new Map();
  function row(bits,trueOutput){
    if(requested.has(bits)){
      if(requested.get(bits)!==trueOutput)throw Error("Inconsistent target");
      return;
    }
    requested.set(bits,trueOutput);
    const computed=[];
    for(const g of slots) {
      const p=fresh(),q=fresh(),o=fresh();
      for(const [signals,value] of [[g.lhs,p],[g.rhs,q]]){
        for(let i=0;i<signals.length;i++){
          if(i<width)clause(-signals[i],bits&(1<<i)?value:-value);
          else {
            const y=computed[i-width];
            clause(-signals[i],-value,y);
            clause(-signals[i],value,-y);
          }
        }
      }
      clause(-g.and,-p,-q,o);clause(-g.and,p,-o);clause(-g.and,q,-o);
      clause(g.and,p,q,-o);clause(g.and,-p,o);clause(g.and,-q,o);
      computed.push(o);
    }
    clause(trueOutput?computed.at(-1):-computed.at(-1));
  }
  for(const bits of positives)row(bits,true);
  for(const bits of [0,...Array.from({length:width},(_,i)=>1<<i)])row(bits,false);
  for(let j=0;j<negatives.length;j+=9)row(negatives[j],false);
  for(let iteration=0;;iteration++){
    console.log(JSON.stringify({event:"search",budget,points,lines,iteration,
      rows:requested.size,variables:S.nvars(),clauses:S.nclauses()}));
    if(!S.solve()){
      console.log(JSON.stringify({event:"UNSAT",budget,points,lines,rows:requested.size}));
      return false;
    }
    const model=S.get_model(), lit=i=>model[i-1]===1;
    const spec=slots.map(g=>[lit(g.and),g.lhs.findIndex(lit),g.rhs.findIndex(lit)]);
    if(spec.some(([,a,b],i)=>a<0||a>b||b>=width+i))throw Error("Invalid decoder output");
    function evaluate(bits) {
      const values=Array.from({length:width},(_,i)=>+(!!(bits&(1<<i))));
      for(const [and,a,b] of spec)values.push(and?values[a]&values[b]:values[a]|values[b]);
      return !!values.at(-1);
    }
    const failures=negatives.filter(evaluate);
    if(positives.some(bits=>!evaluate(bits))||failures.some(bits=>requested.has(bits))){
      throw Error("Candidate violates a modeled row");
    }
    if(!failures.length){
      const degree=kind=>{
        const values=Array.from({length:width},(_,i)=>+(+(i>=shore)===kind));
        for(const [and,a,b] of spec)values.push(and?values[a]+values[b]:Math.max(values[a],values[b]));
        return values.at(-1);
      };
      let genericTested=0;
      for(let b=0;b<=all;b++)if(elements[b].length<=4 && cap(b,pencils)){
        const free=outside(b);
        for(let a=free;;a=(a-1)&free){
          if(elements[a].length<=4 && cap(a,incidence)){
            genericTested++;
            if(evaluate(a|(b<<shore)))throw Error("Candidate passes reduced tests but fails a capped negative");
          }
          if(!a)break;
        }
      }
      console.log(JSON.stringify({event:"SAT",budget,pointDegree:degree(0),
        lineDegree:degree(1),genericTested,active:active.filter(lit).length,spec,output:width+budget-1}));
      return true;
    }
    for(const bits of failures.slice(0,20))row(bits,false);
    console.log(JSON.stringify({event:"refinement",failures:failures.length}));
  }
}
const mode=process.argv[2];
if(mode==="control"){
  const star=starCircuit();
  if(star.length!==64||!solve(64,2,3,star)||solve(64,0,3,star))throw Error("Control verdict differs");
}else if(mode==="search"){
  solve(63,2,3);
}else {
  throw Error("Select control or search");
}