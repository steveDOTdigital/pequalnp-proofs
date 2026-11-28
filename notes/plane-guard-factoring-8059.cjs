const n=13, top=(1<<n)-1;
const indices=Array.from({length:n},(_,i)=>i);
const members=Array.from({length:top+1},(_,m)=>indices.filter(i=>m&(1<<i)));
const lines=indices.map(l=>[0,1,3,9].reduce((m,d)=>m|(1<<((l+d)%n)),0));
const flags=lines.flatMap((m,l)=>members[m].map(p=>[p,l]));
const negative=[];
for(let q=0;q<=top;q++){
  if(members[q].length!==4||lines.some(l=>members[l&q].length>2))continue;
  const missing=lines.reduce((m,l,i)=>m|((l&q?0:1)<<i),0);
  negative.push(q|(missing<<n));
}
if(flags.length!==52||negative.length!==234)throw Error("Wrong posted test domain");
const core=[];
const gate=(and,a,b)=>{core.push({and,read:[a,b]});return 25+core.length;};
const rawOr=lines.map(m=>{
  const [a,...rest]=members[m];
  return rest.reduce((r,p)=>gate(false,r,p),a);
});
const stars=rawOr.slice(1).map((a,i)=>gate(true,a,14+i));
const combine=stars.slice(1,-1).reduce((r,w)=>gate(false,r,w),stars[0]);
const first={and:true,read:[rawOr[0],13]};
const second={and:false,read:[combine,stars.at(-1)]};
function evalGate(tape,{and,read}){
  return and?read.every(i=>tape[i]??false):read.some(i=>tape[i]??false);
}
function evaluate(row){
  const tape=Array.from({length:26},(_,i)=>!!(row&(1<<i)));
  for(const g of core)tape.push(evalGate(tape,g));
  return [evalGate(tape,first),evalGate(tape,second)];
}
const flagRow=(p,l)=>(1<<p)|(1<<(n+l));
if(core.length!==61)throw Error("Wrong core count");
if(flags.some(([p,l])=>!evaluate(flagRow(p,l)).some(Boolean))||
   negative.some(row=>evaluate(row).some(Boolean)))throw Error("Control does not pass");
const one=evaluate(flagRow(0,0)),two=evaluate(flagRow(0,4));
if(!one[0]||one[1]||two[0]||!two[1])throw Error("Exclusivity failed");

const gates=[...core,first,second];
const earlier=26+core.length, last=25+gates.length;
if(gates.some((g,j)=>g.read.length>2||g.read.some(i=>i>=26+j))||
   earlier<26||earlier>=last||gates.length!==63)throw Error("Control violates the posted circuit shape");
const directAndReaders=gates.filter(g=>g.and&&g.read.some(i=>i>=26&&gates[i-26].and)).length;
if(directAndReaders!==0)throw Error("Unexpected direct AND reader");

function variant(factor){
  const t=[...core,first], early=26+core.length;
  const add=(and,a,b)=>{t.push({and,read:[a,b]});return 25+t.length;};
  const raw1=add(false,13,1), raw2=add(false,25,2);
  const h1=add(true,0,raw1), h2=add(true,0,raw2);
  const bridge=add(false,h1,h2);
  let patch;
  if(factor){
    patch=add(true,bridge,add(false,13,25));
  }else{
    patch=add(false,add(true,bridge,13),add(true,bridge,25));
  }
  const out=add(false,early,patch);
  t.push(second);
  return {t,out,last:25+t.length,bridge};
}
function audit(v){
  const {t,out,last,bridge}=v;
  const ants=[];
  const readers=t.map(()=>[]);
  let direct=0,pairs=0;
  for(const [j,g] of t.entries()){
    if(g.read.length!==2||g.read[0]===g.read[1]||g.read.some(i=>i>=26+j))
      throw Error("Bad binary syntax in bridge control");
    const parents=g.read.filter(i=>i>=26).map(i=>i-26);
    const prev=new Set(parents.flatMap(k=>[k,...ants[k]]));
    for(const k of parents)readers[k].push(j);
    ants.push(prev);
    if(g.and){
      if(parents.some(k=>t[k].and))direct++;
      pairs+=[...prev].filter(k=>t[k].and).length;
    }
  }
  const bridges=t.flatMap((g,j)=>!g.and&&[...ants[j]].some(k=>t[k].and)&&
    t.some((q,k)=>q.and&&ants[k].has(j))?[26+j]:[]);
  if(direct||bridges.length!==1||bridges[0]!==bridge)throw Error("Wrong AND-path shape");
  function run(row){
    const signal=Array.from({length:26},(_,i)=>!!(row&(1<<i)));
    for(const g of t)signal.push(evalGate(signal,g));
    return [signal[out],signal[last],signal[bridge]];
  }
  if(flags.some(([p,l])=>!run(flagRow(p,l)).slice(0,2).some(Boolean))||
     negative.some(row=>run(row).slice(0,2).some(Boolean)))throw Error("Bridge control violates the promise");
  if(!negative.some(row=>run(row)[2]))throw Error("The shared bridge should accept a negative");
  const [a0,b0]=run(flagRow(0,0)),[a4,b4]=run(flagRow(0,4));
  if(!a0||b0||a4||!b4)throw Error("Bridge control loses an exclusive flag");
  return {gates:t.length,out,last,directAndReaders:direct,pairs,bridges};
}
const shared=audit(variant(false)),factored=audit(variant(true));
if(shared.gates!==72||factored.gates!==71||shared.pairs!==4||factored.pairs!==2)
  throw Error("Wrong guard factoring change");
console.log(JSON.stringify({shared,factored}));
