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
console.log(JSON.stringify({gates:gates.length,earlier,last,directAndReaders,
  flags:flags.length,negativeQuadrangles:negative.length,
  firstExclusive:[0,0,...one],lastExclusive:[0,4,...two]}));
