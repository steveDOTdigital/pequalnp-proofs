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
console.log(JSON.stringify({coreGates:core.length,totalGates:core.length+3,flags:flags.length,negatives:negative.length,first:[0,0,...one],second:[0,4,...two]}));

const variants = process.argv.includes("--both") ? ["lines", "points"] : ["lines"];
const positives=flags.map(([p,l])=>flagRow(p,l));
const rows=[...positives,...negative];
const all=(1n<<BigInt(rows.length))-1n;
const pos=(1n<<BigInt(positives.length))-1n;
const neg=all^pos;
const firstBit=1n<<BigInt(flags.findIndex(([p,l])=>p===0&&l===0));
const secondBits=flags.flatMap(([p,l],i)=>[4,13,14,27].includes(13*p+l)?[1n<<BigInt(i)]:[]);
if(secondBits.length!==4)throw Error("Wrong ordered witness alternatives");
const raw=Array.from({length:26},(_,i)=>rows.reduce((bits,row,r)=>row&(1<<i)?bits|(1n<<BigInt(r)):bits,0n));

function control(variant){
  if(variant==="lines")return [...core,first,second];
  const gates=[];
  const add=(and,a,b)=>{gates.push({and,read:[a,b]});return 25+gates.length;};
  const ors=indices.map(p=>indices.filter(l=>lines[l]&(1<<p)).map(l=>13+l)
    .reduce((prev,l)=>add(false,prev,l)));
  // Point zero is on both (0,0) and (0,4). Keep it in the first
  // group and use an exclusive flag at (1,0) from the second group.
  const ts=ors.slice(1).map((w,j)=>add(true,w,j+1));
  const tail=ts.slice(1,-1).reduce((a,b)=>add(false,a,b),ts[0]);
  return [...gates,{and:true,read:[ors[0],0]},{and:false,read:[tail,ts.at(-1)]}];
}
function test(a,b){
  const together=a|b;
  return (together&pos)===pos&&(together&neg)===0n&&
    (a&firstBit)!==0n&&(b&firstBit)===0n&&
    secondBits.some(x=>(b&x)!==0n&&(a&x)===0n);
}
function evalMasks(gates,source,change=-1,value=0n){
  const watch=gates.length-2;
  const out=source.slice();
  for(let j=(source.length-26);j<watch;j++){
    const g=gates[j];
    out.push(j===change?value:g.and?out[g.read[0]]&out[g.read[1]]:out[g.read[0]]|out[g.read[1]]);
  }
  function terminal(i){
    if(i===change)return value;
    const {and,read:[a,b]}=gates[i];
    return and?out[a]&out[b]:out[a]|out[b];
  }
  return [terminal(watch),terminal(watch+1),out];
}
function required(alo,blo,ahi,bhi){
  const low=alo|blo,high=ahi|bhi;
  if((low&neg)!==0n||(high&pos)!==pos||(ahi&firstBit)===0n||(blo&firstBit)!==0n)return [];
  let mustSet=pos&~low,mustClear=neg&high;
  if((alo&firstBit)===0n)mustSet|=firstBit;
  if((bhi&firstBit)!==0n)mustClear|=firstBit;
  return secondBits.flatMap(x=>{
    if((bhi&x)===0n||(alo&x)!==0n)return [];
    const ones=mustSet|((blo&x)===0n?x:0n);
    const zeros=mustClear|((ahi&x)!==0n?x:0n);
    return (ones&zeros)===0n?[[ones,zeros]]:[];
  });
}
const counter={bypasses:0,editsConsidered:0,editableLocations:0,definitionsTested:0};
let witness=null;
outer:for(const variant of variants){
  const original=control(variant);
  if(!test(...evalMasks(original,raw)))throw Error("Wrong starting control for "+variant);
  for(let removed=0;removed<61;removed++)for(let replacement=0;replacement<26+removed;replacement++){
    counter.bypasses++;
    const slot=26+removed;
    const remap=i=>i===slot?replacement:i-(i>slot?1:0);
    const gates=original.filter((_,j)=>j!==removed).map(({and,read})=>({and,read:read.map(remap)}));
    const [a,b,tape]=evalMasks(gates,raw);
    if(test(a,b)){witness={variant,removed,replacement,gates};break outer;}
    for(let j=0;j<gates.length;j++){
      counter.editsConsidered++;
      const here=26+Math.min(j,60);
      const src=tape.slice(0,here);
      const req=required(...evalMasks(gates,src,j,0n).slice(0,2),...evalMasks(gates,src,j,all).slice(0,2));
      if(req.length===0)continue;
      counter.editableLocations++;
      const candidates=[{and:false,read:[],value:0n},{and:true,read:[],value:all}];
      for(let i=0;i<here;i++)for(let k=i;k<here;k++){
        candidates.push({and:false,read:[i,k],value:src[i]|src[k]});
        if(i!==k)candidates.push({and:true,read:[i,k],value:src[i]&src[k]});
      }
      for(const {and,read,value} of candidates){
        counter.definitionsTested++;
        if(req.some(([ones,zeros])=>(value&ones)===ones&&(value&zeros)===0n)){
          if(!test(...evalMasks(gates,src,j,value)))throw Error("Replacement condition unsound");
          gates[j]={and,read};
          witness={variant,removed,replacement,change:j,gates};
          break outer;
        }
      }
    }
  }
}
console.log(JSON.stringify({variants,...counter,witness}));
