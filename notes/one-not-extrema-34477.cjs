"use strict";
const n=8;
const vertices=Array.from({length:n},(_,i)=>i);
const edges=[[0,4],[1,4],[0,5],[2,5],[1,6],[2,6],[3,6],[0,7],[3,7],[4,7],[5,7],[6,7]];
const rows=Array.from({length:1<<n},(_,i)=>i);
const bit=rows.map(i=>1n<<BigInt(i));
const truth=row=>edges.some(([a,b])=>(row&(1<<a))&&(row&(1<<b)));
const flags=edges.map(([a,b])=>(1<<a)|(1<<b));
const maxNegative=rows.filter(row=>!truth(row)&&vertices.every(i=>row&(1<<i)||truth(row|(1<<i))));
const witnessMax=row=>maxNegative.some(big=>(row&big)===row);
if(rows.some(row=>!truth(row)&&!witnessMax(row))||
   rows.some(row=>truth(row)&&!flags.some(f=>(row&f)===f)))throw Error("Extrema do not cover the cube");

const table=pred=>rows.reduce((v,row)=>pred(row)?v|bit[row]:v,0n);
const raw=vertices.map(i=>table(row=>(row&(1<<i))!==0));
const coldFlags=table(row=>flags.includes(row));
const negativeTests=table(row=>maxNegative.includes(row));
const tiers=[new Set(raw)];
const seen=new Set(raw);
for(let k=1;k<=3;k++){
  const next=new Set();
  for(let i=0;i<=k-1-i;i++)
    for(const left of tiers[i])for(const right of tiers[k-1-i])
      for(const output of [left&right,left|right])
        if(!seen.has(output))next.add(output);
  for(const output of next)seen.add(output);
  tiers.push(next);
}
const profile=tiers.map((pool,gates)=>{
  let hotEveryFlag=0,coldEveryMaxNegative=0,both=0,possible=0;
  for(const h of pool){
    const a=(h&coldFlags)===coldFlags;
    const b=(h&negativeTests)===0n;
    if(a)hotEveryFlag++;
    if(b)coldEveryMaxNegative++;
    if(a&&b)both++;
    if(!a&&!b)possible++;
  }
  if(hotEveryFlag+coldEveryMaxNegative-both+possible!==pool.size)throw Error("Wrong profile total");
  return {gateCost:gates,total:pool.size,hotEveryFlag,coldEveryMaxNegative,both,possible};
});
console.log(JSON.stringify({flags:flags.length,maximalIndependentSets:maxNegative,profile}));
