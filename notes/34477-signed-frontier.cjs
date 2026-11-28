"use strict";

const graph=[[0,4],[1,4],[0,5],[2,5],[1,6],[2,6],[3,6],[0,7],[3,7],[4,7],[5,7],[6,7]];
const alive=[0,2,3,4,5,6,7];
const edges=graph.filter(e=>e.every(x=>alive.includes(x))).map(e=>e.map(x=>alive.indexOf(x)));
const n=alive.length, rows=1<<n;
const bits=Array.from({length:rows},(_,i)=>1n<<BigInt(i));
const top=(1n<<BigInt(rows))-1n;
const raw=Array.from({length:n},(_,i)=>bits.reduce((x,b,r)=>r&(1<<i)?x|b:x,0n));
const positives=r=>edges.some(([i,j])=>(r&(1<<i))&&(r&(1<<j)));
const target=bits.reduce((x,b,r)=>positives(r)?x|b:x,0n);
const negatives=bits.filter((_,r)=>!positives(r));
const cmp=(a,b)=>a<b?-1:a>b?1:0;
const budget=Number(process.argv[2]??10);
const limit=Number(process.argv[3]??150000);
if(!Number.isSafeInteger(budget)||budget<1||budget>12||!Number.isSafeInteger(limit)||limit<1)
  throw Error("Use a positive budget up to twelve and a positive state limit");
const memo=Array.from({length:budget+1},()=>new Set());
const start=Date.now();
let discovered=0, candidates=0, verdict="unsat";
const path=[];
let witness=null;
function separates(state){
  for(const rowBit of negatives){
    let possible=target;
    for(const signal of state){
      possible&=(signal&rowBit)?signal:top^signal;
      if(!possible)break;
    }
    if(possible)return false;
  }
  return true;
}
function explore(k,signals){
  if(signals.includes(target)){
    verdict="sat";
    witness=path.map(({a,b,out,mode})=>({a:a.toString(16),b:b.toString(16),out:out.toString(16),mode}));
    return true;
  }
  if(k===0||signals.length>k+1)return false;
  signals.sort(cmp);
  const key=signals.map(v=>v.toString(16)).join(".");
  if(memo[k].has(key)||!separates(signals))return false;
  if(discovered>=limit||Date.now()-start>55000){verdict="bounded";return true;}
  memo[k].add(key);
  discovered++;
  for(let i=0;i<signals.length;i++)for(let j=i+1;j<signals.length;j++){
    const a=signals[i],b=signals[j];
    const options=[a&b,a&(top^b),(top^a)&b,a|b];
    const other=signals.filter((_,ix)=>ix!==i&&ix!==j);
    for(let mode=0;mode<options.length;mode++){
      const out=options[mode];
      if(out===0n||signals.includes(out)||options.indexOf(out)!==mode)continue;
      path.push({a,b,out,mode});
      for(let retain=0;retain<4;retain++){
        const next=[...other,out];
        if(retain&1)next.push(a);
        if(retain&2)next.push(b);
        candidates++;
        if(explore(k-1,next))return true;
      }
      path.pop();
    }
  }
  return false;
}
explore(budget,raw.slice());
console.log(JSON.stringify({budget,verdict,discovered,candidates,perLayer:memo.map(x=>x.size),witness,
  seconds:(Date.now()-start)/1000}));
