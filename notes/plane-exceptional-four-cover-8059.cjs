"use strict";

const n=13, vertices=Array.from({length:n},(_,i)=>i), top=(1<<26)-1;
const id=Array.from({length:26},(_,i)=>i);
const bit=i=>1<<i;
const mod=x=>(x%3+3)%3;
const points=[[1,0,0]];
for(let i=1;i<n;i++){
  const [x,y,z]=points[i-1];
  points.push([mod(-z),mod(x+z),y]);
}
function key(v){
  const s=v.find(x=>x!==0);
  if(s===undefined)throw Error("Zero projective vector");
  return v.map(x=>mod(s*x)).join(",");
}
const dot=(a,b)=>mod(a.reduce((s,x,i)=>s+x*b[i],0));
const cross=(a,b)=>[mod(a[1]*b[2]-a[2]*b[1]),mod(a[2]*b[0]-a[0]*b[2]),mod(a[0]*b[1]-a[1]*b[0])];
const mask=xs=>xs.reduce((m,i)=>m|bit(i),0);
const lineSets=points.map((p,l)=>vertices.filter(q=>dot(points[q],cross(p,points[(l+1)%13]))===0));
const lines=lineSets.map(mask);
if(new Set(points.map(key)).size!==13||lines.some((s,i)=>s!==mask([0,1,3,9].map(d=>(i+d)%13))))
  throw Error("Wrong Singer labeling");
const pointIndex=new Map(points.map((p,i)=>[key(p),i]));
const lineIndex=new Map(lines.map((m,i)=>[m,i+13]));
const neighbors=id.map(i=>i<13?mask(vertices.filter(l=>lines[l]&bit(i)).map(l=>l+13)):lines[i-13]);
const quads=[];
for(let p=0;p<(1<<13);p++){
  const ps=vertices.filter(i=>p&bit(i));
  if(ps.length!==4||lines.some(l=>ps.filter(x=>l&bit(x)).length>=3))continue;
  quads.push(p|mask(vertices.filter(l=>(lines[l]&p)===0).map(l=>l+13)));
}
if(quads.length!==234)throw Error("Wrong negative class");
const order=new Set();
const transforms=[];
for(let code=0;code<3**9;code++){
  let t=code;
  const A=Array.from({length:3},()=>Array.from({length:3},()=>{const z=t%3;t=(t-z)/3;return z;}));
  if(dot(A[0],cross(A[1],A[2]))===0)continue;
  const p=points.map(v=>pointIndex.get(key(A.map(row=>dot(v,row)))));
  const l=lineSets.map(s=>lineIndex.get(mask(s.map(i=>p[i]))));
  const a=[...p,...l], name=a.join(",");
  if(new Set(a).size!==26||a.some(x=>x===undefined))throw Error("Nonbijective projectivity");
  if(order.has(name))continue;
  transforms.push(a);order.add(name);
}
if(transforms.length!==5616)throw Error("Wrong projective group size");

const bits=m=>id.filter(i=>m&bit(i));
const size=m=>{let n=0;while(m){m&=m-1;n++;}return n;};
const groups=xs=>xs.flatMap((a,i)=>xs.slice(i+1).flatMap((b,j)=>xs.slice(i+j+2).map(c=>[a,b,c])));
const contains=(a,b)=>(a&b)===b;
const act=(s,a)=>mask(bits(s).map(x=>a[x]));
let visited=0;
function hitting(constraints,budget){
  let rows=[...new Set(constraints)];
  const pop=n=>{let k=0;while(n){n&=n-1n;k++;}return k;};
  rows=rows.map(x=>[x,pop(x)]).sort((a,b)=>a[1]-b[1]).map(([x])=>x);
  const minimal=[];
  for(const row of rows){
    if(row===0n)return null;
    if(!minimal.some(old=>(old&row)===old))minimal.push(row);
  }
  const failed=new Set();
  function rec(rows,k){
    visited++;
    if(!rows.length)return [];
    if(k===0)return null;
    let pack=0n,bound=0;
    for(const x of rows)if((pack&x)===0n){pack|=x;if(++bound>k)return null;}
    const key=k+":"+rows.map(x=>x.toString(36)).join(".");
    if(failed.has(key))return null;
    let choices=rows[0];
    const options=[];
    while(choices){
      const w=choices&-choices;
      choices^=w;
      const rest=rows.filter(c=>(c&w)===0n);
      options.push([w,rest]);
    }
    options.sort((a,b)=>a[1].length-b[1].length);
    for(const [wire,rest] of options){
      const tail=rec(rest,k-1);
      if(tail)return [wire,...tail];
    }
    failed.add(key);
    return null;
  }
  return rec(minimal,budget);
}
function check(F,ordinary,budget,exhaustive=false){
  const x=F.reduce((s,e)=>s|e,0);
  const sources=new Set(bits(x).map(bit));
  for(const c of ordinary){
    const allowed=mask(bits(neighbors[c]&x).filter(v=>!F.includes(bit(c)|bit(v))));
    for(let s=allowed;s;s=(s-1)&allowed)sources.add(s);
  }
  const all=[...sources], sourceBit=i=>1n<<BigInt(i);
  function accepts(s){
    return all.reduce((m,a,i)=>(a&s)?m|sourceBit(i):m,0n);
  }
  const pos=F.map(accepts), neg=quads.map(accepts);
  const constraints=pos.flatMap(a=>neg.map(b=>a&~b));
  const answer=hitting(constraints,budget);
  if(!answer)return null;
  const used=all.filter((_,i)=>answer.includes(sourceBit(i)));
  for(const p of F)for(const q of quads)
    if(!used.some(w=>(w&p)&&(w&q)===0))throw Error("Inadequate source certificate");
  if(!exhaustive)return used;
  const found=new Set();
  const reduced=[...new Set(constraints)].sort((a,b)=>pop(a)-pop(b)).reduce((acc,w)=>{
    if(!acc.some(q=>(q&w)===q))acc.push(w);
    return acc;
  },[]);
  function pop(w){let k=0;while(w){w&=w-1n;k++;}return k;}
  const seen=new Set();
  function extend(chosen,k,from){
    found.add(chosen);
    if(found.size>5000)throw Error("Bounded source census");
    if(k===0)return;
    for(let i=from;i<all.length;i++){
      const q=sourceBit(i);
      if((chosen&q)===0n)extend(chosen|q,k-1,i+1);
    }
  }
  function collect(chosen,k){
    if(seen.has(chosen))return;
    seen.add(chosen);
    const left=reduced.find(c=>(c&chosen)===0n);
    if(left===undefined){extend(chosen,k,0);return;}
    if(!k)return;
    for(let next=left;next;next&=next-1n)
      collect(chosen|(next&-next),k-1);
  }
  collect(0n,budget);
  const localAdj=id.map(i=>F.filter(e=>e&bit(i)).map(e=>bits(e^bit(i))[0]));
  const cores=new Map();
  function walk(first,last,path,n){
    if(n===4)cores.set(path,4);
    if(n===6){
      if(localAdj[last].includes(first))cores.set(path,8);
      return;
    }
    for(const next of localAdj[last])if(!(path&bit(next)))
      walk(first,next,path|bit(next),n+1);
  }
  for(const v of bits(x))walk(v,v,bit(v),1);
  for(const [core,lower] of cores){
    const e=bits(core).filter(v=>v<13).reduce((a,v)=>a+size(neighbors[v]&core),0);
    if(e!==(lower===8?6:3))throw Error("Core has an incidence chord");
    for(let row=core;row;row=(row-1)&core){
      const flag=bits(row).some(v=>v<13&&(neighbors[v]&row)!==0);
      if(!flag&&(lower===8||size(row)<=2)&&!quads.some(q=>(row&q)===row))
        throw Error("Core negative has no quadrangle extension");
    }
  }
  const survivors=[];
  let allSingleton=0;
  for(const pool of found){
    const a=all.filter((_,i)=>(pool&sourceBit(i))!==0n);
    const rawOnly=a.every(m=>size(m)===1);
    if(rawOnly)allSingleton++;
    const g=budget-1;
    if(rawOnly&&g<a.length&&F.length>=a.length-1)continue;
    let pass=true;
    for(const [core,lower] of cores){
      if(a.some(w=>size(w&core)>1))continue;
      const lose=a.filter(w=>(w&core)===0).length;
      if(g-lose<lower){pass=false;break;}
    }
    if(pass)survivors.push(a);
  }
  return {poolCount:found.size,allSingleton,survivors};
}

function combinations(xs,k,from=0){
  if(!k)return [[]];
  const out=[];
  for(let i=from;i<=xs.length-k;i++)for(const more of combinations(xs,k-1,i+1))out.push([xs[i],...more]);
  return out;
}
function match(F,k,used=0,i=0){
  if(!k)return true;
  for(let j=i;j<=F.length-k;j++)if(!(F[j]&used)&&match(F,k-1,used|F[j],j+1))return true;
  return false;
}
const coverReps=[];
for(const shore of [0,13]){
  const S=mask(vertices.map(i=>i+shore));
  const other=bits(top^S);
  for(const o of [2,3]){
    const seen=new Set();
    for(const O0 of combinations(other,o)){
      const O=mask(O0);
      if(seen.has(O))continue;
      for(const a of transforms)seen.add(act(O,a));
      coverReps.push({shore,S,O,V:S|O,complete:true});
    }
    if(seen.size!==combinations(other,o).length)throw Error("Missing opposite-shore configurations");
  }
  const removed=bit(shore);
  if(new Set(transforms.map(a=>act(removed,a))).size!==13)throw Error("Missing omitted vertex");
  const O=neighbors[shore];
  coverReps.push({shore,S:S^removed,O,V:(S^removed)|O,complete:false});
}
const totalFlags=id.flatMap(u=>u<13?bits(neighbors[u]).map(v=>bit(u)|bit(v)):[]);
const result=[];
let pools=0,rawPools=0,livePools=0,leftCases=0;
let bounded=false;
const start=Date.now();
outer:for(const geo of coverReps){
  const {shore,S,O,V,complete}=geo;
  const stable=transforms.filter(a=>act(V,a)===V);
  const seen=new Set();
  const r={shore,opposite:bits(O),complete,orbits:0,cases:0,feasible:0,examples:[],hist:{}};
  result.push(r);
  for(const E0 of combinations(bits(V),4)){
    const E=mask(E0);
    if(seen.has(E))continue;
    for(const a of stable)seen.add(act(E,a));
    if(!E0.some(x=>neighbors[x]&E))continue;
    const good=bits(S&~E&top).filter(x=>size(neighbors[x]&O)<=1).length;
    if(good>=10)continue;
    r.orbits++;
    const base=V&~E&top;
    const available=totalFlags.filter(f=>f&E);
    for(const centerCount of [11,12]){
      const add=centerCount-size(base);
      if(add<0||add>4)continue;
      for(const addRaw of combinations(E0,add)){
        const K=base|mask(addRaw);
        const mandatory=totalFlags.filter(f=>!(f&K));
        if(mandatory.some(f=>!available.includes(f)))throw Error("Inadequate cover");
        const optional=available.filter(f=>!mandatory.includes(f));
        for(let i=0;i<1<<optional.length;i++){
          if(Date.now()-start>80000){bounded=true;break outer;}
          const F=[...mandatory,...optional.filter((_,j)=>i&bit(j))];
          if(!match(F,4))continue;
          const budget=F.length+12-centerCount;
          const got=check(F,bits(K),budget,true);
          r.cases++;
          if(got){
            r.feasible++;
            pools+=got.poolCount;rawPools+=got.allSingleton;livePools+=got.survivors.length;
            if(got.survivors.length){
              leftCases++;
              const key=centerCount+","+F.length+","+got.survivors.length;
              r.hist[key]=(r.hist[key]??0)+1;
              if(r.examples.length<2)r.examples.push({E:E0,K:bits(K),F,budget,sources:got.survivors[0]});
            }
          }
        }
      }
    }
  }
  if(seen.size!==combinations(bits(V),4).length)throw Error("Missing critical cover orbit");
}
const critical={cases:result.reduce((a,b)=>a+b.cases,0),sourcePassing:result.reduce((a,b)=>a+b.feasible,0),
  sourcePools:pools,rawPools,livePools,leftCases};
if(bounded||critical.cases!==15252||pools!==3602||livePools||leftCases)
  throw Error("Critical four-center replay did not finish the exclusion");
visited=0;

const centers=[];
for(let i=0;i<26;i++)for(let j=0;j<i;j++)for(let k=0;k<j;k++)for(let l=0;l<k;l++){
  const e=[l,k,j,i], E=mask(e);
  if(e.some(x=>neighbors[x]&E))centers.push(e);
}
const wideStart=Date.now();
const done=new Set();
const wide=[];
let wideBounded=false;
for(const center of centers){
  const E=mask(center);
  if(done.has(E))continue;
  const stable=transforms.filter(a=>act(E,a)===E);
  for(const a of transforms)done.add(act(E,a));
  const flags=[...new Set(center.flatMap(v=>bits(neighbors[v]).map(u=>bit(v)|bit(u))))];
  const index=new Map(flags.map((f,i)=>[f,i]));
  const im=stable.map(a=>flags.map(f=>index.get(act(f,a))));
  if(im.some(p=>p.some(i=>i===undefined)))throw Error("Wrong stabilizer");
  const visit=new Set();
  const r={center, tested:0,feasible:0,bySize:{},witnesses:[]};
  wide.push(r);
  for(let s=0;s<(1<<flags.length);s++){
    if(visit.has(s))continue;
    if(Date.now()-wideStart>80000){wideBounded=true;break;}
    const which=flags.flatMap((_,i)=>s&bit(i)?[i]:[]);
    for(const a of im)visit.add(mask(which.map(i=>a[i])));
    const F=which.map(i=>flags[i]);
    if(!match(F,4))continue;
    r.tested++;
    const used=check(F,id,F.length-1);
    if(used){
      r.feasible++;
      r.bySize[F.length]=(r.bySize[F.length]??0)+1;
      if(r.witnesses.length<2)r.witnesses.push({F,used});
    }
  }
  if(wideBounded)break;
  if(visit.size!==1<<flags.length)throw Error("Missing flag orbit");
}
if(!wideBounded&&done.size!==centers.length)throw Error("Missing four-cover orbit");
const broad={orbits:wide.length,cases:wide.reduce((a,b)=>a+b.tested,0),
    feasible:wide.reduce((a,b)=>a+b.feasible,0)};
if(wideBounded||broad.cases!==34976||broad.feasible)
  throw Error("Broad four-center replay did not finish the exclusion");
console.log(JSON.stringify({critical,broad,visited}));
