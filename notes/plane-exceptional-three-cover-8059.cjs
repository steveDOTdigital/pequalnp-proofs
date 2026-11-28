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
function check(F,ordinary,budget,requireRaw=false){
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
  if(!requireRaw)return used;
  const found=new Map();
  const reduced=[...new Set(constraints)].sort((a,b)=>pop(a)-pop(b)).reduce((r,w)=>{
    if(!r.some(q=>(q&w)===q))r.push(w);
    return r;
  },[]);
  function pop(w){let k=0;while(w){w&=w-1n;k++;}return k;}
  const seen=new Set();
  let stop=false;
  function augment(chosen,k,from){
    if(stop)return;
    found.set(chosen,true);
    if(found.size>45000){stop=true;return;}
    if(k===0)return;
    for(let i=from;i<all.length;i++){
      const q=1n<<BigInt(i);
      if((chosen&q)===0n)augment(chosen|q,k-1,i+1);
    }
  }
  function collect(chosen,k){
    if(stop||seen.has(chosen))return;
    seen.add(chosen);
    const left=reduced.find(c=>(c&chosen)===0n);
    if(left===undefined){augment(chosen,k,0);return;}
    if(k===0)return;
    for(let next=left;next;next&=next-1n)
      collect(chosen|(next&-next),k-1);
  }
  collect(0n,budget);
  if(stop)throw Error("Source-set enumeration reached its limit");
  const allRaw=all.reduce((s,w,i)=>size(w)===1?s|sourceBit(i):s,0n);
  if(found.size!==1||!found.has(allRaw)||size(x)!==F.length)
    throw Error("Found a nontrivial source set or extra binary budget");
  return {rawSources:size(x),sets:found.size};
}
const result=[];
for(const shore of [0,13])for(const mode of [12,13]){
  const side=vertices.map(i=>i+shore), other=vertices.map(i=>i+(13-shore));
  const fixed=mode===12?mask(other.slice(0,2)):bit(side[0]);
  const orbit=new Set(transforms.map(t=>act(fixed,t)));
  if(orbit.size!==(mode===12?78:13))throw Error("Symmetry coverage failed");
  const stabilizer=transforms.filter(t=>act(fixed,t)===fixed);
  const O=mode===12?fixed:neighbors[side[0]];
  const outside=mode===12?0:fixed;
  const eligible=side.filter(v=>((neighbors[v]&O)===0||
    size(neighbors[v]&O)===1)&&(outside&bit(v))===0);
  const seen=new Set();
  let cases=0, reps=0, successes=0;
  const levels={},examples=[];
  for(const E0 of groups(eligible)){
    const E=mask(E0);
    if(seen.has(E))continue;
    const eo=new Set(stabilizer.map(t=>act(E,t)));
    for(const x of eo)seen.add(x);
    reps++;
    const mandatory=E0.flatMap(v=>bits(neighbors[v]&~O&top).map(u=>bit(v)|bit(u)));
    const optional=E0.flatMap(v=>bits(neighbors[v]&O).map(u=>bit(v)|bit(u)));
    const ordinary=side.filter(i=>!((E|outside)&bit(i))).concat(bits(O));
    if(ordinary.length!==mode||optional.length>3)throw Error("Wrong critical cover");
    for(let f=0;f<(1<<optional.length);f++){
      const F=[...mandatory,...optional.filter((_,j)=>f&bit(j))];
      const budget=F.length+12-mode;
      const got=check(F,ordinary,budget,true);
      cases++;
      if(got){
        successes++;
        levels[F.length]=(levels[F.length]??0)+1;
        if(mode===13)throw Error("Mixed sixteen-vertex cover survived");
        if(examples.length<1)examples.push({E:E0,O:bits(O),budget,data:got});
      }
    }
  }
  if(seen.size!==groups(eligible).length)throw Error("Incomplete exceptional-center orbits");
  result.push({shore,mode,cases,reps,successes,levels,examples});
}
if(result.some(r=>r.successes!==(r.mode===12?12:0)))throw Error("Wrong number of surviving source families");
const critical={classes:result,visited,remainingReadOnceFamilies:24};
visited=0;
const seenCenters=new Set();
const wide=[];
const started=Date.now();
let bounded=false;
function match3(f){
  for(let i=0;i<f.length;i++)
  for(let j=0;j<i;j++)if((f[i]&f[j])===0)
  for(let k=0;k<j;k++)if((f[k]&(f[i]|f[j]))===0)return true;
  return false;
}
outer:for(const center of groups(id)){
  const E=mask(center);
  if(seenCenters.has(E))continue;
  const stabilizer=transforms.filter(a=>act(E,a)===E);
  for(const tr of transforms)seenCenters.add(act(E,tr));
  const f=[...new Set(center.flatMap(c=>bits(neighbors[c]).map(q=>bit(c)|bit(q))))];
  const index=new Map(f.map((e,i)=>[e,i]));
  const opts=stabilizer.map(a=>f.map(e=>index.get(act(e,a))));
  if(opts.some(o=>o.some(i=>i===undefined)))throw Error("Invalid star-union symmetry");
  const seen=new Set();
  const out={center,cases:0,skips:0,survive:0,examples:[]};
  wide.push(out);
  for(let z=0;z<(1<<f.length);z++){
    if(seen.has(z))continue;
    if(Date.now()-started>90000){bounded=true;break outer;}
    const zz=f.flatMap((_,i)=>z&bit(i)?[i]:[]);
    for(const o of opts)seen.add(zz.reduce((a,i)=>a|bit(o[i]),0));
    const F=zz.map(i=>f[i]);
    if(!match3(F)){out.skips++;continue;}
    const w=check(F,id,F.length-1);
    out.cases++;
    if(w){
      const end=F.reduce((a,b)=>a|b,0);
      if(w.length>F.length-1||size(end)<F.length)throw Error("Unexpected source or graph bound");
      out.survive++;
      if(out.examples.length<2)out.examples.push({F,sources:w});
    }
  }
  if(seen.size!==(1<<f.length))throw Error("Incomplete hidden-flag orbits");
}
if(!bounded&&seenCenters.size!==2600)throw Error("Incomplete center orbits");
if(bounded||wide.length!==10||wide.reduce((a,b)=>a+b.cases,0)!==2188||wide.some(x=>x.survive))
  throw Error("Three-center case enumeration did not exclude the source budget");
console.log(JSON.stringify({critical,allThreeCenters:{orbits:wide.length,cases:2188,
  supportsBelowFlagCount:wide.reduce((a,b)=>a+b.survive,0),visited}}));
