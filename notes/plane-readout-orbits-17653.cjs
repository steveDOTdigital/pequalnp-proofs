"use strict";

const n=13;
const ind=Array.from({length:n},(_,i)=>i);
const mod3=x=>(x%3+3)%3;
const step=([x,y,z])=>[mod3(-z),mod3(x+z),y];
const points=[[1,0,0]];
for(let i=1;i<n;i++)points.push(step(points[i-1]));

function key(v){
  const s=v.find(x=>x!==0);
  if(s===undefined)throw Error("Zero projective vector");
  return v.map(x=>mod3(s*x)).join(",");
}
function dot(a,b){return mod3(a.reduce((s,x,i)=>s+x*b[i],0));}
function cross(a,b){
  return [mod3(a[1]*b[2]-a[2]*b[1]),mod3(a[2]*b[0]-a[0]*b[2]),mod3(a[0]*b[1]-a[1]*b[0])];
}
const normals=points.map((p,l)=>cross(p,points[(l+1)%13]));
const mask=ps=>ps.reduce((a,i)=>a|(1<<i),0);
const lines=normals.map(v=>ind.filter(p=>dot(points[p],v)===0));
const masks=lines.map(mask);
if(new Set(points.map(key)).size!==n||new Set(masks).size!==n||
   lines.some((_,l)=>masks[l]!==mask([0,1,3,9].map(d=>(l+d)%n))))throw Error("Wrong Singer plane");
const flags=lines.flatMap((ps,l)=>ps.map(p=>13*p+l));
const reps=[4,13,14,27];
const covered=reps.map(()=>new Set());
const pointByKey=new Map(points.map((p,i)=>[key(p),i]));
const lineByMask=new Map(masks.map((line,i)=>[line,i]));
let gl=0;
for(let code=0;code<3**9;code++){
  let num=code;
  const A=Array.from({length:3},()=>Array.from({length:3},()=>{
    const d=num%3;num=(num-d)/3;return d;
  }));
  if(dot(A[0],cross(A[1],A[2]))===0)continue;
  gl++;
  const imageP=points.map(v=>pointByKey.get(key(A.map(r=>dot(v,r)))));
  const imageL=lines.map(ps=>lineByMask.get(mask(ps.map(p=>imageP[p]))));
  if(new Set(imageP).size!==n||new Set(imageL).size!==n)throw Error("Nonbijective action");
  const image=f=>13*imageP[Math.floor(f/13)]+imageL[f%13];
  const left=image(0);
  reps.forEach((f,i)=>{
    const right=image(f);
    covered[i].add(169*left+right);
    covered[i].add(169*right+left);
  });
}
const coverage=covered.map(s=>s.size);
const total=new Set(covered.flatMap(s=>[...s]));
const targets=flags.flatMap(a=>flags.filter(b=>a!==b).map(b=>169*a+b));
if(gl!==11232||coverage.reduce((a,b)=>a+b,0)!==total.size||
   total.size!==targets.length||targets.some(x=>!total.has(x)))throw Error("Missing ordered flag pairs");
const negativeMasks=[];
for(let p=0;p<(1<<n);p++){
  const chosen=ind.filter(i=>p&(1<<i));
  if(chosen.length!==4||lines.some(ps=>ps.filter(i=>p&(1<<i)).length>=3))continue;
  const missed=ind.filter(l=>(masks[l]&p)===0);
  negativeMasks.push(p|(mask(missed)<<n));
}
if(negativeMasks.length!==234||negativeMasks.reduce((a,b)=>a|b,0)!==(1<<26)-1)
  throw Error("A raw OR operand could be safe");
console.log(JSON.stringify({invertibleMatrices:gl,orbitSizes:coverage,orderedFlagPairs:total.size,
  quadrangles:negativeMasks.length,rawInputsAppearingOnNegatives:26}));
