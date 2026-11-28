"use strict";
const n=8, ids=Array.from({length:n},(_,i)=>i);
const pin=Number(process.argv[2]??-1);
if(!Number.isInteger(pin)||pin < -1||pin>=n)throw Error("Expected a raw input index, or -1");
const graph=[[0,4],[1,4],[0,5],[2,5],[1,6],[2,6],[3,6],[0,7],[3,7],[4,7],[5,7],[6,7]];
const edges=graph.filter(e=>!e.includes(pin));
const bits=i=>ids.filter(x=>i&(1<<x));
const count=x=>bits(x).length;
const edgeIndex=new Map(edges.flatMap(([a,b],i)=>[[8*a+b,i],[8*b+a,i]]));
const rectangles=[];
for(let a=1;a<256;a++)for(let b=1;b<a;b++){
  if(a&b)continue;
  const pairs=bits(a).flatMap(x=>bits(b).map(y=>edgeIndex.get(8*x+y)));
  if(pairs.some(i=>i===undefined))continue;
  const flags=pairs.reduce((m,i)=>m|(1<<i),0);
  rectangles.push({a,b,flags});
}
const indexing=Array.from({length:edges.length},(_,i)=>rectangles.flatMap((r,j)=>r.flags&(1<<i)?[j]:[]));
const searchOrder=Array.from({length:edges.length},(_,i)=>i).sort((a,b)=>indexing[a].length-indexing[b].length);
const decompositions=new Map();
function parts(s){
  if(decompositions.has(s))return decompositions.get(s);
  const list=[];
  for(let a=(s-1)&s;a;a=(a-1)&s)for(let b=(s-1)&s;b>=a;b=(b-1)&s)
    if((a|b)===s)list.push([a,b]);
  decompositions.set(s,list);
  return list;
}
const starting=[10,12,12,11,11,11,10,9];
let bound=Number(process.argv[3]??(pin<0?14:starting[pin])), witness=null;
if(!Number.isInteger(bound)||bound<1||bound>15)throw Error("Expected an exclusive bound from 1 to 15");
const initialBound=bound;
const coverSeen=new Set();
let coverNodes=0, orNodes=0;
function price(wanted,cap,made){
  orNodes++;
  if(wanted.size>cap)return null;
  const pending=[...wanted].filter(s=>!made.has(s)).sort((a,b)=>count(b)-count(a)||b-a);
  if(!pending.length)return [...made];
  const s=pending[0];
  for(const [a,b] of parts(s)){
    const next=new Set(wanted);
    if(count(a)>1)next.add(a);
    if(count(b)>1)next.add(b);
    made.set(s,[a,b]);
    const res=price(next,cap,made);
    if(res)return res;
    made.delete(s);
  }
  return null;
}
const allFlags=(1<<edges.length)-1;
function enumerate(covered,selected){
  coverNodes++;
  const orNeeded=new Set();
  for(const i of selected)
    for(const s of [rectangles[i].a,rectangles[i].b])
      if(count(s)>1)orNeeded.add(s);
  if(2*selected.length-1+orNeeded.size>=bound)return;
  const signature=[...selected].sort((a,b)=>a-b).join(",");
  if(coverSeen.has(signature))return;
  coverSeen.add(signature);
  if(covered===allFlags){
    const rects=selected.map(i=>rectangles[i]);
    for(let i=0;i<rects.length;i++){
      const other=rects.reduce((m,r,j)=>j===i?m:m|r.flags,0);
      if(other===allFlags)return;
    }
    let cap=bound-2*selected.length;
    for(;cap>=orNeeded.size;cap--){
      const got=price(orNeeded,cap,new Map());
      if(!got)break;
      bound=2*selected.length-1+got.length;
      witness={gates:bound,rectangles:rects,ors:got};
      cap=Math.min(cap,bound-2*selected.length+1);
    }
    return;
  }
  const next=searchOrder.find(i=>(covered&(1<<i))===0);
  for(const j of indexing[next]){
    const r=rectangles[j];
    enumerate(covered|r.flags,[...selected,j]);
  }
}
enumerate(0,[]);
if(witness){
  const groups=witness.rectangles.map(({a,b})=>[bits(a),bits(b)]);
  for(let x=0;x<256;x++){
    const values=new Map(ids.map(i=>[1<<i,(x&(1<<i))!==0]));
    for(const [s,[a,b]] of [...witness.ors].sort((u,v)=>count(u[0])-count(v[0]))){
      if(!values.has(a)||!values.has(b))throw Error("Wrong shared OR order");
      values.set(s,values.get(a)||values.get(b));
    }
    const check=witness.rectangles.some(({a,b})=>values.get(a)&&values.get(b));
    const target=edges.some(([a,b])=>(x&(1<<a))&&(x&(1<<b)));
    if(check!==target)throw Error("Incorrect witness");
  }
  witness.groups=groups;
}
console.log(JSON.stringify({pin,initialBound,best:bound,witness,coverNodes,orNodes,uniqueCovers:coverSeen.size,rectangles:rectangles.length}));
