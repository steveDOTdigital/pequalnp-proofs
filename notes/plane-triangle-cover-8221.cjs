const q=13, full=(1<<q)-1;
const idx=Array.from({length:q},(_,i)=>i);
const members=Array.from({length:full+1},(_,m)=>idx.filter(i=>m&(1<<i)));
const lines=idx.map(j=>[0,1,3,9].reduce((s,d)=>s|1<<((j+d)%q),0));
const points=idx.map(i=>lines.reduce((s,m,j)=>s|((m>>i&1)<<j),0));
const isCap=(m,arr)=>arr.every(r=>members[m&r].length<=2);
const exterior=(m,arr)=>full^members[m].reduce((s,i)=>s|arr[i],0);
const options=(capSize,arr,opposite)=>members.flatMap((m,i)=>{
  if(m.length!==capSize||!isCap(i,opposite))return [];
  const e=exterior(i,arr);
  if(members[e].length!==q-(capSize===3?9:10)||!isCap(e,arr))throw Error('Unexpected exterior');
  return [[i,e]];
});
if(members.some((m,i)=>m.length===5&&(isCap(i,points)||isCap(i,lines))))throw Error('Cap exceeds four');
const lineTriangles=options(3,lines,points);
const lineQuads=options(4,lines,points);
const pointQuads=options(4,points,lines);
const pointByKey=new Map(pointQuads.map(([a,b],i)=>[a+','+b,i]));
const edges=lineQuads.map(([b,a])=>members[b].map(l=>{
  const t=b^(1<<l);
  const p=exterior(t,lines);
  const i=pointByKey.get(p+','+t);
  if(i===undefined||((p&a)!==a))throw Error('Missing point extension');
  return i;
}));
const sizes=[];
const unseen=new Set(lineQuads.map((_,i)=>i));
const backward=pointQuads.map(()=>[]);
edges.forEach((xs,u)=>xs.forEach(v=>backward[v].push(u)));
if(backward.some(a=>a.length!==4))throw Error('Not regular');
while(unseen.size){
  const u=unseen.values().next().value;
  unseen.delete(u);
  const stack=[u], right=new Set(); let n=1;
  while(stack.length)for(const v of edges[stack.pop()])if(!right.has(v)){
    right.add(v);
    for(const w of backward[v])if(unseen.delete(w)){stack.push(w);n++;}
  }
  sizes.push([n,right.size]);
}
let core=0;
for(const [b,ext] of lineTriangles)for(const p of members[ext]){
  const a=ext^(1<<p);
  const leftCover=lineQuads.filter(([l,r])=>(l&b)===b&&(r&a)===a);
  const rightCover=pointQuads.filter(([l,r])=>(l&a)===a&&(r&b)===b);
  if(leftCover.length!==1||rightCover.length!==1)throw Error('Nonunique extension');
  core++;
}
let small=0;
for(let b=0;b<=full;b++){
  if(members[b].length>3||!isCap(b,points))continue;
  const ext=exterior(b,lines);
  for(let a=ext;;a=(a-1)&ext){
    if(members[a].length<=3&&isCap(a,lines)){
      if(!lineQuads.some(([l,r])=>(l&b)===b&&(r&a)===a)||
         !pointQuads.some(([l,r])=>(l&a)===a&&(r&b)===b))throw Error('Small cap pair not covered');
      small++;
    }
    if(!a)break;
  }
}
if(lineQuads.length!==234||pointQuads.length!==234||core!==936||
   sizes.length!==1||sizes[0][0]!==234||sizes[0][1]!==234)throw Error('Unexpected covering graph');
console.log(JSON.stringify({small,triangles:lineTriangles.length,lineQuads:lineQuads.length,pointQuads:pointQuads.length,core,components:sizes}));
