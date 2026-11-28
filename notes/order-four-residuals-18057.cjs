"use strict";

const n=21, anchor=148193411399n;
const masks=[693637218693n,214750724172n,43100670213n,2201724715076n,429513539622n,10838245382n,214756769811n,412337856832n,154640061441n,1718003696225n,1387274437386n,3436007392450n,3436108316976n,1168315262978n];
const d=new Set([0,5,7,17,20]);
const ids=Array.from({length:n},(_,i)=>i);
const survives=(m,i)=>(m&(1n<<BigInt(i)))===0n;
const incident=(p,l)=>d.has((l+n-p)%n);
if(ids.some(p=>ids.some(q=>p<q&&ids.filter(l=>incident(p,l)&&incident(q,l)).length!==1)))
  throw Error("Wrong projective incidence");
const rows=masks.map((mask,j)=>{
  const support=anchor|mask;
  const point=ids.filter(p=>survives(support,p));
  const line=ids.filter(l=>survives(support,n+l));
  const neighbors=new Map(point.map(p=>[p,line.filter(l=>incident(p,l))]));
  const mate=new Map();
  function augment(p,visited){
    for(const l of neighbors.get(p)){
      if(visited.has(l))continue;
      visited.add(l);
      if(!mate.has(l)||augment(mate.get(l),visited)){
        mate.set(l,p);return true;
      }
    }
    return false;
  }
  for(const p of point)if(!augment(p,new Set()))throw Error("Unmatched point in case "+j);
  if(mate.size!==point.length||new Set(mate.values()).size!==point.length||
     [...mate].some(([l,p])=>!incident(p,l)))throw Error("Invalid matching");
  const edges=[...neighbors.values()].reduce((s,ls)=>s+ls.length,0);
  const formula=edges+mate.size-1;
  const erasures=j<4?67:j<9?72:76;
  const maxSize=124-erasures;
  if(formula!==maxSize+1)throw Error("Unexpected residual in case "+j);
  return {case:j,points:point.length,lines:line.length,edges,matching:mate.size,formula,maxSize,
    certificate:[...mate].map(([l,p])=>[p,l])};
});
if(rows.length!==14)throw Error("Wrong case count");
console.log(JSON.stringify(rows));
