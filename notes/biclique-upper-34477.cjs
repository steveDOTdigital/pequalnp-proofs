"use strict";

const n=8, ids=Array.from({length:n},(_,i)=>i);
const edges=[[0,4],[1,4],[0,5],[2,5],[1,6],[2,6],[3,6],[0,7],[3,7],[4,7],[5,7],[6,7]];
const contains=(mask,i)=>(mask&(1<<i))!==0;
const members=mask=>ids.filter(i=>contains(mask,i));

function minimumCover(mask){
  const target=edges.filter(([u,v])=>contains(mask,u)&&contains(mask,v));
  const index=new Map(target.flatMap(([u,v],i)=>[[n*u+v,i],[n*v+u,i]]));
  const bicliques=[];
  for(let x=mask;x;x=(x-1)&mask){
    const rest=mask^x;
    for(let y=rest;y;y=(y-1)&rest){
      if(y>x)continue;
      const left=members(x),right=members(y), pairs=left.flatMap(u=>right.map(v=>index.get(n*u+v)));
      if(pairs.some(i=>i===undefined))continue;
      bicliques.push({left,right,cost:left.length+right.length,
        hits:pairs.reduce((e,i)=>e|(1<<i),0)});
    }
  }
  const complete=(1<<target.length)-1;
  const cost=Array(complete+1).fill(Infinity), pick=[];
  cost[0]=0;
  for(let mask=1;mask<=complete;mask++){
    for(const q of bicliques){
      const uncovered=mask&~q.hits;
      if(uncovered===mask||cost[uncovered]+q.cost>=cost[mask])continue;
      cost[mask]=cost[uncovered]+q.cost;
      pick[mask]=q;
    }
  }
  const products=[];
  for(let mask=complete;mask;mask&=~pick[mask].hits){
    const {left,right}=pick[mask];
    products.push([left,right]);
  }
  for(let row=0;row<256;row++){
    const detects=target.some(([u,v])=>contains(row,u)&&contains(row,v));
    const covered=products.some(([a,b])=>a.some(u=>contains(row,u))&&b.some(v=>contains(row,v)));
    if(detects!==covered)throw Error("Coverage changed the edge predicate");
  }
  return {gates:cost[complete]-1,products};
}
const full=minimumCover(255);
const pins=ids.map(i=>minimumCover(255^(1<<i)));
const iso=[0,2,1,3,5,4,6,7];
const set=new Set(edges.flatMap(([a,b])=>[n*a+b,n*b+a]));
if(edges.some(([a,b])=>!set.has(n*iso[a]+iso[b]))||full.gates!==14||
    pins[1].gates!==12||pins[2].gates!==12)throw Error("Incorrect cofactor or symmetry");
console.log(JSON.stringify({full,pinCosts:pins.map(x=>x.gates),pin1:pins[1],iso}));
