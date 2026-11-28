"use strict";
const n=13, all=(1<<n)-1;
const ids=Array.from({length:n},(_,i)=>i);
const count=Array.from({length:all+1},(_,i)=>ids.filter(j=>i&(1<<j)).length);
const lines=ids.map(l=>[0,1,3,9].reduce((m,d)=>m|(1<<((l+d)%n)),0));
if(lines.some((a,i)=>lines.some((b,j)=>i<j&&count[a&b]!==1)))throw Error("Not a plane");
let max=0,profiles={},witnessCount=0;
for(let point=1;point<=all;point++){
  const misses=lines.reduce((m,l,i)=>m|((point&l?0:1)<<i),0);
  if(!misses)continue;
  const a=count[point], b=count[misses], total=a+b;
  if(total>max){max=total;profiles={};witnessCount=0;}
  if(total===max){
    profiles[a+","+b]=(profiles[a+","+b]??0)+1;
    witnessCount++;
  }
}
if(max!==10||Object.keys(profiles).length!==2||profiles["1,9"]!==13||profiles["9,1"]!==13)
  throw Error("Wrong mixed independent-set classification");
console.log(JSON.stringify({mixedIndependentMaximum:max,profiles,witnessCount,minCoverWithoutFullShore:2*n-max}));
