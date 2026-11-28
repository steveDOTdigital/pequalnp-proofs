"use strict";
const n=8, all=(1n<<256n)-1n;
const edges=[[0,4],[1,4],[0,5],[2,5],[1,6],[2,6],[3,6],[0,7],[3,7],[4,7],[5,7],[6,7]];
const starts=[
 [["o",5,6],["o",2,7],["a",8,9],["o",4,6],["o",1,7],["a",11,12],["o",6,7],["a",3,14],
  ["o",4,5],["o",16,7],["a",0,17],["o",10,13],["o",15,18],["o",19,20]],
 [["o",0,7],["o",8,1],["a",9,4],["o",8,2],["a",11,5],
  ["o",1,2],["o",13,7],["o",14,3],["a",15,6],["o",0,3],["a",17,7],["o",10,12],["o",16,18],["o",19,20]]
];
const rows=Array.from({length:256},(_,i)=>i);
const mask=f=>rows.reduce((bits,r)=>f(r)?bits|(1n<<BigInt(r)):bits,0n);
const raw=Array.from({length:n},(_,i)=>mask(x=>(x&(1<<i))!==0));
const target=mask(x=>edges.some(([i,j])=>(x&(1<<i))&&(x&(1<<j))));
function evalPrefix(gates,old=raw){
  const w=[...old];
  for(let j=old.length-n;j<gates.length;j++){
    const [op,a,b]=gates[j],x=w[a],y=w[b];
    w.push(op==="a"?x&y:op==="o"?x|y:all^x);
  }
  return w;
}
function cut(gates,del,dest){
  const wire=del+n, route=i=>i===wire?dest:i>wire?i-1:i;
  return {gates:gates.filter((_,i)=>i!==del).map(([op,a,b])=>[op,route(a),route(b)]),
    out:route(n+gates.length-1)};
}
function test(c){return evalPrefix(c.gates)[c.out]===target;}
let bypasses=0, edits=0, notEdits=0, witness=null, signed=null;
outer:for(const [which,start] of starts.entries()){
  if(!test({gates:start,out:21}))throw Error("Invalid original control");
  for(let del=0;del<14;del++)for(let replacement=0;replacement<n+del;replacement++){
    const c=cut(start,del,replacement);
    bypasses++;
    const w=evalPrefix(c.gates);
    if(w[c.out]===target){witness={which,del,replacement,c};break outer;}
    for(let j=0;j<c.gates.length;j++){
      const fixed=[...c.gates],prefix=w.slice(0,n+j);
      for(let a=0;a<n+j;a++){
        notEdits++;
        fixed[j]=["n",a,a];
        if(!signed&&evalPrefix(fixed,prefix)[c.out]===target)
          signed={which,del,replacement,j,gate:fixed[j],c:{gates:[...fixed],out:c.out}};
        for(let b=a;b<n+j;b++)for(const op of ["a","o"]){
          edits++;
          fixed[j]=[op,a,b];
          if(evalPrefix(fixed,prefix)[c.out]===target){
            witness={which,del,replacement,j,gate:fixed[j],c:{gates:fixed,out:c.out}};
            break outer;
          }
        }
      }
    }
  }
}
if(witness&&!test(witness.c)||signed&&!test(signed.c))throw Error("Witness failed replay");
console.log(JSON.stringify({bypasses,edits,notEdits,witness,signed}));
