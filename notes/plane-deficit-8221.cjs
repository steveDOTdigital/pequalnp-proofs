const {performance}=require("node:perf_hooks");
const bank=13, all=(1<<bank)-1;
const ids=Array.from({length:bank},(_,i)=>i);
const bits=Array.from({length:all+1},(_,m)=>ids.filter(i=>m&(1<<i)));
const pencils=ids.map(p=>[0,1,3,9].reduce((m,d)=>m|1<<((p-d+bank)%bank),0));
const cap=m=>pencils.every(r=>bits[m&r].length<=2);
const quad=bits.flatMap((r,m)=>r.length===4&&cap(m)?[m]:[]);
const pair=bits.flatMap((r,m)=>r.length===2?[m]:[]);
const conflict=quad.map((m,i)=>quad.flatMap((n,j)=>i!==j&&bits[m&n].length===3?[j]:[]));

const optionsByPair=pair.map(p=>{
  const q=quad.flatMap((m,i)=>(m&p)===p?[i]:[]);
  if(q.length!==18)throw Error("Unexpected pair incidence");
  const options=Array.from({length:5},()=>[]);
  function fill(from, positions, mask) {
    options[positions.length].push(mask);
    if(positions.length===4)return;
    for(let i=from;i<q.length;i++)
      if(positions.every(j=>!conflict[q[i]].includes(q[j])))
        fill(i+1,[...positions,i],mask|(1<<i));
  }
  fill(0,[],0);
  return options.map(o=>({q,options:o}));
});
let domains;

function choose(state,q,truth) {
  if(state[q]===-truth)return false;
  if(state[q]===truth)return true;
  state[q]=truth;
  if(truth===1)for(const p of conflict[q]){
    if(state[p]===1)return false;
    state[p]=-1;
  }
  return true;
}
let visits=0,maxDepth=0,contradictions=0;
let started=performance.now();
const budget=Number(process.argv[2]||15000);
function close(state, depth) {
  visits++;
  maxDepth=Math.max(depth,maxDepth);
  if((visits&255)===0&&performance.now()-started>budget)throw Error("search budget");
  let changed=true, branch, score;
  while(changed){
    changed=false;
    branch=undefined;
    score=Infinity;
    for(const {q,options} of domains){
      let yes=0,no=0;
      for(let i=0;i<q.length;i++){
        if(state[q[i]]===1)yes|=1<<i;
        else if(state[q[i]]===-1)no|=1<<i;
      }
      let meet=(1<<q.length)-1, join=0;
      const possible=[];
      for(const t of options)if((t&yes)===yes&&!(t&no)){
        meet&=t;
        join|=t;
        possible.push(t);
      }
      if(!possible.length){contradictions++;return null;}
      for(let i=0;i<q.length;i++)if(!state[q[i]]){
        const flag=1<<i;
        const value=meet&flag?1:join&flag?0:-1;
        if(!value)continue;
        if(!choose(state,q[i],value)){contradictions++;return null;}
        changed=true;
      }
      if(possible.length>1&&possible.length<score){
        score=possible.length;
        let best=Infinity;
        for(let i=0;i<q.length;i++)if(!state[q[i]]){
          const count=possible.reduce((n,m)=>n+((m>>i)&1),0);
          if(!count||count===possible.length)continue;
          const distance=Math.abs(count*2-possible.length);
          if(distance<best){best=distance;branch=q[i];}
        }
      }
    }
  }
  if(branch===undefined){
    const selected=quad.filter((_,q)=>state[q]===1);
    if(selected.length!==51)throw Error("Unexpected terminal state "+selected.length);
    return selected;
  }
  for(const status of [1,-1]){
    const next=state.slice();
    if(choose(next,branch,status)){
      const solved=close(next,depth+1);
      if(solved)return solved;
    }
  }
  return null;
}


// The two sides below are lines and their pencil centers. Joins and meets
// generate the remaining labels from a projective frame.
const neighborhoods=[ids.map(l=>pencils.reduce((m,P,p)=>m|((P>>l&1)<<p),0)),pencils];
const pairs=(xs)=>xs.flatMap((a,i)=>xs.slice(i+1).map(b=>[a,b]));
const join=neighborhoods.map(rows=>rows.map(A=>rows.map(B=>31-Math.clz32(A&B))));
const frames=[];
for(const m of quad){
  const place=[];
  function permutations(todo) {
    if(!todo.length){frames.push([...place]);return;}
    for(let i=0;i<todo.length;i++){
      place.push(todo[i]);
      permutations(todo.filter((_,j)=>i!==j));
      place.pop();
    }
  }
  permutations(bits[m]);
}
const base=frames[0], closure=[new Set(base),new Set()], recipe=[];
while(closure[0].size+closure[1].size<26){
  const old=recipe.length;
  for(let bank=0;bank<2;bank++)for(const [a,b] of pairs([...closure[bank]])){
    const pos=join[bank][a][b];
    if(closure[1-bank].has(pos))continue;
    closure[1-bank].add(pos);
    recipe.push([bank,a,b,pos]);
  }
  if(old===recipe.length)throw Error("Frame closure stalled");
}
const group=frames.map(f=>{
  const map=[[],[]];
  base.forEach((v,i)=>map[0][v]=f[i]);
  for(const [bank,a,b,pos] of recipe)map[1-bank][pos]=join[bank][map[bank][a]][map[bank][b]];
  if(map.some(m=>m.length!==13||new Set(m).size!==13))throw Error("Invalid permutation");
  if(pencils.some((m,i)=>bits[m].reduce((s,j)=>s|(1<<map[0][j]),0)!==pencils[map[1][i]]))
    throw Error("Invalid incidence map");
  return map[0];
});
if(new Set(group.map(g=>g.join(","))).size!==5616)throw Error("Group completeness count");
const asPair=(a,b)=>(1<<a)|(1<<b);
const patterns=new Map();
const key=pat=>pat.map(([p,w])=>p*8+w).sort((a,b)=>a-b).join(",");
function keep(pat){patterns.set(key(pat),pat);}
function triple(vs){
  for(const a of vs)keep(vs.filter(b=>a!==b).map(b=>[asPair(a,b),3]));
}
function four([a,b,c,d]){
  const match=[[asPair(a,b),asPair(c,d)],[asPair(a,c),asPair(b,d)],[asPair(a,d),asPair(b,c)]];
  for(const pc of [[3,0,0],[0,3,0],[0,0,3],[2,1,0],[2,0,1],[1,2,0],
    [0,2,1],[1,0,2],[0,1,2],[1,1,1]]){
    keep(match.flatMap((m,i)=>pc[i]?m.map(z=>[z,pc[i]]):[]));
  }
}
for(const row of bits){
  if(row.length===3)triple(row);
  if(row.length===4)four(row);
}
if(patterns.size!==8008)throw Error("Pattern enumeration");
const roots=[];
const pending=new Set(patterns.keys());
while(pending.size){
  const pick=pending.values().next().value;
  const pat=patterns.get(pick);
  let num=0;
  for(const map of group){
    const rep=key(pat.map(([p,w])=>[bits[p].reduce((m,i)=>m|(1<<map[i]),0),w]));
    if(!patterns.has(rep))throw Error("Orbit escaped the family");
    if(pending.delete(rep))num++;
  }
  if(!num)throw Error("Empty orbit");
  roots.push({pat,num});
}
console.log(JSON.stringify({event:"orbits",patterns:patterns.size,orbits:roots.length,counts:roots.map(x=>x.num)}));
let unresolved=0;
for(const {pat,num} of roots){
  const deficit=new Map(pat);
  domains=pair.map((p,i)=>optionsByPair[i][4-(deficit.get(p)||0)]);
  started=performance.now();
  visits=0;maxDepth=0;contradictions=0;
  try {
    const sol=close(new Int8Array(quad.length),0);
    if(sol){
      if(sol.some(q=>!quad.includes(q))||new Set(sol).size!==51)throw Error("Bad packing");
      for(const p of pair)if(sol.filter(q=>(q&p)===p).length!==4-(deficit.get(p)||0))
        throw Error("Incorrect pair loading");
      for(let i=0;i<sol.length;i++)for(let j=0;j<i;j++)
        if(bits[sol[i]&sol[j]].length>2)throw Error("Shared triangle");
      console.log(JSON.stringify({event:"sat",pat,num,visits,sol}));
      process.exit(0);
    }
    console.log(JSON.stringify({event:"unsat_case",pat,num,visits,maxDepth}));
  } catch(e){
    if(e.message!=="search budget")throw e;
    unresolved++;
    console.log(JSON.stringify({event:"timeout",pat,num,visits,maxDepth}));
  }
}
console.log(JSON.stringify({event:unresolved?"incomplete":"unsat",goal:51,unresolved}));
