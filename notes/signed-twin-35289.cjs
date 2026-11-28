"use strict";

const dim=7;
const goal=0xfffffffeffffffeefefefefcfefaee00n;

const rows=n=>2**n;
const full=n=>(1n<<BigInt(rows(n)))-1n;
const coordinate=(n,i)=>{
  let w=0n;
  for(let r=0;r<rows(n);r++)if(r&(1<<i))w|=1n<<BigInt(r);
  return w;
};
const orient=(w,n)=>(w&1n)?w^full(n):w;
const literals=Array.from({length:8},(_,n)=>Array.from({length:n},(_,i)=>coordinate(n,i)));
const targetKey=(n,t)=>n+":"+orient(t,n).toString(16);
const basic=Array.from({length:8},(_,n)=>{
  const r=literals[n], q=new Map([[0n,0]]);
  for(const x of r)q.set(x,1);
  let tag=2;
  for(let i=0;i<n;i++)for(let j=0;j<i;j++){
    const [a,b]=[r[i],r[j]],m=full(n);
    for(const w of [a&b,a|b,a&(m^b),(m^a)&b]){
      if(!q.has(w))q.set(w,tag++);
    }
  }
  return q;
});

function active(n,w){
  const r=[];
  for(let i=0;i<n;i++){
    const step=BigInt(1<<i), zero=full(n)^literals[n][i];
    if(((w&zero)<<step)!==(w&literals[n][i]))r.push(i);
  }
  return r;
}
function restrictMap(n,fix1,fix2,polarity){
  const uses=Array.from({length:n},(_,i)=>i).filter(i=>i!==fix1);
  return Array.from({length:rows(n-1)},(_,r)=>{
    let out=uses.reduce((w,i,j)=>w|((r&(1<<j))?1<<i:0),0);
    if(fix2===-1?polarity:((Boolean(out&(1<<fix2)))!==polarity))out|=1<<fix1;
    return out;
  });
}
function across(word,map){
  let w=0n;
  for(let j=0;j<map.length;j++)if(word&(1n<<BigInt(map[j])))w|=1n<<BigInt(j);
  return w;
}
function minors(n,t,pairs=true){
  if(n<2)return [];
  const list=[], maps=new Set();
  const add=map=>{
    const k=map.join(",");
    if(maps.has(k))return;
    maps.add(k);
    const target=orient(across(t,map),n-1);
    if(target)list.push({n:n-1,target,map});
  };
  for(let i=0;i<n;i++){
    add(restrictMap(n,i,-1,false));
    add(restrictMap(n,i,-1,true));
  }
  if(pairs)for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
    add(restrictMap(n,i,j,false));
    add(restrictMap(n,i,j,true));
  }
  return list;
}
function compact(n,t){
  const a=active(n,t);
  if(a.length===n)return {n,t:orient(t,n)};
  const map=Array.from({length:rows(a.length)},(_,r)=>a.reduce((v,i,j)=>v|((r&(1<<j))?1<<i:0),0));
  return {n:a.length,t:orient(across(t,map),a.length)};
}

const allStats={complete:0,bounded:0,states:0,visits:0,cuts:0};

function compileProjection(map){
  const bases=new Map();
  for(let j=0;j<map.length;j++){
    const src=map[j], byte=Math.floor(src/8);
    if(!bases.has(byte))bases.set(byte,Array(8).fill(0n));
    bases.get(byte)[src%8]|=1n<<BigInt(j);
  }
  return Array.from(bases,([byte,groups])=>{
    const values=Array(256).fill(0n);
    for(let i=1;i<values.length;i++){
      const low=i&-i, bit=31-Math.clz32(low);
      values[i]=values[i^low]|groups[bit];
    }
    return {shift:BigInt(byte*8),values};
  });
}
function packedAcross(word,tables){
  let out=0n;
  for(const t of tables)out|=t.values[Number((word>>t.shift)&255n)];
  return out;
}
for(const n of [5,6,7]){
  const m=full(n), seeds=[1n,m,m/3n,literals[n][n-1],m^literals[n][1]];
  for(let i=0;i<n;i++)for(let j=-1;j<n;j++)if(j!==i){
    const map=restrictMap(n,i,j,false), fast=compileProjection(map);
    for(const w of seeds)if(packedAcross(w,fast)!==across(w,map))
      throw new Error("Packed projection regression");
  }
}
console.log(JSON.stringify({stage:"projection-checks",result:"pass"}));
function search(n,target,budget,minorCuts,deadline,cap){
  const mask=full(n), root=active(n,target).map(i=>literals[n][i]);
  const neg=[];
  for(let r=0;r<rows(n);r++)if(!(target&(1n<<BigInt(r))))neg.push(1n<<BigInt(r));
  const pos=target, shifts=neg.map((_,i)=>BigInt(i*rows(n)));
  const lex=(a,b)=>a.id-b.id;
  const memo=Array.from({length:budget+1},()=>new Set());
  const wires=new Map();
  let count=0,visits=0,cuts=0,result="unsat",witness;
  const path=[];
  const rules=minorCuts.filter(c=>c.bound>0).sort((a,b)=>b.bound-a.bound)
    .map(c=>({...c,single:basic[c.n],projection:null,cache:new Map()}));
  function signal(w){
    let a=wires.get(w);
    if(!a){a={w,id:wires.size,equal:undefined};wires.set(w,a);}
    return a;
  }
  function agreement(a){
    if(a.equal!==undefined)return a.equal;
    const pos1=pos&a.w,pos0=pos^pos1;
    let word=0n;
    for(let i=0;i<neg.length;i++)word|=((a.w&neg[i])?pos1:pos0)<<shifts[i];
    a.equal=word;
    return word;
  }
  function separates(set){
    if(set.length===0)return !target;
    let bad=agreement(set[0]);
    for(let j=1;j<set.length&&bad;j++)bad&=agreement(set[j]);
    return bad===0n;
  }
  function terminalCut(k,set){
    for(const m of rules){
      if(k>=m.bound+set.length)continue;
      const bought=new Set();
      let zero=0,ok=true;
      for(const a of set){
        let d=m.cache.get(a.w);
        if(d===undefined){
          m.projection??=compileProjection(m.map);
          d=m.single.get(orient(packedAcross(a.w,m.projection),m.n))??-1;
          if(m.cache.size<15000)m.cache.set(a.w,d);
        }
        if(d<0){ok=false;break;}
        if(d===0)zero++;
        if(d>1)bought.add(d);
      }
      if(ok&&k+bought.size<m.bound+zero){cuts++;return true;}
    }
    return false;
  }
  function run(k,ls,known=false){
    if(k<=0||ls.length<2||ls.length>k+1)return false;
    if((++visits&2047)===0&&(Date.now()>deadline||count>=cap||wires.size>300000)){
      result="bounded";return true;
    }
    if(k>1){
      ls.sort(lex);
      const key=ls.map(a=>a.id).join(".");
      if(memo[k].has(key))return false;
      if(memo[k].size<240000)memo[k].add(key);
      if(!known&&!separates(ls))return false;
      if(terminalCut(k,ls))return false;
      count++;
    }
    for(let i=0;i<ls.length;i++)for(let j=i+1;j<ls.length;j++){
      const a=ls[i].w,b=ls[j].w;
      const options=[a&b,a|b,a&(mask^b),(mask^a)&b];
      for(let label=0;label<4;label++){
        const w=options[label];
        if(w===target){
          result="sat";witness=[...path,[a,b,w,label]];return true;
        }
        if(k===1||!w||options.indexOf(w)!==label||ls.some(x=>x.w===w))continue;
        const item=signal(w);
        path.push([a,b,w,label]);
        for(let keep=0;keep<4;keep++){
          const length=ls.length-1+((keep&1)?1:0)+((keep&2)?1:0);
          if(length>k)continue;
          const next=ls.filter((_,h)=>(h!==i||keep&1)&&(h!==j||keep&2));
          next.push(item);
          if(run(k-1,next,keep===3))return true;
        }
        path.pop();
      }
    }
    return false;
  }
  if(!target||root.includes(target)){result="sat";witness=[];}else
    run(budget,root.map(signal),true);
  if(result==="bounded")allStats.bounded++;else allStats.complete++;
  allStats.states+=count;allStats.visits+=visits;allStats.cuts+=cuts;
  return {result,count,visits,cuts,witness:witness?.map(a=>a.map(x=>typeof x==="bigint"?x.toString(16):x))};
}

const memo=new Map();
function lower(n,t,limit,span,over,cutList=[]){
  const c=compact(n,t);
  if(c.n!==n&&!cutList.length)return lower(c.n,c.t,limit,span,over);
  const tt=orient(t,n), key=targetKey(n,tt);
  let v=memo.get(key)??{lower:Math.max(0,c.n-1),upper:Infinity};
  const end=Math.min(Date.now()+span,over);
  while(Date.now()<end&&v.lower<limit&&v.lower<v.upper){
    const run=search(n,tt,v.lower,cutList,end,n<6?75000:140000);
    if(run.result==="unsat"){v.lower++;continue;}
    if(run.result==="sat"){v.upper=v.lower;break;}
    break;
  }
  memo.set(key,v);
  return v.lower;
}

const limit=Date.now()+210000;
const levelSix=minors(dim,goal,true), sixKeys=new Set(levelSix.map(x=>targetKey(x.n,x.target)));
const levelFive=new Map();
for(const c of levelSix)for(const d of minors(c.n,c.target,false))
  levelFive.set(targetKey(d.n,d.target),d);
for(const m of minors(dim,goal,false))for(const p of minors(m.n,m.target,false)){
  const map=p.map.map(i=>m.map[i]);
  levelSix.push({...p,map});
}
for(const d of levelFive.values()){
  if(Date.now()>limit-70000)break;
  lower(d.n,d.target,7,190,limit-70000);
}
const sliceStats=[];
const doneSix=new Set();
for(const c of levelSix){
  const key=targetKey(c.n,c.target);
  if(doneSix.has(key))continue;
  doneSix.add(key);
  const child=minors(c.n,c.target,false).map(x=>({...x,bound:
    memo.get(targetKey(x.n,x.target))?.lower??Math.max(0,active(x.n,x.target).length-1)
  }));
  const bound=lower(c.n,c.target,c.n===6?10:7,620,limit-65000,child);
  sliceStats.push({key,bound});
}
const usable=levelSix.map(c=>({...c,bound:memo.get(targetKey(c.n,c.target))?.lower??
  Math.max(0,active(c.n,c.target).length-1)}));
console.log(JSON.stringify({stage:"minor-bounds",minorSix:sixKeys.size,tables:doneSix.size,
  histogram:sliceStats.reduce((s,m)=>(s[m.bound]=(s[m.bound]??0)+1,s),{}),work:allStats}));
const budget=Number(process.argv[2]??11);
console.log(JSON.stringify({stage:"seven-input",budget,...search(dim,goal,budget,usable,limit,360000),work:allStats}));
