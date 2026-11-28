"use strict";

const dim=8;
const goal=0xfffffffffffffffefffffffffffffefefffffffeffffffeefffefffeeeccaa00n;

const rows=n=>2**n;
const full=n=>(1n<<BigInt(rows(n)))-1n;
const coordinate=(n,i)=>{
  let w=0n;
  for(let r=0;r<rows(n);r++)if(r&(1<<i))w|=1n<<BigInt(r);
  return w;
};
const orient=(w,n)=>(w&1n)?w^full(n):w;
const literals=Array.from({length:9},(_,n)=>Array.from({length:n},(_,i)=>coordinate(n,i)));
const targetKey=(n,t)=>n+":"+orient(t,n).toString(16);
const basic=Array.from({length:9},(_,n)=>{
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

function maskedPatterns(map,n){
  const lane=map.map(row=>1n<<BigInt(row));
  const mask=lane.reduce((all,bit)=>all|bit,0n);
  const words=new Map();
  for(const [w,tag] of basic[n]){
    let lifted=0n;
    for(let j=0;j<lane.length;j++)if(w&(1n<<BigInt(j)))lifted|=lane[j];
    if(words.has(lifted))throw new Error("A restriction did not embed the projected rows");
    words.set(lifted,tag);
  }
  return {anchor:lane[0],mask,words};
}
function maskedClass(w,restriction){
  const masked=w&restriction.mask;
  return restriction.words.get((w&restriction.anchor)?masked^restriction.mask:masked)??-1;
}


const formulaChecks = new Map();

function readOnceLibrary(n){
  if(formulaChecks.has(n))return formulaChecks.get(n);
  const ops=1<<n, mask=full(n), forms=Array(ops);
  for(let i=0;i<n;i++)forms[1<<i]=new Set([literals[n][i]]);
  for(let s=1;s<ops;s++){
    if(forms[s])continue;
    const table=new Set();
    for(let a=(s-1)&s;a;a=(a-1)&s){
      const b=s^a;
      if(a>b)continue;
      for(const x of forms[a])for(const y of forms[b]){
        table.add(x&y);
        table.add(x|y);
        table.add(x&(mask^y));
        table.add((mask^x)&y);
      }
    }
    forms[s]=table;
  }
  const all=[...forms[ops-1]];
  const chunks=Math.ceil(all.length/32);
  const positives=Array.from({length:ops},()=>new Uint32Array(chunks));
  for(let i=0;i<all.length;i++)for(let row=0;row<ops;row++){
    if(all[i]&(1n<<BigInt(row)))positives[row][i>>>5]|=1<<(i&31);
  }
  const total=(1n<<BigInt(all.length))-1n;
  const yes=positives.map(words=>BigInt("0x"+Array.from(words).reverse().map(w=>w.toString(16).padStart(8,"0")).join("")));
  const result={yes,no:yes.map(w=>total^w),total,size:all.length};
  formulaChecks.set(n,result);
  return result;
}


function oneNotSearch(n,target,budget,force,deadline,maxStates,absorb=[],reflection=null,sourceCase=null){
  const mask=full(n), vars=literals[n], rawSet=new Set(vars);
  const constr=force.map(i=>{
    const v=vars[i], zero=mask^v, shift=BigInt(1<<i);
    return {v,zero,shift,diff:(target&zero)^((target&v)>>shift),
      raw:new Set(vars.map(w=>w&zero))};
  });
  const monotoneTarget=vars.every(v=>{
    const off=mask^v;
    let i=vars.indexOf(v);
    return (((target&off)<<BigInt(1<<i))&(mask^target))===0n;
  });
  const exposures=new Map(absorb.map(([q,z])=>{
    let quiet=0n;
    const p=1<<q, t=1<<z, on=r=>Boolean(target&(1n<<BigInt(r)));
    for(let r=0;r<rows(n);r++)
      if(!(r&(p|t))&&!on(r)&&!on(r|p)&&!on(r|t)&&on(r|p|t))quiet|=1n<<BigInt(r);
    if(!quiet)throw Error("The exposure cannot be empty");
    return [vars[q],{z,quiet,shift:BigInt(t)}];
  }));
  const requiredSources=[...exposures.values()];
  const smallSourceAnd=n===8?vars[3]&vars[4]:0n;
  const smallSourceOr=n===8?vars[3]|vars[4]:0n;
  function quietFall(w,p){return (w & p.quiet & ~(w>>p.shift))!==0n;}
  function quietRise(w,p){return ((mask^w) & p.quiet & (w>>p.shift))!==0n;}
  function sourceAllowed(w){
    return (w&(mask^target))!==0n && (target&(mask^w))!==0n
      && requiredSources.every(p=>quietRise(w,p));
  }
  const rowsReflection=reflection?compileProjection(reflection):null;
  const reflectionCache=new Map();
  const allNeg=Array.from({length:rows(n)},(_,i)=>1n<<BigInt(i))
    .filter(w=>!(w&target));
  const memo=Array.from({length:2},()=>Array.from({length:budget+1},()=>new Set()));
  const wires=new Map(), path=[];
  let states=0,visits=0,pruned=0,notStates=0,verdict="unsat",witness=[];
  function get(w){
    if(!wires.has(w))wires.set(w,{w,c:orient(w,n),id:wires.size,sim:null});
    return wires.get(w);
  }
  function agrees(o){
    if(o.sim!==null)return o.sim;
    const on=o.w&target,off=on^target;
    let value=0n;
    for(let i=0;i<allNeg.length;i++){
      const pos=o.w&allNeg[i]?on:off;
      value|=pos<<BigInt(i*rows(n));
    }
    o.sim=value; return value;
  }
  function separate(s){
    if(!s.length)return false;
    let a=agrees(s[0]);
    for(let i=1;i<s.length&&a;i++)a&=agrees(s[i]);
    return a===0n;
  }
  function found(){
    verdict="sat";
    witness=path.map(({op,a,b,out})=>({op,a:a.toString(16),
      b:b?.toString(16),out:out.toString(16)}));
    return true;
  }
  function visit(k,notUnused,set,ready=false){
    if(set.some(v=>v.w===target))return found();
    if(!set.length||set.length>k+1||(!k&&!notUnused))return false;
    if((++visits&2047)===0&&(Date.now()>deadline||states>=maxStates||wires.size>=350000)){
      verdict="bounded";return true;
    }
    set.sort((a,b)=>a.id-b.id);
    const table=memo[notUnused?1:0][k];
    let sig="";
    for(const v of set)sig+=String.fromCharCode(v.id&65535,v.id>>>16);
    if(rowsReflection){
      const image=set.map(v=>{
        if(!reflectionCache.has(v.w)){
          const other=get(packedAcross(v.w,rowsReflection));
          reflectionCache.set(v.w,other);reflectionCache.set(other.w,v);
        }
        return reflectionCache.get(v.w);
      }).sort((a,b)=>a.id-b.id);
      let other="";
      for(const v of image)other+=String.fromCharCode(v.id&65535,v.id>>>16);
      if(other<sig)sig=other;
    }
    if(table.has(sig))return false;
    if(table.size<220000)table.add(sig);
    if(!ready&&!separate(set))return false;
    states++;
    if(notUnused){
      for(let i=0;i<set.length;i++){
        const v=set[i], w=v.w^mask;
        if(!sourceAllowed(v.w)||(sourceCase==="other"&&(v.w===smallSourceAnd||v.w===smallSourceOr)))continue;
        const rawInput=monotoneTarget&&rawSet.has(v.w);
        if(rawInput&&constr.some(p=>p.v===v.w))continue;
        if(set.some(x=>x.w===w))continue;
        const item=get(w);
        path.push({op:"not",a:v.w,out:w});
        notStates++;
        if(!rawInput&&visit(k,false,[...set.slice(0,i),...set.slice(i+1),item],true))return true;
        if(set.length<k+1&&visit(k,false,[...set,item],true))return true;
        path.pop();
      }
    }
    if(!k||set.length<2)return false;
    for(let i=0;i<set.length;i++)for(let j=i+1;j<set.length;j++){
      const a=set[i], b=set[j], both=a.w&b.w, either=a.w|b.w;
      for(const [op,w] of [["and",both],["or",either]]){
        const witnessA=exposures.get(a.c), witnessB=exposures.get(b.c);
        if(witnessA!==undefined&&(notUnused||a.w!==a.c||op!=="or"||!quietFall(b.w,witnessA)))continue;
        if(witnessB!==undefined&&(notUnused||b.w!==b.c||op!=="or"||!quietFall(a.w,witnessB)))continue;
        if(w===target){path.push({op,a:a.w,b:b.w,out:w});return found();}
        if(!w||w===mask||rawSet.has(w)||set.some(v=>v.w===w))continue;
        const c=orient(w,n), eliminate=[];
        let legal=true;
        for(const p of constr){
          const v=c&p.zero;
          if(a.c===p.v||b.c===p.v){
            const dif=v^((c&p.v)>>p.shift);
            if(!v||v===p.zero||(p.diff&dif)!==p.diff){legal=false;break;}
            eliminate.push(p.v);
          }else if(p.raw.has(v)||set.some(s=>(s.c&p.zero)===v)){legal=false;break;}
        }
        if(!legal){pruned++;continue;}
        const fresh=get(w);
        path.push({op,a:a.w,b:b.w,out:w});
        for(let keep=0;keep<4;keep++){
          if(((keep&1)&&eliminate.includes(a.c))||((keep&2)&&eliminate.includes(b.c)))continue;
          const after=set.filter((v,h)=>!eliminate.includes(v.c)
            &&(h!==i||keep&1)&&(h!==j||keep&2));
          after.push(fresh);
          if(visit(k-1,notUnused,after,keep===3&&!eliminate.length))return true;
        }
        path.pop();
      }
    }
    return false;
  }
  if(target===0n||target===mask||rawSet.has(target))verdict="sat";
  else if(sourceCase==="and"||sourceCase==="or"){
    const h=sourceCase==="and"?smallSourceAnd:smallSourceOr;
    if(sourceAllowed(h)){
      const root=active(n,target).map(i=>get(vars[i]));
      const complement=get(mask^h);
      path.push({op:sourceCase,a:vars[3],b:vars[4],out:h},{op:"not",a:h,out:complement.w});
      if(!visit(budget-1,false,[...root,complement],true))
        visit(budget-1,false,[...root,get(h),complement],true);
    }
  }else visit(budget,true,active(n,target).map(i=>get(vars[i])),true);
  return {verdict,states,visits,pruned,notStates,signals:wires.size,witness};
}

const graph=[[0,3],[1,4],[0,5],[1,5],[2,5],[3,5],[0,6],[1,6],[3,6],[4,6],[0,7],[1,7],[2,7],[4,7],[5,7]];
const reflection=[1,0,2,4,3,7,6,5];
const rowsSym=Array.from({length:256},(_,row)=>reflection.reduce((s,i,j)=>s|((row>>j&1)<<i),0));
if(across(goal,rowsSym)!==goal||rowsSym.some((x,i)=>rowsSym[x]!==i))throw Error("Bad graph reflection");
const adjacency=(u,v)=>graph.some(([i,j])=>(u===i&&v===j)||(u===j&&v===i));
const pairs=[[0,3],[1,4]];
for(const [p,z] of pairs)
  if(!adjacency(p,z)||Array.from({length:8},(_,i)=>i).some(t=>adjacency(z,t)&&t!==p&&!adjacency(p,t)))
    throw Error("Bad dominated neighbor");
for(const [p,z] of pairs){
  const bp=1<<p, bz=1<<z;
  for(let r=0;r<256;r++)if(!(r&bp)&&!(goal&(1n<<BigInt(r)))&&!(goal&(1n<<BigInt(r|bp))))
    if((goal&(1n<<BigInt(r|bz)))||!(goal&(1n<<BigInt(r|bz|bp))))throw Error("Exposure row failed");
}
console.log(JSON.stringify({stage:"one-NOT-exposure",pairs,reflection,forced:[0,1,2]}));

for(const [source,span] of [["and",50000],["or",50000],["other",138000]]){
  const result=oneNotSearch(dim,goal,13,[0,1,2],Date.now()+span,320000,pairs,rowsSym,source);
  console.log(JSON.stringify({stage:"quiet-source-case",source,budget:13,...result}));
  if(result.verdict==="sat")break;
}
