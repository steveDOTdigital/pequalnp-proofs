const n = 13;
const fullBank = (1 << n) - 1;
const ids = Array.from({length:n}, (_, i) => i);
const bits = Array.from({length:fullBank + 1}, (_, m) => ids.filter(i => m & (1 << i)));
const lines = ids.map(l => [0,1,3,9].reduce((m,d) => m | (1 << ((l+d) % n)), 0));
const points = ids.map(p => lines.reduce((m,l,j) => m | (((l >> p) & 1) << j), 0));
const flags = lines.flatMap((m,l) => bits[m].map(p => (1 << p) | (1 << (l+n))));
const chosen = (m, list) => bits[m].reduce((z,i) => z | list[i], 0);
const isCap = (m,pencils) => pencils.every(p => bits[p & m].length <= 2);
const rows = [];
for(let q=0;q<=fullBank;q++){
  if(bits[q].length!==4) continue;
  if(isCap(q,lines)) rows.push(q | ((fullBank ^ chosen(q,points)) << n));
  if(isCap(q,points)) rows.push((fullBank ^ chosen(q,lines)) | (q << n));
}
if(rows.length!==468 || new Set(rows).size!==468 ||
  rows.some(row => flags.some(flag => (row & flag) === flag))) throw Error("Wrong posted negative set");

const posBits=(1n<<BigInt(flags.length))-1n;
const allRows=[...flags,...rows], full=(1n<<BigInt(allRows.length))-1n;
const basis=Array.from({length:26},(_,i)=>allRows.reduce((z,u,r)=>
  u&(1<<i)?z|(1n<<BigInt(r)):z,0n));
function count(v,stop=Infinity){
  let c=0;
  while(v&&c<=stop){c++;v&=v-1n;}
  return c;
}
let seed=0xf1d24ac5, probes=0, iterations=0;
function random(k){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%k;}
function tape(gs){
  const out=[...basis];
  for(const [and,a,b] of gs)out.push(and?(out[a]&out[b]):(out[a]|out[b]));
  return out;
}
function control(prefix){
  const gs=[];
  const put=(and,a,b)=>{gs.push([and,a,b]);return 25+gs.length;};
  const leaf=lines.map((l,i)=>{
    const [a,...rest]=bits[l];
    return put(true,rest.reduce((w,x)=>put(false,w,x),a),13+i);
  });
  leaf.slice(1).reduce((w,x)=>put(false,w,x),leaf[0]);
  if(gs.length!==64||gs[0][1]!==0||gs[0][2]!==1)throw Error("Bad star control");
  if(tape(gs).at(-1)!==posBits)throw Error("Exact posted rows fail");
}
function start(prefix,index){
  const same=prefix[0]===0&&prefix[1]===1;
  const gs=same?[]:[[false,...prefix]];
  const put=(and,a,b)=>{gs.push([and,a,b]);return 25+gs.length;};
  const omissions=new Set();
  while(omissions.size<(same?1:2)){
    const l=index===0?4+omissions.size:1+random(12);
    const p=index===0?0:random(4);
    omissions.add(4*l+p);
  }
  const stars=lines.map((l,i)=>{
    const [a,...rest]=bits[l].filter((_,p)=>!omissions.has(i*4+p));
    return put(true,rest.reduce((w,x)=>put(false,w,x),a),13+i);
  });
  stars.slice(1).reduce((w,x)=>put(false,w,x),stars[0]);
  if(gs.length!==63||gs[0][1]!==prefix[0]||gs[0][2]!==prefix[1])
    throw Error("Bad starting circuit");
  return gs;
}
function forced(gs,w,gate,value){
  const bound=26+gate, a=w.slice(0,bound);a.push(value);
  for(let t=gate+1;t<gs.length;t++){
    const [and,l,r]=gs[t];
    a.push(and?(a[l]&a[r]):(a[l]|a[r]));
  }
  return a.at(-1);
}
function bestSwap(gs,index,limit){
  const w=tape(gs), a=forced(gs,w,index,0n), b=forced(gs,w,index,full);
  const sensitivity=a^b;
  const fixed=count((a^posBits)&(full^sensitivity));
  if(fixed>limit)return;
  const target=posBits&sensitivity, bound=index+26;
  let best=limit+1, matches=0, move;
  const original=gs[index];
  for(let p=0;p<bound;p++)for(let q=p;q<bound;q++){
    const l=w[p], r=w[q];
    for(const and of [true,false]){
      if(and===original[0]&&p===Math.min(original[1],original[2])&&q===Math.max(original[1],original[2]))continue;
      probes++;
      const difference=(((and?l&r:l|r)&sensitivity)^target);
      const cost=fixed+count(difference,Math.min(best,limit)-fixed);
      if(cost>limit)continue;
      if(cost<best){best=cost;matches=0;}
      if(cost===best&&random(++matches)===0)move=[and,p,q];
    }
  }
  if(move)return {best,move};
}
function search(prefix,milliseconds){
  const expires=Date.now()+milliseconds;
  let best=Infinity, countStarts=0;
  while(Date.now()<expires){
    const g=start(prefix,countStarts++);
    let cost=count(tape(g).at(-1)^posBits);
    for(let j=0;j<220&&Date.now()<expires;j++){
      iterations++;
      if(cost<best){
        best=cost;
        console.log(JSON.stringify({event:"improved",prefix,cost,iterations,probes}));
      }
      if(cost===0){
        if(tape(g).at(-1)!==posBits)throw Error("Decoded false witness");
        return g;
      }
      const slot=1+random(g.length-1), give=(j%17===15?2:0), result=bestSwap(g,slot,cost+give);
      if(result){g[slot]=result.move;cost=result.best;}
      else if(j%37===31) {
        const bound=slot+26;
        const left=random(bound),right=random(bound);
        g[slot]=[random(2)!==0,Math.min(left,right),Math.max(left,right)];
        cost=count(tape(g).at(-1)^posBits);
      }
    }
  }
  console.log(JSON.stringify({event:"stopped",prefix,best,countStarts,iterations,probes}));
}
control();
const millis=Number(process.argv[2]||12000);
for(const prefix of [[0,1],[0,13],[0,14]]){
  const verified=search(prefix,millis);
  if(verified){console.log(JSON.stringify({event:"witness",prefix,verified,flags:flags.length,negatives:rows.length}));break;}
}
