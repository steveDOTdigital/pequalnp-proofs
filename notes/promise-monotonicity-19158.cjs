/* Emit the unresolved four-by-four synthesis checks with --cases.
   Masks use row-major order, as in the project evaluator. */
function rawTables(n) {
  return Array.from({length:2*n}, (_, q) => {
    let t=0;
    for (let i=0;i<n;i++) for (let j=0;j<n;j++)
      if (q===i || q===n+j) t |= 1<<(n*i+j);
    return t;
  });
}

function formulaCosts(n, allowNot, extra=[]) {
  const full=(1<<(n*n))-1, levels=[[...new Set([0,...rawTables(n),...extra])]];
  const cost=new Int8Array(full+1).fill(-1);
  for (const t of levels[0]) cost[t]=0;
  for (let k=1; ;k++) {
    const next=[];
    function add(t) { if (cost[t]<0) {cost[t]=k;next.push(t);} }
    if (k===1) add(full); // Empty AND.
    if (allowNot) for (const a of levels[k-1]) add(full^a);
    for (let i=0;2*i<k;i++)
      for (const a of levels[i]) for (const b of levels[k-1-i]) {add(a&b);add(a|b);}
    levels.push(next);
    if (cost.every(v=>v>=0)) return cost;
    if (!next.length) throw Error("Unexpected gap before full coverage");
  }
}

function permutations(xs) {
  return xs.length ? xs.flatMap(x=>permutations(xs.filter(y=>x!==y)).map(p=>[x,...p])) : [[]];
}

function orbits(n) {
  const perm=permutations(Array.from({length:n},(_,i)=>i)), maps=[];
  for (const p of perm) for (const q of perm) for (const tr of [false,true])
    maps.push(Array.from({length:n*n},(_,k)=>{
      const i=p[Math.floor(k/n)], j=q[k%n];
      return 1<<(tr ? n*j+i : n*i+j);
    }));
  const seen=new Uint8Array(1<<(n*n)), groups=[];
  for (let t=0;t<seen.length;t++) if (!seen[t]) {
    const group=new Set();
    for (const map of maps) {
      let u=0;for(let k=0;k<map.length;k++) if(t>>k&1)u|=map[k];
      group.add(u);seen[u]=1;
    }
    groups.push([...group]);
  }
  return groups;
}

function rawLower(t,n) {
  const rows=Array(n).fill(0), cols=Array(n).fill(0);
  for (let i=0;i<n;i++) for (let j=0;j<n;j++) if(t>>(n*i+j)&1) {
    rows[i]|=1<<j;cols[j]|=1<<i;
  }
  function maximumMultiplicity(a) {return Math.max(...a.map(x=>a.filter(y=>x===y).length));}
  return 2*n-maximumMultiplicity(rows)-maximumMultiplicity(cols);
}

function checkThree() {
  const raw=rawTables(3), upper=formulaCosts(3,false);
  for(const t of [238,245,350,371,413,427]) upper[t]=7; // Three-label inequality.
  if(Math.max(...upper)!==7)throw Error("Three-label upper bound");
  let states=[[]], reached=new Set([0,511,...raw]);
  for(let k=1;k<=5;k++) {
    const next=new Map();
    for(const list of states) {
      const wires=raw.concat(list), values=new Set();
      for(let i=0;i<wires.length;i++) {
        values.add(511^wires[i]);
        for(let j=0;j<i;j++){values.add(wires[i]&wires[j]);values.add(wires[i]|wires[j]);}
      }
      for(const v of values) if(v && v!==511 && !wires.includes(v)) {
        if(!reached.has(v) && upper[v]>k+1)throw Error("Three-label violation: "+v);
        reached.add(v);
        if(k<5) {const s=list.concat(v).sort((a,b)=>a-b);next.set(s.join(","),s);}
      }
    }
    states=[...next.values()];
  }
  return reached.size;
}

function checkFour() {
  const groups=orbits(4), mono=formulaCosts(4,false), any=formulaCosts(4,true);
  const bounds=groups.map(g=>({t:g[0],m:mono[g[0]],f:any[g[0]],r:rawLower(g[0],4),n:g.length}));
  // Compute one helper, then allow it as a reusable formula leaf.
  for(const helper of [255,1,15|4369]) {
    const cost=formulaCosts(4,false,[helper]);
    groups.forEach((g,i)=>bounds[i].m=Math.min(bounds[i].m,1+Math.min(...g.map(t=>cost[t]))));
  }
  const special=new Map([[31710,11],[31711,9],[13278,9],[15838,9],[14302,11]]);
  for(const b of bounds) if(special.has(b.t)) b.m=Math.min(b.m,special.get(b.t));
  for(const b of bounds) if(b.m>b.f+3)throw Error("Unsettled formula case "+b.t);
  if(groups.length!==192 || bounds.reduce((n,b)=>n+b.n,0)!==65536)throw Error("Orbit coverage");
  return bounds.filter(b=>b.m>b.r+4);
}

const reached=checkThree(), cases=checkFour();
if (reached!==434)throw Error("Three-label census");
if(process.argv.includes("--cases")) console.log(JSON.stringify(cases));
else console.log("All 512 graphs verified at n=3; remaining n=4 checks:",cases.map(x=>x.t).join(", "));
