/* Four column types in the one-per-side complement problem, L-meta-19384. */
const count = new Uint8Array(65536);
for (let m=1; m<count.length; m++) count[m]=1+count[m&(m-1)];
const bitIndex = bit => 31-Math.clz32(bit);

// A pair of rows can be replaced by their OR in all common column sums.
const matching = new Uint8Array(65536);
for (let m=1; m<matching.length; m++) {
  const bit=m&-m, i=bitIndex(bit), rest=m^bit;
  matching[m]=matching[rest];
  for(let b=rest;b;b&=b-1){
    const next=b&-b, j=bitIndex(next);
    matching[m]=Math.max(matching[m],matching[rest^next]+count[i&j]-1);
  }
}

function extraSharing(patterns,mode) {
  const xs=patterns.filter(x=>x!==0).slice();
  let saved=0;
  while(true){
    let best=-1, a=-1, b=-1;
    for(let i=0;i<xs.length;i++) for(let j=0;j<i;j++){
      const k=count[xs[i]&xs[j]];
      if(k<2)continue;
      const union=count[xs[i]|xs[j]];
      const tie=mode===0 ? 0 : mode===1 ? -union : mode===2 ? union : (i*29+j*17+mode*311)%13;
      const score=10*k+tie;
      if(score>best){best=score;a=i;b=j;}
    }
    if(best<0)return saved;
    const common=xs[a]&xs[b];
    xs[a]^=common;xs[b]^=common;xs.push(common);
    saved+=count[common]-1;
  }
}

function readOnceMinorTables() {
  const raw=[7,56,448,73,146,292], sets=Array.from({length:64},()=>new Set());
  const known=new Set([0,511]);
  raw.forEach((w,i)=>sets[1<<i].add(w));
  for(let m=1;m<64;m++){
    for(let a=(m-1)&m;a;a=(a-1)&m){
      const b=m^a;
      if(a>b)continue;
      for(const x of sets[a])for(const y of sets[b]){
        sets[m].add(x&y);sets[m].add(x|y);
      }
    }
    for(const x of sets[m])known.add(x);
  }
  return known;
}

const readOnce=readOnceMinorTables();
function hasForbiddenMinor(rows) {
  for(let i=0;i<rows.length;i++)for(let j=0;j<i;j++)for(let k=0;k<j;k++)
    for(let skip=0;skip<4;skip++){
      let mask=0,bit=0;
      for(const r of [rows[k],rows[j],rows[i]])for(let c=0;c<4;c++)if(c!==skip){
        mask|=(1-((r>>c)&1))<<bit++;
      }
      if(!readOnce.has(mask))return true;
    }
  return false;
}

function specialUpper(rows) {
  const matched=rows.filter(r=>count[r]===3), full=rows.indexOf(15);
  if(full<0 || rows.length!==5)throw Error("Unexpected residual family");
  const residual=rows.find(r=>r!==15 && count[r]!==3);
  const extra=matched.reduce((a,b)=>a&b,15);
  let upper;
  for(let i=0;i<rows.length;i++)for(let j=0;j<4;j++){
    const x=rows[i], y=1<<j;
    const h=matched.map(r=>x===r || !(r&y));
    let value;
    if(h.length===4){
      value=(h[0]&&h[1])||(h[2]&&h[3])||((h[0]||h[1])&&(h[2]||h[3]))||x===15;
      upper=12;
    }else{
      if(h.length!==3 || count[extra]!==1)throw Error("Expected three matched columns");
      const first=h[0]||h[1], crown=(h[0]&&h[1])||(first&&h[2]);
      if(residual===0){
        value=crown || x===15 || (y===extra && (first||h[2]));
        upper=11;
      }else{
        if(!(residual&extra) || count[residual^extra]>1)throw Error("Unexpected extra row");
        value=crown || x===15 || y===extra || (x===residual && y===(residual^extra));
        upper=count[residual^extra]===0?9:11;
      }
    }
    if(Boolean(value)!==Boolean(x&y))throw Error("Wrong explicit small circuit");
  }
  return upper;
}

let checked=0, afterMatching=0, afterGreedy=0, afterMinor=0;
for(let m=0;m<65536;m++){
  const p=count[m];
  if(p<5)continue;
  const rows=[], cols=[0,0,0,0];
  for(let r=0;r<16;r++)if((m>>r)&1){
    rows.push(r);
    for(let j=0;j<4;j++)if((r>>j)&1)cols[j]|=1<<r;
  }
  if(new Set(cols).size!==4)continue;
  checked++;
  const rowUnion=rows.reduce((a,b)=>a|b), colUnion=cols.reduce((a,b)=>a|b);
  let lower=p+3-Number(rows.includes(rowUnion))-Number(cols.includes(colUnion));
  const w=rows.reduce((s,r)=>s+count[r],0);
  let upper=w+3-matching[m];
  if(m&32768)upper=Math.min(upper,w-matching[m&32767]);
  if(upper<=lower+p)continue;
  afterMatching++;
  for(let k=0;k<15;k++){
    upper=Math.min(upper,w+3-extraSharing(rows,k));
    if(m&32768)upper=Math.min(upper,w-extraSharing(rows.filter(r=>r!==15),k));
  }
  if(upper<=lower+p)continue;
  afterGreedy++;
  lower+=Number(hasForbiddenMinor(rows));
  if(upper<=lower+p)continue;
  afterMinor++;
  if(specialUpper(rows)>lower+p)throw Error("Unresolved row set "+m);
}
console.log({checked,afterMatching,afterGreedy,afterMinor,readOnceTables:readOnce.size});
if(checked!==62461 || afterMatching!==555 || afterGreedy!==409 || afterMinor!==21 || readOnce.size!==362)
  throw Error("Census mismatch");
