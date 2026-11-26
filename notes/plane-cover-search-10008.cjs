/* Exact weighted set cover on symmetry orbits. Node 18+, no dependencies. */
const plane = require("./plane-cover-orbits-10008.cjs");
// Nonnegative integer weights only accelerate pruning. Their validity is
// checked by computing fresh maximum gains from the entire orbit catalogue.
const extraWeights = {"67":[[0,0,0,0,0,0,0,0,0,0,20000,0,0,0,0,0,40000,0,0,0,0,0,0,20000,40000,40000,0,20000,0,0,0,0,0,0,0,40000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40000,0,0,40000,0,0,0,0,0,0,0,0,0],[0,3000,2000,2000,3000,0,2000,2000,3000,500,3500,3000,0,3000,500,0,27000,500,500,500,500,500,500,3500,27000,27000,500,3500,0,0,0,500,0,2000,0,27000,2000,3000,3000,0,1000,0,0,3000,2000,2000,0,2000,0,0,0,3000,2000,3000,27000,1000,0,27000,0,2000,3000,2000,3000,0,1000,0,0]],"117":[[0,0,0,0,0,0,0,0,0,0,0,0,10000000000,20000,0,0,0,0,0,10000000000,0,0,0,0,10000000000,0,10000000000,10000000000,0,0,0,0,20000,0,0,0,0,20000,10000000000,0,0,0,0,0,10000000000,0,10000000000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10000000000,20000,10000000000,20000,10000000000,10000000000,0,0,0,0,0,0,0,0,20000,0,0,10000000000,0,0,0,0,0,0,0,20000,0,0,10000000000,0,0,0,0,0,0,0,20000,10000000000,0,10000000000,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,13333,3125,0,0,3125,0,5833,4375,13333,6250,5833,0,0,0,0,0,0,0,0,13333,0,0,0,0,0,0,0,13333,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,13333,0,0,5833,0,4375,3125,0,0,0,5833,0,3125,0,6250,0,0,13333,0,0,0,3750,0,0,0,6250,0,3750,13333,0,0,0,0,0,0,0,0,13333,0,0,0,0,0,0,6250,0,0,0,3750,0,0,0,3750]]};
const witness24 = [[604900420,672663560],[1,1005584175],[266242,1955649116],
  [805306400,1685710272],[232260688,1048784],[1962932189,1]];

function search(instance, budget, large) {
  const weights = [instance.sizes, ...extraWeights[instance.sizes.length]];
  if (weights.some(a=>a.length!==instance.sizes.length ||
      a.some(v=>!Number.isSafeInteger(v)||v<0) || a.reduce((x,y)=>x+y,0)*budget>=2**52))
    throw Error("Invalid weighting");
  const lookup = weights.map(a=>Array.from({length:Math.ceil(a.length/8)},(_,i)=>
    Array.from({length:256},(_,n)=>a.slice(i*8,i*8+8).reduce((sum,v,j)=>sum+(((n>>>j)&1)?v:0),0))));
  function mass(mask) {
    const sums=weights.map(()=>0);
    for(let i=0;mask;i++,mask>>=8n) {
      const byte=Number(mask&255n);
      for(let j=0;j<sums.length;j++) sums[j]+=lookup[j][i][byte];
    }
    return sums;
  }
  const bins=Array.from({length:large+1},()=>[]);
  const maxGain=weights.map(()=>Array(large+1).fill(0));
  for (const [cost,options] of instance.bins) {
    if(cost>large || (cost&(cost-1))!==0) throw Error("Unexpected orbit size");
    for (const [mask,box] of options) {
      const gains=mass(mask);
      bins[cost].push({mask,box,gains});
      gains.forEach((v,j)=>maxGain[j][cost]=Math.max(maxGain[j][cost],v));
    }
  }
  // Relax overlap and allow an orbit to be used repeatedly to overestimate
  // the remaining coverable weight, separately for each weight vector.
  const cap=weights.map((_,j)=>Array.from({length:large+1},(_,limit)=>{
    const dp=Array(budget+1).fill(0);
    for(let b=1;b<=budget;b++) for(let c=1;c<=b && c<=limit;c*=2)
      dp[b]=Math.max(dp[b],maxGain[j][c]+dp[b-c]);
    return dp;
  }));
  function fits(w,b,limit) { return w.every((v,j)=>v<=cap[j][limit][b]); }
  const memo=new Map();
  function smaller(rem,b) {
    if (!rem) return [];
    if (b<=0 || (memo.get(rem)??-1)>=b) return null;
    let limit=1;
    while(limit*2<=b && limit*2<large) limit*=2;
    const w=mass(rem);
    if(!fits(w,b,limit)) return null;
    memo.set(rem,b);
    const choices=[];
    for(let c=1;c<=limit;c*=2) for(const opt of bins[c]) {
      if(w.some((v,j)=>v-opt.gains[j]>cap[j][limit][b-c])) continue;
      const rest=rem&~opt.mask;
      if(rest!==rem && fits(mass(rest),b-c,limit)) choices.push([opt,rest,c]);
    }
    // Any completion must take some option containing this uncovered cell orbit.
    let fewest=null;
    for(let z=rem;z;z&=z-1n) {
      const bit=z&-z, chosen=[];
      for(const item of choices) if(item[0].mask&bit) {
        chosen.push(item);
        if(fewest && chosen.length>=fewest.length) break;
      }
      if(!chosen.length) return null;
      if(!fewest || chosen.length<fewest.length) fewest=chosen;
    }
    for(const [opt,rest,c] of fewest) {
      const tail=smaller(rest,b-c);
      if(tail) return [opt.box,...tail];
    }
    return null;
  }
  bins[large].sort((a,b)=>b.gains[0]-a.gains[0]);
  function largest(rem,b,k,start) {
    if(!k) return smaller(rem,b);
    const w=mass(rem), left=b-k*large;
    const fitsRest=(mass,j,remaining)=>mass<=remaining*maxGain[j][large]+cap[j][large/2][left];
    if(w.some((v,j)=>!fitsRest(v,j,k))) return null;
    for(let i=start;i<bins[large].length;i++) {
      const opt=bins[large][i];
      if(w[0]>k*opt.gains[0]+cap[0][large/2][left]) break;
      if(w.some((v,j)=>!fitsRest(v-opt.gains[j],j,k-1))) continue;
      const rest=rem&~opt.mask;
      if(mass(rest).some((v,j)=>!fitsRest(v,j,k-1))) continue;
      const tail=largest(rest,b-large,k-1,i+1);
      if(tail) return [opt.box,...tail];
    }
    return null;
  }
  for(let k=0;k*large<=budget;k++) {
    const answer=largest(instance.target,budget,k,0);
    if(answer) return answer;
  }
  return null;
}

function elationCheck(rectangles) {
  const x=plane.options(rectangles,[plane.collineation(1,1,1)]);
  const fixed=[...x.bins.get(1).keys()].reduce((a,b)=>a|b,0n), core=x.target&~fixed;
  function count(z) {let n=0;while(z){z&=z-1n;n++;}return n;}
  if(count(core)!==100) throw Error("Elation core size");
  const top=[];
  for(const mask of x.bins.get(5).keys()) {
    const part=mask&core, n=count(part);
    if(n>50) throw Error("Elation core bound");
    if(n===50) top.push(part);
  }
  if(top.length!==40 || top.some(a=>top.some(b=>(a|b)===core))) throw Error("Two-orbit cover");
}

async function main() {
  await plane.verifyInput();
  const rectangles=plane.maximalRectangles();
  if(rectangles.length!==50508) throw Error("Wrong cyclic census");
  const a=plane.collineation(2,1), b=plane.collineation(1,2), b2=plane.collineation(1,4);
  const torus=plane.options(rectangles,[a,b]);
  if(plane.verifyWitness(witness24,[a,b])!==24 || search(torus,23,16))
    throw Error("Wrong full diagonal optimum");
  console.log("Full diagonal group: exact optimum 24.");
  const subgroup=plane.options(rectangles,[a,b2]);
  if(search(subgroup,18,8)) throw Error("Unexpected subgroup cover.");
  console.log("Index-two diagonal subgroup: no cover of size at most 18.");
  elationCheck(rectangles);
  console.log("An elation-invariant 17-cover would need three moving orbits.");
}
main().catch(e=>{console.error(e.message);process.exitCode=1;});
