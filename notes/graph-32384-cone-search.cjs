const fs = require("node:fs");
const vm = require("node:vm");
const path = require("node:path");

const context = vm.createContext({});
const solverSource = fs.readFileSync(path.join(__dirname, "minisolvers.js"), "utf8");
vm.runInContext(solverSource, context);
const MinisatSolver = context.minisolvers.MinisatSolver;

function synthesize({width, gates, allowNot, target, name, forced, requireNot, minimumCone}) {
  const S = new MinisatSolver();
  const v = () => { S.new_var(); return S.nvars(); };
  const clause = (...lits) => S.add_clause(lits);
  const one = lits => {
    clause(...lits);
    for (let i = 0; i < lits.length; i++) {
      for (let j = 0; j < i; j++) clause(-lits[i], -lits[j]);
    }
  };
  const slots = [];
  for (let g = 0; g < gates; g++) {
    const available = width + g;
    const a = Array.from({length: available}, v);
    const b = Array.from({length: available}, v);
    const and = v(), or = v(), not = v();
    slots.push({a,b,and,or,not});
    one(a);
    one(b);
    one([and,or,not]);
    if (!allowNot) clause(-not);
    clause(-not,b[0]);
    for (let i = 0; i < available; i++) {
      for (let j = 0; j <= i; j++) clause(not,-a[i],-b[j]);
    }
  }
  for (let g = 0; g < gates; g++) {
    for (let h = 0; h < g; h++) clause(-slots[g].not,-slots[h].not);
  }
  const active = Array.from({length:gates}, v);
  const maxima = [];
  clause(active.at(-1));
  for (let g=0; g<gates; g++) {
    const slot = slots[g];
    const current = active[g];
    if (g+1 < gates) clause(-current,active[g+1]);
    clause(current,slot.and);
    clause(current,slot.a[0]);
    clause(current,slot.b[1]);
    for (let h=0; h<g; h++) {
      clause(-slot.a[width+h],active[h]);
      clause(-slot.b[width+h],active[h]);
    }
    if (g+1 < gates) {
      clause(-current,...slots.slice(g+1).flatMap(later=>[later.a[width+g],later.b[width+g]]));
    }
    const maximum = slot.a.map(v);
    one(maximum);
    for (let i=0; i<maximum.length; i++) {
      clause(-maximum[i],slot.not,slot.b[i]);
      clause(-maximum[i],-slot.not,slot.a[i]);
    }
    if (g) {
      const prev = maxima.at(-1);
      for (let i=0; i<prev.length; i++) {
        for (let j=0; j<i; j++) clause(-active[g-1],-prev[i],-maximum[j]);
      }
    }
    maxima.push(maximum);
  }
  if (forced) {
    const indexed = new Map(Array.from({length:width},(_,i)=>[i,i]));
    const remaining = forced.map((item,i)=>({item,id:width+i}));
    const ordered = [];
    while (remaining.length) {
      const ready = remaining.filter(({item:[op,u,w]})=>indexed.has(u) && (op==="not" || indexed.has(w)));
      ready.sort(({item:[opA,uA,wA]},{item:[opB,uB,wB]})=>
        Math.max(indexed.get(uA),opA==="not" ? 0 : indexed.get(wA)) -
        Math.max(indexed.get(uB),opB==="not" ? 0 : indexed.get(wB)));
      if (!ready.length) throw Error("Unchecked cyclic control");
      const next = ready[0], [op,u,w] = next.item;
      indexed.set(next.id,width+ordered.length);
      ordered.push([op,indexed.get(u),op==="not" ? 0 : indexed.get(w)]);
      remaining.splice(remaining.indexOf(next),1);
    }
    for (let g = 0; g < ordered.length; g++) {
      const [op, u, w] = ordered[g];
      clause(active[g]);
      const slot = slots[g];
      clause(slot[op]);
      if (op === "not") clause(slot.a[u]);
      else {
        clause(slot.a[Math.min(u,w)]);
        clause(slot.b[Math.max(u,w)]);
      }
    }
  }
  if (requireNot) clause(...slots.map(slot=>slot.not));
  if (minimumCone !== undefined) {
    const inCone=slots.map(v);
    clause(inCone.at(-1));
    const contribution=slots.map((slot,g)=>{
      const counted=v();
      clause(-counted,inCone[g]);
      clause(-counted,-slot.not);
      clause(-inCone[g],slot.not,counted);
      if(g+1===gates) return counted;
      const readers=[];
      for(let h=g+1;h<gates;h++) {
        const consumer=slots[h], a=consumer.a[width+g], b=consumer.b[width+g];
        const reader=v();
        clause(-reader,inCone[h]);
        clause(-reader,-consumer.not);
        clause(-reader,a,b);
        clause(-inCone[h],consumer.not,-a,reader);
        clause(-inCone[h],consumer.not,-b,reader);
        clause(-reader,inCone[g]);
        readers.push(reader);
      }
      clause(-inCone[g],...readers);
      return counted;
    });
    const trueLiteral=v();
    clause(trueLiteral);
    let threshold=Array(minimumCone+1).fill(-trueLiteral);
    threshold[0]=trueLiteral;
    for(const next of contribution) {
      const previous=threshold;
      threshold=[trueLiteral];
      for(let amount=1;amount<=minimumCone;amount++) {
        const point=v(), p=previous[amount], q=previous[amount-1];
        clause(-p,point);
        clause(-next,-q,point);
        clause(p,next,-point);
        clause(p,q,-point);
        threshold.push(point);
      }
    }
    clause(threshold[minimumCone]);
  }
  const rows = 1 << width;
  for (let rawBit=0; rawBit<width; rawBit++) {
    const bitMask=1<<rawBit;
    const essential=Array.from({length:rows},(_,row)=>row).some(row=>
      !(row & bitMask) && !target(row) && !!target(row|bitMask));
    if (!essential) continue;
    const positivePath=[];
    for (const slot of slots) {
      const lhs=v(),rhs=v(),out=v();
      const pathThrough=(selectors,operand)=>{
        for(let wire=0;wire<selectors.length;wire++){
          if(wire<width) clause(-selectors[wire],wire===rawBit?operand:-operand);
          else {
            const parent=positivePath[wire-width];
            clause(-selectors[wire],-operand,parent);
            clause(-selectors[wire],operand,-parent);
          }
        }
      };
      pathThrough(slot.a,lhs);
      pathThrough(slot.b,rhs);
      clause(-slot.not,-out);
      clause(slot.not,-lhs,out);
      clause(slot.not,-rhs,out);
      clause(slot.not,lhs,rhs,-out);
      positivePath.push(out);
    }
    clause(positivePath.at(-1));
  }
  const samples = new Set();
  const rowWires = new Map();
  const raw = (row,i) => (row >> i) & 1;
  function addRow(row) {
    if (samples.has(row)) return;
    samples.add(row);
    const values = [];
    for (const slot of slots) {
      const lhs = v(), rhs = v(), out = v();
      function agree(selectors, branch) {
        for (let i = 0; i < selectors.length; i++) {
          const use = selectors[i];
          if (i < width) clause(-use, raw(row,i) ? branch : -branch);
          else {
            const wire = values[i-width];
            clause(-use,-branch,wire);
            clause(-use,branch,-wire);
          }
        }
      }
      agree(slot.a,lhs);
      agree(slot.b,rhs);
      clause(-slot.and,-lhs,-rhs,out);
      clause(-slot.and,lhs,-out);
      clause(-slot.and,rhs,-out);
      clause(-slot.or,lhs,rhs,-out);
      clause(-slot.or,-lhs,out);
      clause(-slot.or,-rhs,out);
      clause(-slot.not,lhs,out);
      clause(-slot.not,-lhs,-out);
      values.push(out);
    }
    rowWires.set(row,values);
    clause(target(row) ? values.at(-1) : -values.at(-1));
  }
  for (let row = 0; row < rows; row++) {
    let minimal = true, maximal = true;
    const outcome = target(row);
    for (let i = 0; i < width; i++) {
      if (raw(row,i) && target(row ^ (1 << i))) minimal = false;
      if (!raw(row,i) && !target(row ^ (1 << i))) maximal = false;
    }
    if ((outcome && minimal) || (!outcome && maximal) || row === 0 || row === rows-1 ||
        (row & (row-1)) === 0) addRow(row);
  }
  if (allowNot) {
    const atZero=rowWires.get(0), atOne=rowWires.get(rows-1);
    for(let g=0;g<gates;g++) clause(slots[g].not,-atZero[g],atOne[g]);
  }
  const stamp = data => console.log(JSON.stringify({name,gates,allowNot,...data}));
  for (let iteration = 1; ; iteration++) {
    stamp({event:"search",iteration,rows:samples.size,variables:S.nvars(),clauses:S.nclauses()});
    const verdict = S.solve();
    if (!verdict) {
      stamp({event:"UNSAT",iteration,rows:samples.size});
      return {verdict:"UNSAT"};
    }
    const model = S.get_model();
    const lit = i => model[i-1] === 1;
    const spec = slots.map(slot => [
      lit(slot.not) ? "not" : lit(slot.and) ? "and" : "or",
      slot.a.findIndex(lit), slot.b.findIndex(lit),
    ]);
    if (spec.some(([op,a,b],i) => a < 0 || a >= width+i || b < 0 || b >= width+i ||
                                  (op !== "not" && b <= a)) ||
        spec.filter(g => g[0] === "not").length > (allowNot ? 1 : 0)) throw Error("Invalid SAT witness");
    const misses = [];
    for (let row = 0; row < rows; row++) {
      const wires = Array.from({length:width},(_,i)=>raw(row,i));
      for (const [op,a,b] of spec) {
        wires.push(op === "and" ? (wires[a] & wires[b]) : op === "or" ? (wires[a] | wires[b]) : 1-wires[a]);
      }
      if (wires.at(-1) !== +target(row)) {
        if (samples.has(row)) throw Error("Solver model disagrees with its own constraints");
        misses.push(row);
      }
    }
    if (!misses.length) {
      stamp({event:"SAT",iteration,rows:samples.size,replayed:rows,spec,output:width+gates-1});
      return {verdict:"SAT",spec};
    }
    const candidates = [...misses.filter(target).slice(0,8), ...misses.filter(row=>!target(row)).slice(0,8)];
    for (const row of candidates) addRow(row);
    stamp({event:"refine",misses:misses.length,rows:samples.size});
  }
}
const mode = process.argv[2];
if (mode === "sanity") {
  const and = row => row === 3;
  const xor = row => row === 1 || row === 2;
  for (const [name,gates,allowNot,target,expected] of [
    ["and",1,false,and,"SAT"],["xor",3,true,xor,"UNSAT"],["xor",4,true,xor,"SAT"]
  ]) {
    const proof = synthesize({width:2,name,gates,allowNot,target});
    if (proof.verdict !== expected) throw Error("Incorrect verdict on a control");
  }
} else {
  const edges = [3,4,12,5,13,21,14,22,38,7,15,23,39,47,55].map(x=>[x >> 3,x&7]);
  const target = row => edges.some(([a,b]) => (row & (1<<a)) && (row & (1<<b)));
  if (!["monotone","signed","control","signed-cone-control"].includes(mode)) {
    throw Error("Choose monotone, signed, control or signed-cone-control");
  }
  const gates=Number(process.argv[3]);
  const signed=mode==="signed"||mode==="signed-cone-control";
  if(!Number.isSafeInteger(gates)||gates<1||gates>18) throw Error("Unsupported budget");
  const checked=[["or",1,2],["or",4,5],["or",0,7],["or",4,7],["or",1,6],["or",0,12],["or",6,7],["or",5,14],["and",3,0],["and",10,9],["and",11,13],["and",15,8],["or",16,17],["or",20,18],["or",21,19]];
  if(mode==="signed-cone-control") {
    const forced=[...checked,["not",0,0],["or",0,23],["and",22,24]];
    for(const bound of [17,18]) {
      const expected=bound===17?"SAT":"UNSAT";
      const value=synthesize({width:8,gates:18,allowNot:true,target,
        name:"live NOT cone control",forced,requireNot:true,minimumCone:bound});
      if(value.verdict!==expected) throw Error("Incorrect cone count for the live NOT control");
    }
  } else {
    const forced=mode==="control"?checked:undefined;
    const value=synthesize({width:8,gates,allowNot:signed,target,name:"L-meta-32384",forced,
      requireNot:signed,minimumCone:signed?9:undefined});
    if(forced&&value.verdict!=="SAT") throw Error("The checked upper bound was rejected by the encoding");
  }
}