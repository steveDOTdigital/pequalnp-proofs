// Exact two-edit search around Shannon multiplexer circuits. Wire 0 is the
// false value supplied by an out-of-range input in the posted evaluator.
"use strict";
const assert = require("node:assert/strict");
const ALL = (1n << 2048n) - 1n;
const raw = [0n, ...Array(11).fill(0n)];
let target = 0n;
for (let row=0; row<2048; row++) {
  const bit=1n << BigInt(row);
  for (let i=0; i<11; i++) if (row & (1<<i)) raw[i+1] |= bit;
  if (row & (1 << (3+(row&7)))) target |= bit;
}

function shannon(shape) {
  const gates=[];
  function add(op,a,b=0) {
    gates.push([op,a,b]);
    return raw.length+gates.length-1;
  }
  const address=[1,2,3], neg=address.map(w=>add("not",w));
  let level=[4,5,6,7,8,9,10,11], node=0;
  for (let i=0; i<3; i++) {
    const next=[];
    for (let j=0; j<level.length; j+=2,node++) {
      if (shape & (1<<node))
        next.push(add("and",add("or",address[i],level[j]),add("or",neg[i],level[j+1])));
      else
        next.push(add("or",add("and",neg[i],level[j]),add("and",address[i],level[j+1])));
    }
    level=next;
  }
  return gates;
}
function apply(op,a,b) {
  return op==="and" ? a&b : op==="or" ? a|b : ALL^a;
}
function evaluate(gates,removed=-1,alias=0,clamp=-1,value=0n,replacement=null) {
  const w=raw.slice();
  for (let j=0; j<gates.length; j++) {
    const [op,a,b]=j===clamp && replacement ? replacement : gates[j];
    w.push(j===removed ? w[alias] :
           j===clamp && !replacement ? value : apply(op,w[a],w[b]));
  }
  return w;
}
function fit(w,before,ones,zeros) {
  const ok=v=>(v&ones)===ones && !(v&zeros);
  for (let a=0; a<before; a++) {
    if (ok(ALL^w[a])) return ["not",a,0];
    for (let b=0; b<=a; b++) {
      if (ok(w[a]&w[b])) return ["and",a,b];
      if (ok(w[a]|w[b])) return ["or",a,b];
    }
  }
  return null;
}
function search() {
  let aliases=0, locations=0, compatible=0;
  for (let shape=0; shape<128; shape++) {
    const g=shannon(shape);
    assert.equal(evaluate(g).at(-1),target);
    for (let rem=0; rem<24; rem++) for (let alias=0; alias<raw.length+rem; alias++) {
      aliases++;
      const w=evaluate(g,rem,alias);
      if (w.at(-1)===target) return {shape,rem,alias};
      for (let j=0; j<24; j++) {
        if (j===rem) continue;
        locations++;
        const ones=target ^ evaluate(g,rem,alias,j,0n).at(-1);
        const zeros=target ^ evaluate(g,rem,alias,j,ALL).at(-1);
        if (ones & zeros) continue;
        compatible++;
        const replacement=fit(w,raw.length+j,ones,zeros);
        if (replacement) {
          assert.equal(evaluate(g,rem,alias,j,0n,replacement).at(-1),target);
          return {shape,rem,alias,j,replacement,gates:g};
        }
      }
    }
  }
  return {aliases,locations,compatible};
}
// A damaged seven-selector control must be repairable at the known gate.
// The repair is inferred from its suffix constraints, then checked on every row.
const damaged=shannon(0);
const at=5;
damaged[at]=["and",0,0];
const w=evaluate(damaged);
assert.notEqual(w.at(-1),target);
const wanted=target ^ evaluate(damaged,-1,0,at,0n).at(-1);
const forbidden=target ^ evaluate(damaged,-1,0,at,ALL).at(-1);
const patch=fit(w,raw.length+at,wanted,forbidden);
assert(patch);
assert.equal(evaluate(damaged,-1,0,at,0n,patch).at(-1),target);
const result=search();
assert.deepEqual(result,{aliases:72192,locations:1660416,compatible:282912});
console.log(result);
