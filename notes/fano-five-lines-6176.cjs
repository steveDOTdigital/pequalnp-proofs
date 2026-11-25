"use strict";

// Finite intersection graph of five Fano lines, with the private point deleted.
// Line 3 joins the two triple points. The two optional helpers join opposite
// degree-two points on the two completed lines.
const assert = require("node:assert/strict");
const {enumerate, permutations} = require("./fano-three-stars-6176.cjs");
const edges = [[0,6],[0,7],[0,9],[1,7],[1,8],[1,10],[2,5],[2,8],[2,9],
  [3,9],[3,10],[4,5],[4,6],[4,10]];
const helpers = [[5,7],[6,8]];
const lowerAfterPin = [14,14,14,15,14,16,16,16,16,15,15];
const vertices = Array.from({length:11}, (_,i)=>i);

function graph(drop, helperMask) {
  const remaining = vertices.filter(v=>v!==drop);
  const genuine = helpers.filter(([a,b],i)=>(helperMask & (1<<i)) && a!==drop && b!==drop);
  const masks = remaining.map((_,i)=>1<<i);
  for (const [a,b] of genuine) masks.push((1<<remaining.indexOf(a)) | (1<<remaining.indexOf(b)));
  const hood = vertices.map(v=>edges.filter(e=>e.includes(v))
    .reduce((m,e)=>m | (1<<e.find(w=>w!==v)),0));
  const transforms = [];
  for (const linePerm of permutations([0,1,2,3,4])) {
    const image = [...linePerm];
    for (let v=5; v<11; v++) {
      let target = 0;
      for (let i=0; i<5; i++) if (hood[v] & (1<<i)) target |= 1<<linePerm[i];
      const point = vertices.find(i=>i>=5 && hood[i]===target);
      if (point===undefined) break;
      image.push(point);
    }
    if (image.length!==11 || (drop!==null && image[drop]!==drop)) continue;
    const mapped = masks.map(mask=>{
      let result = 0;
      for (let j=0; j<remaining.length; j++) {
        if (mask & (1<<j)) result |= 1<<remaining.indexOf(image[remaining[j]]);
      }
      return masks.indexOf(result);
    });
    if (mapped.every(i=>i>=0)) transforms.push(mapped);
  }
  assert(transforms.length);
  return {rawCount:remaining.length, masks, transforms,
    edges:edges.filter(e=>!e.includes(drop)).map(e=>e.map(v=>remaining.indexOf(v))),
    optimum:drop===null ? 18 : lowerAfterPin[drop]};
}

function pinnedTrial(v, masks) {
  const retained = edges.filter(e=>!e.includes(v));
  const flags = retained.map(([a,b])=>(1<<a) | (1<<b));
  const target = row=>flags.some(f=>(row&f)===f);
  const rows = [...flags];
  for (let row=0; row<2048; row++) {
    if ((row & (1<<v)) || target(row)) continue;
    if (vertices.every(i=>i===v || (row & (1<<i)) || target(row | (1<<i)))) rows.push(row);
  }
  assert(rows.length<=31);
  const values = masks.map(mask=>rows.reduce((s,r,i)=>s | ((r&mask) ? 1<<i : 0),0));
  const allowed = new Set();
  if (v===3) {
    // Every gate in an optimal 15-gate K4 circuit lies in one star or
    // in the OR tree over the four stars. Allow all their boundary values.
    const stars = [];
    for (const c of [0,1,2,4]) {
      const leaves = retained.filter(([a])=>a===c).map(([,b])=>b);
      assert.equal(leaves.length,3);
      for (let m=1; m<8; m++) {
        let value=0, count=0;
        leaves.forEach((a,i)=>{if (m & (1<<i)) {value |= values[a]; count++;}});
        if (count>=2) allowed.add(value);
        if (count===3) stars.push(value & values[c]);
      }
    }
    for (let m=1; m<16; m++) {
      allowed.add(stars.reduce((s,x,i)=>s | ((m & (1<<i)) ? x : 0),0));
    }
  }
  return {v,values,allowed};
}

function restrictionTests(core, limit) {
  const trials = [3,5,6,7,8,9,10,0,1,2,4].map(v=>pinnedTrial(v,core.masks));
  const saved = Array.from({length:limit+1},()=>Array(trials.length).fill(0));
  const outsideStarTree = Array(limit+1).fill(false);
  function feasible(v, removed, depth) {
    const left = limit-removed;
    return left>=lowerAfterPin[v] && !(v===3 && left===15 && outsideStarTree[depth]);
  }
  return {
    gate(depth, out, isOr, a, b) {
      outsideStarTree[depth+1] = outsideStarTree[depth];
      for (const [i,trial] of trials.entries()) {
        const {v,values,allowed} = trial;
        const value = isOr ? values[a]|values[b] : values[a]&values[b];
        values[out] = value;
        let duplicate = value===0;
        for (let j=0; !duplicate && j<out; j++) duplicate = values[j]===value;
        saved[depth+1][i] = saved[depth][i] + Number(duplicate);
        if (v===3 && !duplicate && !allowed.has(value)) outsideStarTree[depth+1]=true;
        if (!feasible(v,saved[depth+1][i],depth+1)) return false;
      }
      return true;
    },
    live(depth, wires) {
      for (const [i,{v,values}] of trials.entries()) {
        let removed = saved[depth][i];
        // Each currently live zero needs a future gate before the output
        // can be nonzero. A binary gate reduces their count by at most one.
        for (const w of wires) if (values[w]===0) removed++;
        if (!feasible(v,removed,depth)) return false;
      }
      return true;
    }
  };
}

function verifyFanoGeometry() {
  const labels = [0,1,2,3,4,5,6];
  const lines = labels.map(i=>(1<<i) | (1<<((i+1)%7)) | (1<<((i+3)%7)));
  const pointHoods = vertices.slice(5).map(v=>edges.filter(([,b])=>b===v)
    .reduce((hood,[a])=>hood | (1<<a),0));
  let checked = 0;
  for (let u=0; u<7; u++) for (let v=u+1; v<7; v++) {
    const common = lines[u] & lines[v];
    const five = labels.filter(i=>i!==u && i!==v);
    const matched = permutations(five).some(order=>{
      const image = labels.map(p=>pointHoods.indexOf(order.reduce((hood,line,i)=>
        hood | ((lines[line] & (1<<p)) ? 1<<i : 0),0))+5);
      if (labels.some(p=>!(common & (1<<p)) && image[p]<5)) return false;
      const pairs = [u,v].map(line=>labels.filter(p=>(lines[line] & ~common) & (1<<p))
        .map(p=>image[p]).sort((a,b)=>a-b).join(",")).sort();
      return pairs.join(";")==="5,7;6,8" && (lines[order[3]] & common)!==0;
    });
    assert(matched);
    checked++;
  }
  assert.equal(checked,21);
}

function verifyControl() {
  const gates = [];
  function gate(isOr,a,b) {
    assert.notEqual(a,b);
    gates.push([isOr,a,b]);
    return 10+gates.length;
  }
  const terms = [];
  for (let c=0; c<5; c++) {
    const leaves = edges.filter(([a])=>a===c).map(([,b])=>b);
    terms.push(gate(false,c,leaves.reduce((a,b)=>gate(true,a,b))));
  }
  const out = terms.reduce((a,b)=>gate(true,a,b));
  assert.equal(gates.length,18);
  for (let row=0; row<2048; row++) {
    const wires = vertices.map(j=>Boolean(row & (1<<j)));
    for (const [isOr,a,b] of gates) wires.push(isOr ? wires[a]||wires[b] : wires[a]&&wires[b]);
    assert.equal(wires[out],edges.some(([a,b])=>wires[a]&&wires[b]));
  }
}

function verifyPinBounds() {
  // Representatives of the four vertex orbits. Removing a paired point
  // leaves only the other helper. All subsets of available helpers are tried.
  for (const v of [0,3,5,9]) {
    const seen = new Set();
    for (let helperMask=0; helperMask<4; helperMask++) {
      const core = graph(v,helperMask);
      const key = core.masks.join(",");
      if (seen.has(key)) continue;
      seen.add(key);
      const result = enumerate(core,core.optimum-1);
      assert.equal(result.solutions,0);
      console.log("deleted",v,"helper mask",helperMask,"lower bound",core.optimum,result.states);
    }
  }
}

function verifyFirstAnd() {
  // By symmetry take triple point 9. In the deleted graph the five line
  // inputs keep their labels and the possible neighbors of point 9 are 0,2,3.
  const adjacent = [0,2,3];
  assert(graph(null,3).transforms.some(p=>p[10]===9));
  const counts = {circuits:0,insertions:0,compatible:0};
  function checkInsertions(gates,out) {
    counts.circuits++;
    const raw = Array.from({length:10},(_,i)=>i<5 ? 1<<(i+1) : 0);
    const wanted = adjacent.reduce((m,line)=>m | (1<<(line+1)),0);
    for (let source=0; source<10+gates.length; source++) {
      const uses = [];
      gates.forEach(([,a,b],i)=>{
        if (a===source) uses.push(2*i);
        if (b===source) uses.push(2*i+1);
      });
      if (out===source) uses.push(2*gates.length);
      for (let mask=1; mask<1<<uses.length; mask++) {
        counts.insertions++;
        const chosen = new Set(uses.filter((_,i)=>mask & (1<<i)));
        // Point 9 is on in all six rows. The restored OR therefore forces
        // selected reads high. Other old points are off; at most one line is on.
        const wires = [...raw];
        gates.forEach(([isOr,a,b],i)=>{
          const x = chosen.has(2*i) ? 63 : wires[a];
          const y = chosen.has(2*i+1) ? 63 : wires[b];
          wires.push(isOr ? x|y : x&y);
        });
        const value = chosen.has(2*gates.length) ? 63 : wires[out];
        for (const line of adjacent) {
          // Skip the row where the other input of the first AND is high.
          // On every remaining row that gate's value must be zero.
          const compare = 63 & ~(1<<(line+1));
          if (((value^wanted)&compare)===0) counts.compatible++;
        }
      }
    }
  }
  for (let h=0; h<4; h++) {
    const core = graph(9,h);
    assert(core.transforms.every(p=>
      adjacent.every(i=>adjacent.includes(p[i]))));
    const result = enumerate(core,15,null,h===0 ? checkInsertions : null);
    assert.equal(result.solutions,h===0 ? 2277 : 0);
    console.log("triple point deleted at 15 gates, helper mask",h,result);
  }
  assert.deepEqual(counts,{circuits:2277,insertions:87939,compatible:0});
  console.log("restoring point 9 with the first AND zero",counts);
}


verifyFanoGeometry();
verifyControl();
if (process.argv.includes("--cofactors")) verifyPinBounds();
for (let helperMask=0; helperMask<4; helperMask++) {
  const core = graph(null,helperMask);
  const result = enumerate(core,17,restrictionTests(core,17));
  assert.equal(result.solutions,0);
  console.log("17 gates, helper mask",helperMask,result);
}

if (process.argv.includes("--first-and")) verifyFirstAnd();
