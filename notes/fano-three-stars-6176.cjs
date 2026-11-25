"use strict";

// Classify every minimum monotone circuit in the two four-line Fano cores.
const assert = require("node:assert/strict");

function permutations(items) {
  if (items.length === 0) return [[]];
  return items.flatMap(item => permutations(items.filter(other => other !== item))
    .map(tail => [item, ...tail]));
}

function makeCore(shape, helpers) {
  const edges = [];
  const transforms = [];
  let rawCount, masks, optimum;
  if (shape === "theta") {
    rawCount = 8;
    optimum = 12;
    for (let i = 0; i < 3; i++) edges.push([0, 2+i], [2+i, 5+i], [5+i, 1]);
    masks = Array.from({length: rawCount}, (_, i) => 1 << i);
    for (const p of permutations([0,1,2])) {
      const left = p.map(i => 2+i);
      const right = p.map(i => 5+i);
      transforms.push([0, 1, ...left, ...right], [1, 0, ...right, ...left]);
    }
  } else {
    rawCount = 10;
    optimum = 15;
    // Four line vertices, then their six pairwise intersections in this order.
    const ends = [3,5,9,6,10,12];
    ends.forEach((pair, i) => {
      for (let j=0; j<4; j++) if (pair & (1<<j)) edges.push([j, 4+i]);
    });
    masks = Array.from({length: rawCount}, (_, i) => 1 << i);
    for (let i=0; i<helpers; i++) masks.push((1<<(4+i)) | (1<<(9-i)));
    for (const p of permutations([0,1,2,3])) {
      const points = ends.map(pair => {
        let image = 0;
        for (let j=0; j<4; j++) if (pair & (1<<j)) image |= 1<<p[j];
        return 4+ends.indexOf(image);
      });
      const vertices = p.concat(points);
      const permutation = masks.map(mask => {
        let mapped = 0;
        for (let i=0; i<rawCount; i++) if (mask & (1<<i)) mapped |= 1<<vertices[i];
        return masks.indexOf(mapped);
      });
      if (permutation.every(i => i >= 0)) transforms.push(permutation);
    }
  }
  return {edges, rawCount, masks, transforms, optimum};
}

function geometry() {
  const points = Array.from({length: 7}, (_,i) => i);
  const lines = points.map(i => (1<<i) | (1<<((i+1)%7)) | (1<<((i+3)%7)));
  const counts = {theta: 0, k4: 0};
  for (let selection=0; selection<128; selection++) {
    const chosen = points.filter(i => selection & (1<<i));
    if (chosen.length !== 4) continue;
    const degree = points.map(p => chosen.filter(i => lines[i] & (1<<p)).length);
    const kept = points.filter(p => degree[p]>=2);
    const old = points.filter(i => !(selection & (1<<i)));
    if (kept.length === 6) {
      counts.k4++;
      assert.equal(degree.filter(d => d===0).length, 1);
      for (const i of old) {
        const pair = kept.filter(p => lines[i] & (1<<p));
        assert.equal(pair.length, 2);
        assert(chosen.every(j => !pair.every(p => lines[j] & (1<<p))));
      }
    } else {
      counts.theta++;
      assert.equal(kept.length, 4);
      assert.equal(degree.filter(d => d===3).length, 1);
      assert.equal(degree.filter(d => d===1).length, 3);
      for (const i of old) {
        const [corner] = kept.filter(p => lines[i] & (1<<p));
        assert.equal(kept.filter(p => lines[i] & (1<<p)).length, 1);
        assert.equal(degree[corner], 2);
        for (const p of points.filter(p => degree[p]===1 && (lines[i] & (1<<p)))) {
          assert(chosen.every(j => !(lines[j] & (1<<p)) || !(lines[j] & (1<<corner))));
        }
      }
    }
  }
  assert.deepEqual(counts, {theta:28,k4:7});
  return counts;
}

// Match the actual gates, including their operands and every branch of the output OR.
function isStarTree(core, gates, depth, output) {
  const {rawCount, masks, edges} = core;
  const neighbors = Array(rawCount).fill(0);
  for (const [a,b] of edges) {
    neighbors[a] |= 1<<b;
    neighbors[b] |= 1<<a;
  }
  const pureOr = masks.map((m,i) => i<rawCount ? m : 0);
  const center = Array(masks.length).fill(-1);
  for (let i=0; i<depth; i++) {
    const [isOr,a,b] = gates[i];
    const x = pureOr[a], y = pureOr[b];
    pureOr.push(isOr && x && y && !(x & y) ? x|y : 0);
    let star = -1;
    if (!isOr && a<rawCount && y===neighbors[a]) star = a;
    if (!isOr && b<rawCount && x===neighbors[b]) star = b;
    center.push(star);
  }
  let centers = 0;
  const todo = [output];
  while (todo.length) {
    const w = todo.pop();
    if (center[w] >= 0) {
      const bit = 1<<center[w];
      if (centers & bit) return false;
      centers |= bit;
    } else {
      if (w<masks.length || !gates[w-masks.length][0]) return false;
      const [,a,b] = gates[w-masks.length];
      todo.push(a,b);
    }
  }
  // In a connected bipartite graph this condition selects one entire shore.
  return edges.every(([a,b]) => ((centers>>a) ^ (centers>>b)) & 1);
}

function enumerate(core, limit) {
  const {edges, rawCount, masks, transforms} = core;
  const width = masks.length;
  const flags = edges.map(([a,b]) => (1<<a) | (1<<b));
  const rows = [...flags];
  const positive = row => flags.some(f => (f & row)===f);
  for (let r=0; r<1<<rawCount; r++) {
    if (!positive(r) && masks.slice(0,rawCount).every(m => (r&m) || positive(r|m))) rows.push(r);
  }
  assert(rows.length < 31);
  const nNeg = rows.length-flags.length;
  const yes = (1<<flags.length)-1, no = ((1<<nNeg)-1)<<flags.length;
  const values = masks.map(m => rows.reduce((v,r,i) => v | ((m&r) ? 1<<i : 0), 0));

  // A positive and a negative row must differ in the right direction
  // on at least one source the remaining monotone circuit can still read.
  const cache = new Map();
  function cover(value) {
    if (cache.has(value)) return cache.get(value);
    const negative = BigInt((~value & no) >>> flags.length);
    let cells = 0n;
    for (let i=0; i<flags.length; i++) {
      if (value & (1<<i)) cells |= negative << BigInt(i*nNeg);
    }
    if (cache.size<60000) cache.set(value,cells);
    return cells;
  }

  const covers = values.map(cover), needed = cover(yes);
  const first = masks.map((_,a) => masks.map((_,b) => transforms.every(p => {
    const x = Math.min(p[a],p[b]), y = Math.max(p[a],p[b]);
    return y>b || (y===b && x>=a);
  })));
  const gates = [];
  let states = 0, solutions = 0, starTrees = 0;
  function visit(live, depth, spare, lastB, lastA) {
    states++;
    if (live.length===1) {
      const out = live[0];
      if (values[out]===yes) {
        assert.equal(depth,core.optimum);
        solutions++;
        if (isStarTree(core,gates,depth,out)) starTrees++;
      }
      return;
    }
    if (depth===limit) return;
    const out = width+depth;
    for (let bi=1; bi<live.length; bi++) {
      const b = live[bi];
      if (b<lastB) continue;
      for (let ai=0; ai<bi; ai++) {
        const a = live[ai];
        if ((b===lastB && a<lastA) || (depth===0 && !first[a][b])) continue;
        let other = 0n;
        for (const w of live) if (w!==a && w!==b) other |= covers[w];
        for (const isOr of [false,true]) {
          const v = isOr ? values[a]|values[b] : values[a]&values[b];
          if (!(v&yes) || !(~v&no)) continue;
          // An OR agreeing with one input on every positive can be bypassed.
          // Dually, an AND agreeing on the negatives can be bypassed.
          const side = isOr ? yes : no;
          if ((values[a]&side)===(v&side) || (values[b]&side)===(v&side)) continue;
          let duplicate = false;
          for (let i=0; i<out; i++) if (values[i]===v) {duplicate=true; break;}
          if (duplicate) continue;
          values[out] = v;
          covers[out] = cover(v);
          const base = other | covers[out];
          for (let keep=0; keep<4; keep++) {
            const cost = (keep&1)+(keep>>1);
            if (cost>spare) continue;
            if ((base | (keep&1 ? covers[a] : 0n) | (keep&2 ? covers[b] : 0n)) !== needed) continue;
            const next = live.filter(w => (w!==a || (keep&1)) && (w!==b || (keep&2)));
            next.push(out);
            gates[depth] = [isOr,a,b];
            visit(next,depth+1,spare-cost,b,a);
          }
        }
      }
    }
  }
  visit(masks.map((_,i)=>i),0,limit-width+1,-1,-1);
  return {states,solutions,starTrees};
}

console.log("Fano geometries", geometry());
for (const [shape,helpers,count] of [["theta",0,45],["k4",0,405],["k4",1,0],["k4",2,0],["k4",3,0]]) {
  const core = makeCore(shape,helpers);
  const lower = enumerate(core,core.optimum-1);
  assert.equal(lower.solutions,0);
  if (shape==="k4") assert.equal(lower.states,[169899,105666,35706,8409][helpers]);
  const result = enumerate(core,core.optimum);
  assert.equal(result.solutions,count);
  assert.equal(result.starTrees,count);
  console.log(shape,helpers,"helpers",result);
}
