// Exact synthesis of the read-once-data multiplexer. Run directly with Node.
"use strict";
const assert = require("node:assert/strict");
const { raw, standardControl, minimumGuards, symmetries } = require("./multiplexer-9939.cjs");
const size = Array.from({ length: 256 }, (_, bits) => bits.toString(2).replaceAll("0","").length);
const gatesToAdd = (a,b,set) => { set.add(a & b); set.add(a | b); };

function librariesByCost() {
  const maps = symmetries(), visited = new Set();
  const groups = Array.from({ length: 9 }, () => new Map());
  const pairs = [];
  for (let i=0; i<8; i++) for (let j=0; j<8; j++)
    if (i !== j && (i & j) === i) pairs.push([i,j]);
  const allPairs = (1 << pairs.length) - 1;
  const separates = Array.from({ length: 256 }, (_,g) => pairs.reduce((bits,[i,j],k) =>
    (g & (1<<i)) && !(g & (1<<j)) ? bits | (1<<k) : bits, 0));
  const serialize = e => String.fromCharCode(...e);
  function canonical(e) {
    let best = serialize(e);
    for (const m of maps) {
      const key = serialize(e.map(g => m[g]).sort((a,b) => a-b));
      if (key < best) best = key;
    }
    return best;
  }
  function visit(extra, covered) {
    const key = serialize(extra);
    if (visited.has(key)) return;
    visited.add(key);
    const h = extra.length, rep = canonical(extra);
    if (h === 7 && rep !== key) return;
    if (h < 7 || covered === allPairs) groups[h].set(rep, extra);
    const available = raw.concat(extra), candidates = new Set();
    for (let i=0; i<available.length; i++) {
      candidates.add(255 ^ available[i]);
      // A final monotone operation cannot separate two still-comparable
      // address rows. At cost eight only trees without a data NOT can fit.
      if (h < 7 || covered === allPairs)
        for (let j=0; j<i; j++) gatesToAdd(available[i], available[j], candidates);
    }
    for (const g of candidates) {
      if (g === 0 || g === 255 || available.includes(g)) continue;
      const nextCovered = covered | separates[g];
      if (h === 7 && nextCovered !== allPairs) continue;
      const next = extra.concat(g).sort((a,b) => a-b);
      if (h === 7) groups[8].set(canonical(next), next);
      else visit(next, nextCovered);
    }
  }
  visit([],0);
  assert.equal(visited.size, 1543109);
  return groups.map(g => [...g.values()]);
}

// Compile "this library needs at most b guards" into Boolean operations
// on tests for available address predicates. Multiple libraries can then
// be checked in one 32-bit word without changing the recurrence.
function compileBudget(budget) {
  const nodes = [null,null], memo = new Map(), features = new Map(), joins = new Map();
  function feature(on,off) {
    const fits = g => (g & on) === on && !(g & off);
    if (raw.some(fits)) return 1;
    const key = (on<<8) | off;
    if (!features.has(key)) {
      features.set(key,nodes.length);
      nodes.push({ allowed: Array.from({length:256},(_,g)=>g).filter(fits) });
    }
    return features.get(key);
  }
  function join(isOr, children) {
    const absorbing = Number(isOr), neutral = 1-absorbing;
    if (children.includes(absorbing)) return absorbing;
    const ids = [...new Set(children.filter(x=>x!==neutral))].sort((a,b)=>a-b);
    if (!ids.length) return neutral;
    if (ids.length===1) return ids[0];
    const key = Number(isOr)+":"+ids.join(",");
    if (!joins.has(key)) {
      joins.set(key,nodes.length);
      nodes.push({ isOr, ids });
    }
    return joins.get(key);
  }
  const lower = (u,p,n) => size[u]===1 ? Number(Boolean(p))+Number(Boolean(n)) : size[u];
  function solve(u,p,n,b) {
    if (b < lower(u,p,n)) return 0;
    if (size[u]===1 && !p && !n) return 1;
    const key = (((u<<16)|(p<<8)|n)*16)+b;
    if (memo.has(key)) return memo.get(key);
    const candidates = [];
    function both(left,right) {
      if (left && right) candidates.push(join(false,[left,right]));
    }
    // Enumerate the exact subset of required constants left after a clamp.
    // The guard must have the indicated value on each constrained address.
    if (b) {
      for (let t=(n-1)&n; n; t=(t-1)&n) {
        const child=solve(u,p,t,b-1);
        if (child) both(feature(u|p|t,n^t),child);
        if (!t) break;
      }
      for (let t=(p-1)&p; p; t=(t-1)&p) {
        const child=solve(u,t,n,b-1);
        if (child) both(feature(p^t,u|n|t),child);
        if (!t) break;
      }
    }
    function split(a,pa,na,d,pd,nd) {
      for (let x=lower(a,pa,na); x<=b-lower(d,pd,nd); x++) {
        const left=solve(a,pa,na,x);
        if (left) both(left,solve(d,pd,nd,b-x));
      }
    }
    for (let a=(u-1)&u; a; a=(a-1)&u) {
      const d=u^a;
      if (a>d) continue;
      for (let s=p;;s=(s-1)&p) {
        split(a,s,n|d,d,p^s,n|a);
        if (!s) break;
      }
      for (let s=n;;s=(s-1)&n) {
        split(a,p|d,s,d,p|a,n^s);
        if (!s) break;
      }
    }
    const result=join(true,candidates);
    memo.set(key,result);
    return result;
  }
  const root=solve(255,0,0,budget);
  return {nodes,root};
}

function select(compiled, libraries, transform) {
  const selected = [];
  for (let i=0; i<libraries.length; i+=32) {
    const batch=libraries.slice(i,i+32), present=new Int32Array(256);
    batch.forEach((lib,j)=>transform(lib).forEach(g=>present[g]|=1<<j));
    const values=new Int32Array(compiled.nodes.length);
    values[1]=-1;
    for (let k=2; k<values.length; k++) {
      const node=compiled.nodes[k];
      let value=0;
      if (node.allowed) {
        for (const g of node.allowed) value |= present[g];
      } else if (node.isOr) {
        for (const child of node.ids) value |= values[child];
      } else {
        value=-1;
        for (const child of node.ids) value &= values[child];
      }
      values[k]=value;
    }
    batch.forEach((lib,j)=>{ if (values[compiled.root] & (1<<j)) selected.push(lib); });
  }
  return selected;
}

// For the survivors of the complemented-library relaxation, allow actual
// NOT gates on data. Consecutive NOTs cancel, so the root either has no NOT
// or has one above a root of the first kind. The child's constants swap.
function exactSigned(library) {
  const memo=new Map();
  function solve(u,p,n,negative) {
    return Math.min(withoutRootNot(u,p,n,negative),1+withoutRootNot(u,n,p,!negative));
  }
  function withoutRootNot(u,p,n,negative) {
    const key=(u<<17)|(p<<9)|(n<<1)|Number(negative);
    if (memo.has(key)) return memo.get(key);
    let best=!negative && !p && !n && size[u]===1 ? 0 : 60;
    for (const g of library) {
      if (!((u|p)&~g) && (n&~g)) best=Math.min(best,1+solve(u,p,n&g,negative));
      if (!((u|n)&g) && (p&g)) best=Math.min(best,1+solve(u,p&~g,n,negative));
    }
    for (let a=(u-1)&u; a; a=(a-1)&u) {
      const b=u^a;
      if (a>b) continue;
      for (let s=p;;s=(s-1)&p) {
        best=Math.min(best,solve(a,s,n|b,negative)+solve(b,p^s,n|a,negative));
        if (!s) break;
      }
      for (let s=n;;s=(s-1)&n) {
        best=Math.min(best,solve(a,p|b,s,negative)+solve(b,p|a,n^s,negative));
        if (!s) break;
      }
    }
    memo.set(key,best);
    return best;
  }
  return solve(255,0,0,false);
}

standardControl();
const groups=librariesByCost();
assert.deepEqual(groups.map(x=>x.length), [1,2,10,54,324,2149,15298,5286,58828]);
const exactEight=compileBudget(8), exactNine=compileBudget(9);
const id = a=>a;
const freeComplements = extra => [...new Set([85,51,15,...extra,...extra.map(g=>255^g)])];
// Fully decoded addresses are a positive control for the tightest test.
const decoded = [Array.from({length:8},(_,i)=>1<<i)];
assert.equal(select(exactEight,decoded,id).length,1);
assert.equal(select(exactEight,[[85,51,15]],id).length,0);
assert.equal(select(exactNine,groups[7],id).length,0);
assert.equal(select(exactEight,groups[8],id).length,0);

// With a NOT on data, at least two such NOTs occur. Pushing them to the
// leaves for a lower bound gives the complemented address library for free.
const remaining=[];
for (let h=0; h<=6; h++) {
  const budget=14-h;
  const survivors=budget===8 ? select(exactEight,groups[h],freeComplements)
                 : budget===9 ? select(exactNine,groups[h],freeComplements)
                 : groups[h].filter(e=>minimumGuards(raw.concat(freeComplements(e)))<=budget);
  for (const extra of survivors) {
    const controls=exactSigned(raw.concat(extra));
    assert(7+h+controls>23);
    remaining.push({h,extra,controls});
  }
}
assert.deepEqual(remaining.map(r=>r.h),[0,2,2]);
console.log("Address-library representatives by cost",groups.map(x=>x.length));
console.log("Data-NOT survivors of the relaxation",remaining);
console.log("No read-once-data circuit with 23 gates; the 24-gate control passed.");
