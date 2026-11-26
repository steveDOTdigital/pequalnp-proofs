// Restricted exact synthesis for the eight-way multiplexer in L-meta-9939.
// Run with node. All address predicates are represented by eight-bit tables.
"use strict";
const assert = require("node:assert/strict");
const raw = [170, 204, 240];

function standardControl() {
  const gates = [];
  function gate(op, a, b) {
    gates.push([op, a, b]);
    return 10 + gates.length;
  }
  const neg = [0,1,2].map(i => gate("not", i));
  let level = Array.from({ length: 8 }, (_, i) => 3 + i);
  for (let i = 0; i < 3; i++) {
    const next = [];
    for (let j = 0; j < level.length; j += 2) {
      next.push(gate("or", gate("and", neg[i], level[j]),
                          gate("and", i, level[j+1])));
    }
    level = next;
  }
  assert.equal(gates.length, 24);
  for (let row = 0; row < 2048; row++) {
    const wire = Array.from({ length: 11 }, (_, i) => Boolean(row & (1 << i)));
    for (const [op, a, b] of gates) {
      wire.push(op === "not" ? !wire[a] : op === "and" ? wire[a] && wire[b] : wire[a] || wire[b]);
    }
    assert.equal(wire[level[0]], wire[3 + (row & 7)]);
  }
}

// Each subproblem describes a tree on the data leaves indexed by selected.
// Addresses in ones or zeros require a constant. The other rows are free.
function minimumGuards(library) {
  const memo = new Map();
  function solve(selected, ones, zeros) {
    if (!ones && !zeros && !(selected & (selected-1))) return 0;
    const key = (selected << 16) | (ones << 8) | zeros;
    if (memo.has(key)) return memo.get(key);
    let best = 60; // Above the budget of interest.
    for (const g of library) {
      if (!((selected|ones) & ~g) && (zeros & ~g))
        best = Math.min(best, 1 + solve(selected, ones, zeros & g));
      if (!((selected|zeros) & g) && (ones & g))
        best = Math.min(best, 1 + solve(selected, ones & ~g, zeros));
    }
    for (let a = (selected-1) & selected; a; a = (a-1) & selected) {
      const b = selected ^ a;
      if (a > b) continue;
      // OR: each branch is zero while its sibling supplies selected data.
      for (let s = ones;; s = (s-1) & ones) {
        best = Math.min(best, solve(a, s, zeros|b) + solve(b, ones^s, zeros|a));
        if (!s) break;
      }
      // AND: the sibling's neutral value is one.
      for (let s = zeros;; s = (s-1) & zeros) {
        best = Math.min(best, solve(a, ones|b, s) + solve(b, ones|a, zeros^s));
        if (!s) break;
      }
    }
    memo.set(key,best);
    return best;
  }
  return solve(255,0,0);
}

const addresses = Array.from({ length: 8 }, (_, i) => i);
function antichain(library) {
  return addresses.every(i => addresses.every(j =>
    i === j || library.some(g => (g & (1<<i)) && !(g & (1<<j)))));
}

function enumerateAddressLibraries(limit) {
  const seen = new Set(), usable = [];
  function visit(extra) {
    const key = String.fromCharCode(...extra);
    if (seen.has(key)) return;
    seen.add(key);
    const all = raw.concat(extra);
    if (antichain(all)) usable.push(extra);
    if (extra.length === limit) return;
    const candidates = new Set();
    all.forEach((a,i) => {
      candidates.add(255 ^ a);
      for (let j = 0; j < i; j++) {
        candidates.add(a & all[j]);
        candidates.add(a | all[j]);
      }
    });
    for (const g of candidates) {
      if (g && g !== 255 && !all.includes(g)) visit(extra.concat(g).sort((a,b) => a-b));
    }
  }
  visit([]);
  return { count: seen.size, usable };
}

// Address-coordinate permutations preserve the source set. Simultaneously
// reversing every address bit and dualizing every predicate does so as well.
function symmetries() {
  const maps = [];
  for (const p of [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]) {
    for (const dual of [false,true]) {
      maps.push(Array.from({ length: 256 }, (_,g) => addresses.reduce((m,i) => {
        const row = p.reduce((v,j,k) => v | (((i>>j)&1)<<k), 0) ^ (dual ? 7 : 0);
        return m | ((((g>>row)&1) ^ Number(dual)) << i);
      }, 0)));
    }
  }
  return maps;
}

module.exports = { raw, standardControl, minimumGuards, enumerateAddressLibraries, symmetries };

if (require.main === module) {
  standardControl();
  const libraries = enumerateAddressLibraries(6);
  assert.equal(libraries.count, 202322);
  const maps = symmetries(), cache = new Map(), totals = {};
  for (const extra of libraries.usable) {
    const key = maps.map(map =>
      String.fromCharCode(...extra.map(g => map[g]).sort((a,b) => a-b))).sort()[0];
    if (!cache.has(key)) cache.set(key, minimumGuards(raw.concat(extra)));
    const value = cache.get(key);
    const row = totals[extra.length] ??= {};
    row[value] = (row[value] ?? 0) + 1;
  }
  assert.deepEqual(totals, {
    3: {14:1}, 4: {14:24}, 5: {12:39,13:12,14:324},
    6: {12:1128,13:2164,14:1648}
  });
  console.log("24-gate control: all 2048 rows passed.");
  console.log("Extra address gates, guard counts and library multiplicities:", totals);
}
