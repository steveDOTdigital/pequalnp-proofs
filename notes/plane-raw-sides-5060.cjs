// Finite checks for L-meta-5060. Run with node; no external dependencies.
"use strict";
const assert = require("node:assert/strict");

const labels = Array.from({ length: 21 }, (_, i) => i);
const differences = [0, 5, 7, 17, 20];
const mask = indices => indices.reduce((bits, i) => bits | (1 << i), 0);
const pointLines = labels.map(i => mask(differences.map(d => (i + d) % 21)));
const linePoints = labels.map(j => mask(differences.map(d => (j + 21 - d) % 21)));
const members = bits => labels.filter(i => bits & (1 << i));
const join = (i, j) => {
  const choices = members(pointLines[i] & pointLines[j]);
  assert.equal(choices.length, 1);
  return choices[0];
};

// Each permutation is checked against the incidence table before it is used.
const generators = [[6,16,15,17,3,10,1,4,11,20,0,12,9,13,18,8,2,19,5,7,14],
  [16,3,8,17,18,1,14,10,19,4,5,15,7,20,2,9,6,12,13,0,11],
  [5,3,20,19,11,15,2,18,4,17,16,8,7,9,10,0,14,13,12,1,6],
  [11,18,16,7,19,6,12,17,9,15,10,20,14,8,1,2,13,3,5,4,0],
  [0,14,10,7,4,5,6,17,18,9,13,12,15,2,16,11,1,3,20,19,8]];
function image(bits, permutation) {
  let result = 0;
  while (bits) {
    const low = bits & -bits;
    result |= 1 << permutation[31 - Math.clz32(low)];
    bits ^= low;
  }
  return result;
}
for (const permutation of generators) {
  assert.deepEqual([...permutation].sort((a, b) => a - b), labels);
  assert(linePoints.every(line => linePoints.includes(image(line, permutation))));
}

function count(bits) {
  let n = 0;
  for (; bits; bits &= bits - 1) n++;
  return n;
}

function pureGroupOrbits() {
  const seen = new Uint8Array(1 << 21);
  const representatives = Array.from({ length: 8 }, () => []);
  const totals = Array(8).fill(0);
  for (let bits = 1; bits < seen.length; bits++) {
    const size = count(bits);
    if (size > 7 || seen[bits]) continue;
    const queue = [bits];
    seen[bits] = 1;
    for (let i = 0; i < queue.length; i++) {
      for (const g of generators) {
        const next = image(queue[i], g);
        if (seen[next]) continue;
        seen[next] = 1;
        queue.push(next);
      }
    }
    totals[size] += queue.length;
    representatives[size].push(bits);
  }
  assert.deepEqual(totals.slice(1), [21, 210, 1330, 5985, 20349, 54264, 116280]);
  return representatives;
}

// On one pure group, a part is either one simple vertex or the members
// using one extra mixed side. Bits index vertices within the pure group.
function pureGroupProfiles(group) {
  const vertices = members(group);
  const full = (1 << vertices.length) - 1;
  const lines = linePoints.map(line =>
    mask(vertices.flatMap((p, i) => (line & (1 << p)) ? [i] : [])));
  const cache = new Map();
  const profiles = new Set();

  function lineUses(part, simple) {
    const key = 2 * part + Number(simple);
    if (cache.has(key)) return cache.get(key);
    const points = members(part);
    const result = [];
    const seen = new Set();
    for (const extra of simple ? [-1] : labels) {
      const extraHits = extra < 0 ? 0 : lines[extra];
      const choices = points.map(v => labels.filter(t => {
        const others = ~(1 << v);
        return !(part & others & ~lines[t]) &&
               !(full & others & ~(lines[t] | extraHits));
      }));
      function choose(i, once, twice) {
        if (i === choices.length) {
          const code = once * (1 << 21) + twice;
          if (!seen.has(code)) result.push([once, twice]);
          seen.add(code);
          return;
        }
        for (const t of choices[i]) {
          const bit = 1 << t;
          if (!(bit & twice)) choose(i + 1, once | bit, twice | (once & bit));
        }
      }
      choose(0, extra < 0 ? 0 : 1 << extra, 0);
    }
    cache.set(key, result);
    return result;
  }

  function check(parts) {
    const profile = parts.map(p => p.simple ? 0 : count(p.bits))
                         .sort((a, b) => a - b).join("");
    if (profiles.has(profile)) return;
    const choices = parts.map(p => lineUses(p.bits, p.simple))
                         .sort((a, b) => a.length - b.length);
    function compatible(i, once, twice) {
      if (i === choices.length) return true;
      for (const [used, doubled] of choices[i]) {
        if (!(once & doubled) && !(twice & used) &&
            compatible(i + 1, once | used, twice | doubled | (once & used))) return true;
      }
      return false;
    }
    if (compatible(0, 0, 0)) profiles.add(profile);
  }

  function partition(i, parts) {
    if (i === vertices.length) return check(parts);
    const bit = 1 << i;
    for (const part of parts) {
      if (part.simple || count(part.bits) === 3) continue;
      part.bits |= bit;
      partition(i + 1, parts);
      part.bits ^= bit;
    }
    for (const simple of [true, false]) {
      parts.push({ bits: bit, simple });
      partition(i + 1, parts);
      parts.pop();
    }
  }
  partition(0, []);
  return profiles;
}

function countCoreSizes(profiles) {
  const memo = new Map();
  function pack(k, pure, room) {
    if (!k) return true;
    if (!pure || k > 6 * pure) return false;
    const key = [k, pure, ...room].join(",");
    if (memo.has(key)) return memo.get(key);
    for (let size = Math.min(k, 6); size > 0; size--) {
      for (const profile of profiles[size]) {
        const jobs = [...profile].map(Number).filter(Boolean);
        if (jobs.length > room.length) continue;
        function place(i, occupied) {
          if (i === jobs.length) {
            return pack(k - size, pure - 1, [...room].sort((a, b) => a - b));
          }
          for (let j = 0; j < room.length; j++) {
            if ((occupied & (1 << j)) || room[j] < jobs[i]) continue;
            room[j] -= jobs[i];
            const ok = place(i + 1, occupied | (1 << j));
            room[j] += jobs[i];
            if (ok) return true;
          }
          return false;
        }
        if (place(0, 0)) {
          memo.set(key, true);
          return true;
        }
      }
    }
    memo.set(key, false);
    return false;
  }

  const survivors = [];
  for (let k = 2; k <= 28; k++) {
    for (let p = Math.ceil(k / 2); p <= Math.min(21, k - 1); p++) {
      const l = k - p;
      for (let mixed = p; mixed + 2 <= k - 4; mixed++) {
        for (let a = 1; mixed + a + 1 <= k - 4; a++) {
          for (let b = 1; mixed + a + b <= k - 4; b++) {
            if (pack(p, a, Array(mixed - p).fill(3)) &&
                pack(l, b, Array(mixed - l).fill(3))) survivors.push([p,l,mixed,a,b]);
          }
        }
      }
    }
  }
  return survivors;
}

function enumerateFourTriangles(visit) {
  const triangles = [], index = new Map();
  for (let a = 0; a < 21; a++) for (let b = a + 1; b < 21; b++) {
    for (let c = b + 1; c < 21; c++) {
      const p = [a, b, c], l = [join(b, c), join(a, c), join(a, b)];
      if (new Set(l).size !== 3) continue;
      index.set(mask(p), triangles.length);
      triangles.push({ p, l, points: mask(p), lines: mask(l) });
    }
  }
  const mapTriangle = (i, g) => index.get(image(triangles[i].points, g));
  const compose = (f, g) => g.map(i => f[i]);
  const inverse = g => {
    const result = [];
    g.forEach((x, i) => result[x] = i);
    return result;
  };

  // Fix the first triangle. From each path taking it to another triangle,
  // a generator edge and a return path give a certified stabilizing symmetry.
  const orbit = [0], mapping = new Map([[0, labels]]), stabilizers = new Map();
  for (let i = 0; i < orbit.length; i++) {
    const t = orbit[i];
    for (const g of generators) {
      const next = mapTriangle(t, g), through = compose(g, mapping.get(t));
      if (!mapping.has(next)) {
        orbit.push(next);
        mapping.set(next, through);
      }
      const fixed = compose(inverse(mapping.get(next)), through);
      assert.equal(mapTriangle(0, fixed), 0);
      stabilizers.set(fixed.join(","), fixed);
    }
  }
  assert.equal(triangles.length, 1120);
  assert.equal(orbit.length, triangles.length);
  const actions = [...stabilizers.values()].map(g => triangles.map((_, i) => mapTriangle(i, g)));
  const levels = [0, 0, 0, 0, 0];
  function extend(selected, pm, lm, symmetries) {
    levels[selected.length]++;
    if (selected.length === 4) return visit(selected.map(i => triangles[i]));
    const seen = new Set();
    triangles.forEach((t, i) => {
      if (seen.has(i) || (pm & t.points) || (lm & t.lines)) return;
      for (const symmetry of symmetries) seen.add(symmetry[i]);
      extend([...selected, i], pm | t.points, lm | t.lines,
             symmetries.filter(symmetry => symmetry[i] === i));
    });
  }
  extend([0], triangles[0].points, triangles[0].lines, actions);
  return levels;
}

function checkGatePairings(triangles, stats) {
  const p = triangles.flatMap(t => t.p), l = triangles.flatMap(t => t.l);
  const adjacent = p.map(v => l.map(w => Boolean(pointLines[v] & (1 << w))));
  const containing = Array.from({ length: 12 }, () => []);
  for (let i = 0; i < 12; i++) for (let j = i + 1; j < 12; j++) {
    if (!adjacent[i][j] || !adjacent[j][i]) continue;
    for (let k = j + 1; k < 12; k++) {
      if (!adjacent[i][k] || !adjacent[k][i] || !adjacent[j][k] || !adjacent[k][j]) continue;
      const t = [i, j, k];
      for (const v of t) containing[v].push(t);
    }
  }
  function check(lineGroups) {
    stats.layouts++;
    const pointSide = p.map((_, i) => 12 + Math.floor(i / 3));
    const lineSide = [];
    lineGroups.forEach((g, i) => g.forEach(v => lineSide[v] = 16 + i));
    const edges = [];
    for (let i = 0; i < 12; i++) for (let j = 0; j < 12; j++) {
      if (!adjacent[i][j]) continue;
      const choices = [];
      for (const a of [i, pointSide[i]]) for (const b of [j, lineSide[j]]) {
        // Physical operands are distinct and their raw sets are disjoint.
        if (a === b || (a < 12 && b === lineSide[a]) ||
            (b < 12 && a === pointSide[b])) continue;
        choices.push([a, b]);
      }
      edges.push(choices);
    }
    const external = [];
    for (const x of labels) {
      if (!l.includes(x)) {
        const neighbors = p.flatMap((v,i) => pointLines[v] & (1 << x) ? [i] : []);
        if (neighbors.length > 3) external.push([...new Set(neighbors.map(i => pointSide[i]))]);
      }
      if (!p.includes(x)) {
        const neighbors = l.flatMap((v,i) => pointLines[x] & (1 << v) ? [i] : []);
        if (neighbors.length > 3) external.push([...new Set(neighbors.map(i => lineSide[i]))]);
      }
    }

    const partner = new Int8Array(20);
    partner.fill(-1);
    function search(useExterior) {
      let best, least = 5;
      for (const choices of edges) {
        if (choices.some(([a,b]) => partner[a] === b)) continue;
        const available = choices.filter(([a,b]) => partner[a] < 0 && partner[b] < 0);
        if (!available.length) return false;
        if (available.length < least) {
          best = available;
          least = available.length;
        }
      }
      if (!best) return !useExterior || external.every(rows => rows.some(r => partner[r] < 0));
      for (const [a,b] of best) {
        partner[a] = b;
        partner[b] = a;
        const ok = search(useExterior);
        partner[a] = -1;
        partner[b] = -1;
        if (ok) return true;
      }
      return false;
    }
    if (search(false)) {
      stats.inside++;
      if (search(true)) stats.both++;
    }
  }
  function partition(remaining, groups) {
    if (!remaining) return check(groups);
    const first = 31 - Math.clz32(remaining & -remaining);
    for (const t of containing[first]) {
      const bits = mask(t);
      if ((remaining & bits) === bits) partition(remaining ^ bits, [...groups, t]);
    }
  }
  partition((1 << 12) - 1, []);
}

// A shore made entirely of simple triples, or the rigid 13-vertex shore,
// forces each extra side on the opposite shore to serve at most one complex
// vertex. The proof explains why rows containing three cannot be used there.
function forcesSingleExtras(size, mixed, pure) {
  return (mixed === size && size === 3 * pure) ||
         (size === 13 && mixed === 16 && pure === 3);
}
function fitsSingleExtras(size, pure, extra, profiles) {
  if (!size) return true;
  if (!pure) return false;
  for (let h = 1; h <= Math.min(6, size); h++) {
    for (const profile of profiles[h]) {
      if (/[23]/.test(profile)) continue;
      const needed = [...profile].filter(x => x === "1").length;
      if (needed <= extra && fitsSingleExtras(size - h, pure - 1, extra - needed, profiles)) return true;
    }
  }
  return false;
}

// In the 13-vertex shore there are three extra labels. Assign each local
// part to a distinct label, respecting total capacity three at each label.
function thirteenProfiles(profiles) {
  const found = new Set();
  function next(k, groups, largest, room, list) {
    if (!k) {
      found.add(list.join("/"));
      return;
    }
    if (!groups) return;
    for (let h = Math.min(k,largest); h >= 1; h--) for (const profile of profiles[h]) {
      const parts = [...profile].filter(x => x !== "0").map(Number);
      function assign(i, occupied) {
        if (i === parts.length) {
          next(k-h, groups-1, h, room, [...list,profile]);
          return;
        }
        for (let j = 0; j < room.length; j++) {
          if ((occupied & (1 << j)) || room[j] < parts[i]) continue;
          room[j] -= parts[i];
          assign(i+1, occupied | (1 << j));
          room[j] += parts[i];
        }
      }
      assign(0,0);
    }
  }
  next(13,3,6,[3,3,3],[]);
  return [...found];
}

const reps = pureGroupOrbits();
const profiles = reps.map(orbits => {
  const result = new Set();
  for (const bits of orbits) for (const s of pureGroupProfiles(bits)) result.add(s);
  return result;
});
assert.equal(profiles[7].size, 0);
assert.deepEqual([...profiles[6]], ["222"]);
const survivors = countCoreSizes(profiles);
assert.deepEqual(survivors.filter(r => r[0]+r[1] <= 26),
                 [[12,12,12,4,4], [13,13,16,3,3], [15,11,15,5,2]]);
assert.deepEqual(thirteenProfiles(profiles), ["222/0111/000"]);
// Every feasible size-four group supplying a simple member has no line
// containing all four. A six-point group cannot be collinear either.
for (const bits of reps[4]) {
  if (pureGroupProfiles(bits).has("0111")) assert(linePoints.every(line => (line & bits) !== bits));
}
const crossChecked = survivors.filter(([p,l,m,a,b]) =>
  (!forcesSingleExtras(p,m,a) || fitsSingleExtras(l,b,m-l,profiles)) &&
  (!forcesSingleExtras(l,m,b) || fitsSingleExtras(p,a,m-p,profiles)));
assert.deepEqual(crossChecked, [
  [12,12,12,4,4], [14,14,14,5,5], [14,14,16,4,4], [14,14,18,3,3], [15,13,16,5,3]
]);
const stats = { layouts: 0, inside: 0, both: 0 };
const levels = enumerateFourTriangles(tris => checkGatePairings(tris, stats));
assert.deepEqual(levels, [0,1,11,1266,101165]);
assert.deepEqual(stats, { layouts: 101165, inside: 2, both: 0 });
console.log("Pure group representatives by size", reps.map(x => x.length));
console.log("Surviving counts before gate pairing", survivors);
console.log("Four-triangle layouts", stats);
// In the (15,13,16,5,3) case there is one spare point-side label,
// serving at most one complex point. Check all pure-group sizes compatible
// with at most one complex point in total.
const pointSizes = new Set();
function collectFifteen(left, remaining, largest, budget, sizes) {
  if (!left) {
    pointSizes.add(sizes.join(","));
    return;
  }
  if (!remaining) return;
  for (let h = Math.min(6,largest,left); h > 0; h--) {
    for (const profile of profiles[h]) {
      const complex = [...profile].reduce((sum,c) => sum+Number(c), 0);
      if (complex <= budget) collectFifteen(left-h,remaining-1,h,budget-complex,[...sizes,h]);
    }
  }
}
collectFifteen(15,5,6,1,[]);
assert.deepEqual([...pointSizes], ["3,3,3,3,3"]);
// The exterior-edge test excludes the 24 case. The single spare row
// argument in the note excludes the remaining asymmetric case at 28.
console.log("Remaining size-28 counts", crossChecked.filter(r => r[0] === 14 && r[1] === 14));

// Enumerate loads of the extra mixed sides on one fourteen-vertex shore.
// A profile digit counts complex members of one pure group sent to one side.
// A zero denotes one simple member and consumes no extra mixed-side capacity.
function fourteenProfiles(mixedCount, pureCount) {
  const outcomes = new Set();
  const loads = Array(mixedCount - 14).fill(0);
  function collect(left, pureLeft, maximum, groups) {
    if (left === 0) {
      outcomes.add(groups.slice().sort().join("/") + ":" + loads.slice().sort().join(""));
      return;
    }
    if (!pureLeft) return;
    for (let size = Math.min(maximum, left); size > 0; size--) {
      for (const profile of profiles[size]) {
        const parts = [...profile].map(Number).filter(Boolean);
        function place(part, used) {
          if (part === parts.length) {
            collect(left - size, pureLeft - 1, size, [...groups, profile]);
            return;
          }
          for (let row = 0; row < loads.length; row++) {
            if ((used & (1 << row)) || loads[row] + parts[part] > 3) continue;
            loads[row] += parts[part];
            place(part + 1, used | (1 << row));
            loads[row] -= parts[part];
          }
        }
        place(0, 0);
      }
    }
  }
  collect(14, pureCount, 6, []);
  return [...outcomes].sort();
}

assert.deepEqual(fourteenProfiles(16, 4), [
  "000/000/000/23:23", "000/000/001/23:33", "000/000/012/012:33"
]);
const eighteenProfiles = fourteenProfiles(18, 3);
assert(eighteenProfiles.length > 0);
assert.deepEqual([...new Set(eighteenProfiles.map(s => s.split(":")[1]))].sort(), ["2333", "3333"]);
for (const layout of eighteenProfiles) {
  const sizes = layout.split(":")[0].split("/").map(group =>
    [...group].reduce((total, digit) => total + (Number(digit) || 1), 0));
  assert(sizes.every(size => size >= 3));
}
// No group of five having the profile 23 has four points on one line.
const fiveGroups = reps[5].filter(group => pureGroupProfiles(group).has("23"));
assert.equal(fiveGroups.length, 3);
assert.deepEqual(fiveGroups.map(group => Math.max(...linePoints.map(line => count(line & group)))).sort(),
                 [2, 3, 3]);

function commonGatePerComponent(edges) {
  const parent = Array.from({ length: 28 }, (_, index) => index);
  function root(vertex) {
    while (parent[vertex] !== vertex) vertex = parent[vertex];
    return vertex;
  }
  // The two endpoints must use the same internal gate on this incidence.
  for (const edge of edges) {
    if (edge.forcedPoint && edge.forcedLine) parent[root(edge.point)] = root(edge.line + 14);
  }
  const allowed = new Map();
  for (const edge of edges) {
    if (!edge.forcedPoint && !edge.forcedLine) continue;
    const id = root(edge.forcedPoint ? edge.point : edge.line + 14);
    const previous = allowed.get(id);
    const common = previous ? previous.filter(gate => edge.options.includes(gate)) : edge.options;
    if (!common.length) return false;
    allowed.set(id, common);
  }
  return true;
}

// A three-edge path tests propagation of the one-internal-gate constraint.
const pathControl = [[0, 0], [1, 0], [1, 1]].map(([point, line]) =>
  ({ point, line, forcedPoint: true, forcedLine: true, options: [3, 9] }));
assert(commonGatePerComponent(pathControl));
assert(!commonGatePerComponent(pathControl.map((edge, i) =>
  ({ ...edge, options: i === 0 ? [3] : i === 2 ? [9] : edge.options }))));

function checkFourteenMixed() {
  const full = (1 << 21) - 1;
  const seen = new Set();
  const stats = { systems: 0, extensions: 0, layouts: 0, componentPass: 0 };
  const bit = i => 1 << i;

  function testLayout(points, lines, pointGroups, lineGroups, extraPoint, extraLine) {
    stats.layouts++;
    // Sides 0..13 are the matched mixed sides. The other ten are the
    // five pure groups of each shore, with its two-member group last.
    const sides = Array.from({ length: 24 }, () => [0, 0]);
    for (let i = 0; i < 14; i++) sides[i] = [bit(i), bit(i)];
    pointGroups.forEach((group, i) => { sides[14 + i][0] = mask(group); });
    lineGroups.forEach((group, i) => { sides[19 + i][1] = mask(group); });
    const mandatory = sides.map(side => side.slice());
    if (points.includes(extraPoint)) sides[18][0] |= bit(points.indexOf(extraPoint));
    if (lines.includes(extraLine)) sides[23][1] |= bit(lines.indexOf(extraLine));

    const pCore = mask(points), lCore = mask(lines);
    const labelsFor = (vertex, shore) => sides.flatMap((s, i) => s[shore] & bit(vertex) ? [i] : []);
    const pSources = points.map((_, i) => labelsFor(i, 0));
    const lSources = lines.map((_, i) => labelsFor(i, 1));
    // An exterior neighbor other than the optional intersection vertex
    // needs a gate with one side outside these 24 retained sides.
    const forcedPoints = points.map((v, i) =>
      pSources[i].length === 2 && !!(pointLines[v] & ~(lCore | bit(extraLine)) & full));
    const forcedLines = lines.map((v, i) =>
      lSources[i].length === 2 && !!(linePoints[v] & ~(pCore | bit(extraPoint)) & full));

    const edges = [];
    for (let i = 0; i < 14; i++) for (let j = 0; j < 14; j++) {
      if (!(pointLines[points[i]] & bit(lines[j]))) continue;
      const options = [];
      for (const a of pSources[i]) for (const b of lSources[j]) {
        // For disjointness use only mandatory reads. This grants the search
        // both possibilities for an optional read on the two-member side.
        if (a === b || (mandatory[a][0] & mandatory[b][0]) || (mandatory[a][1] & mandatory[b][1])) continue;
        options.push(32 * Math.min(a, b) + Math.max(a, b));
      }
      if (!options.length) return;
      edges.push({ point: i, line: j, forcedPoint: forcedPoints[i], forcedLine: forcedLines[j], options });
    }
    if (commonGatePerComponent(edges)) stats.componentPass++;
  }

  enumerateFourTriangles(triangles => {
    const key = triangles.map(t => t.points).sort((a, b) => a - b).join(",");
    if (seen.has(key)) return;
    seen.add(key);
    stats.systems++;
    const basePoints = triangles.flatMap(t => t.p), baseLines = triangles.flatMap(t => t.l);
    const pointGroups = [[0,1,2], [3,4,5], [6,7,8], [9,10,11], [12,13]];
    const unusedPoints = members(full ^ mask(basePoints)), unusedLines = full ^ mask(baseLines);

    for (let i = 0; i < unusedPoints.length; i++) for (let j = i + 1; j < unusedPoints.length; j++) {
      const u = unusedPoints[i], v = unusedPoints[j];
      const points = [...basePoints, u, v], pointSet = mask(points);
      // All joins inside the four triangles are already core lines. Of the
      // joins inside the two-member side, only join(u,v) can be exterior.
      const exception = join(u, v);
      let required = 0;
      for (const line of members(unusedLines)) {
        const neighbors = count(linePoints[line] & pointSet);
        if (neighbors > 3 && (neighbors > 4 || line !== exception)) required |= bit(line);
      }
      if (count(required) > 2) continue;
      for (const a of members(unusedLines & pointLines[v])) for (const b of members(unusedLines & pointLines[u])) {
        if (a === b || (required & ~(bit(a) | bit(b)))) continue;
        stats.extensions++;
        const lines = [...baseLines, a, b], lineSet = mask(lines);
        const extraPoint = members(linePoints[a] & linePoints[b])[0];
        const overloaded = members(full ^ pointSet).filter(x => count(pointLines[x] & lineSet) > 3);
        if (overloaded.length > 1 || overloaded.some(x => count(pointLines[x] & lineSet) > 4)) continue;
        const mutual = points.map((pt, x) => mask(lines.flatMap((line, y) =>
          x !== y && (pointLines[pt] & bit(line)) && (pointLines[points[y]] & bit(lines[x])) ? [y] : [])));

        // A line group is a clique in the mutual-incidence relation on
        // matched indices. Generate each unordered partition by its least
        // unused index and leave the pair until last in the resulting array.
        function partition(left, triples, pair) {
          if (!left) {
            assert(pair && triples.length === 4);
            const extraLine = join(points[pair[0]], points[pair[1]]);
            testLayout(points, lines, pointGroups, [...triples, pair], extraPoint, extraLine);
            return;
          }
          const first = 31 - Math.clz32(left & -left), rest = left ^ bit(first);
          for (const second of members(rest & mutual[first])) {
            const others = rest ^ bit(second);
            if (!pair && (!overloaded.length ||
                (linePoints[lines[first]] & linePoints[lines[second]] & bit(overloaded[0])))) {
              partition(others, triples, [first, second]);
            }
            if (triples.length < 4) for (const third of members(others & mutual[first] & mutual[second])) {
              if (third > second) partition(others ^ bit(third), [...triples, [first, second, third]], pair);
            }
          }
        }
        partition((1 << 14) - 1, [], null);
      }
    }
  });
  return stats;
}
const fourteen = checkFourteenMixed();
assert.deepEqual(fourteen, { systems: 68624, extensions: 2781088, layouts: 1245674, componentPass: 0 });
console.log("Fourteen mixed sides at 28 variables", fourteen);

