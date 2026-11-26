// Exact minimum formula leaves for every subset of Petersen edges away from zero.
// Run with node notes/petersen-marker-formulas.mjs.
import assert from "node:assert/strict";

const edges = [6, 12, 24, 66, 132, 160, 264, 288, 320, 528, 576, 640];
const cold = [50, 104, 116, 138, 208, 276, 402, 548, 554, 770];
const rowCount = 1 << edges.length;
const colCount = 1 << cold.length;

function splits(mask) {
  // Retain exactly one member of each unordered nonempty bipartition.
  const result = [];
  for (let part = (mask - 1) & mask; part > (mask ^ part); part = (part - 1) & mask) {
    result.push(part);
  }
  return result;
}

const common = new Uint16Array(rowCount);
const forbidden = new Uint16Array(colCount);
const weight = new Uint8Array(rowCount);
common[0] = 1022;
for (let mask = 1; mask < rowCount; ++mask) {
  const bit = mask & -mask;
  common[mask] = common[mask ^ bit] & edges[31 - Math.clz32(bit)];
  weight[mask] = weight[mask ^ bit] + 1;
}
for (let mask = 1; mask < colCount; ++mask) {
  const bit = mask & -mask;
  forbidden[mask] = forbidden[mask ^ bit] | cold[31 - Math.clz32(bit)];
}

const cut = Array.from({ length: rowCount }, (_, mask) => splits(mask));
const cost = new Uint8Array(rowCount * colCount);
let proved = 0;
for (let positives = 1; positives < rowCount; ++positives) {
  const offset = positives * colCount;
  for (let negatives = 1; negatives < colCount; ++negatives) {
    if (common[positives] & ~forbidden[negatives]) {
      cost[offset + negatives] = 1;
      continue;
    }
    // No rectangular subproblem needs more than the full star formula's 17 leaves.
    let best = 255;
    for (const left of cut[positives]) {
      const right = positives ^ left;
      best = Math.min(best, cost[left * colCount + negatives] + cost[right * colCount + negatives]);
      if (best === 2) break;
    }
    if (best > 2) {
      for (const left of cut[negatives]) {
        const right = negatives ^ left;
        best = Math.min(best, cost[offset + left] + cost[offset + right]);
        if (best === 2) break;
      }
    }
    assert.ok(best <= 17);
    cost[offset + negatives] = best;
  }
  let cover = 10;
  for (let vertices = 0; vertices < 1024; vertices += 2) {
    if (weight[vertices] < cover &&
        edges.every((edge, i) => !(positives & (1 << i)) || (edge & vertices))) {
      cover = weight[vertices];
    }
  }
  assert.equal(cost[offset + colCount - 1], weight[positives] + cover);
  ++proved;
}
console.log(`${proved} nonempty edge families checked; the full 12-edge family needs ${cost.at(-1)} leaves.`);
