const order = 13;
const allPoints = (1 << order) - 1;
const differenceSet = [0, 1, 3, 9];
const omitted = [46,89,114,177,263,356,450,531,553,586,736,780,802,912,1046,1091,1220,1313,1360,1416,1541,1560,2076,2117,2186,2212,2321,2344,2566,2689,3081,3120,3648,4107,4133,4152,4242,4289,4372,4424,4688,4740,5132,5154,5888,6240,6402,7296];

const bitLists = Array.from({length: allPoints + 1}, (_, mask) => {
  const elements = [];
  for (let i = 0; i < order; i++) if (mask & (1 << i)) elements.push(i);
  return elements;
});
const lines = Array.from({length: order}, (_, l) =>
  differenceSet.reduce((mask, offset) => mask | 1 << ((l + offset) % order), 0));
const pencils = Array.from({length: order}, (_, p) =>
  lines.reduce((mask, line, l) => mask | (((line >> p) & 1) << l), 0));

function isCap(mask, blocks) {
  return blocks.every(block => bitLists[mask & block].length <= 2);
}
function exterior(linesMask) {
  const incidentPoints = bitLists[linesMask].reduce((mask, l) => mask | lines[l], 0);
  return allPoints ^ incidentPoints;
}

const triangles = [];
const quadrangles = [];
for (let mask = 0; mask <= allPoints; mask++) {
  const length = bitLists[mask].length;
  if (length !== 3 && length !== 4) continue;
  if (!isCap(mask, pencils)) continue;
  (length === 3 ? triangles : quadrangles).push(mask);
}
const removed = new Set(omitted);
if (removed.size !== omitted.length || omitted.some(q => !quadrangles.includes(q))) {
  throw Error("The omitted quadrangles are invalid or repeated");
}
const kept = quadrangles.filter(q => !removed.has(q));
for (const t of triangles) {
  const supersets = quadrangles.filter(q => (q & t) === t);
  const getRemovedPoint = q => exterior(t) ^ exterior(q);
  const removedPoints = supersets.map(getRemovedPoint);
  if (supersets.length !== 4 || supersets.filter(q => removed.has(q)).length > 1 ||
      new Set(removedPoints).size !== 4 ||
      removedPoints.some(bit => bitLists[bit].length !== 1 || (bit & exterior(t)) !== bit)) {
    throw Error("A triangle does not have the required four extensions");
  }
}
for (const q of kept) {
  if (!isCap(exterior(q), lines)) throw Error("A selected test fails the point cap");
}
let covered = 0;
for (let b = 0; b <= allPoints; b++) {
  if (bitLists[b].length > 3 || !isCap(b, pencils)) continue;
  const alternatives = kept.filter(q => (q & b) === b);
  const allowed = exterior(b);
  for (let a = allowed; ; a = (a - 1) & allowed) {
    if (bitLists[a].length <= 2) {
      covered++;
      if (!alternatives.some(q => (exterior(q) & a) === a)) {
        throw Error("A permitted small negative is uncovered");
      }
    }
    if (a === 0) break;
  }
}
console.log(JSON.stringify({triangles: triangles.length, quadrangles: quadrangles.length,
  omitted: omitted.length, tests: kept.length, coveredSmallNegatives: covered}));