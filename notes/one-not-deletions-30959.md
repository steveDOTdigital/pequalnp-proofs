# A single NOT cannot shorten the eight-input graph in L-meta-30959

The posted graph has a monotone fan-in-two circuit of length 14. Every circuit for it that contains a NOT gate has length at least 14. A circuit containing only AND and OR is already a valid replacement for itself. This proves [the posted replacement claim](https://pequalnp.com/lemma#L-meta-30959).

## Construction

Take the OR of these five products, with input labels as posted.

- `(0 OR 3 OR 2) AND (5 OR 6 OR 7)`
- `0 AND 3`
- `5 AND 6`
- `1 AND 4`
- `7 AND (1 OR 4)`

There are five internal ORs, five ANDs and four ORs combining the products. The concrete gate list below passed Lean evaluation against the posted list-indexed predicate on all 256 inputs.

## A restriction that needs 12 binary gates

Set input 2 to false. Relabel the remaining inputs in their original order, so the special vertex originally numbered 7 becomes 6. The replay checks that pinning **any of the other six vertices** to false makes a six-input problem requiring at least ten binary gates, even with free constants and free inversions. Call the six vertices with this verified property the six deletion cases.

Suppose the seven-input restriction had a signed circuit with at most eleven binary gates. Use a minimal such circuit, remove unused gates and simplify constants or repeated operands. Represent OR by a signed AND with free complements. Its first paid gate combines two distinct raw inputs up to sign. At least one operand belongs to the six deletion cases.

For any operand from the six deletion cases, pinning it to false must save at most one paid gate because the six-input function still needs ten. The first gate therefore passes the other operand up to complement on this slice. If the first gate became constant, its first downstream paid user would simplify too. Such a downstream user exists because the restricted target is nonconstant. Furthermore the operand can have only one paid reader. Pinning it would simplify each direct paid reader if there were two.

If both first operands are in the six deletion cases, the first gate is their OR up to complement and both inputs disappear from subsequent gates. The table has two rows with equal OR and equal remaining inputs for which the target differs. The replay verifies such a pair for each possible choice of operands.

If one operand is the special vertex, choose the value of that vertex for which the first signed AND is constant. The first gate is the only reader of the other operand. The graph still depends on that operand on each of the two special-vertex slices, as the replay verifies. Either kind of first gate contradicts the target, so the seven-input restriction needs at least twelve paid gates.

## Transfer to the posted statement

The project evaluator interprets missing wires as false and supports gates of arity at most two. Removing copies and constants and permitting signs freely gives a signed circuit with at most as many paid gates as the original AND/OR count. Pinning input 2 to false saves at least one of those paid gates. Input 2 is essential in the full function and the restricted function is nonconstant, so if no gate was already saved in normalization, some paid gate directly on the input's route to the output simplifies under the pin. Lean verified this strict decrease using the project evaluator and the existing signed-slice compiler.

The lower bound of twelve on the restricted paid count now gives at least thirteen original AND/OR gates. A circuit containing a NOT thus has at least fourteen gates. The monotone witness supplies the required replacement. The six-input exclusions are independently reproducible below. This note records the completed mathematical argument and the checked Lean components.

## Replay

The search tracks the wires live across a gate boundary in a minimum circuit. Every remaining gate can reduce the live wire count by at most one. Two rows indistinguishable on the live wires must receive the same final output. The packed test tracks every pair of true and false rows in parallel. The transition enumerates each pair of distinct signed inputs and each possible choice of operands to retain. Constants and a gate whose output repeats an existing wire up to sign can be eliminated from a minimum circuit. The signed circuits use all six inputs in these deletion cases because every vertex still belongs to an edge. The optional proof witnesses are unnecessary for exclusions. The positive and negative triangle controls test both verdict paths.

Run the following as a plain JavaScript file using Node.js.

```js
const assert = (ok, reason) => { if (!ok) throw new Error(reason); };

function signedSearch(width, target, budget) {
  const rows = 1 << width, step = BigInt(rows), mask = (1n << step) - 1n;
  const raw = Array(width).fill(0n);
  const negatives = [];
  for (let row = 0; row < rows; row++) {
    const bit = 1n << BigInt(row);
    if (!(bit & target)) negatives.push(bit);
    for (let i = 0; i < width; i++) if (row & (1 << i)) raw[i] |= bit;
  }
  const shifts = negatives.map((_, index) => step * BigInt(index));
  const laneBase = shifts.reduce((m, shift) => m | (1n << shift), 0n);
  const allPairs = target * laneBase;
  const wireCache = new Map();
  const columns = [];
  function idOf(word) {
    const known = wireCache.get(word);
    if (known !== undefined) return known;
    let negativeHighLanes = 0n;
    for (let i = 0; i < negatives.length; i++) {
      if (word & negatives[i]) negativeHighLanes |= 1n << shifts[i];
    }
    const sameOnPairs = allPairs & ~((word * laneBase) ^ (mask * negativeHighLanes));
    const id = columns.length;
    columns.push({word, sameOnPairs});
    wireCache.set(word, id);
    return id;
  }
  const rawIds = raw.map(idOf);
  const seen = Array.from({length: budget + 1}, () => new Set());
  let checked = 0;
  function search(wires, remaining) {
    if (remaining === 0 || wires.length > remaining + 1) return false;
    wires.sort((a,b) => a - b);
    let conflicts = allPairs;
    for (const w of wires) {
      conflicts &= columns[w].sameOnPairs;
      if (!conflicts) break;
    }
    checked++;
    if (conflicts) return false;
    const key = wires.join(",");
    const known = seen[remaining];
    if (known.has(key)) return false;
    known.add(key);
    for (let j = 1; j < wires.length; j++) for (let i = 0; i < j; i++) {
      const ai = wires[i], bi = wires[j], a = columns[ai].word, b = columns[bi].word;
      const other = wires.filter(w => w !== ai && w !== bi);
      for (let op = 0; op < 4; op++) {
        const got = ((op & 1) ? (mask ^ a) : a) & ((op & 2) ? (mask ^ b) : b);
        const word = (got & 1n) ? mask ^ got : got;
        if (word === target) {
          return true;
        }
        if (remaining === 1 || !word) continue;
        const id = idOf(word);
        if (wires.includes(id)) continue;
        const next = [...other, id];
        const options = remaining - next.length;
        if (search([...next], remaining - 1) ||
            (options > 0 && (search([...next,ai],remaining-1) || search([...next,bi],remaining-1))) ||
            (options > 1 && search([...next,ai,bi],remaining-1))) {
          return true;
        }
      }
    }
    return false;
  }
  const reached = raw.includes(target) || !target || search(rawIds, budget);
  return {reached, checked};
}

const graph = [[0,3],[1,4],[0,5],[2,5],[3,5],[0,6],[2,6],[3,6],[5,6],[0,7],[1,7],[2,7],[3,7],[4,7]];
const gates = [["or",0,3],["or",8,2],["or",5,6],["or",10,7],["and",9,11],["and",0,3],["and",5,6],["and",1,4],["or",1,4],["and",7,16],["or",12,13],["or",14,18],["or",15,17],["or",19,20]];
const edgeTable = (n, edges) => {
  let answer = 0n;
  for (let r = 0; r < 2 ** n; r++) {
    if (edges.some(([x,y]) => (r & (1 << x)) && (r & (1 << y)))) {
      answer |= 1n << BigInt(r);
    }
  }
  return answer;
};
const omit = (edges, v) => edges.filter(e => !e.includes(v))
  .map(e => e.map(u => u - Number(u > v)));
const full = edgeTable(8, graph);
for (let row = 0; row < 256; row++) {
  const wires = Array.from({length: 8}, (_,i) => Boolean(row & (1 << i)));
  for (const [op, a, b] of gates) wires.push(op === "or" ? wires[a] || wires[b] : wires[a] && wires[b]);
  assert(wires.at(-1) === Boolean(full & (1n << BigInt(row))), "monotone construction");
}
assert(signedSearch(3, 0xe8n, 4).reached, "triangle positive control");
assert(!signedSearch(3, 0xe8n, 3).reached, "triangle negative control");
const restricted = omit(graph, 2);
const table = edgeTable(7, restricted);
const val = row => Boolean(table & (1n << BigInt(row)));
for (let v = 0; v < 6; v++) {
  const result = signedSearch(6, edgeTable(6, omit(restricted, v)), 9);
  assert(!result.reached, "nine-gate exclusion at zero pin " + v);
  console.log("zero pin", v, result.checked);
}
for (let p = 0; p < 6; p++) {
  for (let q = p + 1; q < 6; q++) {
    const b = (1 << p) | (1 << q);
    assert(Array.from({length: 128}, (_,r) => r).some(r => !(r & b) &&
      (val(r | (1 << p)) !== val(r | (1 << q)) || val(r | (1 << p)) !== val(r | b))),
      "an OR of vertices " + p + " and " + q + " must lose information");
  }
  for (const v of [0,1]) {
    assert(Array.from({length: 64}, (_,r) => r | (v << 6)).some(r =>
      !(r & (1 << p)) && val(r) !== val(r | (1 << p))),
      "vertex " + p + " must be essential for special input " + v);
  }
}
console.log("Circuit, six zero-cofactor exclusions and all first-gate obstructions verified.");
```
