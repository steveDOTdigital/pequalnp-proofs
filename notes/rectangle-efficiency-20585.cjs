/* Biclique efficiency certificate for L-meta-20585. Run with Node 18+. */
const source = "https://data.pequalnp.com/data/lemma/L-meta-20585.d22fa7045cab.json";
const all = (1n << 128n) - 1n;

function population(x) {
  x -= (x >>> 1) & 0x55555555;
  x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
  return (((x + (x >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24;
}

function transpose(rows) {
  return rows.map((_, j) => rows.reduce((col, row, i) =>
    col | (((row >> BigInt(j)) & 1n) << BigInt(i)), 0n));
}

function findBiclique(rows, rowCount, colCount) {
  const parts = rows.map(row => [0,32,64,96].map(k => Number((row >> BigInt(k)) & 0xffffffffn)));
  const degree = row => row.reduce((s, word) => s + population(word), 0);
  const initial = parts.map((_,i) => i).filter(i => degree(parts[i]) >= colCount)
    .sort((i,j) => degree(parts[i])-degree(parts[j]));
  let visited = 0;

  // Each candidate still has enough columns in common with the prefix.
  // Increasing indices enumerate every possible extension once.
  function search(candidates, needed, a, b, c, d, prefix) {
    visited++;
    for (let i=0; i<=candidates.length-needed; i++) {
      const chosen = candidates[i], row = parts[chosen];
      if (needed === 1) return [...prefix, chosen];
      const x = a & row[0], y = b & row[1], z = c & row[2], w = d & row[3];
      const next = [];
      for (let j=i+1; j<candidates.length; j++) {
        const v = candidates[j], t = parts[v];
        const size = population(x&t[0])+population(y&t[1])+population(z&t[2])+population(w&t[3]);
        if (size >= colCount) next.push(v);
      }
      if (next.length >= needed-1) {
        const found = search(next, needed-1, x, y, z, w, [...prefix, chosen]);
        if (found) return found;
      }
    }
    return null;
  }
  return {found: search(initial, rowCount, -1,-1,-1,-1, []), visited};
}

function verifyUpper(rows, num, den) {
  const columns = transpose(rows);
  let visited = 0;
  // For a <= b, the first b with ab/(a+b) > num/den suffices.
  for (let a=Math.floor(num/den)+1; ; a++) {
    const b = Math.max(a,Math.floor(num*a/(den*a-num))+1);
    for (const side of (a===b ? [rows] : [rows,columns])) {
      const result = findBiclique(side,a,b);
      if (result.found) throw Error("Bound contradicted by "+JSON.stringify(result.found));
      visited += result.visited;
    }
    // Every larger shape then contains the tested (a,b) or its transpose.
    if (b <= a+1) return visited;
  }
}

async function main() {
  const response = await fetch(source);
  if (!response.ok) throw Error("Catalogue HTTP "+response.status);
  const data = await response.json();
  const rows = data.formal_statement.match(/0x[0-9a-f]+/gi).map(BigInt);
  if (data.id !== "L-meta-20585" || rows.length !== 128) throw Error("Wrong statement");
  const cells = rows.reduce((n,r) => n+r.toString(2).replaceAll("0","").length,0);
  if (cells !== 6485) throw Error("Wrong edge count");
  const cols = transpose(rows);
  const witness = [125,74,109,36,68,124,116,10,29];
  const common = witness.reduce((x,j) => x&cols[j], all);
  if (common.toString(2).replaceAll("0","").length !== 12) throw Error("Wrong extremal rectangle");
  const positive = verifyUpper(rows,36,7);
  const complement = verifyUpper(rows.map(r => all^r),9,1);
  console.log({cells, positiveSearchNodes:positive, complementSearchNodes:complement});
}
main().catch(e => { console.error(e.message); process.exitCode=1; });
