/* Symmetry orbits for the zero entries of the posted point-line matrix. */
const full = 0x7fffffff;
const incidence = [1141899472,136315297,272630594,545261188,1090522376,33561105,67122210,134244420,268488840,536977680,1073955360,427073,854146,1708292,3416584,6833168,13666336,27332672,54665344,109330688,218661376,437322752,874645504,1749291008,1351098369,554713091,1109426182,71368717,142737434,285474868,570949736];
const coordinates = [[0,0,1],[1,0,0],[1,1,1],[1,0,1],[2,1,1],[0,1,0],[4,3,1],[2,2,1],[4,0,1],[0,1,1],[1,3,1],[1,1,0],[2,0,1],[4,1,1],[1,4,1],[0,4,1],[2,3,1],[4,4,1],[3,0,1],[3,1,1],[1,2,1],[3,2,1],[2,4,1],[4,2,1],[2,1,0],[4,1,0],[3,4,1],[3,1,0],[0,2,1],[0,3,1],[3,3,1]];
const ids = Array.from({length:31}, (_,i) => i);
const rotate = m => ((m << 1) & full) | (m >>> 30);
const bitIndex = value => 31 - Math.clz32(value & -value);

function canonicalRotation(m) {
  let least = m;
  for (let i=1; i<31; i++) {
    m = rotate(m);
    least = Math.min(least,m);
  }
  return least;
}

// An intersection of zero neighborhoods is a closed column set. Complete its
// row set with every row avoiding those columns. Enumerate up to cyclic shift.
function maximalRectangles() {
  const seen = new Set([full]), queue = [full], rectangles = [];
  for (let i=0; i<queue.length; i++) {
    const columns = queue[i];
    let rowSet = 0;
    for (const j of ids) {
      const next = columns & ~incidence[j];
      if (next === columns) rowSet |= 1 << j;
      else {
        const rep = canonicalRotation(next);
        if (!seen.has(rep)) { seen.add(rep); queue.push(rep); }
      }
    }
    if (columns && rowSet) rectangles.push([rowSet,columns]);
  }
  return rectangles;
}

function collineation(xScale,yScale,xShift=0) {
  // Projective representatives normalize the last nonzero coordinate to one.
  const lookup = new Map(coordinates.map((v,i) => [v.join(","),i]));
  const inverse = [0,1,3,2,4];
  const point = coordinates.map(([x,y,z]) => {
    const t = [(x*xScale+xShift*z)%5,y*yScale%5,z];
    const k = inverse[t[2] || t[1] || t[0]];
    return lookup.get(t.map(v=>v*k%5).join(","));
  });
  const line = ids.map(j=>ids.find(k=>ids.every(i=>
    ((incidence[i]>>>j)&1) === ((incidence[point[i]]>>>k)&1))));
  if (point.includes(undefined) || line.includes(undefined) ||
      new Set(point).size!==31 || new Set(line).size!==31) throw Error("Invalid collineation");
  return [point,line];
}

function transformTable(permutation) {
  return Array.from({length:4}, (_,chunk)=>Array.from({length:256}, (_,byte)=>{
    let result=0;
    for (let i=0;i<8;i++) if ((byte>>>i)&1 && 8*chunk+i<31) result |= 1<<permutation[8*chunk+i];
    return result;
  }));
}
function applyMap(m,t) {
  return t[0][m&255]|t[1][(m>>>8)&255]|t[2][(m>>>16)&255]|t[3][(m>>>24)&255];
}
function cellOrbits(gens) {
  const id = ids.map(()=>new Int16Array(31).fill(-1)), sizes=[];
  for (const i of ids) for (const j of ids) {
    if ((incidence[i]>>>j)&1 || id[i][j]>=0) continue;
    const n = sizes.length, queue = [[i,j]];
    id[i][j]=n;
    for (let k=0;k<queue.length;k++) for (const [r,c] of gens) {
      const a=r[queue[k][0]], b=c[queue[k][1]];
      if (id[a][b]<0) {id[a][b]=n;queue.push([a,b]);}
    }
    sizes.push(queue.length);
  }
  return {sizes,bits:id.map(row=>Array.from(row,v=>v<0?0n:1n<<BigInt(v)))};
}
function options(rectangles,gens) {
  const {sizes,bits}=cellOrbits(gens);
  const tables=gens.map(([,cols])=>transformTable(cols));
  const seen=new Set(), bins=new Map();
  for (const [row0,col0] of rectangles) {
    let r=row0,c=col0;
    for (let k=0;k<31;k++,r=rotate(r),c=rotate(c)) {
      if (seen.has(c)) continue;
      const orbit=[c];seen.add(c);
      for (let i=0;i<orbit.length;i++) for (const t of tables) {
        const v=applyMap(orbit[i],t);
        if (!seen.has(v)) { seen.add(v);orbit.push(v); }
      }
      // Its size is the number of rectangles paid. The cells in one
      // representative identify exactly the cell orbits covered by the union.
      let mask=0n;
      for (let x=r;x;x&=x-1) for (let y=c;y;y&=y-1) mask |= bits[bitIndex(x)][bitIndex(y)];
      if (!bins.has(orbit.length)) bins.set(orbit.length,new Map());
      bins.get(orbit.length).set(mask,[r,c]);
    }
  }
  if (seen.size!==1565748 || sizes.reduce((a,b)=>a+b,0)!==775) throw Error("Incomplete catalogue");
  return {sizes,bins,target:(1n<<BigInt(sizes.length))-1n};
}
function verifyWitness(seeds,gens) {
  const tables=gens.map(([r,c])=>[transformTable(r),transformTable(c)]);
  const boxes=new Map();
  for (const seed of seeds) {
    const queue=[seed];
    for (let i=0;i<queue.length;i++) {
      const [r,c]=queue[i],key=r+","+c;
      if (boxes.has(key)) continue;
      boxes.set(key,[r,c]);
      for (const [a,b] of tables) queue.push([applyMap(r,a),applyMap(c,b)]);
    }
  }
  const covered=ids.map(()=>0);
  for (const [r,c] of boxes.values()) for(let x=r;x;x&=x-1) covered[bitIndex(x)] |= c;
  if (!ids.every(i=>covered[i]===(full^incidence[i]))) throw Error("Wrong witness");
  return boxes.size;
}

async function verifyInput() {
  const r=await fetch("https://data.pequalnp.com/data/lemma/L-meta-10008.a5a3ea2794ed.json");
  if (!r.ok) throw Error("Catalogue HTTP "+r.status);
  const statement=(await r.json()).formal_statement;
  const matches=[...statement.matchAll(/\(\[([0-9, ]+)\]/g)];
  if (matches.length!==2 || matches.some(m=>m[1].split(",").map(Number).join()!==incidence.join()) ||
      !ids.every(i=>rotate(incidence[i])===incidence[(i+1)%31])) throw Error("Matrix mismatch");
}

module.exports={verifyInput,maximalRectangles,collineation,options,verifyWitness};
