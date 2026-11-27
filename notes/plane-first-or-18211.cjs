const bank=13, all=(1<<bank)-1;
const ids=Array.from({length:bank},(_,i)=>i);
const bits=Array.from({length:all+1},(_,m)=>ids.filter(i=>m&(1<<i)));
const pencils=ids.map(p=>[0,1,3,9].reduce((m,d)=>m|1<<((p-d+bank)%bank),0));
const cap=m=>pencils.every(r=>bits[m&r].length<=2);
const quad=bits.flatMap((r,m)=>r.length===4&&cap(m)?[m]:[]);
const pair=bits.flatMap((r,m)=>r.length===2?[m]:[]);
// The two sides below are lines and their pencil centers. Joins and meets
// generate the remaining labels from a projective frame.
const neighborhoods=[ids.map(l=>pencils.reduce((m,P,p)=>m|((P>>l&1)<<p),0)),pencils];
const pairs=(xs)=>xs.flatMap((a,i)=>xs.slice(i+1).map(b=>[a,b]));
const join=neighborhoods.map(rows=>rows.map(A=>rows.map(B=>31-Math.clz32(A&B))));
const frames=[];
for(const m of quad){
  const place=[];
  function permutations(todo) {
    if(!todo.length){frames.push([...place]);return;}
    for(let i=0;i<todo.length;i++){
      place.push(todo[i]);
      permutations(todo.filter((_,j)=>i!==j));
      place.pop();
    }
  }
  permutations(bits[m]);
}
const base=frames[0], closure=[new Set(base),new Set()], recipe=[];
while(closure[0].size+closure[1].size<26){
  const old=recipe.length;
  for(let bank=0;bank<2;bank++)for(const [a,b] of pairs([...closure[bank]])){
    const pos=join[bank][a][b];
    if(closure[1-bank].has(pos))continue;
    closure[1-bank].add(pos);
    recipe.push([bank,a,b,pos]);
  }
  if(old===recipe.length)throw Error("Frame closure stalled");
}
const group=frames.map(f=>{
  const map=[[],[]];
  base.forEach((v,i)=>map[0][v]=f[i]);
  for(const [bank,a,b,pos] of recipe)map[1-bank][pos]=join[bank][map[bank][a]][map[bank][b]];
  if(map.some(m=>m.length!==13||new Set(m).size!==13))throw Error("Invalid permutation");
  if(pencils.some((m,i)=>bits[m].reduce((s,j)=>s|(1<<map[0][j]),0)!==pencils[map[1][i]]))
    throw Error("Invalid incidence map");
  return map;
});
if(new Set(group.map(g=>g.flat().join(","))).size!==5616)throw Error("Group completeness count");

const onLine=ids.map(l=>pencils.reduce((m,P,p)=>m|((P>>l&1)<<p),0));
function neighborsUnion(mask,neighborhoods) {
  return bits[mask].reduce((m,v)=>m|neighborhoods[v],0);
}
const lifted=group.map(([l,p])=>[...p,...l.map(i=>i+13)]);
const dual=[...ids.map(p=>((13-p)%13)+13),...ids.map(l=>(13-l)%13)];
const symmetries=[...lifted,...lifted.map(g=>g.map(i=>dual[i]))];
const flags=onLine.flatMap((m,l)=>bits[m].map(p=>(1<<p)|(1<<(13+l))));
const negatives=quad.flatMap(q=>{
  const pointQuad=bits[q].reduce((m,l)=>m|(1<<((13-l)%13)),0);
  const exLines=all^neighborsUnion(pointQuad,pencils);
  const exPoints=all^neighborsUnion(q,onLine);
  if(bits[exLines].length!==3||bits[exPoints].length!==3)throw Error("Incorrect exterior");
  return [pointQuad|(exLines<<13),exPoints|(q<<13)];
});

const prefixes=[[],...Array.from({length:26},(_,i)=>[i]),
  ...Array.from({length:26},(_,i)=>Array.from({length:25-i},(_,j)=>[i,j+i+1])).flat()];
const key=inputs=>[...inputs].sort((a,b)=>a-b).join(",");
const remaining=new Set(prefixes.map(key));
const cases=[];
while(remaining.size){
  const representative=remaining.values().next().value;
  const input=representative?representative.split(",").map(Number):[];
  let size=0;
  for(const perm of symmetries)if(remaining.delete(key(input.map(i=>perm[i]))))size++;
  cases.push({input,size});
}
if(JSON.stringify(cases)!==JSON.stringify([
  {input:[],size:1},{input:[0],size:26},{input:[0,1],size:156},
  {input:[0,13],size:52},{input:[0,14],size:117}
]))throw Error("Unexpected first-OR orbits");

function starCircuit(){
  // Use line zero first, so the first gate is the OR of points zero and one.
  const gates=[];
  const step=(and,a,b)=>{gates.push({and,inputs:[a,b]});return 26+gates.length-1;};
  const stars=onLine.map((neighbors,l)=>{
    const [p,...rest]=bits[neighbors];
    const leaves=rest.reduce((w,q)=>step(false,w,q),p);
    return step(true,leaves,13+l);
  });
  stars.slice(1).reduce((w,s)=>step(false,w,s),stars[0]);
  return gates;
}
function testPrefix(prefix,tail,output) {
  if(prefix.and||prefix.inputs.length>2||tail.some(g=>g.inputs.length!==2))
    throw Error("Wrong gate model");
  const compute=(row)=>{
    const wires=Array.from({length:26},(_,i)=>!!(row&(1<<i)));
    const advance=(g)=>{
      const values=g.inputs.map(i=>wires[i]??false);
      wires.push(g.and?values.every(Boolean):values.some(Boolean));
    };
    advance(prefix);
    tail.forEach(advance);
    return !!wires[output];
  };
  if(flags.some(w=>!compute(w))||negatives.some(compute))throw Error("Control fails the desk tests");
  return {inputs:prefix.inputs,tailGates:tail.length,flagRows:flags.length,maximalFalseRows:new Set(negatives).size};
}
const star=starCircuit();
if(star.length!==64||key(star[0].inputs)!=="0,1")throw Error("Wrong first gate of star circuit");
const shifted=star.map(g=>({...g,inputs:g.inputs.map(i=>i>=26?i+1:i)}));
const controls=cases.map(({input})=>key(input)==="0,1"?
  testPrefix(star[0],star.slice(1),26+63):
  testPrefix({and:false,inputs:input},shifted,26+64));
console.log(JSON.stringify({cases,controls}));
