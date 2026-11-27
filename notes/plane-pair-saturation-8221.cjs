const fs = require("node:fs");
const vm = require("node:vm");
const ctx = vm.createContext({});
vm.runInContext(fs.readFileSync(process.env.PNP_PINNED_MINICARD, "utf8"), ctx);
const Sat = ctx.minisolvers.MinisatSolver;
const binarySubsets = Array.from({length:8192},(_,mask)=>
  Array.from({length:13},(_,n)=>n).filter(n=>mask&(1<<n)));
const pencil = Array.from({length:13},(_,point)=>
  [0,1,3,9].reduce((s,d)=>s|(1<<((point-d+13)%13)),0));
const between = (m,q)=> (m&q)===m;
const nonconcurrent = m=>pencil.every(p=>binarySubsets[p&m].length<3);
const choose = size=>binarySubsets.flatMap((s,m)=>s.length===size&&nonconcurrent(m)?[m]:[]);
const q = choose(4), t = choose(3), p = choose(2);
function run(full) {
  const S = new Sat();
  const lits = q.map(()=>S.new_var());
  const rows = ms=>ms.map(mask=>q.flatMap((n,i)=>between(mask,n)?[lits[i]]:[]));
  const triples = rows(t), pairs = rows(full?p:[p[0]]);
  if(triples.some(row=>row.length!==4)||pairs.some(row=>row.length!==18))throw Error("Incorrect incidence counts");
  for(const row of triples)
    for(let i=1;i<4;i++)
      for(let j=0;j<i;j++)S.add_clause([-row[i],-row[j]]);
  for(const row of pairs)
    for(let i=2;i<row.length;i++)
      for(let j=1;j<i;j++)
        for(let k=0;k<j;k++) S.add_clause(row.filter((_,g)=>g!==i&&g!==j&&g!==k));
  console.log(JSON.stringify({test:full?"all-pairs":"one-pair",clauses:S.nclauses(),sat:S.solve()}));
  S.delete();
}
try { run(false); run(true); } catch (e) { console.error(String(e)); process.exitCode=1; }
