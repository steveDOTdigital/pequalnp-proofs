const F=1865323, raw=10, n=24;
const inputs=Array.from({length:raw},(_,v)=>{
  let table=0;
  for(let a=0;a<4;a++)for(let b=0;b<6;b++)if(a===v||4+b===v)table|=1<<(a*6+b);
  return table;
});
const full=(1<<n)-1;
function requires(slot) {
  // A positive entry and a negative entry with the same other shore.
  for(let a=0;a<4;a++)for(let b=0;b<6;b++){
    if(!(F&(1<<(6*a+b))))continue;
    if(slot===a)for(let other=0;other<4;other++)
      if(!(F&(1<<(6*other+b))))return {positive:[a,b],negative:[other,b]};
    if(slot===4+b)for(let other=0;other<6;other++)
      if(!(F&(1<<(6*a+other))))return {positive:[a,b],negative:[a,other]};
  }
  throw Error("No witness of raw read necessity");
}
const essential=inputs.map((_,i)=>requires(i));
const rows=Array.from({length:4},(_,i)=>(F>>(6*i))&63);
console.log(JSON.stringify({phase:"essential_raw",essential,rows}));

function modular(leaves){
  const dim=leaves.length, universe=(1<<dim)-1;
  const signature=Array.from({length:n},(_,i)=>leaves.reduce((z,l,p)=>z|((l.table>>i&1)<<p),0));
  const forces=new Map(), wanted=(outside)=>{
    let known=forces.get(outside);
    if(known)return known;
    const partitions=new Map();
    for(let i=0;i<n;i++){
      const key=signature[i]&outside, bit=1<<i;
      partitions.set(key,(partitions.get(key)||0)|bit);
    }
    let need=0;
    for(const group of partitions.values())if((group&F)&&(group&(full^F)))need|=group;
    const v=[need&F,need&(full^F)];forces.set(outside,v);return v;
  };
  const menus=Array.from({length:universe+1},()=>new Map());
  for(let mask=1;mask<=universe;mask++){
    const [yes,no]=wanted(universe^mask), options=menus[mask];
    const passes=x=>(x&yes)===yes&&!(x&no);
    if((mask&(mask-1))===0){
      const id=31-Math.clz32(mask), leaf=leaves[id];
      if(passes(leaf.table))options.set(leaf.table,{leaf:leaf.id});
      continue;
    }
    const anchor=mask&-mask;
    for(let left=(mask-1)&mask;left;left=(left-1)&mask){
      if(!(left&anchor))continue;
      const right=mask^left;
      for(const [a,A] of menus[left])for(const [b,B] of menus[right]){
        const x=a&b,y=a|b;
        if(passes(x)&&!options.has(x))options.set(x,{and:true,A,B});
        if(passes(y)&&!options.has(y))options.set(y,{and:false,A,B});
      }
    }
  }
  return menus;
}
function check(spec){
  for(let a=0;a<4;a++)for(let b=0;b<6;b++){
    const tape=Array.from({length:raw},(_,i)=>i===a||i===4+b);
    spec.forEach(([op,p,q],i)=>{
      if(p<0||q<0||p>=raw+i||q>=raw+i)throw Error("Invalid backward reads");
      tape.push(op==="and"?tape[p]&&tape[q]:tape[p]||tape[q]);
    });
    if(tape.at(-1)!==!!(F&(1<<(6*a+b))))throw Error("Decoded bad witness");
  }
  return 24;
}
function output(t,H,shape){
  const spec=[];
  const emit=node=>{
    if(node.leaf!==undefined){
      if(node.leaf===10)return share;
      return node.leaf;
    }
    const p=emit(node.A),q=emit(node.B);
    spec.push([node.and?"and":"or",p,q]);return raw+spec.length-1;
  };
  let share;
  if(H)share=emit(H);
  emit(t);
  if(spec.length>10)throw Error("Decoded circuit too long");
  console.log(JSON.stringify({found:true,shape,spec,pass:check(spec)}));
  process.exit(0);
}
const inputsWithID=inputs.map((table,id)=>({table,id}));
const menus=modular(inputsWithID);
const f=menus.at(-1).get(F);
if(f)output(f,null,"read_once");
for(const extra of inputsWithID){
  const repeated=modular([...inputsWithID,extra]).at(-1).get(F);
  if(repeated)output(repeated,null,"repeated_raw");
}
console.log(JSON.stringify({phase:"formulas",found:false,optionCount:menus.reduce((s,m)=>s+m.size,0)}));
let helperCases=0;
for(let mask=1;mask<(1<<raw)-1;mask++){
  if((mask&(mask-1))===0)continue;
  const outside=inputsWithID.filter((_,i)=>!(mask&(1<<i)));
  for(const [table,H] of menus[mask]){
    helperCases++;
    const h={table,id:10}, tail=modular([...outside,h,h]).at(-1).get(F);
    if(tail)output(tail,H,"one_shared");
  }
}
console.log(JSON.stringify({found:false,helperCases,target:F,covers:["read_once","one_repeated_raw","one_shared_gate"]}));
