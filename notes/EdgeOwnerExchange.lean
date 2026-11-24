import PEqualNP.Defs

namespace EdgeOwnerExchange
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

-- Prefix and suffix monotonicity from our singleton-frontier calculation.
def increases (xs ys : List Bool) :=
  xs.length = ys.length ∧ ∀ i, xs.getD i false = true → ys.getD i false = true

theorem snoc {xs ys : List Bool} {a b : Bool} (h : increases xs ys) (ab : a=true → b=true) :
    increases (xs++[a]) (ys++[b]) := by
  obtain ⟨len,ord⟩ := h
  refine ⟨by simp [len],?_⟩
  intro i
  by_cases hi : i<xs.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (len ▸ hi)]
    exact ord i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),← len]
    cases i-xs.length with
    | zero => exact ab
    | succ j => simp [List.getD_eq_getElem?_getD]

def advance (xs : List Bool) (g : Gate) :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

theorem advanceMono (xs ys : List Bool) (g : Gate) (op : g.op=.and ∨ g.op=.or)
    (h : increases xs ys) : increases (advance xs g) (advance ys g) := by
  apply snoc h
  rcases op with e|e
  · simp only [e, GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro all w hw
    exact h.2 w (all w hw)
  · simp only [e, GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨w,hw,hit⟩
    exact ⟨w,hw,h.2 w hit⟩

theorem foldMono (gs : List Gate) (ops : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (xs ys : List Bool) (h : increases xs ys) :
    increases (gs.foldl advance xs) (gs.foldl advance ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g tail ih =>
    exact ih (fun k hk => ops k (List.mem_cons_of_mem _ hk)) _ _
      (advanceMono xs ys g (ops g List.mem_cons_self) h)



def frame (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) : Circuit :=
  ⟨pre ++ g :: post, o⟩

def value (pre : List Gate) (g : Gate) (x : List Bool) : Bool :=
  let tape := pre.foldl advance x
  g.op.eval (g.inputs.map fun w => tape.getD w false)

def context (pre post : List Gate) (o : ℕ) (x : List Bool) (b : Bool) : Bool :=
  (post.foldl advance ((pre.foldl advance x) ++ [b])).getD o false

theorem eval_frame (pre post : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    (frame pre g post o).eval x = context pre post o x (value pre g x) := by
  change ((pre ++ g :: post).foldl advance x).getD o false = _
  simp [List.foldl_append,context,value,advance]

theorem tapePrefix (gs : List Gate) (x : List Bool) : ∃ y, gs.foldl advance x = x ++ y := by
  induction gs generalizing x with
  | nil => exact ⟨[],by simp⟩
  | cons g gs ih =>
    obtain ⟨y,hy⟩ := ih (advance x g)
    exact ⟨[_] ++ y,by simpa [advance,List.append_assoc] using hy⟩

theorem raw_value {n : ℕ} (u v : Fin n) (pre : List Gate) (x : Fin n → Bool) :
    value pre ⟨.and,[u.val,v.val]⟩ (List.ofFn x) = (x u && x v) := by
  obtain ⟨y,h⟩ := tapePrefix pre (List.ofFn x)
  have atRaw (w : Fin n) : ((List.ofFn x)++y).getD w.val false = x w := by
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD,w.isLt]
  simp only [value,h,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,atRaw]

theorem forceMono (pre post : List Gate) (o : ℕ)
    (ops : ∀ g ∈ post, g.op=.and ∨ g.op=.or) (x : List Bool) (a b : Bool)
    (ab : a=true → b=true) :
    context pre post o x a=true → context pre post o x b=true :=
  (foldMono post ops _ _ (snoc ⟨rfl,fun _ h => h⟩ ab)).2 o

theorem rawMono {n : ℕ} (x y : Fin n → Bool) (xy : ∀ i, x i=true → y i=true) :
    increases (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases hi : i<n
  · simpa [List.getD_eq_getElem?_getD,hi] using xy ⟨i,hi⟩
  · simp [List.getD_eq_getElem?_getD,hi]

theorem rawLegal (pre post : List Gate) (g : Gate) (o : ℕ) (u v : ℕ)
    (hm : Monotone2 (frame pre g post o)) :
    Monotone2 (frame pre ⟨.and,[u,v]⟩ post o) := by
  intro z hz
  change z ∈ pre ++ _ :: post at hz
  rcases List.mem_append.mp hz with left|right
  · exact hm z (List.mem_append_left _ left)
  · rcases List.mem_cons.mp right with rfl|right
    · simp
    · exact hm z (List.mem_append_right _ (List.mem_cons_of_mem _ right))

theorem graph_truth {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p l, G.Adj p l ∧ x p=true ∧ x l=true := by
  simp [graphFun]

theorem atEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (edge : G.Adj u v) : graphFun G ∅ (pairInput u v)=true :=
  (graph_truth _ _).2 ⟨u,v,edge,by simp [pairInput],by simp [pairInput]⟩

def pivotal {n : ℕ} (pre post : List Gate) (o : ℕ) (a b : Fin n) :=
  context pre post o (List.ofFn (pairInput a b)) false = false

theorem single_rewire {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g : Gate) (o : ℕ) (u v : Fin n)
    (hm : Monotone2 (frame pre g post o))
    (correct : circuitFun n (frame pre g post o) = graphFun G ∅)
    (one : ∀ a b : Fin n, G.Adj a b → pivotal pre post o a b →
      pairInput a b u = true ∧ pairInput a b v = true)
    (edge : G.Adj u v) :
    circuitFun n (frame pre ⟨.and,[u.val,v.val]⟩ post o) = graphFun G ∅ := by
  let new := frame pre ⟨GateOp.and,[u.val,v.val]⟩ post o
  have legal := rawLegal pre post g o u v hm
  have ops : ∀ z ∈ post, z.op=.and ∨ z.op=.or := fun z hz =>
    (hm z (List.mem_append_right _ (List.mem_cons_of_mem _ hz))).1
  have high (a b : Fin n) (ab : G.Adj a b) :
      new.eval (List.ofFn (pairInput a b))=true := by
    have old := (congrFun correct (pairInput a b)).trans (atEdge G ab)
    change (frame pre g post o).eval _ = true at old
    rw [eval_frame] at old
    change (frame pre ⟨.and,[u.val,v.val]⟩ post o).eval _=true
    rw [eval_frame,raw_value]
    by_cases loss : pivotal pre post o a b
    · obtain ⟨pu,pv⟩ := one a b ab loss
      rw [pu,pv]
      exact forceMono pre post o ops _ _ _ (fun _ => rfl) old
    · have lo : context pre post o (List.ofFn (pairInput a b)) false = true := by
        simpa [pivotal] using loss
      exact forceMono pre post o ops _ _ _ (by simp) lo
  funext x
  change new.eval (List.ofFn x) = graphFun G ∅ x
  cases target : graphFun G ∅ x with
  | true =>
    obtain ⟨a,b,ab,pa,pb⟩ := (graph_truth _ _).1 target
    have xy : ∀ i, pairInput a b i=true → x i=true := by
      intro i h
      rcases of_decide_eq_true h with rfl|rfl
      · exact pa
      · exact pb
    exact (foldMono new.gates (fun z hz => (legal z hz).1) _ _ (rawMono _ _ xy)).2 o (high a b ab)
  | false =>
    have off : (x u && x v) = false := by
      cases hu : x u <;> cases hv : x v <;> try rfl
      exact False.elim (Bool.noConfusion (target.symm.trans ((graph_truth _ _).2 ⟨u,v,edge,hu,hv⟩)))
    have orig := (congrFun correct x).trans target
    change (frame pre g post o).eval _=false at orig
    rw [eval_frame] at orig
    change (frame pre ⟨.and,[u.val,v.val]⟩ post o).eval _=false
    rw [eval_frame,raw_value,off]
    cases h : context pre post o (List.ofFn x) false with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion (orig.symm.trans (forceMono pre post o ops _ _ _ (by simp) h)))

theorem conePrefix (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    ∃ y, gs.foldl (coneStep n) cs = cs ++ y := by
  induction gs generalizing cs with
  | nil => exact ⟨[],by simp⟩
  | cons g gs ih =>
    obtain ⟨y,hy⟩ := ih (coneStep n cs g)
    exact ⟨[_] ++ y,by simpa [coneStep,List.append_assoc] using hy⟩

theorem coneLength (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => simp [ih,coneStep]; omega

theorem rawOwns {n : ℕ} (pre post : List Gate) (o : ℕ) (u v : Fin n) :
    Owns n (frame pre ⟨.and,[u.val,v.val]⟩ post o) pre.length u v := by
  let g : Gate := ⟨.and,[u.val,v.val]⟩
  let C := frame pre g post o
  have idx : (gateAt C pre.length).op = .and := by
    simp [C,frame,gateAt,List.getD_eq_getElem?_getD,g]
  let x := List.ofFn (pairInput u v)
  let before := pre.foldl advance x
  have length (gs : List Gate) (xs : List Bool) : (gs.foldl advance xs).length=xs.length+gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons z gs ih => simp [ih,advance]; omega
  have lb : before.length=n+pre.length := by simp [before,x,length]
  have hg : value pre g x=true := by simp [g,x,raw_value,pairInput]
  obtain ⟨r,hr⟩ := tapePrefix post (advance before g)
  have val : gateVal n C pre.length (pairInput u v)=true := by
    change ((pre ++ g :: post).foldl advance x).getD (n+pre.length) false=true
    rw [List.foldl_append,List.foldl_cons,hr]
    change ((before ++ [value pre g x]) ++ r).getD _ _ = _
    rw [hg,←lb]
    simp [List.append_assoc,List.getD_eq_getElem?_getD]
  let cs := pre.foldl (coneStep n) []
  have len : cs.length=pre.length := by simp [cs,coneLength]
  have one : coneStep n cs g = cs ++ [[]] := by
    simp [coneStep,g,Nat.not_le_of_lt u.isLt,Nat.not_le_of_lt v.isLt]
  obtain ⟨t,ht⟩ := conePrefix n post (coneStep n cs g)
  have no : (cones n C).getD pre.length [] = [] := by
    change ((pre ++ g :: post).foldl (coneStep n) []).getD _ _ = _
    rw [List.foldl_append,List.foldl_cons,ht,one,←len]
    simp [List.append_assoc,List.getD_eq_getElem?_getD]
  exact ⟨by simp [frame],idx,val,fun i _ inc => by
    change i ∈ (cones n C).getD pre.length [] at inc
    rw [no] at inc
    cases inc⟩


theorem tapeLength (gs : List Gate) (xs : List Bool) : (gs.foldl advance xs).length=xs.length+gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons z gs ih => simp [ih,advance]; omega

theorem earlierOwner {n : ℕ} (pre tail : List Gate) (o j : ℕ) (hj : j < pre.length)
    (u v : Fin n) :
    Owns n (⟨pre ++ tail,o⟩ : Circuit) j u v ↔ Owns n (⟨pre,o⟩ : Circuit) j u v := by
  let C : Circuit := ⟨pre ++ tail,o⟩
  let D : Circuit := ⟨pre,o⟩
  have gate (i : ℕ) (hi : i < pre.length) : gateAt C i = gateAt D i := by
    exact List.getD_append _ _ _ _ hi
  have gv (i : ℕ) (hi : i < pre.length) (x : Fin n → Bool) : gateVal n C i x = gateVal n D i x := by
    change ((pre ++ tail).foldl advance (List.ofFn x)).getD _ _ = _
    rw [List.foldl_append]
    obtain ⟨r,h⟩ := tapePrefix tail (pre.foldl advance (List.ofFn x))
    rw [h,List.getD_append _ _ _ _ (by simp [tapeLength,hi])]
    rfl
  have cone (i : ℕ) : InCone n C i j ↔ InCone n D i j := by
    change i ∈ ((pre ++ tail).foldl (coneStep n) []).getD j [] ↔ _
    rw [List.foldl_append]
    obtain ⟨r,h⟩ := conePrefix n tail (pre.foldl (coneStep n) [])
    rw [h,List.getD_append _ _ _ _ (by simp [coneLength,hj])]
    rfl
  change Owns n C j u v ↔ Owns n D j u v
  unfold Owns
  rw [gate j hj,gv j hj]
  have hc : j < C.gates.length := by simp [C]; omega
  have hd : j < D.gates.length := hj
  simp only [hc,hd,true_and]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro all i ij inc op
    have hi := ij.trans hj
    rw [← gv i hi]
    exact all i ij ((cone i).2 inc) ((congrArg Gate.op (gate i hi)).trans op)
  · intro all i ij inc op
    have hi := ij.trans hj
    rw [gv i hi]
    exact all i ij ((cone i).1 inc) ((congrArg Gate.op (gate i hi)).symm.trans op)

theorem previous {n : ℕ} (pre post : List Gate) (g z : Gate) (o j : ℕ) (hj : j<pre.length)
    (u v : Fin n) : Owns n (frame pre z post o) j u v ↔ Owns n (frame pre g post o) j u v :=
  (earlierOwner pre (z::post) o j hj u v).trans (earlierOwner pre (g::post) o j hj u v).symm

section Repair
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def soundUntil (C : Circuit) (k : ℕ) : Prop :=
  ∀ j < k, (gateAt C j).op=.and → ∃ u v, G.Adj u v ∧ Owns n C j u v

theorem extend_owner (pre post : List Gate) (g : Gate) (o : ℕ) (u v : Fin n)
    (hm : Monotone2 (frame pre g post o))
    (correct : circuitFun n (frame pre g post o) = graphFun G ∅)
    (before : soundUntil G (frame pre g post o) pre.length)
    (one : ∀ a b : Fin n, G.Adj a b → pivotal pre post o a b →
      pairInput a b u = true ∧ pairInput a b v = true) (edge : G.Adj u v) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧
      D.size=(frame pre g post o).size ∧ soundUntil G D (pre.length+1) := by
  let z : Gate := ⟨.and,[u.val,v.val]⟩
  refine ⟨frame pre z post o,rawLegal pre post g o u v hm,single_rewire G pre post g o u v hm correct one edge,?_,?_⟩
  · simp [Circuit.size,frame]
  · intro j hj op
    by_cases h : j=pre.length
    · subst j; exact ⟨u,v,edge,rawOwns pre post o u v⟩
    · have lt : j<pre.length := by omega
      have opOld : (gateAt (frame pre g post o) j).op=.and := by
        change ((pre ++ g :: post).getD j _).op=.and
        change ((pre ++ z :: post).getD j _).op=.and at op
        rw [List.getD_append _ _ _ _ lt] at op ⊢
        exact op
      obtain ⟨a,b,ab,own⟩ := before j lt opOld
      exact ⟨a,b,ab,(previous pre post g z o j lt a b).2 own⟩
end Repair


section Normalization
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem normalize_unique (C : Circuit) (hm : Monotone2 C)
    (correct : circuitFun n C=graphFun G ∅)
    (repairable : ∀ (pre post : List Gate) (g : Gate) (o : ℕ),
      let D := frame pre g post o
      Monotone2 D → circuitFun n D=graphFun G ∅ → D.size=C.size →
      soundUntil G D pre.length → g.op=.and →
      (¬ ∃ a b, G.Adj a b ∧ Owns n D pre.length a b) →
      ∃ u v, G.Adj u v ∧ ∀ a b, G.Adj a b → pivotal pre post o a b →
        pairInput a b u=true ∧ pairInput a b v=true) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧ D.size=C.size ∧
      soundUntil G D D.size := by
  have go : ∀ k ≤ C.size, ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧
      D.size=C.size ∧ soundUntil G D k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨C,hm,correct,rfl,fun j hj => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨D,md,eq,sz,prior⟩ := ih (by omega)
      have less : k < D.gates.length := by change k < D.size; omega
      let pre := D.gates.take k
      have plen : pre.length=k := by simp [pre,Nat.min_eq_left (Nat.le_of_lt less)]
      obtain ⟨g,post,tail⟩ : ∃ g post, D.gates.drop k=g::post := by
        cases h : D.gates.drop k with
        | nil =>
          have len := congrArg List.length h
          simp at len
          omega
        | cons g post => exact ⟨g,post,rfl⟩
      have split : frame pre g post D.output = D := by
        cases D with
        | mk gs o =>
          change (⟨gs.take k ++ g :: post,o⟩ : Circuit) = ⟨gs,o⟩
          rw [←tail]; simp
      have tick : (gateAt D k).op=g.op := by
        calc
          _ = (gateAt (frame pre g post D.output) pre.length).op := by rw [split,plen]
          _ = _ := by simp [gateAt,frame,List.getD_eq_getElem?_getD]
      by_cases done : g.op=.and → ∃ u v, G.Adj u v ∧ Owns n D k u v
      · refine ⟨D,md,eq,sz,fun j hj h => ?_⟩
        by_cases e : j=k
        · subst j; exact done (tick.symm.trans h)
        · exact prior j (by omega) h
      · push Not at done
        obtain ⟨hand,bad⟩ := done
        have miss : ¬ ∃ a b, G.Adj a b ∧ Owns n (frame pre g post D.output) pre.length a b := by
          rw [split,plen]; rintro ⟨a,b,edge,own⟩; exact bad a b edge own
        obtain ⟨u,v,adj,one⟩ := repairable pre post g D.output (split ▸ md) (split ▸ eq)
          (split ▸ sz) (by simpa [split,plen] using prior) hand miss
        obtain ⟨E,me,ec,es,ep⟩ := extend_owner G pre post g D.output u v (split ▸ md)
          (split ▸ eq) (by simpa [split,plen] using prior) one adj
        exact ⟨E,me,ec,es.trans (split ▸ sz),by simpa [plen] using ep⟩
  obtain ⟨D,md,eq,sz,owns⟩ := go C.size (by rfl)
  exact ⟨D,md,eq,sz,sz ▸ owns⟩
end Normalization

section PrivateReader
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

def independent (S : Finset V) := ∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v

theorem independent_insert {S : Finset V} {y : V} (ok : independent G S)
    (miss : ∀ z ∈ S, ¬G.Adj y z) : independent G (insert y S) := by
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with ea|ina
  · subst a
    rcases Finset.mem_insert.mp hb with eb|inb
    · subst b; exact G.loopless.irrefl _
    · exact miss _ inb
  · rcases Finset.mem_insert.mp hb with eb|inb
    · subst b; exact fun adj => miss _ ina adj.symm
    · exact ok _ ina _ inb

/-- If a private OR is already on, no neighbor of x can be added while
remaining independent: switching x on would then be masked. -/
theorem dominating_witness (x : V) (W : Finset V → Prop)
    (mono : ∀ S T, S ⊆ T → W S → W T)
    (masked : ∀ T, x ∉ T → independent G T → W T → ∀ y ∈ T, ¬G.Adj x y)
    (I : Finset V) (outside : x ∉ I) (ok : independent G I) (hot : W I)
    (y : V) (neighbor : G.Adj x y) : ∃ z ∈ I, G.Adj y z := by
  by_contra! none
  have good := independent_insert G ok none
  have nx : x ∉ insert y I := by simp [neighbor.ne,outside]
  exact masked (insert y I) nx good (mono I _ (Finset.subset_insert _ _) hot) y
    (Finset.mem_insert_self _ _) neighbor

omit [DecidableEq V] in
theorem distinct_representatives {x y t z : V} (common : ∀ a b : V, a ≠ b →
    ∀ c d : V, G.Adj a c → G.Adj b c → G.Adj a d → G.Adj b d → c=d)
    (different : y≠t) (xy : G.Adj x y) (xt : G.Adj x t)
    (yz : G.Adj y z) (tz : G.Adj t z) (outside : x≠z) : False :=
  outside (common y t different x z xy.symm xt.symm yz tz)

theorem pin_price (s low high U : ℕ) (lo : U ≤ low+3) (hi : U ≤ high+4)
    (cases : (low+3 ≤ s) ∨ (high+4 ≤ s)) : U ≤ s := by omega
end PrivateReader


theorem two_pivots {n : ℕ} (G : SimpleGraph (Fin n)) (pre post : List Gate) (o : ℕ)
    (nonempty : ∃ x y, G.Adj x y)
    (fail : ¬∃ u v, G.Adj u v ∧ ∀ a b, G.Adj a b → pivotal pre post o a b →
      pairInput a b u = true ∧ pairInput a b v=true) :
    ∃ u v a b, G.Adj u v ∧ pivotal pre post o u v ∧ G.Adj a b ∧
      pivotal pre post o a b ∧ ¬(pairInput a b u=true ∧ pairInput a b v=true) := by
  classical
  obtain ⟨x,y,xy⟩ := nonempty
  have some : ∃ u v, G.Adj u v ∧ pivotal pre post o u v := by
    by_contra! none
    exact fail ⟨x,y,xy,fun a b adj lost => False.elim (none a b adj lost)⟩
  obtain ⟨u,v,uv,loss⟩ := some
  have another : ¬∀ a b, G.Adj a b → pivotal pre post o a b →
      pairInput a b u=true ∧ pairInput a b v=true := fun all => fail ⟨u,v,uv,all⟩
  push Not at another
  obtain ⟨a,b,ab,other,bad⟩ := another
  exact ⟨u,v,a,b,uv,loss,ab,other,by tauto⟩

section Menu
variable {E I : Type*} (old : E → Bool) (lo hi : E → Bool) (hit : I → E → Bool)
  (positive : E → Prop)

theorem two_sources (a b : I) (e : E)
    (increasing : lo e=true → hi e=true)
    (original : (if old e then hi e else lo e)=true ↔ positive e)
    (cover : positive e → lo e=false → hit a e=true ∨ hit b e=true)
    (allowed : ¬positive e → hi e=true → hit a e=false ∧ hit b e=false) :
    (if hit a e || hit b e then hi e else lo e)=true ↔ positive e := by
  by_cases pos : positive e
  · have h := original.mpr pos
    have H : hi e=true := by cases ho : old e <;> simp [ho] at h <;> first | exact h | exact increasing h
    cases l : lo e with
    | false =>
      rcases cover pos l with h|h <;> simp [h,H,pos]
    | true => simp [H,pos]
  · have L : lo e=false := by
      cases l : lo e with
      | false => rfl
      | true =>
        have H := increasing l
        exact False.elim (pos (original.mp (by simp [H,l])))
    cases h : hi e with
    | false => simp [L,pos]
    | true =>
      obtain ⟨x,y⟩ := allowed pos h
      simp [x,y,L,pos]
end Menu

end EdgeOwnerExchange
