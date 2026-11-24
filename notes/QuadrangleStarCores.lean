import PEqualNP.Defs

namespace QuadrangleStarCores

open PEqualNP.HeptadCover

abbrev V := Fin 13

-- Each mask describes a quadrangle disjoint from the zero line.
def witnesses : List ℕ := [116, 308, 340, 404, 420, 464, 1124, 1136, 1188, 1232, 1248, 1316, 1328, 1348, 1360, 2132, 2160, 2196, 2256, 2272, 2372, 2436, 2464, 2496, 3120, 3204, 3216, 3232, 3332, 3360, 4148, 4196, 4244, 4260, 4320, 4400, 4496, 4512, 4544, 5188, 5252, 5264, 5312, 5392, 5440, 6164, 6192, 6212, 6240, 6432, 6464, 7172, 7184, 7424]

def points (r : ℕ) (d : V) : Finset V :=
  Finset.univ.filter fun p => r.testBit (p-d).val

def good (a b c : V) : Prop :=
  a = b ∨ a = c ∨ b = c ∨ ∀ j : V,
    ¬(a ∈ singerLines3 j ∧ b ∈ singerLines3 j ∧ c ∈ singerLines3 j)

instance (a b c : V) : Decidable (good a b c) := inferInstanceAs (Decidable
  (a = b ∨ a = c ∨ b = c ∨ ∀ j : V,
    ¬(a ∈ singerLines3 j ∧ b ∈ singerLines3 j ∧ c ∈ singerLines3 j)))

set_option maxRecDepth 24000 in
theorem baseCover : ∀ a b c : V,
    a ∉ singerLines3 0 → b ∉ singerLines3 0 → c ∉ singerLines3 0 → good a b c →
    ∃ r ∈ witnesses, r.testBit a.val = true ∧ r.testBit b.val = true ∧ r.testBit c.val = true := by
  decide +kernel

set_option maxRecDepth 24000 in
theorem baseValid : ∀ r ∈ witnesses, IsQuadrangle singerLines3 (points r 0) ∧
    (0 : V) ∈ missLines singerLines3 (points r 0) := by decide +kernel

theorem shiftInc : ∀ a j d : V, a-d ∈ singerLines3 (j-d) ↔ a ∈ singerLines3 j := by decide +kernel

def shift (s : Finset V) (d : V) : Finset V := s.map (Equiv.addRight d).toEmbedding

theorem shift_mem (s : Finset V) (p d : V) : p ∈ shift s d ↔ p-d ∈ s := by
  simp only [shift, Finset.mem_map, Equiv.toEmbedding_apply, Equiv.coe_addRight]
  constructor
  · rintro ⟨q,hq,rfl⟩
    simpa using hq
  · intro h
    exact ⟨p-d,h,sub_add_cancel _ _⟩

theorem shift_line (j d : V) : shift (singerLines3 (j-d)) d = singerLines3 j := by
  ext p
  rw [shift_mem,shiftInc]

theorem shift_points (r : ℕ) (d : V) : shift (points r 0) d = points r d := by
  ext p
  simp [shift_mem,points]

theorem shift_quad {s : Finset V} (h : IsQuadrangle singerLines3 s) (d : V) :
    IsQuadrangle singerLines3 (shift s d) := by
  refine ⟨by simpa [shift] using h.1,?_⟩
  intro j
  rw [←shift_line j d]
  change ((s.map _) ∩ ((singerLines3 (j-d)).map _)).card ≤ 2
  rw [←Finset.map_inter,Finset.card_map]
  exact h.2 (j-d)

theorem extension (l a b c : V)
    (ha : a ∉ singerLines3 l) (hb : b ∉ singerLines3 l) (hc : c ∉ singerLines3 l)
    (hg : good a b c) :
    ∃ Q, IsQuadrangle singerLines3 Q ∧ l ∈ missLines singerLines3 Q ∧
      a ∈ Q ∧ b ∈ Q ∧ c ∈ Q := by
  have off (p : V) (h : p ∉ singerLines3 l) : p-l ∉ singerLines3 0 := by
    simpa using (mt (shiftInc p l l).mp h)
  have tr : good (a-l) (b-l) (c-l) := by
    rcases hg with eq|eq|eq|nc
    · exact Or.inl (congrArg (fun x => x-l) eq)
    · exact Or.inr (Or.inl (congrArg (fun x => x-l) eq))
    · exact Or.inr (Or.inr (Or.inl (congrArg (fun x => x-l) eq)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      intro j h
      have back (p : V) (hh : p-l ∈ singerLines3 j) : p ∈ singerLines3 (j+l) := by
        apply (shiftInc p (j+l) l).mp
        simpa using hh
      exact nc (j+l) ⟨back a h.1,back b h.2.1,back c h.2.2⟩
  obtain ⟨r,hr,ra,rb,rc⟩ := baseCover _ _ _ (off a ha) (off b hb) (off c hc) tr
  obtain ⟨shape,miss⟩ := baseValid r hr
  refine ⟨points r l,shift_points r l ▸ shift_quad shape l,?_,?_,?_,?_⟩
  · simp only [missLines,Finset.mem_filter,Finset.mem_univ,true_and] at miss ⊢
    rw [Finset.disjoint_left] at miss ⊢
    intro p hp hq
    apply miss (by simpa using (shiftInc p l l).mpr hp : p-l ∈ singerLines3 0)
    simpa [points] using hq
  all_goals simp_all [points]


theorem uniqueJoin : ∀ a b j k : V, a ≠ b → a ∈ singerLines3 j → b ∈ singerLines3 j →
    a ∈ singerLines3 k → b ∈ singerLines3 k → j=k := by decide +kernel

def noExtension (l a b c : V) : Prop :=
  ¬∃ Q, IsQuadrangle singerLines3 Q ∧ l ∈ missLines singerLines3 Q ∧
      a ∈ Q ∧ b ∈ Q ∧ c ∈ Q

theorem blocked (l a b c : V) (ha : a ∉ singerLines3 l)
    (hb : b ∉ singerLines3 l) (hc : c ∉ singerLines3 l) (h : noExtension l a b c) :
    b ≠ c ∧ ∃ j, a ∈ singerLines3 j ∧ b ∈ singerLines3 j ∧ c ∈ singerLines3 j := by
  have bad : ¬good a b c := fun yes => h (extension l a b c ha hb hc yes)
  unfold good at bad
  push Not at bad
  exact ⟨bad.2.2.1,bad.2.2.2⟩

-- On one old line the partner is unique if no partner triple can be extended.
theorem forcedPartner (l j a d b c : V) (ha : a ∉ singerLines3 l)
    (hd : d ∉ singerLines3 l) (hb : b ∉ singerLines3 l) (hc : c ∉ singerLines3 l)
    (aj : a ∈ singerLines3 j) (dj : d ∈ singerLines3 j) (bj : b ∉ singerLines3 j)
    (first : noExtension l a b c) (second : noExtension l d b c) : a=d := by
  obtain ⟨bc,t,at',bt,ct⟩ := blocked l a b c ha hb hc first
  obtain ⟨_,u,du,bu,cu⟩ := blocked l d b c hd hb hc second
  have eq := uniqueJoin b c t u bc bt ct bu cu
  subst u
  by_contra ad
  have tj := uniqueJoin a d t j ad at' du aj dj
  exact bj (tj ▸ bt)

end QuadrangleStarCores

namespace QuadrangleStarCores.Control

open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
  ⟨.or,[0,1]⟩,
  ⟨.or,[26,3]⟩,
  ⟨.or,[27,9]⟩,
  ⟨.and,[13,28]⟩,
  ⟨.and,[29,13]⟩,
  ⟨.and,[30,28]⟩,
  ⟨.or,[1,2]⟩,
  ⟨.or,[32,4]⟩,
  ⟨.or,[33,10]⟩,
  ⟨.and,[14,34]⟩,
  ⟨.or,[2,3]⟩,
  ⟨.or,[36,5]⟩,
  ⟨.or,[37,11]⟩,
  ⟨.and,[15,38]⟩,
  ⟨.or,[3,4]⟩,
  ⟨.or,[40,6]⟩,
  ⟨.or,[41,12]⟩,
  ⟨.and,[16,42]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.or,[44,7]⟩,
  ⟨.or,[45,0]⟩,
  ⟨.and,[17,46]⟩,
  ⟨.or,[5,6]⟩,
  ⟨.or,[48,8]⟩,
  ⟨.or,[49,1]⟩,
  ⟨.and,[18,50]⟩,
  ⟨.or,[6,7]⟩,
  ⟨.or,[52,9]⟩,
  ⟨.or,[53,2]⟩,
  ⟨.and,[19,54]⟩,
  ⟨.or,[7,8]⟩,
  ⟨.or,[56,10]⟩,
  ⟨.or,[57,3]⟩,
  ⟨.and,[20,58]⟩,
  ⟨.or,[8,9]⟩,
  ⟨.or,[60,11]⟩,
  ⟨.or,[61,4]⟩,
  ⟨.and,[21,62]⟩,
  ⟨.or,[9,10]⟩,
  ⟨.or,[64,12]⟩,
  ⟨.or,[65,5]⟩,
  ⟨.and,[22,66]⟩,
  ⟨.or,[10,11]⟩,
  ⟨.or,[68,0]⟩,
  ⟨.or,[69,6]⟩,
  ⟨.and,[23,70]⟩,
  ⟨.or,[11,12]⟩,
  ⟨.or,[72,1]⟩,
  ⟨.or,[73,7]⟩,
  ⟨.and,[24,74]⟩,
  ⟨.or,[12,0]⟩,
  ⟨.or,[76,2]⟩,
  ⟨.or,[77,8]⟩,
  ⟨.and,[25,78]⟩,
  ⟨.or,[31,35]⟩,
  ⟨.or,[80,39]⟩,
  ⟨.or,[81,43]⟩,
  ⟨.or,[82,47]⟩,
  ⟨.or,[83,51]⟩,
  ⟨.or,[55,59]⟩,
  ⟨.or,[85,63]⟩,
  ⟨.or,[86,67]⟩,
  ⟨.or,[87,71]⟩,
  ⟨.or,[88,75]⟩,
  ⟨.or,[89,79]⟩],90⟩

def row (P L : Finset V) :=
  (List.ofFn fun p : V => decide (p ∈ P)) ++ (List.ofFn fun l : V => decide (l ∈ L))

def value (w : ℕ) (P L : Finset V) := (circuit.wires (row P L)).getD w false

def pairOr (a b : Bool) := GateOp.or.eval [a,b]
def pairAnd (a b : Bool) := GateOp.and.eval [a,b]
def arm (X Y : V → Bool) (l : V) : Bool :=
  let p := pairOr (pairOr (pairOr (X l) (X (l+1))) (X (l+3))) (X (l+9))
  let h := pairAnd (Y l) p
  if l=0 then pairAnd (pairAnd h (Y l)) p else h

def group (X Y : V → Bool) (l : V) (xs : List V) :=
  xs.foldl (fun a i => pairOr a (arm X Y i)) (arm X Y l)


inductive Expr where
  | pt (i : V)
  | ln (i : V)
  | bottom
  | both (a b : Expr)
  | either (a b : Expr)
  deriving DecidableEq

def Expr.val (X Y : V → Bool) : Expr → Bool
  | .pt i => X i
  | .ln i => Y i
  | .bottom => false
  | .both a b => pairAnd (a.val X Y) (b.val X Y)
  | .either a b => pairOr (a.val X Y) (b.val X Y)

def step (ws : List Expr) (g : Gate) : List Expr :=
  let inp := g.inputs.map fun i => ws.getD i .bottom
  ws ++ [match g.op, inp with
    | .and, [a,b] => .both a b
    | .or, [a,b] => .either a b
    | _, _ => .bottom]

def bin (g : Gate) := g.inputs.length=2 ∧ (g.op=.and ∨ g.op=.or)

theorem simulate (X Y : V → Bool) (gs : List Gate) (ws : List Expr)
    (ok : ∀ g ∈ gs, bin g) :
    (gs.foldl step ws).map (Expr.val X Y) =
    gs.foldl (fun t g => t ++ [g.op.eval (g.inputs.map fun i => t.getD i false)])
      (ws.map (Expr.val X Y)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih _ (fun q h => ok _ (List.mem_cons_of_mem _ h))]
    obtain ⟨len,op⟩ := ok g (by simp)
    obtain ⟨a,b,ab⟩ := List.length_eq_two.mp len
    have lookup (i : ℕ) : (ws.map (Expr.val X Y)).getD i false = (ws.getD i .bottom).val X Y := by
      change (ws.map (Expr.val X Y)).getD i ((Expr.bottom).val X Y) = _
      rw [List.getD_map]
    rcases op with op|op <;> simp only [step,op,ab,List.map_cons,List.map_nil,List.map_append,Expr.val,lookup,pairAnd,pairOr]

def start : List Expr := (List.ofFn fun i : V => Expr.pt i) ++ List.ofFn fun i : V => Expr.ln i

def symbolicArm (l : V) : Expr :=
  let p := Expr.either (.either (.either (.pt l) (.pt (l+1))) (.pt (l+3))) (.pt (l+9))
  let h := Expr.both (.ln l) p
  if l=0 then .both (.both h (.ln l)) p else h

def symbolicGroup (l : V) (xs : List V) :=
  xs.foldl (fun a i => .either a (symbolicArm i)) (symbolicArm l)

theorem armValue (l : V) (X Y : V → Bool) : (symbolicArm l).val X Y = arm X Y l := by
  by_cases h : l=0 <;> simp [symbolicArm,arm,h,Expr.val]

theorem groupValue (l : V) (xs : List V) (X Y : V → Bool) :
    (symbolicGroup l xs).val X Y = group X Y l xs := by
  have fold (t : List V) (a : Expr) :
      (t.foldl (fun e i => Expr.either e (symbolicArm i)) a).val X Y =
        t.foldl (fun e i => pairOr e (arm X Y i)) (a.val X Y) := by
    induction t generalizing a with
    | nil => rfl
    | cons i is ih => simp only [List.foldl_cons,ih,Expr.val,armValue]
  exact (fold xs (symbolicArm l)).trans (by rw [armValue];rfl)

set_option maxRecDepth 30000 in
theorem trees : (circuit.gates.foldl step start).getD 84 .bottom = symbolicGroup 0 [1,2,3,4,5] ∧
    (circuit.gates.foldl step start).getD 90 .bottom = symbolicGroup 6 [7,8,9,10,11,12] := by decide +kernel

def binaryTest (g : Gate) := decide (g.inputs.length=2) && match g.op with
  | .and | .or => true
  | _ => false

theorem gateBinary : ∀ g ∈ circuit.gates, bin g := by
  have yes : circuit.gates.all binaryTest = true := by decide +kernel
  intro g h
  have hit := List.all_eq_true.mp yes g h
  cases g with
  | mk op inputs => cases op <;> simp_all [binaryTest,bin]

theorem outputs (P L : Finset V) :
    let X := fun p : V => decide (p ∈ P)
    let Y := fun l : V => decide (l ∈ L)
    value 84 P L = group X Y 0 [1,2,3,4,5] ∧
    value 90 P L = group X Y 6 [7,8,9,10,11,12] := by
  let X := fun p : V => decide (p ∈ P)
  let Y := fun l : V => decide (l ∈ L)
  have tape : start.map (Expr.val X Y) = row P L := by
    simp [start,row,Expr.val,X,Y]
  have sim := simulate X Y circuit.gates start gateBinary
  rw [tape] at sim
  change _ = circuit.wires (row P L) at sim
  have wire (j : ℕ) : value j P L = ((circuit.gates.foldl step start).getD j .bottom).val X Y := by
    unfold value
    rw [←sim]
    change ((circuit.gates.foldl step start).map (Expr.val X Y)).getD j (Expr.bottom.val X Y) = _
    rw [List.getD_map]
  rw [wire 84,wire 90,trees.1,trees.2,groupValue,groupValue]
  exact ⟨rfl,rfl⟩

theorem neighbors : ∀ l : V, l ∈ singerLines3 l ∧ l+1 ∈ singerLines3 l ∧
    l+3 ∈ singerLines3 l ∧ l+9 ∈ singerLines3 l := by decide +kernel

theorem arm_off (P : Finset V) (l : V) :
    arm (fun p => decide (p∈P)) (fun j => decide (j ∈ missLines singerLines3 P)) l = false := by
  by_cases h : l ∈ missLines singerLines3 P
  · have dis : Disjoint (singerLines3 l) P := (Finset.mem_filter.mp h).2
    have say (p : V) (hp : p ∈ singerLines3 l) : p ∉ P := Finset.disjoint_left.mp dis hp
    obtain ⟨a,b,c,d⟩ := neighbors l
    simp [arm,pairAnd,pairOr,GateOp.eval,say _ a,say _ b,say _ c,say _ d]
  · simp [arm,pairAnd,GateOp.eval,h]

theorem reject (P : Finset V) :
    value 84 P (missLines singerLines3 P) = false ∧ value 90 P (missLines singerLines3 P) = false := by
  obtain ⟨u,v⟩ := outputs P (missLines singerLines3 P)
  rw [u,v]
  simp [group,arm_off,pairOr,GateOp.eval]

set_option maxRecDepth 30000 in
theorem cover : ∀ p l : V, p ∈ singerLines3 l →
    group (fun i => decide (i ∈ ({p} : Finset V))) (fun i => decide (i ∈ ({l} : Finset V))) 0 [1,2,3,4,5] = true ∨
    group (fun i => decide (i ∈ ({p} : Finset V))) (fun i => decide (i ∈ ({l} : Finset V))) 6 [7,8,9,10,11,12] = true := by decide +kernel

def isDirect (j : ℕ) : Prop :=
  (NestedCover.gateAt circuit j).op = .and ∧
  ∃ w ∈ (NestedCover.gateAt circuit j).inputs, 26 ≤ w ∧ (NestedCover.gateAt circuit (w-26)).op = .and

def opIsAnd : GateOp → Bool
  | .and => true
  | _ => false

theorem and_iff (op : GateOp) : opIsAnd op = true ↔ op = .and := by cases op <;> simp [opIsAnd]

def directTest (j : ℕ) :=
  let g := NestedCover.gateAt circuit j
  opIsAnd g.op && g.inputs.any (fun w => decide (26≤w) && opIsAnd (NestedCover.gateAt circuit (w-26)).op)

theorem direct_iff (j : ℕ) : directTest j = true ↔ isDirect j := by
  simp [directTest,isDirect,and_iff]

theorem two_direct : ∀ j : Fin 65, directTest j.val = decide (j.val=4 ∨ j.val=5) := by decide +kernel

theorem exact_size : circuit.size=65 := rfl

theorem cover_wires (p l : V) (h : p ∈ singerLines3 l) :
    value 84 {p} {l} = true ∨ value 90 {p} {l} = true := by
  obtain ⟨u,v⟩ := outputs {p} {l}
  rw [u,v]
  exact cover p l h

theorem private_flags :
    (value 84 {0} {0} = true ∧ value 90 {0} {0} = false) ∧
    (value 84 {6} {6} = false ∧ value 90 {6} {6} = true) := by decide +kernel


def legalOp : GateOp → Bool
  | .and | .or => true
  | _ => false

theorem legalOp_iff (op : GateOp) : legalOp op = true ↔ op = .and ∨ op = .or := by
  cases op <;> simp [legalOp]

theorem syntax_check : ∀ j : Fin 65,
    let g := NestedCover.gateAt circuit j.val
    legalOp g.op = true ∧ g.inputs.length ≤ 2 ∧ ∀ w ∈ g.inputs, w < 26+j.val := by decide +kernel

theorem well_formed : Monotone2 circuit ∧ NestedCover.ReadsBack 26 circuit := by
  constructor
  · intro g hg
    obtain ⟨j,hj,eq⟩ := List.getElem_of_mem hg
    have atGate : NestedCover.gateAt circuit j = g := by
      simpa [NestedCover.gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using eq
    have facts := syntax_check ⟨j,hj⟩
    change legalOp (NestedCover.gateAt circuit j).op = true ∧ _ at facts
    rw [atGate] at facts
    exact ⟨(legalOp_iff g.op).mp facts.1,facts.2.1⟩
  · intro j hj
    exact (syntax_check ⟨j,hj⟩).2.2

theorem marked : ∃ u ∈ Finset.range circuit.size, ∃ v ∈ Finset.range circuit.size,
    u ≠ v ∧ isDirect u ∧ isDirect v ∧ ∀ j ∈ Finset.range circuit.size,
      isDirect j → j=u ∨ j=v := by
  refine ⟨4,by decide,5,by decide,by decide,(direct_iff 4).mp (by decide),
    (direct_iff 5).mp (by decide),?_⟩
  intro j hj h
  have ok := (direct_iff j).mpr h
  rw [show directTest j = decide (j=4 ∨ j=5) from two_direct ⟨j,Finset.mem_range.mp hj⟩] at ok
  simpa using ok


theorem feasible65 :
    circuit.size = 65 ∧ Monotone2 circuit ∧ NestedCover.ReadsBack 26 circuit ∧
    84 < 26 + circuit.size ∧ 90 < 26 + circuit.size ∧
    (∀ p l : V, p ∈ singerLines3 l → value 84 {p} {l} = true ∨ value 90 {p} {l} = true) ∧
    (∀ Q : Finset V, IsQuadrangle singerLines3 Q →
      value 84 Q (missLines singerLines3 Q) = false ∧ value 90 Q (missLines singerLines3 Q) = false) ∧
    (∃ p l : V, p ∈ singerLines3 l ∧ value 84 {p} {l} = true ∧ value 90 {p} {l} = false) ∧
    (∃ p l : V, p ∈ singerLines3 l ∧ value 90 {p} {l} = true ∧ value 84 {p} {l} = false) ∧
    (∃ u ∈ Finset.range circuit.size, ∃ v ∈ Finset.range circuit.size,
      u ≠ v ∧ isDirect u ∧ isDirect v ∧ ∀ j ∈ Finset.range circuit.size,
        isDirect j → j=u ∨ j=v) := by
  exact ⟨exact_size,well_formed.1,well_formed.2,by decide,by decide,cover_wires,
    fun Q _ => reject Q,⟨0,0,by decide,private_flags.1⟩,
    ⟨6,6,by decide,private_flags.2.2,private_flags.2.1⟩,marked⟩

end QuadrangleStarCores.Control
