import PEqualNP.Defs

namespace PlaneTwoOutputs8059

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover

abbrev V := Fin 13

def circuit : Circuit := ⟨[
  ⟨.or,[0,1]⟩, ⟨.or,[26,3]⟩, ⟨.or,[27,9]⟩,
  ⟨.or,[1,2]⟩, ⟨.or,[29,4]⟩, ⟨.or,[30,10]⟩,
  ⟨.or,[2,3]⟩, ⟨.or,[32,5]⟩, ⟨.or,[33,11]⟩,
  ⟨.or,[3,4]⟩, ⟨.or,[35,6]⟩, ⟨.or,[36,12]⟩,
  ⟨.or,[4,5]⟩, ⟨.or,[38,7]⟩, ⟨.or,[39,0]⟩,
  ⟨.or,[5,6]⟩, ⟨.or,[41,8]⟩, ⟨.or,[42,1]⟩,
  ⟨.or,[6,7]⟩, ⟨.or,[44,9]⟩, ⟨.or,[45,2]⟩,
  ⟨.or,[7,8]⟩, ⟨.or,[47,10]⟩, ⟨.or,[48,3]⟩,
  ⟨.or,[8,9]⟩, ⟨.or,[50,11]⟩, ⟨.or,[51,4]⟩,
  ⟨.or,[9,10]⟩, ⟨.or,[53,12]⟩, ⟨.or,[54,5]⟩,
  ⟨.or,[10,11]⟩, ⟨.or,[56,0]⟩, ⟨.or,[57,6]⟩,
  ⟨.or,[11,12]⟩, ⟨.or,[59,1]⟩, ⟨.or,[60,7]⟩,
  ⟨.or,[12,0]⟩, ⟨.or,[62,2]⟩, ⟨.or,[63,8]⟩,
  ⟨.and,[14,31]⟩, ⟨.and,[15,34]⟩, ⟨.and,[16,37]⟩,
  ⟨.and,[17,40]⟩, ⟨.and,[18,43]⟩, ⟨.and,[19,46]⟩,
  ⟨.and,[20,49]⟩, ⟨.and,[21,52]⟩, ⟨.and,[22,55]⟩,
  ⟨.and,[23,58]⟩, ⟨.and,[24,61]⟩, ⟨.and,[25,64]⟩,
  ⟨.or,[65,66]⟩, ⟨.or,[77,67]⟩, ⟨.or,[78,68]⟩,
  ⟨.or,[79,69]⟩, ⟨.or,[80,70]⟩, ⟨.or,[81,71]⟩,
  ⟨.or,[82,72]⟩, ⟨.or,[83,73]⟩, ⟨.or,[84,74]⟩,
  ⟨.or,[85,75]⟩, ⟨.and,[13,28]⟩, ⟨.or,[86,76]⟩],88⟩

def row (P L : Finset V) :=
  (List.ofFn fun p : V => decide (p ∈ P)) ++ (List.ofFn fun l : V => decide (l ∈ L))

def value (w : ℕ) (P L : Finset V) := (circuit.wires (row P L)).getD w false

def pairOr (a b : Bool) := GateOp.or.eval [a,b]
def pairAnd (a b : Bool) := GateOp.and.eval [a,b]
def arm (X Y : V → Bool) (l : V) : Bool :=
  let p := pairOr (pairOr (pairOr (X l) (X (l+1))) (X (l+3))) (X (l+9))
  pairAnd (Y l) p

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
  Expr.both (.ln l) p

def symbolicGroup (l : V) (xs : List V) :=
  xs.foldl (fun a i => .either a (symbolicArm i)) (symbolicArm l)

theorem armValue (l : V) (X Y : V → Bool) : (symbolicArm l).val X Y = arm X Y l := by
  simp [symbolicArm,arm,Expr.val]

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
theorem trees : (circuit.gates.foldl step start).getD 87 .bottom = symbolicGroup 0 [] ∧
    (circuit.gates.foldl step start).getD 88 .bottom = symbolicGroup 1 [2,3,4,5,6,7,8,9,10,11,12] := by decide +kernel

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
    value 87 P L = group X Y 0 [] ∧
    value 88 P L = group X Y 1 [2,3,4,5,6,7,8,9,10,11,12] := by
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
  rw [wire 87,wire 88,trees.1,trees.2,groupValue,groupValue]
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
    value 87 P (missLines singerLines3 P) = false ∧ value 88 P (missLines singerLines3 P) = false := by
  obtain ⟨u,v⟩ := outputs P (missLines singerLines3 P)
  rw [u,v]
  simp [group,arm_off,pairOr,GateOp.eval]

set_option maxRecDepth 30000 in
theorem cover : ∀ p l : V, p ∈ singerLines3 l →
    group (fun i => decide (i ∈ ({p} : Finset V))) (fun i => decide (i ∈ ({l} : Finset V))) 0 [] = true ∨
    group (fun i => decide (i ∈ ({p} : Finset V))) (fun i => decide (i ∈ ({l} : Finset V))) 1 [2,3,4,5,6,7,8,9,10,11,12] = true := by decide +kernel

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

theorem no_direct : ∀ j : Fin 63, directTest j.val = false := by decide +kernel

theorem exact_size : circuit.size=63 := rfl

theorem cover_wires (p l : V) (h : p ∈ singerLines3 l) :
    value 87 {p} {l} = true ∨ value 88 {p} {l} = true := by
  obtain ⟨u,v⟩ := outputs {p} {l}
  rw [u,v]
  exact cover p l h

theorem private_flags :
    (value 87 {0} {0} = true ∧ value 88 {0} {0} = false) ∧
    (value 87 {0} {4} = false ∧ value 88 {0} {4} = true) := by decide +kernel


def legalOp : GateOp → Bool
  | .and | .or => true
  | _ => false

theorem legalOp_iff (op : GateOp) : legalOp op = true ↔ op = .and ∨ op = .or := by
  cases op <;> simp [legalOp]

theorem syntax_check : ∀ j : Fin 63,
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

theorem noneDirect : ∀ j < circuit.size, ¬ isDirect j := by
  intro j bound hit
  have bad := (direct_iff j).mpr hit
  rw [no_direct ⟨j,bound⟩] at bad
  contradiction

theorem directCount :
    ({j | j < circuit.size ∧ isDirect j} : Set Nat).encard = 0 := by
  have no : ({j | j < circuit.size ∧ isDirect j} : Set Nat) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro j hit
    exact noneDirect j hit.1 hit.2
  rw [no]
  simp

theorem feasible63 :
    circuit.size = 63 ∧ Monotone2 circuit ∧ NestedCover.ReadsBack 26 circuit ∧
    26 ≤ (87 : Nat) ∧ 87 < (25 : Nat) + circuit.size ∧
    (∀ p l : V, p ∈ singerLines3 l → value 87 {p} {l} = true ∨ value 88 {p} {l} = true) ∧
    (∀ Q : Finset V, IsQuadrangle singerLines3 Q →
      (value 87 Q (missLines singerLines3 Q) || value 88 Q (missLines singerLines3 Q)) = false) ∧
    (∀ b : Bool, ∃ p l : V, p ∈ singerLines3 l ∧ value 87 {p} {l} = b ∧
      value 88 {p} {l} = !b) := by
  refine ⟨exact_size,well_formed.1,well_formed.2,by decide,by decide,cover_wires,?_,?_⟩
  · intro Q _
    rw [(reject Q).1,(reject Q).2]
    rfl
  · intro b
    cases b
    · exact ⟨0,4,by decide,private_flags.2.1,private_flags.2.2⟩
    · exact ⟨0,0,by decide,private_flags.1.1,private_flags.1.2⟩

theorem factorGuard (b : Bool) (guards : List Bool) :
    guards.any (fun g => b && g) = (b && guards.any id) := by
  cases b <;> induction guards <;> simp_all

#print axioms directCount
#print axioms feasible63
#print axioms factorGuard

end PlaneTwoOutputs8059
