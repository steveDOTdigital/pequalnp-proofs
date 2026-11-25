import PEqualNP.Defs

namespace FanoCosts6176

open PEqualNP.CircuitLowerBounds

/-- Minimum occurrences of the selected shore, with two also representing impossibility. -/
def cost (p : Bool × Bool) : ℕ := if p.1 then 0 else if p.2 then 1 else 2

def mul (a b : Bool × Bool) : Bool × Bool :=
  (a.1 && b.1, (a.1 && b.2) || (a.2 && b.1))

theorem mulCost (a b : Bool × Bool) : cost (mul a b) = min 2 (cost a + cost b) := by
  obtain ⟨p,q⟩ := a
  obtain ⟨r,s⟩ := b
  cases p <;> cases q <;> cases r <;> cases s <;> decide

def gateCost (op : GateOp) (xs : List ℕ) : ℕ :=
  match op with
  | .or => xs.foldl min 2
  | .and => xs.foldl (fun a b => min 2 (a+b)) 0
  | _ => 2

def run (C : Circuit) (xs : List ℕ) : List ℕ :=
  C.gates.foldl (fun w g => w ++ [gateCost g.op (g.inputs.map fun i => w.getD i 2)]) xs

private theorem meetCost (xs : List (Bool × Bool)) (acc : Bool × Bool) :
    cost (xs.foldl mul acc) = (xs.map cost).foldl (fun a b => min 2 (a+b)) (cost acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons p ps ih => simp only [List.foldl_cons,List.map_cons,ih,mulCost]

private theorem orCost (xs : List (Bool × Bool)) (acc : Bool × Bool) :
    cost (acc.1 || xs.any Prod.fst, acc.2 || xs.any Prod.snd) =
      (xs.map cost).foldl min (cost acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.any_cons,List.map_cons,List.foldl_cons]
    obtain ⟨a,b⟩ := acc
    obtain ⟨c,d⟩ := p
    have h := ih (a || c,b || d)
    cases a <;> cases b <;> cases c <;> cases d <;> simpa [cost] using h

def pairGate (op : GateOp) (ps : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | .or => (ps.any Prod.fst, ps.any Prod.snd)
  | .and => ps.foldl mul (true,false)
  | _ => (false,false)

theorem gateTransfer (op : GateOp) (ps : List (Bool × Bool)) :
    cost (pairGate op ps) = gateCost op (ps.map cost) := by
  cases op with
  | and => exact meetCost ps (true,false)
  | or => simpa [cost,pairGate,gateCost] using orCost ps (false,false)
  | _ => rfl

def pairStep (w : List (Bool × Bool)) (g : Gate) : List (Bool × Bool) :=
  w ++ [pairGate g.op (g.inputs.map fun i => w.getD i (false,false))]

theorem lookup (w : List (Bool × Bool)) (i : ℕ) :
    (w.map cost).getD i 2 = cost (w.getD i (false,false)) := by
  simp only [List.getD, List.getElem?_map]
  cases w[i]? <;> rfl

theorem foldTransfer (gs : List Gate) (w : List (Bool × Bool)) :
    (gs.foldl pairStep w).map cost =
      gs.foldl (fun t g => t ++ [gateCost g.op (g.inputs.map fun i => t.getD i 2)]) (w.map cost) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g tail ih =>
    simp only [List.foldl_cons,ih]
    simp only [pairStep,List.map_append,List.map_cons,List.map_nil,gateTransfer,List.map_map,
      Function.comp_def,lookup]

def seed (side : ℕ → Bool) (x : List Bool) :=
  x.zipIdx.map fun (b,i) => if b then (if side i then 1 else 0) else 2

theorem transfer (C : Circuit) (side : ℕ → Bool) (x : List Bool) :
    (PEqualNP.ReadK.linearParts C side x).map cost = run C (seed side x) := by
  let w := x.zipIdx.map fun (b,i) => if side i then (false,b) else (b,false)
  change (C.gates.foldl pairStep w).map cost = _
  rw [foldTransfer]
  change run C (w.map cost) = run C (seed side x)
  apply congrArg (run C)
  simp only [w, seed, List.map_map,Function.comp_def]
  apply List.map_congr_left
  rintro ⟨b,i⟩ _
  cases b <;> cases h : side i <;> simp [cost]

theorem degreeOne (C : Circuit) (side : ℕ → Bool) (x : List Bool) (out : ℕ)
    (h : (run C (seed side x)).getD out 2 = 1) :
    ((PEqualNP.ReadK.linearParts C side x).getD out (false,false)).2 = true := by
  rw [← transfer, lookup] at h
  rcases hq : (PEqualNP.ReadK.linearParts C side x).getD out (false,false) with ⟨a,b⟩
  rw [hq] at h
  cases a <;> cases b <;> simp_all [cost]

def truthCost (b : Bool) : ℕ := if b then 0 else 2

private theorem minTruth (a b : Bool) :
    truthCost (a || b) = min (truthCost a) (truthCost b) := by cases a <;> cases b <;> decide

private theorem addTruth (a b : Bool) :
    truthCost (a && b) = min 2 (truthCost a + truthCost b) := by cases a <;> cases b <;> decide

theorem boolLookup (w : List Bool) (i : ℕ) :
    (w.map truthCost).getD i 2 = truthCost (w.getD i false) := by
  simp only [List.getD,List.getElem?_map]
  cases w[i]? <;> rfl

theorem ordinary (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 14 C) (x : List Bool) :
    (run C (x.map truthCost)).getD C.output 2 = truthCost (C.eval x) := by
  let boolStep := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let numeric := fun (t : List ℕ) (g : Gate) =>
    t ++ [gateCost g.op (g.inputs.map fun i => t.getD i 2)]
  have fold (gs : List Gate) (w : List Bool) (valid : ∀ g ∈ gs,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
      (gs.foldl boolStep w).map truthCost = gs.foldl numeric (w.map truthCost) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g tail ih =>
      simp only [List.foldl_cons]
      rw [ih _ (fun g h => valid g (List.mem_cons_of_mem _ h))]
      apply congrArg (fun t => tail.foldl numeric t)
      obtain ⟨op,arity⟩ := valid g (by simp)
      rcases ins : g.inputs with _ | ⟨i,is⟩ <;> simp_all
      rcases is with _ | ⟨j,rest⟩ <;> simp_all
      rcases op with e|e <;>
        simp only [boolStep,numeric,ins,List.map_append,List.map_cons,List.map_nil,boolLookup,e,gateCost,
          List.foldl_cons,List.foldl_nil] <;>
        cases ha : w.getD i false <;> cases hb : w.getD j false <;> rfl
  have h := fold C.gates x (fun g mem => ⟨ao.1 _ mem,ao.2.2 _ mem⟩)
  change (C.gates.foldl numeric (x.map truthCost)).getD C.output 2 =
    truthCost ((C.gates.foldl boolStep x).getD C.output false)
  rw [← h,boolLookup]

open PEqualNP.TopForm in
theorem ordinaryChild : ∀ (C : Circuit), IsAO2 14 C → ∀ x : List Bool,
      (fun (xs : List ℕ) => (C.gates.foldl (fun w g =>
        let ys := g.inputs.map fun i => w.getD i 2
        w ++ [match g.op with
          | .or => ys.foldl min 2
          | .and => ys.foldl (fun a b => min 2 (a+b)) 0
          | _ => 2]) xs).getD C.output 2) (x.map fun b => if b then 0 else 2) =
        (if C.eval x then 0 else 2) := by
  intro C ao x
  exact ordinary C ao x

theorem linearChild : ∀ (C : Circuit) (side : ℕ → Bool) (x : List Bool),
      (fun (xs : List ℕ) => (C.gates.foldl (fun w g =>
        let ys := g.inputs.map fun i => w.getD i 2
        w ++ [match g.op with
          | .or => ys.foldl min 2
          | .and => ys.foldl (fun a b => min 2 (a+b)) 0
          | _ => 2]) xs).getD C.output 2) (x.zipIdx.map fun (b,i) => if b then (if side i then 1 else 0) else 2) = 1 →
        ((PEqualNP.ReadK.linearParts C side x).getD C.output (false,false)).2 = true := by
  intro C side x h
  exact degreeOne C side x C.output h

end FanoCosts6176
