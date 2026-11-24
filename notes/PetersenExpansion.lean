import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenExpansion

-- Ground constants have no source occurrences. Negation does not change the count.
inductive Expr (n : ℕ)
  | const (b : Bool)
  | src (f : DMFormula n)
  | neg (e : Expr n)
  | and (e d : Expr n)
  | or (e d : Expr n)

def Expr.value {n} (x : Fin n → Bool) : Expr n → Bool
  | .const b => b
  | .src f => f.eval x
  | .neg e => !(e.value x)
  | .and e d => e.value x && d.value x
  | .or e d => e.value x || d.value x

def Expr.mass {n} : Expr n → ℕ
  | .const _ => 0
  | .src f => f.leaves
  | .neg e => e.mass
  | .and e d | .or e d => e.mass + d.mass

def dual {n} : DMFormula n → DMFormula n
  | .lit i b => .lit i (!b)
  | .and f g => .or (dual f) (dual g)
  | .or f g => .and (dual f) (dual g)

theorem dual_props {n} (f : DMFormula n) :
    (dual f).leaves = f.leaves ∧ ∀ x, (dual f).eval x = !(f.eval x) := by
  induction f with
  | lit i b => cases b <;> simp [dual, DMFormula.leaves, DMFormula.eval]
  | and f g hf hg => simp [dual, DMFormula.leaves, DMFormula.eval, hf.1, hg.1, hf.2, hg.2]
  | or f g hf hg => simp [dual, DMFormula.leaves, DMFormula.eval, hf.1, hg.1, hf.2, hg.2]

theorem normalize {n} (e : Expr n) :
    (∃ b : Bool, ∀ x, e.value x = b) ∨
    ∃ f : DMFormula n, f.leaves ≤ e.mass ∧ ∀ x, f.eval x = e.value x := by
  induction e with
  | const b => exact Or.inl ⟨b, fun _ => rfl⟩
  | src f => exact Or.inr ⟨f, le_rfl, fun _ => rfl⟩
  | neg e ih =>
    rcases ih with ⟨b,h⟩ | ⟨f,k,h⟩
    · exact Or.inl ⟨!b, fun x => by simp [Expr.value,h]⟩
    · exact Or.inr ⟨dual f,(dual_props f).1 ▸ k,fun x => by simp [Expr.value,(dual_props f).2,h]⟩
  | and e d he hd =>
    rcases he with ⟨b,h⟩ | ⟨f,k,h⟩ <;> rcases hd with ⟨c,j⟩ | ⟨g,l,j⟩
    · exact Or.inl ⟨b && c,fun x => by simp [Expr.value,h,j]⟩
    · cases b
      · exact Or.inl ⟨false,fun x => by simp [Expr.value,h]⟩
      · exact Or.inr ⟨g,by simp only [Expr.mass]; omega,fun x => by simp [Expr.value,h,j]⟩
    · cases c
      · exact Or.inl ⟨false,fun x => by simp [Expr.value,j]⟩
      · exact Or.inr ⟨f,by simp only [Expr.mass]; omega,fun x => by simp [Expr.value,h,j]⟩
    · exact Or.inr ⟨.and f g,Nat.add_le_add k l,fun x => by simp [Expr.value,DMFormula.eval,h,j]⟩
  | or e d he hd =>
    rcases he with ⟨b,h⟩ | ⟨f,k,h⟩ <;> rcases hd with ⟨c,j⟩ | ⟨g,l,j⟩
    · exact Or.inl ⟨b || c,fun x => by simp [Expr.value,h,j]⟩
    · cases b
      · exact Or.inr ⟨g,by simp only [Expr.mass]; omega,fun x => by simp [Expr.value,h,j]⟩
      · exact Or.inl ⟨true,fun x => by simp [Expr.value,h]⟩
    · cases c
      · exact Or.inr ⟨f,by simp only [Expr.mass]; omega,fun x => by simp [Expr.value,h,j]⟩
      · exact Or.inl ⟨true,fun x => by simp [Expr.value,j]⟩
    · exact Or.inr ⟨.or f g,Nat.add_le_add k l,fun x => by simp [Expr.value,DMFormula.eval,h,j]⟩

def build {n} (op : GateOp) (args : List (Expr n)) : Expr n :=
  match op with
  | .and => args.foldr Expr.and (.const true)
  | .or => args.foldr Expr.or (.const false)
  | .not => .neg (args.headD (.const false))
  | _ => .const false

def massOp (op : GateOp) (args : List ℕ) : ℕ :=
  if op.eval [false] then args.headD 0 else args.sum

theorem build_ok {n} (op : GateOp) (args : List (Expr n)) (valid : op = .and ∨ op = .or ∨ op = .not) :
    (build op args).mass = massOp op (args.map Expr.mass) ∧
    ∀ x, (build op args).value x = op.eval (args.map (Expr.value x)) := by
  rcases valid with rfl | rfl | rfl
  · induction args with
    | nil => exact ⟨rfl,fun _ => rfl⟩
    | cons a l ih =>
      exact ⟨congrArg (a.mass + ·) ih.1,fun x => congrArg (a.value x && ·) (ih.2 x)⟩
  · induction args with
    | nil => exact ⟨rfl,fun _ => rfl⟩
    | cons a l ih =>
      exact ⟨congrArg (a.mass + ·) ih.1,fun x => congrArg (a.value x || ·) (ih.2 x)⟩
  · cases args <;> exact ⟨rfl,fun _ => rfl⟩

def addGate {n} (w : List (Expr n)) (g : Gate) : List (Expr n) :=
  w ++ [build g.op (g.inputs.map fun i => w.getD i (.const false))]

theorem at_map {α β} (h : α → β) (w : List α) (i : ℕ) (d : α) :
    h (w.getD i d) = (w.map h).getD i (h d) := by
  simp [List.getD, List.getElem?_map, Option.getD_map]

theorem fold_map {α β} (h : α → β) (step : α → Gate → α) (next : β → Gate → β)
    (gs : List Gate) (valid : ∀ g ∈ gs, ∀ w, h (step w g) = next (h w) g)
    (w : α) : h (gs.foldl step w) = gs.foldl next (h w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih (fun k hk => valid k (List.mem_cons_of_mem _ hk)),valid g (by simp)]

theorem expansion (n : ℕ) (C : Circuit) (hc : FanInTwo C) (fs : List (DMFormula n)) :
    let w := C.gates.foldl (fun (w : List ℕ) g =>
      let args := g.inputs.map fun i => w.getD i 0
      w ++ [if g.op.eval [false] then args.headD 0 else args.sum]) (fs.map DMFormula.leaves)
    (∃ b : Bool, ∀ x, C.eval (fs.map fun f => f.eval x) = b) ∨
    ∃ f : DMFormula n, f.leaves ≤ w.getD C.output 0 ∧
      ∀ x, f.eval x = C.eval (fs.map fun d => d.eval x) := by
  let w := C.gates.foldl addGate (fs.map Expr.src)
  let result := w.getD C.output (.const false)
  have legal (g : Gate) (hg : g ∈ C.gates) : g.op = .and ∨ g.op = .or ∨ g.op = .not :=
    (hc g hg).1
  have vals (x : Fin n → Bool) : result.value x = C.eval (fs.map fun f => f.eval x) := by
    change Expr.value x (w.getD _ _) = _
    rw [at_map (Expr.value x) w C.output (.const false)]
    unfold w Circuit.eval Circuit.wires
    congr 1
    rw [fold_map (List.map (Expr.value x)) addGate
      (fun (v : List Bool) g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) C.gates]
    · simp [List.map_map,Function.comp_def,Expr.value]
    · intro g hg v
      simp only [addGate,List.map_append,List.map_cons,List.map_nil,(build_ok _ _ (legal g hg)).2,List.map_map,Function.comp_def,at_map (Expr.value x),Expr.value]
  have mass : result.mass = _ := at_map Expr.mass w C.output (.const false)
  rcases normalize result with ⟨b,h⟩ | ⟨f,k,h⟩
  · exact Or.inl ⟨b,fun x => (vals x).symm.trans (h x)⟩
  · refine Or.inr ⟨f,?_,fun x => (h x).trans (vals x)⟩
    apply k.trans
    rw [mass]
    unfold w
    rw [fold_map (List.map Expr.mass) addGate
      (fun (v : List ℕ) g => v ++ [massOp g.op (g.inputs.map fun i => v.getD i 0)]) C.gates]
    · simp [List.map_map,Function.comp_def,Expr.mass,massOp]
    · intro g hg v
      simp only [addGate,List.map_append,List.map_cons,List.map_nil,(build_ok _ _ (legal g hg)).1,List.map_map,Function.comp_def,at_map Expr.mass,Expr.mass]

end PetersenExpansion
