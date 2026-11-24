import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PlaneClauseCompiler

abbrev Family (n : ℕ) := Finset (Finset (Fin n))

def holds (x : Fin n → Bool) (f : Family n) : Prop :=
  ∀ s ∈ f, ∃ i ∈ s, x i = true

def product (f h : Family n) : Family n := f.biUnion (fun a => h.image (a ∪ ·))

theorem holds_product (x : Fin n → Bool) (f h : Family n) :
    holds x (product f h) ↔ holds x f ∨ holds x h := by
  classical
  constructor
  · intro hp
    by_cases left : holds x f
    · exact Or.inl left
    right
    simp only [holds, not_forall, not_exists] at left
    obtain ⟨a, ha, none⟩ := left
    intro b hb
    have ab : a ∪ b ∈ product f h :=
      Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨b,hb,rfl⟩⟩
    obtain ⟨i, hi, hot⟩ := hp _ ab
    rcases Finset.mem_union.mp hi with first | second
    · exact False.elim (none i ⟨first, hot⟩)
    · exact ⟨i, second, hot⟩
  · intro sides s hs
    obtain ⟨a, ha, member⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp member
    rcases sides with left | right
    · obtain ⟨i, hi, hx⟩ := left a ha
      exact ⟨i, Finset.mem_union_left _ hi, hx⟩
    · obtain ⟨i, hi, hx⟩ := right b hb
      exact ⟨i, Finset.mem_union_right _ hi, hx⟩

theorem holds_union (x : Fin n → Bool) (f h : Family n) :
    holds x (f ∪ h) ↔ holds x f ∧ holds x h := by
  simp only [holds, Finset.mem_union, or_imp, forall_and]

def atom (i : Fin n) : Family n := {{i}}
def bot (n : ℕ) : Family n := {∅}
def value (x : Fin n → Bool) (s : Family n) : Bool :=
  decide (∀ a ∈ s, ∃ i ∈ a, x i = true)

@[simp] theorem val_true (x : Fin n → Bool) (f : Family n) :
    value x f = true ↔ holds x f := by simp [value, holds]
@[simp] theorem val_atom (x : Fin n → Bool) (i : Fin n) : value x (atom i) = x i := by
  cases hv : x i <;> simp [value, atom, hv]
@[simp] theorem val_bot (x : Fin n → Bool) : value x (bot n) = false := by simp [value, bot]

def combine (g : Gate) (u v : Family n) : Family n :=
  if g.op.eval [false, true] then product u v else u ∪ v

def step (w : List (Family n)) (g : Gate) : List (Family n) :=
  w ++ [combine g (w.getD (g.inputs.getD 0 0) (bot n)) (w.getD (g.inputs.getD 1 0) (bot n))]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem val_getD (x : Fin n → Bool) (w : List (Family n)) (i : ℕ) :
    value x (w.getD i (bot n)) = (w.map (value x)).getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · simp [Nat.le_of_not_gt hi]

theorem val_union (x : Fin n → Bool) (a b : Family n) :
    value x (a ∪ b) = (value x a && value x b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [val_true, Bool.and_eq_true, holds_union]

theorem val_product (x : Fin n → Bool) (a b : Family n) :
    value x (product a b) = (value x a || value x b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [val_true, Bool.or_eq_true, holds_product]

theorem map_step (x : Fin n → Bool) (w : List (Family n)) (g : Gate)
    (kind : g.op = .and ∨ g.op = .or) (a b : ℕ) (ins : g.inputs = [a,b]) :
    (step w g).map (value x) = boolStep (w.map (value x)) g := by
  simp only [step, boolStep, List.map_append, List.map_singleton, ins]
  congr 1
  apply congrArg List.singleton
  rcases kind with h | h <;>
    simp [combine, h, GateOp.eval, val_product, val_union] <;>
    cases w[a]? <;> cases w[b]? <;> simp

theorem map_run (x : Fin n → Bool) (gs : List Gate) (w : List (Family n))
    (shape : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b]) :
    (gs.foldl step w).map (value x) = gs.foldl boolStep (w.map (value x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,a,b,ab⟩ := shape g List.mem_cons_self
    simp only [List.foldl_cons]
    rw [ih _ (fun k hk => shape k (List.mem_cons_of_mem _ hk)), map_step x w g op a b ab]

theorem saved (gs : List Gate) (w : List (Family n)) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i (bot n) = w.getD i (bot n) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD i _ = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem gate_value (gs : List Gate) (w : List (Family n)) (j : ℕ) (hj : j < gs.length)
    (a b : ℕ) (ins : gs[j].inputs = [a,b]) (ha : a < w.length+j) (hb : b < w.length+j) :
    let result := gs.foldl step w
    result.getD (w.length+j) (bot n) = combine gs[j] (result.getD a (bot n)) (result.getD b (bot n)) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at ha hb ins ⊢
      dsimp only [List.foldl_cons]
      rw [saved gs _ _ (by simp [step]), saved gs _ a (by simp [step]; omega),
        saved gs _ b (by simp [step]; omega)]
      simp only [step]
      rw [List.getD_append _ _ _ _ ha, List.getD_append _ _ _ _ hb]
      simp [ins]
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have len : (step w g).length = w.length+1 := by simp [step]
      have eq : w.length + (j+1) = (step w g).length + j := by omega
      simpa only [List.foldl_cons, List.getElem_cons_succ, eq] using
        ih (step w g) j hj' ins (by omega) (by omega)

theorem compile (n : ℕ) (C : Circuit) (mono : Monotone2 C)
    (order : ∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a,b] ∧ a < b ∧ b < n+j) :
    ∃ F : ℕ → Finset (Finset (Fin n)),
      (∀ i : Fin n, F i = {{i}}) ∧
      (∀ j (hj : j < C.size), ∃ a b, C.gates[j].inputs = [a,b] ∧ a < b ∧ b < n+j ∧
        F (n+j) = (if C.gates[j].op.eval [false,true] then
          (F a).biUnion (fun u => (F b).image (u ∪ ·)) else F a ∪ F b)) ∧
      (∀ xs : List Bool, xs.length = n → ∀ w, (C.wires xs).getD w false = true ↔
        ∀ t ∈ F w, ∃ i ∈ t, xs.getD i.val false = true) := by
  let inputs := List.ofFn (atom (n := n))
  let regs := C.gates.foldl step inputs
  let F := fun i => regs.getD i (bot n)
  have length : inputs.length = n := List.length_ofFn
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    change (C.gates.foldl step inputs).getD i.val _ = _
    rw [saved _ _ _ (by rw [length]; exact i.isLt)]
    simp [inputs, i.isLt, atom]
  · intro j hj
    have someGate : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
    obtain ⟨a,b,ins,ab,bj⟩ := order j _ someGate
    refine ⟨a,b,ins,ab,bj,?_⟩
    have eq := gate_value C.gates inputs j hj a b ins (by omega) (by omega)
    change F (inputs.length+j) = combine _ (F a) (F b) at eq
    simpa only [length, combine, product] using eq
  · intro xs hlen w
    let x := fun i : Fin n => xs.getD i.val false
    have exactInput : List.ofFn x = xs := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi hj
        simp [x, List.getElem?_eq_getElem hj]
    have shape : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] := by
      intro g hg
      obtain ⟨j, hj, hjg⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a,b,ins,_⟩ := order j g (hjg ▸ List.getElem?_eq_getElem hj)
      exact ⟨(mono _ hg).1, a,b,ins⟩
    have start : inputs.map (value x) = List.ofFn x := by simp [inputs, Function.comp_def]
    have sem := map_run x C.gates inputs shape
    rw [start, exactInput] at sem
    have out := val_getD x regs w
    change value x (F w) = (regs.map (value x)).getD w false at out
    change regs.map (value x) = C.gates.foldl boolStep xs at sem
    rw [sem] at out
    change value x (F w) = (C.wires xs).getD w false at out
    rw [← out, val_true]
    rfl

end PlaneClauseCompiler
