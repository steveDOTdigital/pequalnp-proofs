import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PlaneGateProjection

def bit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

def step (w : List Bool) (g : Gate) : List Bool := w ++ [bit w g]

-- One replacement selects an actual operand of an AND; every other gate is unchanged.
def projects (g h : Gate) : Prop :=
  g = h ∨ (g.op = .and ∧ ∃ i ∈ g.inputs, h.op = .or ∧ h.inputs = [i])

def below (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem bit_mono {g h : Gate} {x y : List Bool}
    (kind : g.op = .and ∨ g.op = .or) (choice : projects g h) (w : below x y)
    (yes : bit x g = true) : bit y h = true := by
  rcases choice with rfl | ⟨op,i,hi,newOp,newIns⟩
  · rcases kind with ha | ho
    · simp only [bit, ha, GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, id_eq] at yes ⊢
      exact fun j hj => w.2 j (yes j hj)
    · simp [bit, ho, GateOp.eval, List.any_eq_true] at yes ⊢
      obtain ⟨j,hj,fired⟩ := yes
      exact ⟨j,hj,w.2 j fired⟩
  · have hit : x.getD i false = true := by
      have all := List.all_eq_true.mp (show (g.inputs.map (fun j => x.getD j false)).all id = true
        by simpa only [bit, op, GateOp.eval] using yes)
      exact all _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
    simpa [bit, newOp, newIns, GateOp.eval] using w.2 i hit

theorem extend {x y : List Bool} (w : below x y) {a b : Bool}
    (up : a = true → b = true) : below (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases raw : i < x.length
  · rw [List.getD_append _ _ _ _ raw, List.getD_append _ _ _ _ (w.1 ▸ raw)]
    exact w.2 i
  by_cases last : i = x.length
  · subst i
    have left : (x ++ [a]).getD x.length false = a := by simp
    have right : (y ++ [b]).getD x.length false = b := by rw [w.1]; simp
    rw [left, right]
    exact up
  have xx : (x ++ [a]).length ≤ i := by simp; omega
  have yy : (y ++ [b]).length ≤ i := by simp; have := w.1; omega
  rw [List.getD_eq_default _ _ xx, List.getD_eq_default _ _ yy]
  exact id

-- The projection proof uses prefixes. Reads beyond a prefix retain the desk's false default.
theorem run_mono (steps : List (Gate × Gate)) (x y : List Bool)
    (w : below x y)
    (valid : ∀ p ∈ steps, (p.1.op = .and ∨ p.1.op = .or) ∧ projects p.1 p.2) :
    below ((steps.map Prod.fst).foldl step x) ((steps.map Prod.snd).foldl step y) := by
  induction steps generalizing x y with
  | nil => exact w
  | cons p ps ih =>
    obtain ⟨kind,choice⟩ := valid p List.mem_cons_self
    exact ih (step x p.1) (step y p.2) (extend w (bit_mono kind choice w))
      (fun z hz => valid z (List.mem_cons_of_mem p hz))

-- At an anchored negative row, a gate with a true anchor operand is a copy
-- of the other wire. If neither was active, stabilization keeps both false.
theorem selectBit (left0 right0 left right : Bool)
    (upLeft : left0 = true → left = true) (upRight : right0 = true → right = true)
    (stable : (left0 || right0) = false → (left || right) = false) :
    (left && right) = (if left0 then right else left) := by
  cases left0 <;> cases right0 <;> cases left <;> cases right <;> simp_all

theorem exact_run (ps : List (Gate × Gate)) (x : List Bool)
    (agree : ∀ pre g post, ps = pre ++ g :: post →
      let w := (pre.map Prod.fst).foldl step x
      bit w g.1 = bit w g.2) :
    (ps.map Prod.fst).foldl step x = (ps.map Prod.snd).foldl step x := by
  induction ps generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have atHead := agree [] g gs rfl
    have start : step x g.1 = step x g.2 := by
      change bit x g.1 = bit x g.2 at atHead
      simp only [step, atHead]
    have tail := ih (step x g.1) (fun pre h post split => by
      have result := agree (g::pre) h post (by simp [split])
      exact result)
    simpa only [List.map_cons, List.foldl_cons, start] using tail

theorem output_dominates (ps : List (Gate × Gate)) (o : ℕ)
    (valid : ∀ p ∈ ps, (p.1.op = .and ∨ p.1.op = .or) ∧ projects p.1 p.2) (x : List Bool) :
    (Circuit.mk (ps.map Prod.fst) o).eval x = true →
    (Circuit.mk (ps.map Prod.snd) o).eval x = true :=
  (run_mono ps x x ⟨rfl, fun _ => id⟩ valid).2 o

end PlaneGateProjection
