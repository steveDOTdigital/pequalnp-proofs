import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenFinalAnd4073

private def extend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldLength (gs : List Gate) (w : List Bool) :
    (gs.foldl extend w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, extend, Nat.add_comm, Nat.add_left_comm]

private def finish (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.and, [a, b]⟩], 11 + C.size⟩

private theorem finishLegal (C : Circuit) (a b : ℕ) (h : FanInTwo C) :
    FanInTwo (finish C a b) := by
  intro g mem
  change g ∈ C.gates ++ [_] at mem
  simp only [List.mem_append, List.mem_singleton] at mem
  rcases mem with old | rfl
  · exact h g old
  · simp

private theorem finishEval (C : Circuit) (a b : ℕ) (x : List Bool) (hx : x.length = 11) :
    (finish C a b).eval x = ((C.wires x).getD a false && (C.wires x).getD b false) := by
  have len : (C.wires x).length = 11 + C.size := by
    change (C.gates.foldl extend x).length = 11 + C.gates.length
    rw [foldLength, hx]
  change ((C.gates ++ [_]).foldl extend x).getD (11 + C.size) false = _
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  change ((C.wires x) ++ [_]).getD (11 + C.size) false = _
  rw [List.getD_append_right _ _ _ _ (by omega : (C.wires x).length ≤ 11 + C.size), len, Nat.sub_self]
  simp [GateOp.eval, List.getD]
  rfl

/-- Exact implication between the two posted desk statements. -/
theorem postedFrom1884 (lower :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       have x6 : (Fin (10 : ℕ) → Bool) → Bool := fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ));       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x1.wires (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))])).getD x8 Bool.false;       (∃ (x8 : Fin (10 : ℕ) → Bool), x7 x8 x2 = Bool.true ∧ x7 x8 x3 = Bool.false) → (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x2 = Bool.false ∧ x7 x9 x3 = Bool.true) → (∀ (x10 : Fin (10 : ℕ) → Bool), x6 x10 = Bool.true → x7 x10 x2 = Bool.true ∧ x7 x10 x3 = Bool.true) → ∃ (x11 : Fin (10 : ℕ) → Bool), x6 x11 = Bool.false ∧ x7 x11 x2 = Bool.true ∧ x7 x11 x3 = Bool.true := by
  intro C a b legal budget
  dsimp only
  intro _ _ covers
  let D := finish C a b
  have size : D.size ≤ 18 := by
    change (C.gates ++ [_]).length ≤ 18
    simpa [Circuit.size] using Nat.succ_le_succ budget
  obtain ⟨x, bad⟩ := lower D id (fun y => !y) (finishLegal C a b legal) size
  simp only [Function.comp_id] at bad
  rw [show D = finish C a b from rfl, finishEval _ _ _ _ (by simp)] at bad
  let pins := List.ofFn x ++ [!x 0]
  let f := (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)))
  change ((C.wires pins).getD a false && (C.wires pins).getD b false) ≠ f x at bad
  cases value : f x with
  | false =>
    refine ⟨x, value, ?_⟩
    cases ha : (C.wires pins).getD a false <;> cases hb : (C.wires pins).getD b false <;>
      simp_all [pins]
  | true =>
    obtain ⟨ha, hb⟩ := covers x value
    exact False.elim (bad (by simpa [pins, value] using (Bool.and_eq_true_iff.mpr ⟨ha, hb⟩)))

end PetersenFinalAnd4073

#print axioms PetersenFinalAnd4073.postedFrom1884
