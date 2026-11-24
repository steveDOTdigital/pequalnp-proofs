import PetersenFinalNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenBinaryBudget

private def paid (g : Gate) : ℕ :=
  ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)

private theorem count (gs : List Gate) : (gs.map paid).sum ≤ gs.length ∧
    ((gs.map paid).sum = gs.length → ∀ g ∈ gs, g.op ≠ GateOp.not) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have cap : paid g ≤ 1 := by unfold paid; split <;> (first | decide | split <;> decide)
    obtain ⟨le,strict⟩ := ih
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    refine ⟨by omega,?_⟩
    intro eq z hz
    rcases List.mem_cons.mp hz with rfl | mem
    · intro h
      have : paid z = 0 := by simp [paid,h,GateOp.eval]
      omega
    · exact strict (by omega) z mem

theorem strict (C : Circuit) (h : FanInTwo C) (a b : List Bool)
    (lengths : a.length = b.length) (increasing : ∀ i : ℕ, a.getD i false = true → b.getD i false = true)
    (yes : C.eval a = true) (no : C.eval b = false) :
    (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum < C.size := by
  obtain ⟨le,allMono⟩ := count C.gates
  change (C.gates.map paid).sum < C.gates.length
  by_contra! ge
  have noNot := allMono (by omega)
  have mono : FinalNotWires.mono C.gates := by
    intro g hg
    have op : g.op = .and ∨ g.op = .or ∨ g.op = .not := (h g hg).1
    exact op.elim Or.inl (fun alt => Or.inr (alt.resolve_right (noNot g hg)))
  have bad := FinalNotWires.fold_mono C.gates a b mono lengths increasing C.output yes
  rw [← show C.eval b = (FinalNotWires.fold C.gates b).getD C.output false from rfl,no] at bad
  contradiction

end PetersenBinaryBudget
