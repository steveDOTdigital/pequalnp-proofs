import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PlaneSafeCounting

theorem cover : ∀ P L : Finset (Fin 13), P.card+L.card ≤ 13 →
    (∀ p l : Fin 13, p-l ∈ ([0,1,3,9] : List (Fin 13)) → p∈P ∨ l∈L) →
    P=∅ ∨ L=∅ := by
  intro P L card covers
  have sub : Finset.univ \ P ⊆ L := by
    intro v hv
    have h := covers v v (by simp)
    exact h.resolve_left (Finset.mem_sdiff.mp hv).2
  have comp : Finset.univ \ P = L := by
    apply Finset.eq_of_subset_of_card_le sub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P)]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  have next (p : Fin 13) (hp : p ∈ P) : p+1 ∈ P := by
    have edge : (p+1)-p ∈ ([0,1,3,9] : List (Fin 13)) := by simp
    rcases covers (p+1) p edge with h|h
    · exact h
    · rw [← comp] at h
      exact False.elim ((Finset.mem_sdiff.mp h).2 hp)
  by_cases empty : P = ∅
  · exact Or.inl empty
  right
  obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have reach : ∀ d : Fin 13, p + d ∈ P := by
    intro d
    induction d using Fin.induction with
    | zero => simpa using hp
    | succ k ih =>
      have step : (p + k.castSucc) + 1 = p + k.succ := by
        rw [add_assoc]
        congr 1
        exact Fin.ext (by simp)
      exact step ▸ next _ ih
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  rw [← comp] at hl
  apply (Finset.mem_sdiff.mp hl).2
  simpa using reach (l-p)

-- A gate with two empty-support operands reads two zero wires. Counting
-- their uses recovers the degree identity without any topological assumption.
theorem accounting (gs : List Gate) (s : ℕ → Bool) (arity : ∀ g ∈ gs, g.inputs.length = 2) :
    let both := fun g : Gate => g.inputs.all s
    let born := fun g : Gate => !(g.op.eval [false,true]) && g.inputs.all s
    let one := fun g : Gate => !(g.op.eval [false,true]) && g.inputs.any s && !(g.inputs.all s)
    let zero := fun g : Gate => !(g.op.eval [false,true] && g.inputs.any s)
    (gs.flatMap Gate.inputs).countP (fun i => !(s i)) + gs.countP both +
      gs.countP born + gs.countP one = gs.length + gs.countP zero := by
  dsimp only
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have inductionStep := ih (fun a h => arity a (List.mem_cons_of_mem g h))
    simp only [Bool.not_and] at inductionStep
    have length := arity g List.mem_cons_self
    obtain ⟨op,ins⟩ := g
    change ins.length = 2 at length
    rcases ins with _|⟨a,ins⟩ <;> simp at length
    rcases ins with _|⟨b,ins⟩ <;> simp at length
    cases ins with
    | cons c cs => simp at length
    | nil =>
      simp only [List.flatMap_cons,List.countP_append,List.countP_cons,List.length_cons]
      cases ha : s a <;> cases hb : s b <;> cases gateType : op.eval [false,true] <;>
        simp [ha,hb] <;> omega

end PlaneSafeCounting
