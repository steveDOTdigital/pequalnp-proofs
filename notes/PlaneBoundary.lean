import Mathlib

namespace PlaneBoundary

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 65536 in
theorem no_empty_four_by_four : let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      ∀ s t : Finset (Fin 13), (∀ p ∈ s, ∀ l ∈ t, ¬ near p l) → s.card ≤ 3 ∨ t.card ≤ 3 := by
  let off (s : Finset (Fin 13)) := Finset.univ.filter fun j : Fin 13 =>
    ∀ i ∈ s, (i.val + j.val) % 13 ∉ ([0,1,3,9] : List ℕ)
  let fours := (Finset.univ : Finset (Fin 13)).powersetCard 4
  have certified : (fours.filter fun s => 3 < (off s).card) = ∅ := by
    dsimp only [fours,off]
    decide +kernel
  intro near s t miss
  by_cases small : s.card ≤ 3
  · exact Or.inl small
  right
  obtain ⟨q,sub,card⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ s.card)
  have hq : q ∈ fours := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,card⟩
  have cover : t ⊆ off q := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i hi => miss i (sub hi) j hj⟩
  have cap : (off q).card ≤ 3 := by
    by_contra! bad
    have flag : q ∈ fours.filter (fun s => 3 < (off s).card) := Finset.mem_filter.mpr ⟨hq,bad⟩
    rw [certified] at flag
    exact Finset.notMem_empty q flag
  exact (Finset.card_le_card cover).trans cap

end PlaneBoundary
