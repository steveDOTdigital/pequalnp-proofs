import PEqualNP.Defs

namespace EightVertex8399
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [8, 3]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.and, [3, 14]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.and, [6, 17]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [19, 15]⟩,
    ⟨.or, [20, 16]⟩,
    ⟨.or, [21, 18]⟩], 22⟩

theorem upper : HasCircuitSize 8 target 15 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro g hg
    simp [witness] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel

/-- It suffices to rule out the single budget immediately below the posted bound. -/
theorem posted_iff : (∀ t, HasCircuitSize 8 target t → 15 ≤ t) ↔
    ¬ HasCircuitSize 8 target 14 := by
  constructor
  · intro h small
    have := h 14 small
    omega
  · intro h t ht
    by_contra! lt
    obtain ⟨C, ok, bound, hit⟩ := ht
    exact h ⟨C, ok, by omega, hit⟩

end EightVertex8399
