import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_741

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first three gates cover the square on vertices zero, one, three
-- and four. The remaining five edges form two adjacent stars.
def prism10 : Circuit :=
  ⟨[⟨.or,[0,4]⟩, ⟨.or,[1,3]⟩, ⟨.and,[6,7]⟩,
    ⟨.or,[0,1]⟩, ⟨.or,[9,5]⟩, ⟨.and,[2,10]⟩,
    ⟨.or,[3,4]⟩, ⟨.and,[5,12]⟩, ⟨.or,[8,11]⟩, ⟨.or,[14,13]⟩],15⟩

set_option maxRecDepth 10000 in
lemma ten_suffice : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 10 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  refine ⟨prism10, ?_, rfl, ?_⟩
  · intro g hg
    simp [prism10] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide

end PEqualNP.Outside.L_meta_741
