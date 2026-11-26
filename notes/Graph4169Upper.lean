import PEqualNP.Defs.Represents

namespace Graph4169Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  { gates := [⟨.not,[0]⟩, ⟨.and,[1,0]⟩, ⟨.or,[1,0]⟩, ⟨.or,[2,6]⟩, ⟨.and,[8,7]⟩, ⟨.or,[4,9]⟩, ⟨.and,[5,3]⟩, ⟨.or,[10,11]⟩, ⟨.not,[12]⟩], output := 13 }

theorem nine : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5,
    C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
    (4169 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms nine
end Graph4169Upper
