import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace TwoLit34075

def circuit : Circuit :=
  { gates := [⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [1, 4]⟩,
              ⟨.or, [8, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.not, [10]⟩,
              ⟨.or, [7, 11]⟩, ⟨.and, [9, 12]⟩], output := 13 }

theorem upper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34075 : Nat).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

-- The exact independently matched catalogue statement.
theorem catalogue22571 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34075 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := upper

#print axioms catalogue22571

end TwoLit34075
