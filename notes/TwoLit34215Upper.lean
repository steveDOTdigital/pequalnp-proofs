import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace TwoLit34215

def circuit : Circuit :=
  { gates := [⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.and, [2, 3]⟩,
              ⟨.or, [4, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [10, 9]⟩,
              ⟨.or, [3, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [13, 8]⟩], output := 14 }

theorem nine : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34215 : Nat).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end TwoLit34215
