import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace TwoLit35891

def circuit : Circuit :=
  { gates := [⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.not, [7]⟩,
              ⟨.and, [0, 8]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [4, 5]⟩,
              ⟨.and, [1, 11]⟩, ⟨.or, [12, 10]⟩], output := 13 }

theorem eight : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (35891 : Nat).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end TwoLit35891
