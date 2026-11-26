import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace TwoLit2113951

def circuit : Circuit :=
  { gates := [⟨.not, [0]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 3]⟩,
              ⟨.or, [8, 4]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [10, 5]⟩,
              ⟨.not, [11]⟩], output := 12 }

theorem upper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (2113951 : Nat).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end TwoLit2113951
