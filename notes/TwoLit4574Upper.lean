import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace TwoLit4574

def circuit : Circuit :=
  { gates := [⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [5, 3]⟩,
              ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.not, [8]⟩,
              ⟨.and, [6, 10]⟩, ⟨.or, [9, 11]⟩], output := 12 }

theorem upper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5,
    C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
    (4574 : Nat).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end TwoLit4574
