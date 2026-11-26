import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace Mask3956829

def graph (u : Fin 5) (v : Fin 5) : Bool :=
  (3956829 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [11, 7]⟩,
              ⟨.and, [11, 4]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [12, 4]⟩,
              ⟨.or, [6, 15]⟩, ⟨.and, [14, 15]⟩, ⟨.not, [16]⟩,
              ⟨.or, [18, 17]⟩],
    output := 19 }

theorem upper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧ Represents graph C := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms upper
end Mask3956829
