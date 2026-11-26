import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace Mask14285

def graph (u : Fin 4) (v : Fin 4) : Bool :=
  (14285 : Nat).testBit (4 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 4]⟩,
              ⟨.and, [10, 9]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [12, 3]⟩,
              ⟨.or, [8, 9]⟩, ⟨.and, [14, 13]⟩, ⟨.not, [15]⟩],
    output := 16 }

theorem upper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧ Represents graph C := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask14285
