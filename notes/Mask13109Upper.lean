import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask13109

def graph (u : Fin 3) (v : Fin 6) : Bool :=
  (13109 : Nat).testBit (6 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [3, 7]⟩,
              ⟨.or, [5, 2]⟩, ⟨.or, [6, 12]⟩, ⟨.and, [10, 13]⟩,
              ⟨.or, [11, 8]⟩, ⟨.or, [15, 12]⟩, ⟨.and, [9, 16]⟩,
              ⟨.or, [14, 17]⟩],
    output := 18 }

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask13109
