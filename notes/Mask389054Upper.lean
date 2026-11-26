import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask389054

def graph (u : Fin 4) (v : Fin 6) : Bool :=
  (389054 : Nat).testBit (6 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 1]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [10, 4]⟩,
              ⟨.or, [5, 6]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [14, 8]⟩,
              ⟨.and, [11, 15]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [12, 17]⟩,
              ⟨.or, [16, 18]⟩],
    output := 19 }

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask389054
