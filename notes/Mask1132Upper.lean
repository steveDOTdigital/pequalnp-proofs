import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask1132

def graph (u : Fin 3) (v : Fin 5) : Bool :=
  (1132 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [5, 6]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [3, 4]⟩,
              ⟨.and, [1, 10]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [9, 11]⟩,
              ⟨.or, [13, 12]⟩],
    output := 14 }

theorem upper : RepSizeAtMost graph 7 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask1132
