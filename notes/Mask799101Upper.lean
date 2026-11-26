import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask799101

def graph (u : Fin 4) (v : Fin 6) : Bool :=
  (799101 : Nat).testBit (6 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [10, 6]⟩,
              ⟨.or, [12, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [14, 8]⟩,
              ⟨.or, [15, 9]⟩, ⟨.or, [16, 3]⟩, ⟨.and, [11, 17]⟩,
              ⟨.or, [13, 18]⟩],
    output := 19 }

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask799101
