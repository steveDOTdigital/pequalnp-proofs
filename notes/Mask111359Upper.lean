import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask111359

def graph (u : Fin 4) (v : Fin 5) : Bool :=
  (111359 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [1, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [10, 5]⟩,
              ⟨.or, [6, 8]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [0, 13]⟩,
              ⟨.or, [9, 7]⟩, ⟨.or, [15, 3]⟩, ⟨.and, [11, 16]⟩,
              ⟨.or, [14, 17]⟩],
    output := 18 }

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask111359
