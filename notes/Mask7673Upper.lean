import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask7673

def graph (u : Fin 3) (v : Fin 5) : Bool :=
  (7673 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩,
              ⟨.or, [0, 1]⟩, ⟨.and, [11, 6]⟩, ⟨.and, [0, 7]⟩,
              ⟨.or, [3, 10]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 15]⟩],
    output := 16 }

theorem upper : RepSizeAtMost graph 9 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask7673
