import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask125

def graph (u : Fin 3) (v : Fin 5) : Bool :=
  (125 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [3, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [3, 5]⟩,
              ⟨.or, [10, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [0, 12]⟩,
              ⟨.or, [13, 9]⟩],
    output := 14 }

theorem upper : RepSizeAtMost graph 7 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask125
