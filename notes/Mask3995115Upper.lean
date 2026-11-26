import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask3995115

def graph (u : Fin 4) (v : Fin 6) : Bool :=
  (3995115 : Nat).testBit (6 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 3]⟩,
              ⟨.or, [4, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [10, 8]⟩,
              ⟨.or, [11, 9]⟩, ⟨.and, [14, 12]⟩, ⟨.or, [13, 17]⟩,
              ⟨.and, [15, 16]⟩, ⟨.or, [19, 18]⟩],
    output := 20 }

theorem upper : RepSizeAtMost graph 11 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask3995115
