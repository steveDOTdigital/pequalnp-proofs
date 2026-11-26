import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask241143

def graph (u : Fin 4) (v : Fin 5) : Bool :=
  (241143 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 1]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 2]⟩,
              ⟨.or, [9, 3]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [4, 5]⟩,
              ⟨.and, [6, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [10, 13]⟩,
              ⟨.or, [17, 16]⟩],
    output := 18 }

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask241143
