import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask36830

def graph (u : Fin 4) (v : Fin 5) : Bool :=
  (36830 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 1]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [9, 4]⟩,
              ⟨.or, [2, 6]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [12, 7]⟩,
              ⟨.or, [14, 8]⟩, ⟨.or, [15, 3]⟩, ⟨.and, [11, 16]⟩,
              ⟨.or, [13, 17]⟩],
    output := 18 }

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask36830
