import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask106299

def graph (u : Fin 4) (v : Fin 5) : Bool :=
  (106299 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [9, 6]⟩,
              ⟨.or, [2, 7]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [5, 13]⟩,
              ⟨.or, [4, 14]⟩, ⟨.or, [12, 8]⟩, ⟨.and, [11, 16]⟩,
              ⟨.or, [17, 15]⟩],
    output := 18 }

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask106299
