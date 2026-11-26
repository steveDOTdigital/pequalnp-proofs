import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask3256

def graph (u : Fin 3) (v : Fin 5) : Bool :=
  (3256 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [8, 4]⟩,
              ⟨.or, [8, 5]⟩, ⟨.and, [10, 2]⟩, ⟨.or, [9, 7]⟩,
              ⟨.and, [11, 13]⟩, ⟨.or, [14, 12]⟩],
    output := 15 }

theorem upper : RepSizeAtMost graph 8 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask3256
