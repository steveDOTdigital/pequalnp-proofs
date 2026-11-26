import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask1274

def graph (u : Fin 3) (v : Fin 5) : Bool :=
  (1274 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 3]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [1, 6]⟩,
              ⟨.or, [8, 5]⟩, ⟨.or, [4, 2]⟩, ⟨.and, [9, 12]⟩,
              ⟨.or, [10, 7]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [15, 13]⟩],
    output := 16 }

theorem upper : RepSizeAtMost graph 9 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask1274
