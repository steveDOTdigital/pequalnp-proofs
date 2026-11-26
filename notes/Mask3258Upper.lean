import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask3258

def graph (u : Fin 3) (v : Fin 5) : Bool :=
  (3258 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [8, 9]⟩,
              ⟨.or, [8, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [10, 2]⟩,
              ⟨.or, [12, 7]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [15, 13]⟩],
    output := 16 }

theorem upper : RepSizeAtMost graph 9 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask3258
