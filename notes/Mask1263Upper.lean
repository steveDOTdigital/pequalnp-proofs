import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask1263Construction

def graph (u : Fin 3) (v : Fin 5) : Bool :=
  (1263 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 1]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [9, 3]⟩,
              ⟨.or, [4, 5]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [12, 10]⟩],
    output := 13 }

theorem upper : RepSizeAtMost graph 6 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask1263Construction
