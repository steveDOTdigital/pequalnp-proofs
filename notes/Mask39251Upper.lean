import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds

namespace Mask39251

def graph (u : Fin 4) (v : Fin 5) : Bool :=
  (39251 : Nat).testBit (5 * u.val + v.val)

-- The first four terms are the four rows, unioned at the output.
def circuit : Circuit :=
  { gates := [
      ⟨.or, [4, 5]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [0, 10]⟩,
      ⟨.or, [5, 7]⟩, ⟨.and, [1, 12]⟩,
      ⟨.or, [5, 6]⟩, ⟨.and, [2, 14]⟩,
      ⟨.and, [3, 4]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [15, 16]⟩,
      ⟨.or, [17, 18]⟩], output := 19 }

theorem eleven : PEqualNP.Represents.RepSizeAtMost graph 11 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask39251
