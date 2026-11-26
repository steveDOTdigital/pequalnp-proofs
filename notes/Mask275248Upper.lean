import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask275248

def graph (u : Fin 4) (v : Fin 6) : Bool :=
  (275248 : Nat).testBit (6 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [8, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [6, 7]⟩,
              ⟨.and, [1, 12]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [2, 14]⟩,
              ⟨.and, [3, 4]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [15, 16]⟩,
              ⟨.or, [17, 18]⟩],
    output := 19 }

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask275248
