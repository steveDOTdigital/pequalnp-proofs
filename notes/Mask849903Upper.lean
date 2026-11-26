import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask849903

def graph (u : Fin 4) (v : Fin 6) : Bool :=
  (849903 : Nat).testBit (6 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [0, 1]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 9]⟩,
              ⟨.or, [10, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩,
              ⟨.and, [13, 15]⟩, ⟨.or, [16, 14]⟩, ⟨.and, [11, 12]⟩,
              ⟨.or, [18, 17]⟩],
    output := 19 }

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask849903
