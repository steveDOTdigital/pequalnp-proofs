import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask36279

def graph (u : Fin 4) (v : Fin 5) : Bool :=
  (36279 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [5,6]⟩, ⟨.or, [9,8]⟩, ⟨.and, [0,10]⟩,
              ⟨.or, [6,7]⟩, ⟨.and, [1,12]⟩, ⟨.and, [2,5]⟩,
              ⟨.or, [11,13]⟩, ⟨.or, [4,14]⟩, ⟨.or, [15,16]⟩], output := 17 }

theorem nine : RepSizeAtMost graph 9 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask36279
