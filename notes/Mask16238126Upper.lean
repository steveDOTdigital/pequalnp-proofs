import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace Mask16238126

def graph (u v : Fin 5) : Bool := (16238126 : Nat).testBit (5 * u.val + v.val)

def eightGate : Circuit :=
  { gates := [⟨.and, [0,5]⟩, ⟨.or, [10,9]⟩, ⟨.or, [1,2]⟩,
              ⟨.or, [12,11]⟩, ⟨.or, [5,11]⟩, ⟨.and, [12,14]⟩,
              ⟨.not, [13]⟩, ⟨.or, [15,16]⟩], output := 17 }

theorem eight : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ Represents graph C := by
  refine ⟨eightGate, ?_, ?_, ?_⟩
  · intro g hg
    simp only [eightGate, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end Mask16238126
