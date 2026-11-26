import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Graph4868853174714768465

def graph (u v : Fin 8) : Bool :=
  (4868853174714768465 : Nat).testBit (8 * u.val + v.val)

-- Shared row and column unions feed six conjunctions.
def circuit : Circuit :=
  { gates := [⟨.or,[1,9]⟩,
              ⟨.or,[4,10]⟩,
              ⟨.or,[3,11]⟩,
              ⟨.or,[7,12]⟩,
              ⟨.or,[6,14]⟩,
              ⟨.or,[2,15]⟩,
              ⟨.or,[0,16]⟩,
              ⟨.or,[0,19]⟩,
              ⟨.or,[13,18]⟩,
              ⟨.or,[8,20]⟩,
              ⟨.or,[8,21]⟩,
              ⟨.or,[17,18]⟩,
              ⟨.or,[5,24]⟩,
              ⟨.or,[17,21]⟩,
              ⟨.and,[16,27]⟩,
              ⟨.and,[22,19]⟩,
              ⟨.and,[20,26]⟩,
              ⟨.and,[28,29]⟩,
              ⟨.and,[5,13]⟩,
              ⟨.and,[23,25]⟩,
              ⟨.or,[30,31]⟩,
              ⟨.or,[32,33]⟩,
              ⟨.or,[34,35]⟩,
              ⟨.or,[36,37]⟩,
              ⟨.or,[38,39]⟩], output := 40 }

theorem twentyFive : RepSizeAtMost graph 25 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms twentyFive
end Graph4868853174714768465
