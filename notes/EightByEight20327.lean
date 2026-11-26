import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Graph11871860300395540620

def graph (u v : Fin 8) : Bool :=
  (11871860300395540620 : Nat).testBit (8 * u.val + v.val)

-- Four products of shared row and column unions cover all 24 accepted cells.
def circuit : Circuit :=
  { gates := [⟨.or,[12,14]⟩,
              ⟨.or,[0,16]⟩,
              ⟨.or,[3,9]⟩,
              ⟨.or,[7,14]⟩,
              ⟨.or,[1,15]⟩,
              ⟨.or,[6,13]⟩,
              ⟨.or,[2,8]⟩,
              ⟨.or,[20,22]⟩,
              ⟨.or,[19,23]⟩,
              ⟨.and,[21,24]⟩,
              ⟨.or,[10,12]⟩,
              ⟨.or,[4,26]⟩,
              ⟨.or,[2,27]⟩,
              ⟨.or,[18,8]⟩,
              ⟨.and,[28,29]⟩,
              ⟨.or,[5,11]⟩,
              ⟨.or,[18,4]⟩,
              ⟨.or,[17,32]⟩,
              ⟨.and,[31,33]⟩,
              ⟨.or,[17,7]⟩,
              ⟨.or,[20,10]⟩,
              ⟨.and,[35,36]⟩,
              ⟨.or,[25,30]⟩,
              ⟨.or,[38,34]⟩,
              ⟨.or,[39,37]⟩], output := 40 }

theorem twentyFive : RepSizeAtMost graph 25 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms twentyFive
end Graph11871860300395540620
