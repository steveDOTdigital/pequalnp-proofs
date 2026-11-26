import PEqualNP.Defs.Represents

namespace Mask39161Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The three rectangles are {1,2} × {1,2}, {0} × {3,4}, and {0,1,3} × {0}.
def circuit : Circuit :=
  { gates := [⟨.or,[1,2]⟩, ⟨.or,[5,6]⟩, ⟨.and,[9,10]⟩,
              ⟨.or,[7,8]⟩, ⟨.and,[0,12]⟩, ⟨.or,[0,1]⟩,
              ⟨.or,[14,3]⟩, ⟨.and,[15,4]⟩, ⟨.or,[11,13]⟩, ⟨.or,[17,16]⟩], output := 18 }

theorem upper : PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 5) => (39161 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms upper
end Mask39161Upper
