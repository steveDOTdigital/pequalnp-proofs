import PEqualNP.Defs.Represents

namespace Mask36058Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Four rectangles cover all 20 promised pairs with the requested output values.
def circuit : Circuit :=
  { gates := [⟨.or,[7,8]⟩, ⟨.and,[0,9]⟩, ⟨.or,[0,1]⟩, ⟨.or,[11,2]⟩,
              ⟨.and,[5,12]⟩, ⟨.and,[1,6]⟩, ⟨.or,[2,3]⟩, ⟨.and,[4,15]⟩,
              ⟨.or,[10,13]⟩, ⟨.or,[14,16]⟩, ⟨.or,[17,18]⟩], output := 19 }

theorem upper : PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 5) => (36058 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms upper
end Mask36058Upper
