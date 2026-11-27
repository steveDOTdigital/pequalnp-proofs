import PEqualNP.Defs.Represents

namespace Mask1865323

open PEqualNP.CircuitLowerBounds

def graph (u : Fin 4) (v : Fin 6) : Bool :=
  (1865323 : Nat).testBit (6 * u.val + v.val)

def witness : Circuit :=
  ⟨[⟨.or,[2,3]⟩,
    ⟨.or,[7,8]⟩,⟨.and,[1,11]⟩,
    ⟨.or,[5,6]⟩,⟨.and,[10,13]⟩,
    ⟨.or,[7,9]⟩,⟨.or,[5,15]⟩,⟨.and,[0,16]⟩,
    ⟨.or,[14,17]⟩,⟨.or,[12,18]⟩,⟨.or,[19,4]⟩],20⟩

theorem upper : PEqualNP.Represents.RepSizeAtMost graph 11 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms upper

end Mask1865323
