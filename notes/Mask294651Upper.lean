import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace Mask294651

def graph (u : Fin 4) (v : Fin 6) : Bool :=
  (294651 : Nat).testBit (6 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or,[5,6]⟩, ⟨.and,[2,10]⟩, ⟨.or,[0,1]⟩,
              ⟨.or,[7,8]⟩, ⟨.or,[13,9]⟩, ⟨.or,[5,14]⟩,
              ⟨.and,[12,15]⟩, ⟨.or,[4,11]⟩, ⟨.or,[17,16]⟩], output := 18 }

theorem nine : RepSizeAtMost graph 9 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

-- Delete the first of the twin rows and the last of the triple columns.
theorem restriction : ∀ (u : Fin 3) (v : Fin 5),
    graph ⟨u.val + 1, by omega⟩ ⟨v.val, by omega⟩ =
      (1275 : Nat).testBit (5 * u.val + v.val) := by decide +kernel

end Mask294651
