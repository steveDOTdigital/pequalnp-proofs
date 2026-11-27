import PEqualNP.Defs
namespace Graph2180761Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  { gates := [⟨.or,[0,1]⟩, ⟨.and,[0,1]⟩, ⟨.or,[6,3]⟩, ⟨.and,[2,8]⟩,
              ⟨.or,[6,2]⟩, ⟨.not,[10]⟩, ⟨.and,[4,11]⟩, ⟨.or,[7,9]⟩,
              ⟨.or,[13,12]⟩, ⟨.or,[14,5]⟩, ⟨.not,[15]⟩], output := 16 }

theorem eleven : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (2180761 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms eleven
end Graph2180761Upper
