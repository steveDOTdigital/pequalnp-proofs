import PEqualNP.Defs

namespace EightVertexOneNot34872

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List Nat := [0,3,0,4,1,4,0,5,2,5,3,5,1,6,2,6,3,6,5,6,0,7,1,7,2,7,4,7,5,7]

def posted (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def control : Circuit := ⟨[
  ⟨.or,[6,5]⟩,
  ⟨.or,[8,0]⟩,
  ⟨.and,[9,3]⟩,
  ⟨.or,[7,5]⟩,
  ⟨.or,[2,0]⟩,
  ⟨.and,[11,12]⟩,
  ⟨.or,[7,1]⟩,
  ⟨.or,[14,0]⟩,
  ⟨.and,[15,4]⟩,
  ⟨.or,[7,6]⟩,
  ⟨.or,[5,2]⟩,
  ⟨.or,[18,1]⟩,
  ⟨.and,[17,19]⟩,
  ⟨.or,[10,13]⟩,
  ⟨.or,[21,16]⟩,
  ⟨.or,[22,20]⟩], 23⟩

theorem size : control.size = 16 := by decide +kernel

theorem legal : Monotone2 control := by
  intro g mem
  simp only [control,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem backward : NestedCover.ReadsBack 8 control := by
  unfold NestedCover.ReadsBack
  exact fun j h => (show ∀ (j : Fin 16), ∀ i ∈ (NestedCover.gateAt control j.val).inputs,
      i < 8+j.val from by decide +kernel) ⟨j,h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem value : ∀ x : Fin 8 → Bool, control.eval (List.ofFn x) = posted x := by decide +kernel

#print axioms size
#print axioms legal
#print axioms backward
#print axioms value

end EightVertexOneNot34872
