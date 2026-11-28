import PEqualNP.Defs

namespace EightVertexOneNot34187

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List Nat := [0,3,0,4,1,4,0,5,1,5,4,5,1,6,2,6,3,6,4,6,0,7,2,7,3,7,4,7,5,7,6,7]

def posted (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def control : Circuit := ⟨[
  ⟨.or,[5,3]⟩,
  ⟨.and,[8,0]⟩,
  ⟨.or,[7,6]⟩,
  ⟨.or,[3,2]⟩,
  ⟨.and,[10,11]⟩,
  ⟨.or,[7,4]⟩,
  ⟨.or,[6,5]⟩,
  ⟨.or,[14,0]⟩,
  ⟨.and,[13,15]⟩,
  ⟨.or,[7,1]⟩,
  ⟨.or,[14,4]⟩,
  ⟨.and,[17,18]⟩,
  ⟨.or,[9,12]⟩,
  ⟨.or,[20,16]⟩,
  ⟨.or,[21,19]⟩], 22⟩

theorem size : control.size = 15 := by decide +kernel

theorem legal : Monotone2 control := by
  intro g mem
  simp only [control,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem backward : NestedCover.ReadsBack 8 control := by
  unfold NestedCover.ReadsBack
  exact fun j h => (show ∀ (j : Fin 15), ∀ i ∈ (NestedCover.gateAt control j.val).inputs,
      i < 8+j.val from by decide +kernel) ⟨j,h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem value : ∀ x : Fin 8 → Bool, control.eval (List.ofFn x) = posted x := by decide +kernel

#print axioms size
#print axioms legal
#print axioms backward
#print axioms value

end EightVertexOneNot34187
