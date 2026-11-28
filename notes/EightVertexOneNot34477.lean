import PEqualNP.Defs

namespace EightVertexOneNot34477

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List Nat := [0,4,1,4,0,5,2,5,1,6,2,6,3,6,0,7,3,7,4,7,5,7,6,7]

def posted (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
     (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
     (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def control : Circuit := ⟨[
  ⟨.or,[5,6]⟩, ⟨.or,[2,7]⟩, ⟨.and,[8,9]⟩,
  ⟨.or,[4,6]⟩, ⟨.or,[1,7]⟩, ⟨.and,[11,12]⟩,
  ⟨.or,[6,7]⟩, ⟨.and,[3,14]⟩,
  ⟨.or,[4,5]⟩, ⟨.or,[16,7]⟩, ⟨.and,[0,17]⟩,
  ⟨.or,[10,13]⟩, ⟨.or,[15,18]⟩, ⟨.or,[19,20]⟩], 21⟩

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

theorem size : control.size = 14 := by decide +kernel

theorem legal : Monotone2 control := by
  intro g mem
  simp only [control,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem backward : NestedCover.ReadsBack 8 control := by
  unfold NestedCover.ReadsBack
  exact fun j h => (show ∀ (j : Fin 14), ∀ i ∈ (NestedCover.gateAt control j.val).inputs,
    i < 8+j.val from by decide +kernel) ⟨j,h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem value : ∀ x : Fin 8 → Bool, control.eval (List.ofFn x) = posted x := by decide +kernel

#print axioms legal
#print axioms backward
#print axioms value

end EightVertexOneNot34477
