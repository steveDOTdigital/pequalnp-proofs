import PEqualNP.Defs

namespace EightVertexOneNot35719

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List Nat := [0,3,1,4,0,5,1,5,2,5,3,5,0,6,1,6,3,6,4,6,0,7,1,7,2,7,4,7,5,7]

def posted (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def control : Circuit := ⟨[
  ⟨.or,[0,5]⟩,
  ⟨.and,[8,3]⟩,
  ⟨.or,[1,7]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.and,[10,11]⟩,
  ⟨.or,[0,1]⟩,
  ⟨.or,[13,3]⟩,
  ⟨.or,[14,4]⟩,
  ⟨.and,[6,15]⟩,
  ⟨.or,[5,7]⟩,
  ⟨.or,[13,2]⟩,
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

def reflect (i : Fin 8) : Fin 8 :=
  match i.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 4
  | 4 => 3
  | 5 => 7
  | 6 => 6
  | _ => 5

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem reflected : ∀ x : Fin 8 → Bool, posted (fun i => x (reflect i)) = posted x := by
  decide +kernel

#print axioms reflected
#print axioms size
#print axioms legal
#print axioms backward
#print axioms value

end EightVertexOneNot35719
