import PEqualNP.Defs

namespace EightVertexOneNot35289

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List Nat := [0,3,1,4,2,4,0,5,1,5,3,5,0,6,2,6,3,6,1,7,2,7,4,7,5,7]

def posted (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def control : Circuit := ⟨[
  ⟨.or,[4,6]⟩, ⟨.or,[8,7]⟩, ⟨.and,[2,9]⟩,
  ⟨.or,[1,7]⟩, ⟨.or,[4,5]⟩, ⟨.and,[11,12]⟩,
  ⟨.and,[7,1]⟩, ⟨.or,[5,6]⟩, ⟨.or,[0,3]⟩,
  ⟨.and,[15,16]⟩, ⟨.and,[3,0]⟩, ⟨.or,[10,13]⟩,
  ⟨.or,[19,14]⟩, ⟨.or,[20,17]⟩, ⟨.or,[21,18]⟩], 22⟩

theorem size : control.size = 15 := by decide +kernel

theorem legal : Monotone2 control := by
  intro g mem
  simp only [control,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem backward : NestedCover.ReadsBack 8 control := by
  unfold NestedCover.ReadsBack
  exact fun j h => (show ∀ (j : Fin 15), ∀ i ∈ (NestedCover.gateAt control j.val).inputs,
    i < 8+j.val from by decide +kernel) ⟨j,h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem value : ∀ x : Fin 8 → Bool, control.eval (List.ofFn x) = posted x := by decide +kernel

def outside (x : Fin 8 → Bool) : Bool :=
  (x 1 && x 4) || (x 2 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
  (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)

set_option maxRecDepth 10000 in
theorem twinStructure : ∀ x : Fin 8 → Bool, posted x =
    ((x 0 && x 3) || ((x 0 || x 3) && (x 5 || x 6)) || outside x) := by decide +kernel

def twinRow (fixed varying : Fin 8) (pin toggled : Bool) (i : Fin 8) : Bool :=
  (decide (i=fixed) && pin) || (decide (i=varying) && toggled) || (decide (i=5) && !pin)

theorem twinRows : ∀ b : Bool,
    posted (twinRow 0 3 b false) = false ∧ posted (twinRow 0 3 b true) = true ∧
    posted (twinRow 3 0 b false) = false ∧ posted (twinRow 3 0 b true) = true := by decide +kernel

#print axioms value
#print axioms twinStructure
#print axioms twinRows

end EightVertexOneNot35289
