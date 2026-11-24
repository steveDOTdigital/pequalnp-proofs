import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace ThreeCube

open PEqualNP.CircuitLowerBounds

def edges : List (Fin 8 × Fin 8) :=
  [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]

def edgeValue (x : Fin 8 → Bool) : Bool :=
  edges.any fun p => x p.1 && x p.2

def gates : List Gate :=
  [⟨.or, [1, 2]⟩,
   ⟨.or, [4, 7]⟩,
   ⟨.or, [8, 4]⟩,
   ⟨.or, [8, 7]⟩,
   ⟨.or, [9, 1]⟩,
   ⟨.or, [9, 2]⟩,
   ⟨.and, [0, 10]⟩,
   ⟨.and, [3, 11]⟩,
   ⟨.and, [5, 12]⟩,
   ⟨.and, [6, 13]⟩,
   ⟨.or, [14, 15]⟩,
   ⟨.or, [16, 17]⟩,
   ⟨.or, [18, 19]⟩]

def circuit : Circuit := ⟨gates, 20⟩

theorem size_eq : circuit.size = 13 := rfl

def tag : GateOp → Bool
  | .and | .or => true
  | _ => false

theorem binary_monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  have all : gates.all (fun h => tag h.op && decide (h.inputs.length ≤ 2)) = true := rfl
  have h := List.all_eq_true.mp all g hg
  have good : tag g.op = true ∧ g.inputs.length ≤ 2 := by simpa using h
  refine ⟨?_, good.2⟩
  have valid := good.1
  cases e : g.op <;> simp_all [tag]

theorem and_count : (gates.filter fun g => match g.op with | .and => true | _ => false).length = 4 := by
  decide +kernel

def formula (x : Fin 8 → Bool) : Bool :=
  let p := x 1 || x 2
  let q := x 4 || x 7
  ((x 0 && (p || x 4)) || (x 3 && (p || x 7))) ||
    ((x 5 && (q || x 1)) || (x 6 && (q || x 2)))

theorem evaluation (x : Fin 8 → Bool) : circuit.eval (List.ofFn x) = edgeValue x := by
  let bits := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7]
  have repr : circuit.eval bits = formula x := by
    simp [formula, bits, circuit, Circuit.eval, Circuit.wires, gates, GateOp.eval, List.getD]
  change circuit.eval bits = _
  rw [repr]
  simp [formula, edgeValue, edges]
  generalize x 0 = z0
  generalize x 1 = z1
  generalize x 2 = z2
  generalize x 3 = z3
  generalize x 4 = z4
  generalize x 5 = z5
  generalize x 6 = z6
  generalize x 7 = z7
  revert z0 z1 z2 z3 z4 z5 z6 z7
  decide +kernel

theorem edge_iff (x : Fin 8 → Bool) :
    circuit.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u, v) ∈ edges ∧ x u = true ∧ x v = true := by
  rw [evaluation]
  simp [edgeValue, List.any_eq_true]

def deskEdges : List (Nat × Nat) :=
  [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]

theorem desk_evaluation (x : Fin 8 → Bool) :
    circuit.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ deskEdges ∧ x u = true ∧ x v = true := by
  have same : ∀ u v : Fin 8, (u, v) ∈ edges ↔ (u.val, v.val) ∈ deskEdges := by
    decide +kernel
  rw [edge_iff]
  simp_rw [same]

end ThreeCube
