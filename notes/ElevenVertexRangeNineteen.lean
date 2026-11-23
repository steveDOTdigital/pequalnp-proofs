import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace ElevenVertexRange19

open PEqualNP.CircuitLowerBounds

def edges : List (Fin 11 × Fin 11) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def edgeValue (x : Fin 11 → Bool) : Bool :=
  edges.any fun p => x p.1 && x p.2

def gates : List Gate :=
  [⟨.or, [7, 10]⟩,
   ⟨.or, [6, 9]⟩,
   ⟨.and, [11, 12]⟩,
   ⟨.or, [1, 4]⟩,
   ⟨.or, [14, 9]⟩,
   ⟨.or, [0, 8]⟩,
   ⟨.and, [15, 16]⟩,
   ⟨.and, [10, 0]⟩,
   ⟨.or, [8, 9]⟩,
   ⟨.or, [5, 17]⟩,
   ⟨.and, [19, 20]⟩,
   ⟨.or, [6, 7]⟩,
   ⟨.or, [3, 13]⟩,
   ⟨.and, [22, 23]⟩,
   ⟨.or, [5, 10]⟩,
   ⟨.and, [25, 2]⟩,
   ⟨.or, [1, 10]⟩,
   ⟨.and, [27, 4]⟩,
   ⟨.or, [18, 21]⟩,
   ⟨.or, [29, 24]⟩,
   ⟨.or, [30, 26]⟩,
   ⟨.or, [31, 28]⟩]

def circuit : Circuit := ⟨gates, 32⟩

theorem size_eq : circuit.size = 22 := rfl

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

theorem and_count : (gates.filter fun g => match g.op with | .and => true | _ => false).length = 7 := by
  decide +kernel

def formula (x : Fin 11 → Bool) : Bool :=
  let d := (x 7 || x 10) && (x 6 || x 9)
  let h := ((x 1 || x 4) || x 9) && (x 0 || x 8)
  let t₁ := x 10 && x 0
  let t₂ := (x 8 || x 9) && (x 5 || h)
  let t₃ := (x 6 || x 7) && (x 3 || d)
  let t₄ := (x 5 || x 10) && x 2
  let t₅ := (x 1 || x 10) && x 4
  (((t₁ || t₂) || t₃) || t₄) || t₅

theorem evaluation (x : Fin 11 → Bool) : circuit.eval (List.ofFn x) = edgeValue x := by
  let bits := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10]
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
  generalize x 8 = z8
  generalize x 9 = z9
  generalize x 10 = z10
  revert z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
  decide +kernel

theorem edge_iff (x : Fin 11 → Bool) :
    circuit.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u, v) ∈ edges ∧ x u = true ∧ x v = true := by
  rw [evaluation]
  simp [edgeValue, List.any_eq_true]

def onSet (s : List Nat) (i : Fin 11) : Bool := s.contains i.val

theorem dirty_examples :
    edgeValue (onSet [0,1,3,5]) = false ∧
    (Circuit.wires circuit (List.ofFn (onSet [0,1,3,5]))).getD 17 false = true ∧
    edgeValue (onSet [9,10]) = false ∧
    (Circuit.wires circuit (List.ofFn (onSet [9,10]))).getD 13 false = true := by
  decide +kernel

theorem clean_terminals (x : Fin 11 → Bool) (w : Nat)
    (hw : w ∈ ([18,21,24,26,28] : List Nat)) :
    (circuit.wires (List.ofFn x)).getD w false = true → edgeValue x = true := by
  rw [← evaluation]
  let bits := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10]
  change (circuit.wires bits).getD w false = true → circuit.eval bits = true
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [bits, circuit, Circuit.eval, Circuit.wires, gates, GateOp.eval, List.getD]
    tauto

def deskEdges : List (Nat × Nat) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

theorem desk_evaluation (x : Fin 11 → Bool) :
    circuit.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 11, (u.val, v.val) ∈ deskEdges ∧ x u = true ∧ x v = true := by
  have same : ∀ u v : Fin 11, (u, v) ∈ edges ↔ (u.val, v.val) ∈ deskEdges := by
    decide +kernel
  rw [edge_iff]
  simp_rw [same]

end ElevenVertexRange19
