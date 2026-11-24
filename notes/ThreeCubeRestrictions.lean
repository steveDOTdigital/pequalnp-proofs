import Mathlib
import PEqualNP.MetaComplexity.L106

namespace ThreeCubeRestrictions

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 8 × Fin 8) :=
  [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]

def value (x : Fin 8 → Bool) := edges.any fun e => x e.1 && x e.2

def adjacent (a b : Fin 8) : Bool :=
  edges.contains (a,b) || edges.contains (b,a)

-- Forcing y to one still leaves an edge on which changing x changes the answer.
theorem distinguishing_neighbor : ∀ x y : Fin 8, x ≠ y →
    ∃ z : Fin 8, z ≠ y ∧ adjacent x z = true ∧ adjacent y z = false := by
  decide +kernel

-- The six surviving vertices appear around the cycle as 1, 3, 2, 6, 4, 5.
def twoDeleted (x : Fin 6 → Bool) : Bool :=
  value ![false, x 0, x 2, x 1, x 4, x 5, x 3, false]

def cyclic (x : Fin 6 → Bool) : Bool :=
  decide (∃ i j : Fin 6, (i.val + 1) % 6 = j.val ∧ x i = true ∧ x j = true)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem twoDeleted_is_cycle : ∀ x, twoDeleted x = cyclic x := by
  decide +kernel

theorem twoDeleted_exact (s : ℕ) : HasCircuitSize 6 twoDeleted s ↔ 8 ≤ s := by
  rw [show twoDeleted = cyclic from funext twoDeleted_is_cycle]
  have bound := PEqualNP.MetaComplexity.L106 6 s (by decide)
  change HasCircuitSize 6 cyclic s ↔ 9 ≤ s + 1 at bound
  exact bound.trans (by omega)

-- With only vertex 0 removed, the input coordinates are cube vertices 1 to 7.
def oneDeleted (x : Fin 7 → Bool) : Bool :=
  value ![false, x 0, x 1, x 2, x 3, x 4, x 5, x 6]

def gates : List Gate :=
  [⟨.or,[1,6]⟩, ⟨.or,[7,0]⟩, ⟨.or,[7,3]⟩, ⟨.or,[0,3]⟩, ⟨.or,[10,6]⟩,
   ⟨.and,[2,8]⟩, ⟨.and,[4,11]⟩, ⟨.and,[5,9]⟩, ⟨.or,[12,13]⟩, ⟨.or,[15,14]⟩]

def circuit : Circuit := ⟨gates,16⟩

theorem oneDeleted_size : circuit.size = 10 := rfl

def allowed : GateOp → Bool
  | .and | .or => true
  | _ => false

theorem oneDeleted_monotone : Monotone2 circuit := by
  intro g hg
  have all : gates.all (fun h => allowed h.op && decide (h.inputs.length ≤ 2)) = true := rfl
  have h := List.all_eq_true.mp all g hg
  have good : allowed g.op = true ∧ g.inputs.length ≤ 2 := by simpa using h
  refine ⟨?_, good.2⟩
  have valid := good.1
  cases e : g.op <;> simp_all [allowed]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem oneDeleted_eval : ∀ x : Fin 7 → Bool,
    circuit.eval (List.ofFn x) = oneDeleted x := by
  decide +kernel

end ThreeCubeRestrictions
