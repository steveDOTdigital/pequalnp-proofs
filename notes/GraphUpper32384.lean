import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace GraphUpper32384

def edges : List ℕ := [0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7]

def graph (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : Circuit :=
  ⟨[
    ⟨.or, [1,2]⟩,
    ⟨.or, [4,5]⟩,
    ⟨.or, [0,7]⟩,
    ⟨.or, [4,7]⟩,
    ⟨.or, [1,6]⟩,
    ⟨.or, [0,12]⟩,
    ⟨.or, [6,7]⟩,
    ⟨.or, [5,14]⟩,
    ⟨.and, [3,0]⟩,
    ⟨.and, [10,9]⟩,
    ⟨.and, [11,13]⟩,
    ⟨.and, [15,8]⟩,
    ⟨.or, [16,17]⟩,
    ⟨.or, [20,18]⟩,
    ⟨.or, [21,19]⟩], 22⟩

theorem size : witness.size = 15 := rfl

set_option maxHeartbeats 4500000 in
set_option maxRecDepth 12000 in
theorem table (a b c d e f g h : Bool) :
    witness.eval (List.ofFn ![a,b,c,d,e,f,g,h]) = graph ![a,b,c,d,e,f,g,h] := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide +kernel

theorem truth (x : Fin 8 → Bool) : witness.eval (List.ofFn x) = graph x := by
  have fromBits : (![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7] : Fin 8 → Bool) = x := by
    funext i
    fin_cases i <;> rfl
  exact fromBits ▸ table (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

#print axioms truth

end GraphUpper32384