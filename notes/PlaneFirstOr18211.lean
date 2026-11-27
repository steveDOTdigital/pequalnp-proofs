import PEqualNP.Defs.MetaComplexityLgpMono

namespace PlaneFirstOr18211

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def firstValue (first : Gate) (x : Fin 26 → Bool) : Bool :=
  first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false)

def rawPorts (first : Gate) : Finset Nat :=
  (first.inputs.filter (fun i => i < 26)).toFinset

theorem portsCard {first : Gate} (arity : first.inputs.length ≤ 2) :
    (rawPorts first).card ≤ 2 := by
  unfold rawPorts
  calc
    _ ≤ (first.inputs.filter (fun i => i < 26)).length := List.toFinset_card_le _
    _ ≤ first.inputs.length := List.length_filter_le ..
    _ ≤ 2 := arity

theorem rawPortRead (first : Gate) (x : Fin 26 → Bool) (isOr : first.op = GateOp.or) :
    firstValue first x = true ↔
    ∃ i ∈ rawPorts first, (List.ofFn x).getD i false = true := by
  unfold firstValue rawPorts
  rw [isOr, GateOp.eval, List.any_eq_true]
  constructor
  · rintro ⟨b, member, yes⟩
    obtain ⟨i, hi, eq⟩ := List.mem_map.mp member
    have read : (List.ofFn x).getD i false = true := eq.trans yes
    have bound : i < 26 := by
      by_contra beyond
      have off : (List.ofFn x)[i]? = none := by
        apply List.getElem?_eq_none
        simpa using (Nat.le_of_not_gt beyond)
      rw [List.getD_eq_getElem?_getD, off] at read
      exact Bool.noConfusion read
    refine ⟨i, ?_, read⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨hi, by simpa using bound⟩
  · rintro ⟨i, member, yes⟩
    rw [List.mem_toFinset, List.mem_filter] at member
    exact ⟨_, List.mem_map.mpr ⟨i, member.1, rfl⟩, yes⟩

theorem firstEquivalent {left right : Gate}
    (orLeft : left.op = GateOp.or) (orRight : right.op = GateOp.or)
    (same : rawPorts left = rawPorts right) (x : Fin 26 → Bool) :
    firstValue left x = firstValue right x := by
  have iffVals := (rawPortRead left x orLeft).trans
    ((by rw [same]) : (∃ i ∈ rawPorts left, (List.ofFn x).getD i false = true) ↔
      ∃ i ∈ rawPorts right, (List.ofFn x).getD i false = true)
  have eq := iffVals.trans (rawPortRead right x orRight).symm
  cases l : firstValue left x <;> cases r : firstValue right x <;> simp_all

theorem replacedPrefix {left right : Gate} (tail : Circuit)
    (orLeft : left.op = GateOp.or) (orRight : right.op = GateOp.or)
    (same : rawPorts left = rawPorts right) (x : Fin 26 → Bool) :
    tail.eval (List.ofFn x ++ [firstValue left x]) =
      tail.eval (List.ofFn x ++ [firstValue right x]) := by
  rw [firstEquivalent orLeft orRight same x]

def addFirst (first : Gate) (tail : Circuit) : Circuit :=
  ⟨first :: tail.gates, tail.output⟩

theorem evalAddedFirst (first : Gate) (tail : Circuit) (x : Fin 26 → Bool) :
    (addFirst first tail).eval (List.ofFn x) = tail.eval (List.ofFn x ++ [firstValue first x]) := by
  rfl

theorem addedFirstSize (first : Gate) (tail : Circuit) :
    (addFirst first tail).size = tail.size + 1 := by
  rfl

theorem addedFirstMono (first : Gate) (tail : Circuit) (mono : Monotone2 tail)
    (isOr : first.op = GateOp.or) (arity : first.inputs.length ≤ 2) :
    Monotone2 (addFirst first tail) := by
  intro g member
  change g ∈ first :: tail.gates at member
  rcases List.mem_cons.mp member with rfl | inTail
  · exact ⟨by simp [isOr], arity⟩
  · exact mono g inTail

#print axioms replacedPrefix
#print axioms evalAddedFirst
#print axioms addedFirstMono

end PlaneFirstOr18211
