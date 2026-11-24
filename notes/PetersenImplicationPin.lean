import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenImplicationPin

abbrev Bits := Fin 9 → Bool
def physical (x : Bits) : List Bool := List.ofFn x ++ [!x 0]
def value (l : List ℕ) (x : Bits) := GateOp.or.eval (l.map fun k => (physical x).getD k false)

theorem canonical (l : List ℕ) (len : l.length = 2) (range : ∀ k ∈ l, k < 10)
    (nontrivial : ¬∀ k ∈ l, k = 0 ∨ k = 9) (holds : 9 ∈ l) :
    ∃ j : Fin 9, j ≠ 0 ∧ ∀ x : Bits, value l x = (!x 0 || x j) := by
  obtain ⟨a,b,rfl⟩ : ∃ a b, l = [a,b] := by
    cases l with
    | nil => simp at len
    | cons a tail =>
      cases tail with
      | nil => simp at len
      | cons b rest =>
        have h : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        exact ⟨a,b,by rw [h]⟩
  have read (x : Bits) (j : Fin 9) : (physical x).getD j.val false = x j := by
    rw [physical,List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact j.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa using j.isLt),List.getElem_ofFn]
  have neg (x : Bits) : (physical x).getD 9 false = !x 0 := rfl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at holds
  rcases holds with h | h
  · subst a
    have small : b < 10 := range b (by simp)
    have other : b ≠ 0 ∧ b ≠ 9 := by
      constructor <;> intro e <;> subst b <;> apply nontrivial <;> simp
    let j : Fin 9 := ⟨b,by omega⟩
    refine ⟨j,fun e => other.1 (congrArg Fin.val e),?_⟩
    intro x
    have rb : (physical x).getD b false = x j := read x j
    simp only [value,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,neg,rb]
  · subst b
    have small : a < 10 := range a (by simp)
    have other : a ≠ 0 ∧ a ≠ 9 := by
      constructor <;> intro e <;> subst a <;> apply nontrivial <;> simp
    let j : Fin 9 := ⟨a,by omega⟩
    refine ⟨j,fun e => other.1 (congrArg Fin.val e),?_⟩
    intro x
    have ra : (physical x).getD a false = x j := read x j
    simp only [value,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,neg,ra]
    exact Bool.or_comm _ _

theorem local_gate (a b : Bool) :
    (a && (!a || b)) = (a && b) ∧ (a || (!a || b)) = true ∧
    (a && !a) = false ∧ (a || !a) = true := by
  cases a <;> cases b <;> decide

end PetersenImplicationPin
