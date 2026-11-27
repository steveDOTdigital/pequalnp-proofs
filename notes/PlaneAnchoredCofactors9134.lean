import PlaneRectangles9134
import Mathlib.Tactic.Ring

namespace PlaneRectangles9134

variable {X Y : Type} [Preorder X] [OrderBot X] [Preorder Y] [OrderBot Y]

def retained (plan : (i : ℕ) → Step X Y i) (keepFirst : ℕ → Bool)
    (anchor : X × Y) (i : ℕ) : Set (X × Y) :=
  match plan i with
  | .left p => p ×ˢ Set.univ
  | .right p => Set.univ ×ˢ p
  | .empty => ∅
  | .copy a => retained plan keepFirst anchor a
  | .join a b => retained plan keepFirst anchor a ∪ retained plan keepFirst anchor b
  | .split a b => {z | (z.1,anchor.2) ∈ retained plan keepFirst anchor a ∧
      (anchor.1,z.2) ∈ retained plan keepFirst anchor b}
  | .marked a b => if keepFirst i then retained plan keepFirst anchor a else retained plan keepFirst anchor b
termination_by i
decreasing_by all_goals exact Fin.isLt _

theorem retainedContains (plan : (i : ℕ) → Step X Y i) (W : ℕ → Set (X × Y))
    (ok : valid plan W) (keepFirst : ℕ → Bool) (anchor : X × Y) (i : ℕ) :
    W i ⊆ retained plan keepFirst anchor i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have rule := ok i
    rw [retained]
    cases h : plan i with
    | left p => simp [h] at rule; simp [rule.1]
    | right p => simp [h] at rule; simp [rule.1]
    | empty => simp [h] at rule; simp [rule]
    | copy a => simp [h] at rule; simpa only [rule] using ih a a.isLt
    | join a b =>
      simp only [h] at rule
      rw [rule]
      exact Set.union_subset_union (ih a a.isLt) (ih b b.isLt)
    | split a b =>
      simp only [h] at rule
      rw [rule.1]
      rintro ⟨x,y⟩ ⟨yesA,yesB⟩
      exact ⟨ih a a.isLt ((rule.2.1 x anchor.2).mpr ((rule.2.1 x y).mp yesA)),
        ih b b.isLt ((rule.2.2 anchor.1 y).mpr ((rule.2.2 x y).mp yesB))⟩
    | marked a b =>
      simp only [h] at rule
      rw [rule]
      intro z hz
      cases chosen : keepFirst i
      · simpa only [chosen, Bool.false_eq_true, if_false] using ih b b.isLt hz.2
      · simpa only [chosen, if_true] using ih a a.isLt hz.1

theorem retainedAgrees (plan : (i : ℕ) → Step X Y i) (W : ℕ → Set (X × Y))
    (ok : valid plan W) (keepFirst : ℕ → Bool) (anchor : X × Y) (tests : Set (X × Y))
    (slices : ∀ z ∈ tests, (z.1,anchor.2) ∈ tests ∧ (anchor.1,z.2) ∈ tests)
    (choices : ∀ i (a b : Fin i), plan i = .marked a b → ∀ z ∈ tests,
      (z ∈ W (if keepFirst i then (a : ℕ) else b)) ↔ z ∈ W i)
    (i : ℕ) (z : X × Y) (test : z ∈ tests) :
    z ∈ retained plan keepFirst anchor i ↔ z ∈ W i := by
  induction i using Nat.strong_induction_on generalizing z with
  | ind i ih =>
    have rule := ok i
    rw [retained]
    cases h : plan i with
    | left p => simp [h] at rule; simp [rule.1]
    | right p => simp [h] at rule; simp [rule.1]
    | empty => simp [h] at rule; simp [rule]
    | copy a => simp [h] at rule; simpa only [rule] using ih a a.isLt z test
    | join a b =>
      simp only [h] at rule
      simp [rule, ih a a.isLt z test, ih b b.isLt z test]
    | split a b =>
      simp only [h] at rule
      have aSlice := ih a a.isLt (z.1,anchor.2) (slices z test).1
      have bSlice := ih b b.isLt (anchor.1,z.2) (slices z test).2
      have enterA : ((z.1,anchor.2) ∈ W a) ↔ z ∈ W a :=
        (rule.2.1 z.1 anchor.2).trans (rule.2.1 z.1 z.2).symm
      have enterB : ((anchor.1,z.2) ∈ W b) ↔ z ∈ W b :=
        (rule.2.2 anchor.1 z.2).trans (rule.2.2 z.1 z.2).symm
      rw [rule.1, Set.mem_ofPred_eq, Set.mem_inter_iff, aSlice,bSlice,enterA,enterB]
    | marked a b =>
      have same := choices i a b h z test
      cases chosen : keepFirst i
      · simpa only [chosen, Bool.false_eq_true, if_false] using
          (ih b b.isLt z test).trans (by simpa [chosen] using same)
      · simpa only [chosen, if_true] using
          (ih a a.isLt z test).trans (by simpa [chosen] using same)

theorem anchoredArithmetic (q n t s : ℕ) (plane : n = q^2+q+1)
    (marks : 100*t ≤ 49*q)
    (surviving : n*(q+1) ≤ 2*s+2*t*(q+1)^2) : n*(q+1) ≤ 100*s := by
  have qSquares : q*(q+1)^2 ≤ n*(q+1) := by
    calc
      q*(q+1)^2 ≤ q*(q+1)^2+(q+1) := Nat.le_add_right _ _
      _ = n*(q+1) := by rw [plane]; ring
  have losses : 100*(2*t*(q+1)^2) ≤ 98*(n*(q+1)) := by
    calc
      _ = 2*((100*t)*(q+1)^2) := by ring
      _ ≤ 2*((49*q)*(q+1)^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ marks)
      _ = 98*(q*(q+1)^2) := by ring
      _ ≤ 98*(n*(q+1)) := Nat.mul_le_mul_left _ qSquares
  omega

#print axioms retainedContains
#print axioms retainedAgrees
#print axioms anchoredArithmetic

end PlaneRectangles9134