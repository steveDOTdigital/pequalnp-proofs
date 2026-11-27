import Mathlib.Data.Set.Prod
import Mathlib.Order.UpperLower.Basic

namespace PlaneRectangles9134

variable {X Y : Type} [Preorder X] [OrderBot X] [Preorder Y] [OrderBot Y]

inductive Step (X Y : Type) (i : ℕ) where
  | left (p : Set X)
  | right (p : Set Y)
  | empty
  | copy (a : Fin i)
  | join (a b : Fin i)
  | split (a b : Fin i)
  | marked (a b : Fin i)

def valid (plan : (i : ℕ) → Step X Y i) (W : ℕ → Set (X × Y)) : Prop :=
  ∀ i, match plan i with
  | .left p => W i = p ×ˢ Set.univ ∧ IsUpperSet p ∧ ⊥ ∉ p
  | .right p => W i = Set.univ ×ˢ p ∧ IsUpperSet p ∧ ⊥ ∉ p
  | .empty => W i = ∅
  | .copy a => W i = W a
  | .join a b => W i = W a ∪ W b
  | .split a b =>
    W i = W a ∩ W b ∧
      (∀ x y, (x,y) ∈ W a ↔ (x,⊥) ∈ W a) ∧
      (∀ x y, (x,y) ∈ W b ↔ (⊥,y) ∈ W b)
  | .marked a b => W i = W a ∩ W b

def raw (plan : (i : ℕ) → Step X Y i) (i : ℕ) : Set (X × Y) :=
  match plan i with
  | .left p => p ×ˢ Set.univ
  | .right p => Set.univ ×ˢ p
  | .empty => ∅
  | .copy a => raw plan a
  | .join a b => raw plan a ∪ raw plan b
  | .split _ _ => ∅
  | .marked _ _ => ∅
termination_by i
decreasing_by all_goals exact Fin.isLt _

def clean (plan : (i : ℕ) → Step X Y i) (i : ℕ) : Set (X × Y) :=
  match plan i with
  | .left p => p ×ˢ Set.univ
  | .right p => Set.univ ×ˢ p
  | .empty => ∅
  | .copy a => clean plan a
  | .join a b => clean plan a ∪ clean plan b
  | .split a b => {z | (z.1,⊥) ∈ raw plan a ∧ (⊥,z.2) ∈ raw plan b}
  | .marked _ _ => ∅
termination_by i
decreasing_by all_goals exact Fin.isLt _

theorem upperAndBottom (plan : (i : ℕ) → Step X Y i) (W : ℕ → Set (X × Y))
    (ok : valid plan W) (i : ℕ) : IsUpperSet (W i) ∧ ((⊥,⊥) : X × Y) ∉ W i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have rule := ok i
    cases classification : plan i with
    | left p =>
      rw [classification] at rule
      rw [rule.1]
      refine ⟨?_,by simpa using rule.2.2⟩
      intro a b order mem
      exact ⟨rule.2.1 order.1 mem.1,Set.mem_univ _⟩
    | right p =>
      rw [classification] at rule
      rw [rule.1]
      refine ⟨?_,by simpa using rule.2.2⟩
      intro a b order mem
      exact ⟨Set.mem_univ _,rule.2.1 order.2 mem.2⟩
    | empty =>
      rw [classification] at rule
      rw [rule]
      refine ⟨?_,by simp⟩
      intro a b order member
      simp at member
    | copy a =>
      rw [classification] at rule
      simpa only [rule] using ih a a.isLt
    | join a b =>
      rw [classification] at rule
      rw [rule]
      exact ⟨(ih a a.isLt).1.union (ih b b.isLt).1, by simp [(ih a a.isLt).2,(ih b b.isLt).2]⟩
    | split a b =>
      rw [classification] at rule
      rw [rule.1]
      exact ⟨(ih a a.isLt).1.inter (ih b b.isLt).1, by simp [(ih a a.isLt).2]⟩
    | marked a b =>
      rw [classification] at rule
      rw [rule]
      exact ⟨(ih a a.isLt).1.inter (ih b b.isLt).1, by simp [(ih a a.isLt).2]⟩

theorem approximationsSound (plan : (i : ℕ) → Step X Y i) (W : ℕ → Set (X × Y))
    (ok : valid plan W) (i : ℕ) : raw plan i ⊆ W i ∧ clean plan i ⊆ W i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have rule := ok i
    rw [raw,clean]
    cases classification : plan i with
    | left p =>
      rw [classification] at rule
      simp [rule.1]
    | right p =>
      rw [classification] at rule
      simp [rule.1]
    | empty =>
      simp only [classification] at rule
      simp [rule]
    | copy a =>
      simp only [classification] at rule
      simpa only [rule] using ih a a.isLt
    | join a b =>
      simp only [classification] at rule
      rw [rule]
      exact ⟨Set.union_subset_union (ih a a.isLt).1 (ih b b.isLt).1,
        Set.union_subset_union (ih a a.isLt).2 (ih b b.isLt).2⟩
    | split a b =>
      simp only [classification] at rule
      refine ⟨Set.empty_subset _,?_⟩
      rintro ⟨x,y⟩ ⟨hA,hB⟩
      rw [rule.1]
      exact ⟨(rule.2.1 x y).mpr ((ih a a.isLt).1 hA),
        (rule.2.2 x y).mpr ((ih b b.isLt).1 hB)⟩
    | marked a b => exact ⟨Set.empty_subset _,Set.empty_subset _⟩

theorem markedFalse (plan : (i : ℕ) → Step X Y i) (W : ℕ → Set (X × Y))
    (ok : valid plan W) (x : X) (y : Y)
    (unmarked : ∀ i, ∀ a b : Fin i, plan i = .marked a b → (x,y) ∉ W i) (i : ℕ) :
    ((x,⊥) ∈ raw plan i ↔ (x,⊥) ∈ W i) ∧
    ((⊥,y) ∈ raw plan i ↔ (⊥,y) ∈ W i) ∧
    ((x,y) ∈ clean plan i ↔ (x,y) ∈ W i) := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have rule := ok i
    rw [raw,clean]
    cases classification : plan i with
    | left p =>
      rw [classification] at rule
      simp [rule.1]
    | right p =>
      rw [classification] at rule
      simp [rule.1]
    | empty =>
      simp only [classification] at rule
      simp [rule]
    | copy a =>
      simp only [classification] at rule
      simpa only [rule] using ih a a.isLt
    | join a b =>
      simp only [classification] at rule
      rcases ih a a.isLt with ⟨aL,aR,aBoth⟩
      rcases ih b b.isLt with ⟨bL,bR,bBoth⟩
      simp [rule,aL,aR,aBoth,bL,bR,bBoth]
    | split a b =>
      simp only [classification] at rule
      have noA := (upperAndBottom plan W ok a).2
      have noB := (upperAndBottom plan W ok b).2
      have aL := (ih a a.isLt).1
      have bR := (ih b b.isLt).2.1
      simp only [rule.1, Set.mem_inter_iff, Set.mem_empty_iff_false, Set.mem_ofPred_eq, aL,bR]
      have suppressedA : (⊥,y) ∉ W a := fun yes => noA ((rule.2.1 ⊥ y).mp yes)
      have suppressedB : (x,⊥) ∉ W b := fun yes => noB ((rule.2.2 x ⊥).mp yes)
      simp [suppressedA,suppressedB,rule.2.1 x y,rule.2.2 x y]
    | marked a b =>
      have no := unmarked i a b classification
      have mono := (upperAndBottom plan W ok i).1
      have leftOrder : (x,(⊥ : Y)) ≤ (x,y) := ⟨le_rfl,bot_le⟩
      have rightOrder : ((⊥ : X),y) ≤ (x,y) := ⟨bot_le,le_rfl⟩
      have noL : (x,⊥) ∉ W i := fun mem => no (mono leftOrder mem)
      have noR : (⊥,y) ∉ W i := fun mem => no (mono rightOrder mem)
      simp [no,noL,noR]

#print axioms approximationsSound
#print axioms markedFalse

end PlaneRectangles9134