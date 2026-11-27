import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
open scoped BigOperators

namespace PlaneRectangles9134

theorem countBound {Flag Gate : Type} [DecidableEq Flag] [DecidableEq Gate]
    (flags : Finset Flag) (marks : Finset Gate) (activation : Gate → Finset Flag) (s : ℕ)
    (unmarked : (flags \ marks.biUnion activation).card ≤ s)
    (small : ∀ gate ∈ marks, (activation gate).card ≤ 99) :
    flags.card ≤ s + 99 * marks.card := by
  have covering : flags ⊆ (flags \ marks.biUnion activation) ∪ marks.biUnion activation := by
    intro f hf
    by_cases seen : f ∈ marks.biUnion activation
    · exact Finset.mem_union_right _ seen
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hf,seen⟩)
  have covered := Finset.card_le_card covering
  have union := Finset.card_union_le (flags \ marks.biUnion activation) (marks.biUnion activation)
  have overlaps := Finset.card_biUnion_le (s := marks) (t := activation)
  have weights : (∑ gate ∈ marks, (activation gate).card) ≤ 99 * marks.card := by
    calc
      _ ≤ ∑ _gate ∈ marks, (99 : ℕ) := Finset.sum_le_sum small
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem someMarkWide {Flag Gate : Type} [DecidableEq Flag] [DecidableEq Gate]
    (flags : Finset Flag) (marks : Finset Gate) (activation : Gate → Finset Flag) (s n q : ℕ)
    (incidences : flags.card = n*(q+1))
    (unmarked : (flags \ marks.biUnion activation).card ≤ s)
    (budget : 100 * marks.card < n*q)
    (counter : 100*s < n*(q+1)) :
    ∃ gate ∈ marks, 100 ≤ (activation gate).card := by
  by_contra! none
  have bound := countBound flags marks activation s unmarked (fun gate found => by
    have := none gate found
    omega)
  have larger : n*q ≤ n*(q+1) := Nat.mul_le_mul_left n (Nat.le_succ q)
  omega

#print axioms someMarkWide

end PlaneRectangles9134