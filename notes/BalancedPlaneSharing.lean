import BalancedPlane9796

namespace BalancedPlane9796
open FlagCrossRank OneShorePairRank

-- The entries are the union of three edge-disjoint perfect matchings.
def cubicMask : Fin 12 → Nat := ![1041, 2082, 7, 140, 26, 560, 1096, 2240, 289, 832, 1664, 2308]
def core (e : Fin 12 × Fin 12) : Prop := (cubicMask e.1).testBit e.2.val = true
instance : DecidablePred core := fun _ => inferInstanceAs (Decidable (_ = true))

def outsideCore := Finset.univ.filter (fun e : Fin 12 × Fin 12 => I e.1 e.2 ∧ ¬ core e)
def pointCore (p : Fin 12) := Finset.univ.filter (fun e : Fin 12 × Fin 12 => core e ∧ p = e.1)
def lineCore (l : Fin 12) := Finset.univ.filter (fun e : Fin 12 × Fin 12 => core e ∧ l = e.2)

theorem coreGeometry : outsideCore.card = 8 ∧
    (∀ p, (pointCore p).card ≤ 3) ∧ (∀ l, (lineCore l).card ≤ 3) := by decide +kernel

def incidentCore {H : Type} : Label (Fin 12) (Fin 12) H → Finset (Fin 12 × Fin 12) :=
  Sum.elim pointCore (Sum.elim lineCore (fun _ => ∅))

theorem retainedCapacity {H : Type} [Fintype H] [DecidableEq H] (u v : H → Fin 12)
    [DecidableRel (kept I u v)] (K : Finset (Label (Fin 12) (Fin 12) H))
    (hit : ∀ e : retained I u v, left I u v e ∈ K ∨ right I u v e ∈ K) :
    Fintype.card (retained I u v) ≤ 8 + 3*K.card := by
  classical
  let D := Finset.univ.filter (fun e : Fin 12 × Fin 12 => kept I u v e.1 e.2)
  have incl : D ⊆ outsideCore ∪ K.biUnion incidentCore := by
    intro e he
    have ok : kept I u v e.1 e.2 := (Finset.mem_filter.mp he).2
    by_cases hc : core e
    · apply Finset.mem_union_right
      rcases hit ⟨e,ok⟩ with hp | hl
      · exact Finset.mem_biUnion.mpr ⟨_,hp,by simp [left,incidentCore,pointCore,hc]⟩
      · exact Finset.mem_biUnion.mpr ⟨_,hl,by simp [right,incidentCore,lineCore,hc]⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ok.1,hc⟩)
  have per (w : Label (Fin 12) (Fin 12) H) : (incidentCore w).card ≤ 3 := by
    rcases w with p | (l | h)
    · exact coreGeometry.2.1 p
    · exact coreGeometry.2.2 l
    · simp [incidentCore]
  have cap : (K.biUnion incidentCore).card ≤ 3*K.card := calc
    _ ≤ ∑ w ∈ K, (incidentCore w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ K, (3 : Nat) := Finset.sum_le_sum (fun w _ => per w)
    _ = _ := by simp [Nat.mul_comm]
  have dc : Fintype.card (retained I u v) = D.card := by
    simp [D,retained,FlagCrossRank.Flag,Fintype.card_subtype]
  have bound := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  rw [coreGeometry.1] at bound
  omega

theorem sharingPenalty {H : Type} [Fintype H] [DecidableEq H] (u v : H → Fin 12)
    [DecidableRel (kept I u v)] (proper : ∀ h, u h ≠ v h)
    (T : FlagCrossRank.Tree (Label (Fin 12) (Fin 12) H))
    (correct : ∀ X Y, T.val (bits u v X Y) = true ↔ ∃ p l, I p l ∧ X p ∧ Y l)
    (shared : 2 * Fintype.card H ≤ T.cost (fun w => if physical w then 0 else 1))
    (s : Nat) (size : T.leaves + Fintype.card H ≤ s + 1) : 165 + Fintype.card H ≤ 3*s := by
  have loss := eraseCount I u v squareFree proper
  rw [geometry.1] at loss
  have rank := rawRetained I u v squareFree T correct (12 - (2 * Fintype.card H)/3) (by
    intro K hit
    have cap := retainedCapacity u v K hit
    omega)
  have both := splitLeaves T
  omega

#print axioms sharingPenalty
end BalancedPlane9796
