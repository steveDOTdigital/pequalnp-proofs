import PlaneTests7915

namespace PlaneExactTwo8221

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PlaneSupport7915
open PlaneTests7915

theorem rowAddCases (A B : Bank) (i : Fin 26) :
    row A B i = Fin.addCases (fun p : Fin 13 => decide (p ∈ A))
      (fun l : Fin 13 => decide (l ∈ B)) i := by
  apply Fin.addCases (m := 13) (n := 13) (motive := fun i : Fin 26 =>
    row A B i = Fin.addCases (fun p : Fin 13 => decide (p ∈ A))
      (fun l : Fin 13 => decide (l ∈ B)) i)
  · intro p
    simpa only [Fin.addCases_left] using rowLeft A B p
  · intro l
    simpa only [Fin.addCases_right] using rowRight A B l

theorem rowMonotone {A B P Q : Bank} (left : P ⊆ A) (right : Q ⊆ B) (i : Fin 26) :
    row P Q i = true → row A B i = true := by
  apply Fin.addCases (m := 13) (n := 13) (motive := fun i : Fin 26 =>
    row P Q i = true → row A B i = true)
  · intro p
    simp only [rowLeft, decide_eq_true_eq]
    exact fun hp => left hp
  · intro l
    simp only [rowRight, decide_eq_true_eq]
    exact fun hl => right hl

theorem smallerAcceptedRow (C : Circuit) (mono : Monotone2 C) (A B : Bank)
    (accept : circuitFun 26 C (row A B) = true) :
    ∃ P Q : Bank, P ⊆ A ∧ Q ⊆ B ∧
      P.card ≤ C.lineDeg 26 (Finset.range 13) ∧
      Q.card ≤ C.lineDeg 26 (Finset.Ico 13 26) ∧ circuitFun 26 C (row P Q) = true := by
  obtain ⟨S,hot,pcap,lcap,force⟩ :=
    circuitSupport C mono (Finset.range 13) (Finset.Ico 13 26) (row A B) accept
  refine ⟨leftProjection S, rightProjection S, ?_, ?_, (leftSize S).trans pcap,
    (rightSize S).trans lcap, force _ ?_⟩
  · intro p hp
    have live := hot (Fin.castAdd 13 p) (Finset.mem_filter.mp hp).2
    simpa only [rowLeft, decide_eq_true_eq] using live
  · intro l hl
    have live := hot (Fin.natAdd 13 l) (Finset.mem_filter.mp hl).2
    simpa only [rowRight, decide_eq_true_eq] using live
  · intro i
    apply Fin.addCases (m := 13) (n := 13) (motive := fun i : Fin 26 =>
      i ∈ S → row (leftProjection S) (rightProjection S) i = true)
    · intro p hp
      simpa only [rowLeft, decide_eq_true_eq] using
        (show p ∈ leftProjection S from Finset.mem_filter.mpr ⟨by simp, hp⟩)
    · intro l hl
      simpa only [rowRight, decide_eq_true_eq] using
        (show l ∈ rightProjection S from Finset.mem_filter.mpr ⟨by simp, hl⟩)

theorem rejectsAllIndependent {near : Fin 13 → Fin 13 → Prop} [DecidableRel near]
    (C : Circuit) (mono : Monotone2 C) (A B : Bank)
    (points : C.lineDeg 26 (Finset.range 13) ≤ 2)
    (lines : C.lineDeg 26 (Finset.Ico 13 26) ≤ 2)
    (reject : ∀ P Q : Bank, admissible near P Q → circuitFun 26 C (row P Q) = false)
    (disjoint : ∀ p ∈ A, ∀ l ∈ B, ¬ near p l) :
    circuitFun 26 C (row A B) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepts
  obtain ⟨P,Q,pA,qB,pCap,qCap,small⟩ := smallerAcceptedRow C mono A B accepts
  have cap : admissible near P Q :=
    ⟨fun p hp l hl => disjoint p (pA hp) l (qB hl),
      fun l => (Finset.card_le_card (Finset.filter_subset (fun p => near p l) P)).trans (pCap.trans points),
      fun p => (Finset.card_le_card (Finset.filter_subset (fun l => near p l) Q)).trans (qCap.trans lines)⟩
  rw [reject P Q cap] at small
  contradiction

theorem acceptsFlagSuperset (C : Circuit) (mono : Monotone2 C)
    (A B : Bank) (p l : Fin 13) (hp : p ∈ A) (hl : l ∈ B)
    (flag : circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) :
    circuitFun 26 C (row A B) = true := by
  obtain ⟨S, hot, _, _, force⟩ :=
    circuitSupport C mono (Finset.range 13) (Finset.Ico 13 26) _ flag
  apply force _
  intro i hi
  have live := hot i hi
  simp only [decide_eq_true_eq] at live
  rcases live with rfl | rfl
  · simpa only [rowLeft, decide_eq_true_eq] using hp
  · simpa only [rowRight, decide_eq_true_eq] using hl

theorem computesExactIncidence {near : Fin 13 → Fin 13 → Prop} [DecidableRel near]
    (C : Circuit) (mono : Monotone2 C)
    (points : C.lineDeg 26 (Finset.range 13) ≤ 2)
    (lines : C.lineDeg 26 (Finset.Ico 13 26) ≤ 2)
    (flags : ∀ p l : Fin 13, near p l →
      circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true)
    (reject : ∀ P Q : Bank, admissible near P Q → circuitFun 26 C (row P Q) = false)
    (A B : Bank) :
    circuitFun 26 C (row A B) = true ↔ ∃ p ∈ A, ∃ l ∈ B, near p l := by
  constructor
  · intro accepts
    by_contra missing
    have disjoint : ∀ p ∈ A, ∀ l ∈ B, ¬ near p l := by
      intro p hp l hl edge
      exact missing ⟨p,hp,l,hl,edge⟩
    rw [rejectsAllIndependent C mono A B points lines reject disjoint] at accepts
    contradiction
  · rintro ⟨p,hp,l,hl,edge⟩
    exact acceptsFlagSuperset C mono A B p l hp hl (flags p l edge)

#print axioms computesExactIncidence

end PlaneExactTwo8221
