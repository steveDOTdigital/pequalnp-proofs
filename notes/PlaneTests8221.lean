import PlaneTests7915

namespace PlaneTests8221

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PlaneSupport7915
open PlaneTests7915
open Finset

theorem acceptsCoveredTest {near : Fin 13 → Fin 13 → Prop} [DecidableRel near]
    (pointLimit lineLimit : ℕ) (tests : Finset (Bank × Bank))
    (coverage : ∀ A B, admissible near A B → A.card ≤ pointLimit → B.card ≤ lineLimit →
      ∃ T ∈ tests, A ⊆ T.1 ∧ B ⊆ T.2)
    (C : Circuit) (mono : Monotone2 C)
    (points : C.lineDeg 26 (Finset.range 13) ≤ pointLimit)
    (lines : C.lineDeg 26 (Finset.Ico 13 26) ≤ lineLimit)
    (A B : Bank) (ok : admissible near A B) (yes : circuitFun 26 C (row A B) = true) :
    ∃ T ∈ tests, ∀ y : Fin 26 → Bool,
      (∀ p ∈ T.1, y (Fin.castAdd 13 p) = true) →
      (∀ l ∈ T.2, y (Fin.natAdd 13 l) = true) → circuitFun 26 C y = true := by
  obtain ⟨S,hot,pcap,lcap,force⟩ := circuitSupport C mono (Finset.range 13) (Finset.Ico 13 26) (row A B) yes
  have leftSub : leftProjection S ⊆ A := by
    intro p hp
    have live := hot (Fin.castAdd 13 p) (Finset.mem_filter.mp hp).2
    simpa only [rowLeft, decide_eq_true_eq] using live
  have rightSub : rightProjection S ⊆ B := by
    intro l hl
    have live := hot (Fin.natAdd 13 l) (Finset.mem_filter.mp hl).2
    simpa only [rowRight, decide_eq_true_eq] using live
  obtain ⟨T, inTests, containLeft, containRight⟩ :=
    coverage _ _ (subsetAdmissible ok leftSub rightSub)
      ((leftSize S).trans (pcap.trans points)) ((rightSize S).trans (lcap.trans lines))
  refine ⟨T,inTests,?_⟩
  intro y leftHot rightHot
  apply force y
  intro i hi
  by_cases left : i.val < 13
  · let p : Fin 13 := ⟨i.val,left⟩
    have wire : Fin.castAdd 13 p = i := Fin.ext rfl
    have chosen : p ∈ leftProjection S := Finset.mem_filter.mpr ⟨by simp,wire ▸ hi⟩
    rw [← wire]
    exact leftHot p (containLeft chosen)
  · let l : Fin 13 := ⟨i.val-13,by omega⟩
    have wire : Fin.natAdd 13 l = i := by
      apply Fin.ext
      change 13+(i.val-13) = i.val
      omega
    have chosen : l ∈ rightProjection S := Finset.mem_filter.mpr ⟨by simp,wire ▸ hi⟩
    rw [← wire]
    exact rightHot l (containRight chosen)

#print axioms acceptsCoveredTest

end PlaneTests8221
