import PlaneSupport7915

namespace PlaneTests7915

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PlaneSupport7915
open Finset

abbrev Bank := Finset (Fin 13)

def row (A B : Bank) (i : Fin 26) : Bool :=
  if h : i.val < 13 then decide ((⟨i.val,h⟩ : Fin 13) ∈ A)
  else decide ((⟨i.val-13,by omega⟩ : Fin 13) ∈ B)

theorem rowLeft (A B : Bank) (p : Fin 13) :
    row A B (Fin.castAdd 13 p) = decide (p ∈ A) := by
  simp [row,p.isLt]

theorem rowRight (A B : Bank) (l : Fin 13) :
    row A B (Fin.natAdd 13 l) = decide (l ∈ B) := by
  have negative : ¬ (Fin.natAdd 13 l).val < 13 := by
    change ¬ 13+l.val < 13
    omega
  rw [row,dif_neg negative]
  congr 2
  apply Fin.ext
  change 13+l.val-13 = l.val
  omega

def leftProjection (S : Finset (Fin 26)) : Bank :=
  Finset.univ.filter (fun p => Fin.castAdd 13 p ∈ S)

def rightProjection (S : Finset (Fin 26)) : Bank :=
  Finset.univ.filter (fun l => Fin.natAdd 13 l ∈ S)

theorem leftSize (S : Finset (Fin 26)) :
    (leftProjection S).card ≤ shoreCount (Finset.range 13) S := by
  have inj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := by
    intro a b eq
    apply Fin.ext
    exact congrArg (fun v : Fin 26 => v.val) eq
  rw [← Finset.card_image_of_injective (leftProjection S) inj]
  apply Finset.card_le_card
  intro j hj
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).2,Finset.mem_range.mpr p.isLt⟩

theorem rightSize (S : Finset (Fin 26)) :
    (rightProjection S).card ≤ shoreCount (Finset.Ico 13 26) S := by
  have inj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := by
    intro a b eq
    apply Fin.ext
    have numbers := congrArg Fin.val eq
    change 13+a.val = 13+b.val at numbers
    omega
  rw [← Finset.card_image_of_injective (rightProjection S) inj]
  apply Finset.card_le_card
  intro j hj
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hj
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).2,?_⟩
  rw [Finset.mem_Ico]
  change 13 ≤ 13+l.val ∧ 13+l.val < 26
  omega

def admissible (near : Fin 13 → Fin 13 → Prop) [DecidableRel near] (A B : Bank) : Prop :=
  (∀ p ∈ A, ∀ l ∈ B, ¬ near p l) ∧
  (∀ l, (A.filter (fun p => near p l)).card ≤ 2) ∧
  (∀ p, (B.filter (fun l => near p l)).card ≤ 2)

theorem subsetAdmissible {near : Fin 13 → Fin 13 → Prop} [DecidableRel near]
    {A B P L : Bank} (h : admissible near A B) (pa : P ⊆ A) (lb : L ⊆ B) :
    admissible near P L := by
  refine ⟨fun p hp l hl => h.1 p (pa hp) l (lb hl),?_,?_⟩
  · intro l
    apply le_trans _ (h.2.1 l)
    apply Finset.card_le_card
    intro p hp
    obtain ⟨inP, relation⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨pa inP,relation⟩
  · intro p
    apply le_trans _ (h.2.2 p)
    apply Finset.card_le_card
    intro l hl
    obtain ⟨inL, relation⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨lb inL,relation⟩

theorem acceptsCoveredTest {near : Fin 13 → Fin 13 → Prop} [DecidableRel near]
    (tests : Finset (Bank × Bank))
    (coverage : ∀ A B, admissible near A B → A.card ≤ 2 → B.card ≤ 3 →
      ∃ T ∈ tests, A ⊆ T.1 ∧ B ⊆ T.2)
    (C : Circuit) (mono : Monotone2 C)
    (points : C.lineDeg 26 (Finset.range 13) ≤ 2)
    (lines : C.lineDeg 26 (Finset.Ico 13 26) ≤ 3)
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

end PlaneTests7915