import PEqualNP.Defs.GenericRejection

namespace PlaneMinimalJunk8851

open PEqualNP.GenericRejection
open PEqualNP.CircuitLowerBounds

variable {N : Nat}

def Minimal (F : Finset (Fin N) → Finset (Fin N) → Prop) (X Y : Finset (Fin N)) : Prop :=
  F X Y ∧ ∀ A B, A ⊆ X → B ⊆ Y → F A B → A = X ∧ B = Y

noncomputable def family (S : Fin N → Finset (Fin N))
    (F : Finset (Fin N) → Finset (Fin N) → Prop) :
    Finset (Finset (Fin N) × Finset (Fin N)) := by
  classical
  exact Finset.univ.filter fun j => IsFalseInput S j.1 j.2 ∧ Minimal F j.1 j.2

theorem family_mem (S : Fin N → Finset (Fin N))
    (F : Finset (Fin N) → Finset (Fin N) → Prop) (j : Finset (Fin N) × Finset (Fin N)) :
    j ∈ family S F ↔ IsFalseInput S j.1 j.2 ∧ Minimal F j.1 j.2 := by
  classical
  simp [family]

theorem minimalBelow (F : Finset (Fin N) → Finset (Fin N) → Prop)
    (X Y : Finset (Fin N)) (positive : F X Y) :
    ∃ A B, A ⊆ X ∧ B ⊆ Y ∧ Minimal F A B := by
  classical
  let property := fun t : Nat =>
    ∃ A B : Finset (Fin N), A ⊆ X ∧ B ⊆ Y ∧ F A B ∧ A.card + B.card = t
  have existsMeasure : ∃ t, property t := ⟨X.card+Y.card,X,Y,fun _ h => h,fun _ h => h,positive,rfl⟩
  obtain ⟨A,B,left,right,accepted,weight⟩ := Nat.find_spec existsMeasure
  refine ⟨A,B,left,right,accepted,?_⟩
  intro P L belowA belowB yes
  have sameOrMore : Nat.find existsMeasure ≤ P.card+L.card :=
    Nat.find_min' existsMeasure ⟨P,L,belowA.trans left,belowB.trans right,yes,rfl⟩
  have p := Finset.card_le_card belowA
  have l := Finset.card_le_card belowB
  exact ⟨Finset.eq_of_subset_of_card_le belowA (by omega),
    Finset.eq_of_subset_of_card_le belowB (by omega)⟩

theorem falseBelow (S : Fin N → Finset (Fin N))
    {A B X Y : Finset (Fin N)} (none : IsFalseInput S X Y)
    (left : A ⊆ X) (right : B ⊆ Y) : IsFalseInput S A B := by
  intro l hl
  apply Finset.disjoint_left.mpr
  intro p incident present
  exact Finset.disjoint_left.mp (none l (right hl)) incident (left present)

theorem falseIfNoFlag (S : Fin N → Finset (Fin N)) (X Y : Finset (Fin N))
    (bad : ¬ incidenceFun S X Y = true) : IsFalseInput S X Y := by
  intro l hl
  apply Finset.disjoint_left.mpr
  intro p onLine hp
  apply bad
  unfold incidenceFun
  exact decide_eq_true ⟨p,hp,l,hl,onLine⟩

theorem normalForm (S : Fin N → Finset (Fin N))
    (F : Finset (Fin N) → Finset (Fin N) → Prop) (q : Nat)
    (up : ∀ A B X Y, A ⊆ X → B ⊆ Y → F A B → F X Y)
    (acceptIncidence : ∀ X Y, incidenceFun S X Y = true → F X Y)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → ¬ F X Y) :
    ∃ J : Finset (Finset (Fin N) × Finset (Fin N)),
      (∀ j ∈ J, q < j.2.card ∧ IsFalseInput S j.1 j.2) ∧
      (∀ j ∈ J, ∀ k ∈ J, k.1 ⊆ j.1 → k.2 ⊆ j.2 → k = j) ∧
      (∀ X Y, F X Y ↔ incidenceFun S X Y = true ∨
        ∃ j ∈ J, j.1 ⊆ X ∧ j.2 ⊆ Y) := by
  refine ⟨family S F,?_,?_,?_⟩
  · intro j mem
    obtain ⟨independent,h⟩ := (family_mem S F j).mp mem
    refine ⟨?_,independent⟩
    by_contra failed
    exact sound j.1 j.2 (Nat.le_of_not_gt failed) independent h.1
  · intro j mem k inFamily a b
    have jm := ((family_mem S F j).mp mem).2
    have km := ((family_mem S F k).mp inFamily).2
    obtain ⟨sameA,sameB⟩ := jm.2 k.1 k.2 a b km.1
    exact Prod.ext sameA sameB
  · intro X Y
    constructor
    · intro yes
      by_cases edge : incidenceFun S X Y = true
      · exact Or.inl edge
      · obtain ⟨A,B,left,right,minimal⟩ := minimalBelow F X Y yes
        have independent := falseBelow S (falseIfNoFlag S X Y edge) left right
        exact Or.inr ⟨⟨A,B⟩,(family_mem S F ⟨A,B⟩).mpr ⟨independent,minimal⟩,left,right⟩
    · rintro (incident | ⟨j,mem,left,right⟩)
      · exact acceptIncidence X Y incident
      · exact up j.1 j.2 X Y left right ((family_mem S F j).mp mem).2.1

#print axioms normalForm

end PlaneMinimalJunk8851
