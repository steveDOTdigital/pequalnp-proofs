import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

namespace FiveLineCover

theorem unionEstimate {V I : Type*} [DecidableEq V] [DecidableEq I]
    (L : I → Finset V) (five : ∀ i, (L i).card=5)
    (linear : ∀ i j, i≠j → (L i ∩ L j).card≤1) (K : Finset I) :
    5*K.card ≤ (K.biUnion L).card + K.card.choose 2 := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | @insert i K fresh ih =>
    have sub : L i ∩ K.biUnion L ⊆ K.biUnion (fun j => L i ∩ L j) := by
      intro p hp
      obtain ⟨a,b⟩ := Finset.mem_inter.mp hp
      obtain ⟨j,hj,inJ⟩ := Finset.mem_biUnion.mp b
      exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_inter.mpr ⟨a,inJ⟩⟩
    have sumBound : (∑ j ∈ K, (L i ∩ L j).card) ≤ K.card := by
      calc
        _ ≤ ∑ _j ∈ K, 1 := Finset.sum_le_sum fun j hj => linear i j (by rintro rfl; exact fresh hj)
        _ = _ := by simp
    have overlap : (L i ∩ K.biUnion L).card ≤ K.card :=
      (Finset.card_le_card sub).trans ((Finset.card_biUnion_le).trans sumBound)
    have split := Finset.card_union_add_card_inter (L i) (K.biUnion L)
    rw [Finset.card_insert_of_notMem fresh,Finset.biUnion_insert,Nat.choose_succ_succ]
    rw [five] at split
    change 5*(K.card+1) ≤ (L i ∪ K.biUnion L).card + (K.card.choose 1 + K.card.choose 2)
    simp only [Nat.choose_one_right]
    omega

theorem seeds : let S := fun l : Fin 21 => ({l,l+1,l+4,l+14,l+16} : Finset (Fin 21))
    let Z := fun X : Finset (Fin 21) => Finset.univ.filter (fun l : Fin 21 => Disjoint X (S l))
    let W := fun Y : Finset (Fin 21) => Finset.univ \ Y.biUnion S
    ∀ X, X = W (Z X) → X.card ≤ 5 ∨ ∃ T : Finset (Fin 21), T.card ≤ 5 ∧ X = W T := by
  classical
  let S := fun l : Fin 21 => ({l,l+1,l+4,l+14,l+16} : Finset (Fin 21))
  let Z := fun X : Finset (Fin 21) => Finset.univ.filter (fun l : Fin 21 => Disjoint X (S l))
  let W := fun Y : Finset (Fin 21) => Finset.univ \ Y.biUnion S
  have five : ∀ l, (S l).card=5 := by decide
  have linear : ∀ i j, i≠j → (S i ∩ S j).card ≤ 1 := by decide
  change ∀ X, X = W (Z X) → X.card ≤ 5 ∨ ∃ T : Finset (Fin 21), T.card ≤ 5 ∧ X = W T
  intro X closed
  by_cases tiny : X.card ≤ 5
  · exact Or.inl tiny
  right
  by_cases few : (Z X).card ≤ 5
  · exact ⟨Z X,few,closed⟩
  obtain ⟨T,hT,ct⟩ := Finset.exists_subset_card_eq (s:=Z X) (n:=5) (by omega)
  have size := unionEstimate S five linear T
  rw [ct] at size
  have unionSize : 15 ≤ (T.biUnion S).card := by change 25 ≤ (T.biUnion S).card + 10 at size; omega
  have subset : X ⊆ W T := by
    intro p hp
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ p,?_⟩
    rintro h
    obtain ⟨l,hl,pl⟩ := Finset.mem_biUnion.mp h
    exact (Finset.disjoint_left.mp (Finset.mem_filter.mp (hT hl)).2) hp pl
  have room : (W T).card ≤ 6 := by
    dsimp only [W]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  exact ⟨T,le_of_eq ct,Finset.eq_of_subset_of_card_le subset (by omega)⟩

end FiveLineCover
