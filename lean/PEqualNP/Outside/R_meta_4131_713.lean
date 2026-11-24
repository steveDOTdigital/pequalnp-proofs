import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Bits zero to three are an independent set whose four vertices have just two neighbors each.
-- The eleven-bit fields list the twenty-two independent sets of size four.
theorem PEqualNP.Outside.R_meta_4131_713
    (classify : let G := edgeGraph 11 (List.ofFn fun i : Fin 16 => let w := (182734661465985816910654985662253763081 : ℕ) >>> (8*i.val)
      (w / 16 % 16,w % 16))
    ∀ I : Finset (Fin 11), I.card=4 → (∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v) →
      ∃ i : Fin 22, ∀ v : Fin 11, ((5337049209409285386193401725542463193349738924283176925588630423176538127 : ℕ) >>> (11*i.val)).testBit v.val = true ↔ v ∈ I)
    (density : let G := edgeGraph 11 (List.ofFn fun i : Fin 16 => let w := (182734661465985816910654985662253763081 : ℕ) >>> (8*i.val)
      (w / 16 % 16,w % 16))
    ∀ S : Finset (Fin 11), S.card ≤ 4+([1,2,3,5,8,12,16] : List ℕ).countP (fun k => decide (k ≤ (S.sym2 ∩ G.edgeFinset).card)))
    (charge : let G := edgeGraph 11 (List.ofFn fun i : Fin 16 => let w := (182734661465985816910654985662253763081 : ℕ) >>> (8*i.val)
      (w / 16 % 16,w % 16))
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let U := Ustar G C
      let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      U.card ≤ B → B < 2*U.card → B-U.card < ([1,2,3,5,8,12,16] : List ℕ).countP (fun k => decide (k ≤ U.card)) →
      let A : Finset (Fin 11) := {0,1,2,3}
      let H := G.deleteEdges (↑U)
      ∀ K : Finset (Fin 11), Disjoint K A → (∀ u ∈ K, ∀ v ∈ K, ¬H.Adj u v) →
        let N := A.filter (fun v => ∃ w ∈ K, H.Adj w v)
        (∃ i : Fin 22, ∀ v : Fin 11, ((5337049209409285386193401725542463193349738924283176925588630423176538127 : ℕ) >>> (11*i.val)).testBit v.val = true → v ∈ K ∪ (A \ N)) →
        K.card ≤ B-U.card+N.card) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) x1; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x2 x3 →       PEqualNP.TopForm.TopForm x2 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → ∀ (x12 x13 : Finset (Fin (11 : ℕ))), x12.card = (7 : ℕ) → x2.IsVertexCover ↑x12 → x13 ⊆ x12 → (x2.deleteEdges ↑x8).IsVertexCover ↑(x12 \ x13) → x13.card ≤ x9 - x8.card := by
  dsimp only
  intro C short least top junked lo hi T X seven cover sub residual
  classical
  let G := edgeGraph 11 (List.ofFn fun i : Fin 16 => let w := (182734661465985816910654985662253763081 : ℕ) >>> (8*i.val)
      (w / 16 % 16,w % 16))
  let U := Ustar G C
  let H := G.deleteEdges (↑U)
  let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  let A : Finset (Fin 11) := {0,1,2,3}
  let S := Finset.univ \ (T \ X)
  let I := Finset.univ \ T
  let K := S \ A
  let N := A.filter (fun v => ∃ w ∈ K, H.Adj w v)
  change X.card ≤ B-U.card
  have dis (u) (hu : u ∈ S) (v) (hv : v ∈ S) : ¬ H.Adj u v := by
    intro h
    rcases residual h with h' | h'
    · exact (Finset.mem_sdiff.mp hu).2 h'
    · exact (Finset.mem_sdiff.mp hv).2 h'
  have safe (u) (hu : u ∈ I) (v) (hv : v ∈ I) : ¬ G.Adj u v := by
    intro h
    rcases cover h with h' | h'
    · exact (Finset.mem_sdiff.mp hu).2 h'
    · exact (Finset.mem_sdiff.mp hv).2 h'
  have iSize : I.card = 4 := by
    rw [show I = Finset.univ \ T from rfl,Finset.card_sdiff_of_subset (Finset.subset_univ _),seven]
    rfl
  obtain ⟨i,word⟩ := classify I iSize safe
  have part : Disjoint K A := Finset.disjoint_left.mpr (fun _ h => (Finset.mem_sdiff.mp h).2)
  have kS : K ⊆ S := Finset.sdiff_subset
  have neigh : N ⊆ A \ (S ∩ A) := by
    intro v hv
    obtain ⟨a,w,hw,adj⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_sdiff.mpr ⟨a,fun both => dis w (kS hw) v (Finset.mem_inter.mp both).1 adj⟩
  have included : I ⊆ K ∪ (A \ N) := by
    intro v hv
    have hs : v ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp h).1⟩
    by_cases ha : v ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ha,fun hn => (Finset.mem_sdiff.mp (neigh hn)).2 (Finset.mem_inter.mpr ⟨hs,ha⟩)⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs,ha⟩)
  have na := Finset.card_le_card neigh
  have nsplit := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_right : S∩A ⊆ A)
  have ksplit := Finset.card_sdiff_add_card_inter S A
  have ssplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (T \ X))
  have tsplit := Finset.card_sdiff_add_card_eq_card sub
  have ac : A.card=4 := by decide
  have total : (Finset.univ : Finset (Fin 11)).card=11 := by simp
  change K.card + (S∩A).card = S.card at ksplit
  change S.card + (T\X).card = _ at ssplit
  let thresholds : List ℕ := [1,2,3,5,8,12,16]
  let rank := fun m : ℕ => thresholds.countP (fun k => decide (k ≤ m))
  by_cases small : B-U.card < rank U.card
  · have bound : K.card ≤ B-U.card+N.card :=
      charge C short least top junked lo hi small K part (fun u hu v hv => dis u (kS hu) v (kS hv))
        ⟨i,fun v h => included ((word v).mp h)⟩
    omega
  · have internal : S.sym2 ∩ G.edgeFinset ⊆ U := by
      intro e
      induction e using Sym2.ind with
      | _ u v =>
        intro h
        obtain ⟨both,edge⟩ := Finset.mem_inter.mp h
        have pts := Finset.mem_sym2_iff.mp both
        have hu : u ∈ S := pts u (by simp)
        have hv : v ∈ S := pts v (by simp)
        have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp edge
        by_contra outside
        exact dis u hu v hv (SimpleGraph.deleteEdges_adj.mpr ⟨adj,outside⟩)
    have inc : rank (S.sym2 ∩ G.edgeFinset).card ≤ rank U.card := by
      apply List.countP_mono_left
      intro k _ small
      exact decide_eq_true ((of_decide_eq_true small).trans (Finset.card_le_card internal))
    have maxSize : S.card ≤ 4+rank (S.sym2 ∩ G.edgeFinset).card := density S
    omega
