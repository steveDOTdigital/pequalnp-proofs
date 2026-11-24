import PEqualNP.Defs

namespace QuadrangleFourClauses

open PEqualNP.HeptadCover

/-- Each pair of witnesses forces two different covering sets. -/
theorem packing_bound {n m t k : ℕ} (S : Fin m → Finset (Fin n))
    (R : Finset (Fin n × Fin m)) (Q : Fin t → Finset (Fin n))
    (valid : ∀ i, IsQuadrangle S (Q i))
    (apart : ∀ i j, i ≠ j → ∃ e ∈ R, PairIn (supp S (Q i) ∪ supp S (Q j)) e)
    (cover : HasCover S R k) : t ≤ k := by
  classical
  obtain ⟨F, count, free, covers⟩ := cover
  have member (i : Fin t) : Q i ∈ quadrangles S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (valid i).1⟩, (valid i).2⟩
  have pick (i : Fin t) : ∃ V : ↥F, supp S (Q i) ⊆ V.val := by
    obtain ⟨V,hV,hQ⟩ := covers _ (member i)
    exact ⟨⟨V,hV⟩,hQ⟩
  choose f hf using pick
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    obtain ⟨e,he,hp,hl⟩ := apart i j ne
    have sub : supp S (Q i) ∪ supp S (Q j) ⊆ (f j).val :=
      Finset.union_subset (eq ▸ hf i) (hf j)
    exact free _ (f j).property e he ⟨sub hp, sub hl⟩
  have h : t ≤ F.card := by simpa using Fintype.card_le_of_injective f inj
  exact h.trans count

abbrev V := Fin 13
def points (mask : ℕ) : Finset V := Finset.univ.filter fun p => mask.testBit p.val

theorem certificate {t k : ℕ} (R : Finset (V × V)) (masks : Fin t → ℕ)
    (valid : ∀ i, IsQuadrangle singerLines3 (points (masks i)))
    (apart : ∀ i j, i ≠ j → ∃ e ∈ R, PairIn
      (supp singerLines3 (points (masks i)) ∪ supp singerLines3 (points (masks j))) e) :
    HasCover singerLines3 R k → t ≤ k :=
  packing_bound singerLines3 R (fun i => points (masks i)) valid apart

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000


-- 2-matching orbit of size 468.
theorem matching_1 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1)} k) : 3 ≤ k := by
  apply certificate {(0, 0), (1, 1)} ![2272, 105, 39] _ _ h <;> decide +kernel

-- 2-matching orbit of size 702.
theorem matching_2 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1)} k) : 4 ≤ k := by
  apply certificate {(0, 0), (2, 1)} ![2272, 116, 105, 39] _ _ h <;> decide +kernel

-- 3-matching orbit of size 2808.
theorem matching_3 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2)} k) : 5 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2)} ![4544, 116, 449, 83, 39] _ _ h <;> decide +kernel

-- 3-matching orbit of size 468.
theorem matching_4 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 12)} k) : 5 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 12)} ![2272, 116, 105, 58, 39] _ _ h <;> decide +kernel

-- 3-matching orbit of size 1404.
theorem matching_5 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (3, 2)} k) : 5 ≤ k := by
  apply certificate {(0, 0), (1, 1), (3, 2)} ![4544, 449, 105, 83, 78] _ _ h <;> decide +kernel

-- 3-matching orbit of size 5616.
theorem matching_6 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2)} k) : 6 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2)} ![4544, 2272, 449, 105, 83, 39] _ _ h <;> decide +kernel

-- 3-matching orbit of size 1404.
theorem matching_7 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 5)} k) : 5 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 5)} ![2272, 2196, 2185, 105, 39] _ _ h <;> decide +kernel

-- 3-matching orbit of size 936.
theorem matching_8 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1), (5, 5)} k) : 7 ≤ k := by
  apply certificate {(0, 0), (2, 1), (5, 5)} ![2272, 2196, 116, 2185, 105, 29, 39] _ _ h <;> decide +kernel

-- 3-matching orbit of size 936.
theorem matching_9 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1), (5, 9)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (2, 1), (5, 9)} ![2496, 2272, 340, 116, 201, 105, 71, 39] _ _ h <;> decide +kernel

-- 3-matching orbit of size 468.
theorem matching_10 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1), (8, 5)} k) : 6 ≤ k := by
  apply certificate {(0, 0), (2, 1), (8, 5)} ![2464, 2196, 308, 2185, 297, 29] _ _ h <;> decide +kernel

-- 3-matching orbit of size 936.
theorem matching_11 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1), (8, 7)} k) : 7 ≤ k := by
  apply certificate {(0, 0), (2, 1), (8, 7)} ![6240, 2464, 116, 308, 609, 297, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_12 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (3, 3)} k) : 7 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (3, 3)} ![4544, 420, 897, 105, 387, 39, 78] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_13 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (4, 3)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (4, 3)} ![2464, 464, 116, 897, 387, 83, 39, 29] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_14 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (4, 4)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (4, 4)} ![6464, 464, 116, 449, 1602, 83, 78, 29] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_15 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (4, 8)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (4, 8)} ![5312, 464, 1124, 116, 4289, 195, 83, 39, 29] _ _ h <;> decide +kernel

-- 4-matching orbit of size 1404.
theorem matching_16 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (5, 4)} k) : 6 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (5, 4)} ![4544, 1348, 116, 449, 1602, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_17 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (5, 5)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (5, 5)} ![2272, 5264, 2196, 4737, 105, 83, 29, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_18 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (5, 9)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (5, 9)} ![2272, 464, 340, 449, 105, 83, 71, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_19 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (6, 3)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (6, 3)} ![4544, 2464, 116, 897, 449, 387, 83, 39, 71] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_20 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (6, 5)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (6, 5)} ![4544, 5264, 2196, 116, 4737, 449, 83, 29, 71] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_21 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (6, 6)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (6, 6)} ![4544, 6432, 116, 449, 297, 275, 83, 71] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_22 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (8, 5)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (8, 5)} ![4544, 5264, 2196, 308, 4737, 449, 275, 29] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_23 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (8, 7)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (8, 7)} ![4544, 6240, 308, 4673, 449, 83, 275, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_24 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (8, 8)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (8, 8)} ![4544, 5312, 1124, 308, 4289, 449, 195, 275, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 1404.
theorem matching_25 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (9, 6)} k) : 7 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (9, 6)} ![4544, 116, 833, 297, 275, 594, 533] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_26 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 2), (9, 8)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 2), (9, 8)} ![4544, 1124, 4289, 833, 195, 594, 39, 550] _ _ h <;> decide +kernel

-- 4-matching orbit of size 1404.
theorem matching_27 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 12), (3, 2)} k) : 7 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 12), (3, 2)} ![1232, 116, 232, 449, 58, 83, 29] _ _ h <;> decide +kernel

-- 4-matching orbit of size 1872.
theorem matching_28 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (2, 12), (5, 9)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (1, 1), (2, 12), (5, 9)} ![2272, 2256, 340, 116, 201, 105, 58, 71, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_29 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (3, 2), (6, 3)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (3, 2), (6, 3)} ![4544, 2464, 897, 449, 105, 387, 83, 78] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_30 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (3, 2), (6, 6)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (1, 1), (3, 2), (6, 6)} ![4544, 6432, 449, 297, 105, 275, 83, 58, 78] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_31 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (3, 2), (8, 5)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (3, 2), (8, 5)} ![4544, 5264, 4737, 449, 2185, 297, 275, 270] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_32 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (3, 2), (8, 8)} k) : 10 ≤ k := by
  apply certificate {(0, 0), (1, 1), (3, 2), (8, 8)} ![4544, 4320, 4289, 449, 105, 297, 195, 275, 78, 270] _ _ h <;> decide +kernel

-- 4-matching orbit of size 468.
theorem matching_33 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (3, 2), (9, 6)} k) : 7 ≤ k := by
  apply certificate {(0, 0), (1, 1), (3, 2), (9, 6)} ![4544, 833, 297, 616, 275, 594, 58] _ _ h <;> decide +kernel

-- 4-matching orbit of size 936.
theorem matching_34 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (3, 2), (9, 8)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (3, 2), (9, 8)} ![4544, 4289, 833, 105, 616, 195, 594, 78] _ _ h <;> decide +kernel

-- 4-matching orbit of size 5616.
theorem matching_35 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2), (6, 3)} k) : 10 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2), (6, 3)} ![4544, 2464, 2272, 897, 449, 801, 105, 387, 83, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_36 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2), (6, 6)} k) : 10 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2), (6, 6)} ![4544, 6432, 2272, 5392, 449, 297, 105, 275, 83, 1059] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_37 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2), (7, 6)} k) : 10 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2), (7, 6)} ![4544, 6432, 2272, 5392, 449, 297, 275, 195, 1059, 166] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_38 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2), (7, 7)} k) : 10 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2), (7, 7)} ![4544, 6240, 2272, 4673, 449, 609, 83, 195, 39, 166] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_39 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2), (7, 11)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2), (7, 11)} ![4544, 2272, 1360, 116, 833, 449, 105, 195, 166] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_40 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2), (8, 8)} k) : 11 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2), (8, 8)} ![4544, 4320, 2464, 5312, 4289, 449, 105, 297, 195, 275, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_41 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2), (11, 8)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2), (11, 8)} ![4544, 4320, 2272, 4289, 105, 2337, 195, 39, 2083] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_42 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2), (12, 3)} k) : 11 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2), (12, 3)} ![4544, 2464, 4320, 897, 4289, 801, 4137, 387, 4115, 39, 4131] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_43 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 2), (12, 11)} k) : 10 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 2), (12, 11)} ![4544, 4320, 1360, 116, 833, 4289, 105, 4137, 4115, 4131] _ _ h <;> decide +kernel

-- 4-matching orbit of size 468.
theorem matching_44 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 5), (7, 11)} k) : 7 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 5), (7, 11)} ![2272, 2196, 116, 2185, 105, 29, 166] _ _ h <;> decide +kernel

-- 4-matching orbit of size 936.
theorem matching_45 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (1, 1), (5, 5), (11, 11)} k) : 8 ≤ k := by
  apply certificate {(0, 0), (1, 1), (5, 5), (11, 11)} ![2272, 2196, 116, 2185, 105, 2337, 29, 2083] _ _ h <;> decide +kernel

-- 4-matching orbit of size 2808.
theorem matching_46 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1), (5, 5), (7, 7)} k) : 12 ≤ k := by
  apply certificate {(0, 0), (2, 1), (5, 5), (7, 7)} ![6240, 2272, 6164, 2196, 116, 420, 6657, 2185, 609, 533, 141, 39] _ _ h <;> decide +kernel

-- 4-matching orbit of size 936.
theorem matching_47 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1), (5, 5), (7, 11)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (2, 1), (5, 5), (7, 11)} ![2272, 2196, 116, 420, 2185, 105, 29, 141, 101] _ _ h <;> decide +kernel

-- 4-matching orbit of size 234.
theorem matching_48 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1), (5, 9), (6, 3)} k) : 15 ≤ k := by
  apply certificate {(0, 0), (2, 1), (5, 9), (6, 3)} ![2496, 2464, 2272, 2436, 340, 420, 116, 2433, 201, 801, 105, 135, 71, 39, 101] _ _ h <;> decide +kernel

-- 4-matching orbit of size 936.
theorem matching_49 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1), (8, 5), (12, 3)} k) : 9 ≤ k := by
  apply certificate {(0, 0), (2, 1), (8, 5), (12, 3)} ![2464, 4512, 3204, 4244, 420, 2689, 4233, 801, 1157] _ _ h <;> decide +kernel

-- 4-matching orbit of size 117.
theorem matching_50 {k : ℕ} (h : HasCover singerLines3 {(0, 0), (2, 1), (8, 5), (12, 11)} k) : 6 ≤ k := by
  apply certificate {(0, 0), (2, 1), (8, 5), (12, 11)} ![4512, 4244, 308, 4233, 297, 29] _ _ h <;> decide +kernel

namespace Control
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
attribute [local instance] gateOpDecEq
def circuit : Circuit := ⟨[
  ⟨.or,[0,4]⟩,
  ⟨.or,[0,10]⟩,
  ⟨.or,[0,2]⟩,
  ⟨.and,[26,27]⟩,
  ⟨.and,[29,28]⟩,
  ⟨.or,[30,1]⟩,
  ⟨.or,[31,3]⟩,
  ⟨.or,[32,9]⟩,
  ⟨.and,[13,33]⟩,
  ⟨.or,[1,2]⟩,
  ⟨.or,[35,4]⟩,
  ⟨.or,[36,10]⟩,
  ⟨.and,[14,37]⟩,
  ⟨.or,[2,3]⟩,
  ⟨.or,[39,5]⟩,
  ⟨.or,[40,11]⟩,
  ⟨.and,[15,41]⟩,
  ⟨.or,[3,4]⟩,
  ⟨.or,[43,6]⟩,
  ⟨.or,[44,12]⟩,
  ⟨.and,[16,45]⟩,
  ⟨.or,[26,5]⟩,
  ⟨.or,[47,7]⟩,
  ⟨.and,[17,48]⟩,
  ⟨.or,[1,5]⟩,
  ⟨.or,[50,6]⟩,
  ⟨.or,[51,8]⟩,
  ⟨.and,[18,52]⟩,
  ⟨.or,[2,6]⟩,
  ⟨.or,[54,7]⟩,
  ⟨.or,[55,9]⟩,
  ⟨.and,[19,56]⟩,
  ⟨.or,[3,7]⟩,
  ⟨.or,[58,8]⟩,
  ⟨.or,[59,10]⟩,
  ⟨.and,[20,60]⟩,
  ⟨.or,[4,8]⟩,
  ⟨.or,[62,9]⟩,
  ⟨.or,[63,11]⟩,
  ⟨.and,[21,64]⟩,
  ⟨.or,[5,9]⟩,
  ⟨.or,[66,10]⟩,
  ⟨.or,[67,12]⟩,
  ⟨.and,[22,68]⟩,
  ⟨.or,[27,6]⟩,
  ⟨.or,[70,11]⟩,
  ⟨.and,[23,71]⟩,
  ⟨.or,[1,7]⟩,
  ⟨.or,[73,11]⟩,
  ⟨.or,[74,12]⟩,
  ⟨.and,[24,75]⟩,
  ⟨.or,[28,8]⟩,
  ⟨.or,[77,12]⟩,
  ⟨.and,[25,78]⟩,
  ⟨.or,[34,38]⟩,
  ⟨.or,[80,42]⟩,
  ⟨.or,[81,46]⟩,
  ⟨.or,[82,49]⟩,
  ⟨.or,[83,53]⟩,
  ⟨.or,[84,57]⟩,
  ⟨.or,[85,61]⟩,
  ⟨.or,[86,65]⟩,
  ⟨.or,[87,69]⟩,
  ⟨.or,[88,72]⟩,
  ⟨.or,[89,76]⟩,
  ⟨.or,[90,79]⟩],91⟩

def negative (Q : Finset V) : List Bool :=
  (List.ofFn fun p : V => decide (p ∈ Q)) ++
    List.ofFn fun l : V => decide (l ∈ missLines singerLines3 Q)
def positive (p l : V) := (List.ofFn fun x : V => decide (x = p)) ++
    List.ofFn fun x : V => decide (x = l)

theorem legal : circuit.size = 66 ∧ IsAO2 26 circuit ∧
    ∀ g ∈ circuit.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 := by decide +kernel

theorem nested : 2 ≤ andPairs 26 circuit := by
  let pairs : Finset (ℕ × ℕ) := {(3,4),(4,8)}
  have h : pairs ⊆ ((Finset.range circuit.gates.length ×ˢ Finset.range circuit.gates.length).filter
    fun p => (NestedCover.gateAt circuit p.1).op = GateOp.and ∧
      (NestedCover.gateAt circuit p.2).op = GateOp.and ∧ InCone 26 circuit p.1 p.2) := by
    intro z hz
    simp only [pairs, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> apply Finset.mem_filter.mpr <;> constructor <;> decide +kernel
  exact (show 2 ≤ pairs.card by decide +kernel).trans (Finset.card_le_card h)


def columns : List ℕ := [21267647932558653966456409364858142735,383123885216472193321938824228924510030888933844320496,421249166673845622906455986947968221627240078468018624746655584000,28269552615204982991039747802374303684400097056640787270173276652609531904,14821359152876935205038519184338652964899642757295722577836653506891434993582080,60693585084871743398195594648116858791127980526833738047510242927419626536469266432,15481102310305559856035695098914896367900703621935189166232202587515154025043661422592,47063822414511786737851390051690047366924133726592046081792544186667326449236825866240,85222744390852597868332330120911423297863806697644260807887910317817303611028635910144,55856118534855912622012973856616675977480791384275189457075237126550773389875589677056,95942071248034570143833874949499104803975645391565036468943321943781348322280617279488,105023084989999623479767934664793526427953900324363011593570096315728187448237815234560,92673584114754297274178194621562596166319030007956434925751907891303784538361917603840,68474690567574807165520736185166229565077946407558820603830388837240340106319323205649,28388737254956218245519693818862016033640982303584322000559165678912889025746142560544,19305278582757665988638440884101056423068351293818335910142748522475092214596496269824,31110685055065111915859403911234043695009815985307817475773029022129921415367138361344,77221088466000323751352707261372556282497583955816314117047290692588472591312943841282,31082713160093451919918316402287643060519983522550242816725580014368992202112177799232,62210946972833689044774085837178343915633155083543786715821341436685676617645217022976,7771031284151652478651662408361361182302680379876990073495280871440635575570469519360,242907718465329148554778932356980399183885326393317309766224604338067853454235664384,60708420974602492270460625915525246815462760049024019468969714839678123410764857344,15543723139207503448521780344835106209904116458518452374415374072374969112555482513412,485667310211535361979484621869134742313916614754224648627338233592439359043943792768,31094249375048090654975134876575633319374233006239140014675250968882439555066441500680]
def quadMasks : List ℕ := [39,71,135,2055,83,275,2067,4115,1059,2083,4131,195,4163,387,1155,1283,2307,5123,29,77,141,1037,85,533,2069,101,549,1061,1157,2181,1541,2565,281,1049,2073,105,297,1065,4137,201,329,2185,4233,2313,5129,6153,337,593,1297,1553,4625,5137,6161,609,4193,801,1313,2337,2593,6177,449,4289,833,4673,897,2433,1665,2689,4737,5249,1793,6657,78,142,270,4110,166,550,4134,2118,4166,390,774,2310,2566,4614,58,154,282,2074,170,1066,4138,202,1098,2122,2314,4362,3082,5130,562,2098,4146,210,594,2130,402,658,4370,4626,674,1186,2594,3106,1218,1602,2626,4674,5186,898,1666,1794,4866,3330,5378,3586,156,284,540,332,1100,4236,780,1548,4620,5132,116,308,564,4148,340,2132,404,2196,4244,4628,6164,1124,4196,420,1188,4260,804,1316,1348,2372,5188,6212,2436,3204,5252,1796,3332,3588,6660,7172,312,568,1080,664,2200,1560,3096,232,616,1128,680,4264,808,4392,2248,840,2376,1608,2632,2696,4744,4872,6408,3592,6664,7176,624,1136,2160,1328,4400,3120,6192,464,1232,2256,1360,1616,4496,1680,4752,3216,5264,5392,7184,1248,2272,4320,2656,6240,928,2464,4512,2720,3232,3360,6432,2496,4544,5312,1856,4928,5440,6464,6720,4992,3712,7424]
def flagIndex (p l : V) := (List.range 169 |>.filter fun z =>
  decide ((⟨z / 13 % 13, Nat.mod_lt _ (by decide)⟩ : V) ∈
    singerLines3 (⟨z%13, Nat.mod_lt _ (by decide)⟩ : V))).idxOf (13*p.val+l.val)
def quadIndex (Q : Finset V) := 52 + quadMasks.idxOf (Q.sum fun p => 2^p.val)
def bitRow (i : ℕ) := columns.map fun v => v.testBit i

def wordStep (ws : List ℕ) (g : Gate) : List ℕ :=
  let a := ws.getD (g.inputs.getD 0 0) 0
  let b := ws.getD (g.inputs.getD 1 0) 0
  ws ++ [if g.op = .and then a &&& b else a ||| b]

theorem simulate (i : ℕ) (gs : List Gate) (ws : List ℕ)
    (ok : ∀ g ∈ gs, g.inputs.length=2 ∧ (g.op=.and ∨ g.op=.or)) :
    (gs.foldl wordStep ws).map (fun v => v.testBit i) =
      gs.foldl (fun t g => t ++ [g.op.eval (g.inputs.map fun j => t.getD j false)])
        (ws.map fun v => v.testBit i) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih _ (fun q h => ok q (List.mem_cons_of_mem _ h))]
    obtain ⟨len,op⟩ := ok g (by simp)
    obtain ⟨a,b,ab⟩ := List.length_eq_two.mp len
    have read (j : ℕ) : (ws.map fun v => v.testBit i).getD j false = (ws.getD j 0).testBit i := by
      rw [← Nat.zero_testBit i, List.getD_map]
    simp only [ab,List.map_cons,List.map_nil,read]
    rcases op with op|op <;> simp [wordStep,op,ab,GateOp.eval]

def words := circuit.gates.foldl wordStep columns

theorem tape (i j : ℕ) : (circuit.wires (bitRow i)).getD j false = (words.getD j 0).testBit i := by
  have ok : ∀ g ∈ circuit.gates, g.inputs.length=2 ∧ (g.op=.and ∨ g.op=.or) := by decide +kernel
  have tab := simulate i circuit.gates columns ok
  change words.map (fun v => v.testBit i) = circuit.wires (bitRow i) at tab
  rw [← tab]
  rw [← Nat.zero_testBit i, List.getD_map]

theorem output_word : words.getD circuit.output 0 = 4503599627370495 := by decide +kernel

theorem positives : ∀ p l : V, p ∈ singerLines3 l → circuit.eval (positive p l) = true := by
  have enc : ∀ p l : V, p ∈ singerLines3 l → bitRow (flagIndex p l) = positive p l ∧
      (4503599627370495 : ℕ).testBit (flagIndex p l) = true := by decide +kernel
  intro p l h
  obtain ⟨eq,bit⟩ := enc p l h
  rw [←eq, Circuit.eval,tape,output_word,bit]

theorem negatives : ∀ Q ∈ quadrangles singerLines3, circuit.eval (negative Q) = false := by
  let wrong := (quadrangles singerLines3).filter fun Q =>
    ¬ (bitRow (quadIndex Q) = negative Q ∧ (4503599627370495 : ℕ).testBit (quadIndex Q) = false)
  have none : wrong = ∅ := by decide +kernel
  intro Q h
  have good : bitRow (quadIndex Q) = negative Q ∧
      (4503599627370495 : ℕ).testBit (quadIndex Q) = false := by
    by_contra bad
    have hx : Q ∈ wrong := Finset.mem_filter.mpr ⟨h,bad⟩
    rw [none] at hx
    exact Finset.notMem_empty Q hx
  rw [←good.1, Circuit.eval,tape,output_word,good.2]

def witness (g w : ℕ) : ℕ :=
  match g, w with
  | 3, 26 => 58
  | 3, 27 => 1066
  | 4, 29 => 1080
  | 4, 28 => 78
  | 8, 13 => 116
  | 8, 33 => 39
  | 12, 14 => 105
  | 12, 37 => 39
  | 16, 15 => 83
  | 16, 41 => 39
  | 20, 16 => 39
  | 20, 45 => 71
  | 23, 17 => 78
  | 23, 48 => 39
  | 27, 18 => 29
  | 27, 52 => 39
  | 31, 19 => 275
  | 31, 56 => 39
  | 35, 20 => 39
  | 35, 60 => 135
  | 39, 21 => 39
  | 39, 64 => 2055
  | 43, 22 => 71
  | 43, 68 => 39
  | 46, 23 => 142
  | 46, 71 => 39
  | 50, 24 => 29
  | 50, 75 => 39
  | 53, 25 => 58
  | 53, 78 => 39
  | _, _ => 0

theorem strict : ∀ j < circuit.size, (NestedCover.gateAt circuit j).op = .and →
    ∀ w ∈ (NestedCover.gateAt circuit j).inputs, ∃ Q ∈ quadrangles singerLines3,
    (circuit.wires (negative Q)).getD (26+j) false ≠
      (circuit.wires (negative Q)).getD w false := by
  have cert : ∀ j : Fin 66, (NestedCover.gateAt circuit j.val).op = .and →
      ∀ w ∈ (NestedCover.gateAt circuit j.val).inputs,
        let Q := points (witness j.val w)
        IsQuadrangle singerLines3 Q ∧ (circuit.wires (negative Q)).getD (26+j.val) false ≠
          (circuit.wires (negative Q)).getD w false := by decide +kernel
  intro j hj h w hw
  obtain ⟨hq, hd⟩ := cert ⟨j,hj⟩ h w hw
  exact ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _,hq.1⟩,hq.2⟩,hd⟩
end Control

end QuadrangleFourClauses
