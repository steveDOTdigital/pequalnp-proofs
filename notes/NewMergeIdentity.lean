import PEqualNP.Defs.NewLowMerge
import PEqualNP.MetaComplexity.Helpers.LowMergeMain

namespace NewMergeIdentity

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge PEqualNP.MetaComplexity.LowMergeProof

variable {P L : ℕ} (inc : Fin P → Fin L → Bool) (C : Circuit) (w : Fin L)

theorem labels (t : ℕ) : classLabel P L inc C t w = lab inc C w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold classLabel at ih ⊢
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih]
    rfl

theorem new_iff (t : ℕ) : IsNewLowMerge P L inc C t w ↔
    IsLow P L inc C t w ∧ 2 ≤ (labs inc C w t).card := by
  simp only [IsNewLowMerge, classesMet, labels, labs]

-- Identify the entire next label set, including the empty-alive-set case.
theorem step_set (t : ℕ) (h : IsLow P L inc C t w) :
    lineLabs inc C w (t+1) =
      (lineLabs inc C w t \ labs inc C w t) ∪
      (if (labs inc C w t).Nonempty then {(labs inc C w t).sup id} else ∅) := by
  let S := Finset.univ.filter (fun p : Fin P => inc p w = true)
  let A := aliveSet P L C t w
  let T := labs inc C w t
  let X := lineLabs inc C w t
  have sub : A ⊆ S := alive_sub_line inc C t w h
  ext v
  constructor
  · intro hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    by_cases hit : lab inc C w t p ∈ T
    · have hn : T.Nonempty := ⟨_,hit⟩
      apply Finset.mem_union_right
      change _ ∈ (if T.Nonempty then {T.sup id} else ∅)
      rw [ite_eq_left hn]
      exact Finset.mem_singleton.mpr (ite_eq_left ⟨h,hit⟩)
    · apply Finset.mem_union_left
      have eq : lab inc C w (t+1) p = lab inc C w t p := ite_eq_right (fun a => hit a.2)
      rw [eq]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hp,hit⟩
  · intro hv
    rcases Finset.mem_union.mp hv with left | right
    · obtain ⟨hx,ht⟩ := Finset.mem_sdiff.mp left
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨p,hp,ite_eq_right (fun a => ht a.2)⟩
    · by_cases hn : T.Nonempty
      · change v ∈ (if T.Nonempty then {T.sup id} else ∅) at right
        rw [ite_eq_left hn, Finset.mem_singleton] at right
        obtain ⟨a,ha⟩ := hn
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_image.mpr ⟨p,sub hp,(ite_eq_left ⟨h,ha⟩).trans right.symm⟩
      · change v ∈ (if T.Nonempty then {T.sup id} else ∅) at right
        simp [hn] at right

theorem step_count (hC : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (t : ℕ) : (lineLabs inc C w (t+1)).card + (if IsNewLowMerge P L inc C t w then 1 else 0)
      = (lineLabs inc C w t).card := by
  by_cases h : IsLow P L inc C t w
  · rw [step_set inc C w t h]
    let T := labs inc C w t
    let X := lineLabs inc C w t
    have sub : T ⊆ X := Finset.image_subset_image (alive_sub_line inc C t w h)
    have partition := Finset.card_sdiff_add_card_eq_card sub
    have bound : T.card ≤ 2 := by
      change (labs inc C w t).card ≤ 2
      rcases labs_bound inc C w hC hf t h with hm | ⟨_,hm⟩ <;> omega
    change ((X \ T) ∪ (if T.Nonempty then {T.sup id} else ∅)).card + _ = X.card
    by_cases hn : T.Nonempty
    · obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup T hn id
      have outside : T.sup id ∉ X \ T := fun hh => (Finset.mem_sdiff.mp hh).2 (he ▸ ha)
      rw [ite_eq_left hn, Finset.union_singleton, Finset.card_insert_of_notMem outside]
      have pos := Finset.card_pos.mpr hn
      by_cases hnw : IsNewLowMerge P L inc C t w
      · have hh : 2 ≤ T.card := ((new_iff inc C w t).mp hnw).2
        simp [hnw]
        omega
      · have hh : ¬ 2 ≤ T.card := fun ht => hnw ((new_iff inc C w t).mpr ⟨h,ht⟩)
        simp [hnw]
        omega
    · rw [ite_eq_right hn, Finset.union_empty]
      have z := Finset.not_nonempty_iff_eq_empty.mp hn
      have hc : T.card = 0 := by rw [z]; rfl
      have neg : ¬IsNewLowMerge P L inc C t w := by
        intro yes
        have h2 : 2 ≤ T.card := ((new_iff inc C w t).mp yes).2
        omega
      simp [neg]
      omega
  · have he : lineLabs inc C w (t+1) = lineLabs inc C w t := by
      unfold lineLabs
      rw [lab_succ_of_not_low inc C w t h]
    simp [he, new_iff, h]

theorem prefix_identity (hC : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (t : ℕ) : (lineLabs inc C w t).card +
      ((Finset.range t).filter (fun g => IsNewLowMerge P L inc C g w)).card =
      (Finset.univ.filter (fun p : Fin P => inc p w = true)).card := by
  induction t with
  | zero => simp [lineLabs,lab,Finset.card_image_of_injective _ Fin.val_injective]
  | succ t ih =>
    have step := step_count inc C w hC hf t
    rw [Finset.range_add_one,Finset.filter_insert]
    split_ifs at * with hm
    · rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · omega

theorem line_identity (hC : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hout : ∀ pts, V C w C.output pts = lineSum P L inc w pts) :
    ((Finset.range (P+L+C.gates.length)).filter (fun g => IsNewLowMerge P L inc C g w)).card =
      (Finset.univ.filter (fun p : Fin P => inc p w = true)).card - 1 := by
  let S := Finset.univ.filter (fun p : Fin P => inc p w = true)
  let limit := P+L+C.gates.length
  have total := prefix_identity inc C w hC hf limit
  change (lineLabs inc C w limit).card + _ = S.card at total
  change ((Finset.range limit).filter (fun g => IsNewLowMerge P L inc C g w)).card = S.card - 1
  rcases S.eq_empty_or_nonempty with empty|⟨p,hp⟩
  · have z : S.card = 0 := by rw [empty]; rfl
    omega
  have onLine : inc p w = true := (Finset.mem_filter.mp hp).2
  have low : IsLow P L inc C C.output w := fun pts h => (hout pts) ▸ h
  have valid : C.output < limit := by
    by_contra! far
    have he := hout (ind p)
    rw [V_big C w _ _ far, lineSum_ind, onLine] at he
    exact Bool.false_ne_true he
  have sub : S ⊆ aliveSet P L C C.output w := by
    intro x hx
    rw [alive_mem,hout,lineSum_ind]
    exact (Finset.mem_filter.mp hx).2
  have one := card_image_le_one inc C w limit S _ sub (const_later inc C w _ _ valid low)
  have pos : 0 < (lineLabs inc C w limit).card :=
    Finset.card_pos.mpr ⟨_,Finset.mem_image_of_mem _ hp⟩
  change (lineLabs inc C w limit).card ≤ 1 at one
  omega

-- Count the very same pairs in gate order. A line of degree zero contributes zero.
theorem summed_identity (hC : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hout : ∀ v : Fin L, ∀ pts, V C v C.output pts = lineSum P L inc v pts) :
    (∑ g ∈ Finset.range (P+L+C.gates.length),
      (Finset.univ.filter (fun v : Fin L => IsNewLowMerge P L inc C g v)).card) =
    ∑ v : Fin L, ((Finset.univ.filter (fun p : Fin P => inc p v = true)).card - 1) := by
  simp_rw [← line_identity inc C _ hC hf (hout _)]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem new_is_low_merge (hC : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (g : ℕ) (h : IsNewLowMerge P L inc C g w) : IsLowMerge P L inc C g w := by
  obtain ⟨isLow,atLeastTwo⟩ := (new_iff inc C w g).mp h
  rcases labs_bound inc C w hC hf g isLow with one | both
  · omega
  · exact both.1

-- The profile of a wire is its set of live points on a single-line input.
-- In a four-cycle-free incidence graph, different lines newly merged by the
-- same gate require different profiles, even if that gate reads line inputs.
def mergedLines (g : ℕ) : Finset (Fin L) :=
  Finset.univ.filter (fun v : Fin L => IsNewLowMerge P L inc C g v)

def profiles (g : ℕ) : Finset (Finset (Fin P)) :=
  Finset.univ.image (fun v : Fin L => aliveSet P L C g v)

def NoSquare (inc : Fin P → Fin L → Bool) : Prop :=
  ∀ p q u v, p ≠ q → u ≠ v → inc p u = true → inc p v = true →
    inc q u = true → inc q v = true → False

theorem profile_bound (sq : NoSquare inc) (g : ℕ) :
    (mergedLines inc C g).card ≤ (profiles (P:=P) (L:=L) C g).card := by
  let f := fun v : Fin L => aliveSet P L C g v
  have inject : Set.InjOn f (mergedLines inc C g : Set (Fin L)) := by
    intro u hu v hv equal
    have nu := (Finset.mem_filter.mp hu).2
    have nv := (Finset.mem_filter.mp hv).2
    have pair : 1 < (f u).card := by
      have h := ((new_iff inc C u g).mp nu).2
      exact h.trans (Finset.card_image_le (f:=lab inc C u g))
    obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp pair
    have U := alive_sub_line inc C g u nu.1
    have V := alive_sub_line inc C g v nv.1
    have hpv : p ∈ f v := equal ▸ hp
    have hqv : q ∈ f v := equal ▸ hq
    by_contra uv
    exact sq p q u v ne uv (Finset.mem_filter.mp (U hp)).2
      (Finset.mem_filter.mp (V hpv)).2 (Finset.mem_filter.mp (U hq)).2
      (Finset.mem_filter.mp (V hqv)).2
  calc
    _ = ((mergedLines inc C g).image f).card := (Finset.card_image_of_injOn inject).symm
    _ ≤ _ := Finset.card_le_card (Finset.image_subset_image (Finset.subset_univ _))

-- The lines inside T may produce different profiles. All lines outside T give
-- a common profile. This applies in particular if g reads only the lines in T.
theorem support_bound (sq : NoSquare inc) (g : ℕ) (T : Finset (Fin L))
    (outside : ∀ u ∉ T, ∀ v ∉ T, aliveSet P L C g u = aliveSet P L C g v) :
    (mergedLines inc C g).card ≤ T.card+1 := by
  let f := fun v : Fin L => aliveSet P L C g v
  let U := Finset.univ \ T
  have images : (profiles (P:=P) (L:=L) C g) = T.image f ∪ U.image f := by
    unfold profiles
    rw [← Finset.image_union]
    congr 1
    ext v
    simp [U]
  have one : (U.image f).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    exact outside u (Finset.mem_sdiff.mp hu).2 v (Finset.mem_sdiff.mp hv).2
  have cap := profile_bound inc C sq g
  rw [images] at cap
  exact cap.trans ((Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le one))

-- Charge only actual gates; input wires contribute no new merges. A different
-- exceptional set is allowed at every gate in the same circuit.
theorem summed_support_bound (sq : NoSquare inc) (hC : IsMonotoneCircuit C)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hout : ∀ v : Fin L, ∀ pts, V C v C.output pts = lineSum P L inc v pts)
    (T : ℕ → Finset (Fin L))
    (outside : ∀ g < C.gates.length, ∀ u ∉ T g, ∀ v ∉ T g,
      aliveSet P L C (P+L+g) u = aliveSet P L C (P+L+g) v) :
    (∑ v : Fin L, ((Finset.univ.filter (fun p : Fin P => inc p v = true)).card-1)) ≤
      ∑ g ∈ Finset.range C.gates.length, ((T g).card+1) := by
  rw [← summed_identity inc C hC hf hout]
  change (∑ g ∈ Finset.range (P+L+C.gates.length), (mergedLines inc C g).card) ≤ _
  rw [Finset.sum_range_add]
  have raw : (∑ g ∈ Finset.range (P+L), (mergedLines inc C g).card) = 0 := by
    apply Finset.sum_eq_zero
    intro g hg
    have empty : mergedLines inc C g = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro v hv
      have low := new_is_low_merge inc C v hC hf g (Finset.mem_filter.mp hv).2
      exact (Nat.not_le_of_gt (Finset.mem_range.mp hg)) low.1
    simp [empty]
  rw [raw,zero_add]
  exact Finset.sum_le_sum (fun g hg => support_bound inc C sq _ (T g)
    (outside g (Finset.mem_range.mp hg)))

-- The eight-cycle, with points first. Both circuits have the optimal 11 gates.
-- Red and blue point stars meet only at the last OR of the first circuit.
def octInc (p v : Fin 4) : Bool := decide (p=v ∨ p=v+1)

def pointStars : Circuit :=
  ⟨[⟨.or,[7,4]⟩,⟨.and,[0,8]⟩,⟨.or,[4,5]⟩,⟨.and,[1,10]⟩,
    ⟨.or,[5,6]⟩,⟨.and,[2,12]⟩,⟨.or,[6,7]⟩,⟨.and,[3,14]⟩,
    ⟨.or,[9,13]⟩,⟨.or,[11,15]⟩,⟨.or,[16,17]⟩],18⟩

def lineStars : Circuit :=
  ⟨[⟨.or,[0,1]⟩,⟨.and,[4,8]⟩,⟨.or,[1,2]⟩,⟨.and,[5,10]⟩,
    ⟨.or,[2,3]⟩,⟨.and,[6,12]⟩,⟨.or,[3,0]⟩,⟨.and,[7,14]⟩,
    ⟨.or,[9,13]⟩,⟨.or,[11,15]⟩,⟨.or,[16,17]⟩],18⟩

theorem octagon_comp (C : Circuit) (h : C=pointStars ∨ C=lineStars) :
    ∀ x y : Fin 4 → Bool, C.eval (List.ofFn x ++ List.ofFn y) =
      decide (∃ p v : Fin 4, octInc p v = true ∧ x p = true ∧ y v = true) := by
  rcases h with rfl|rfl <;> decide +kernel

theorem octagon_merges (C : Circuit) (index : Fin 4 → ℕ)
    (shape : (C=pointStars ∧ index=(fun _ => 18)) ∨
      (C=lineStars ∧ index=(fun w => 8+2*w.val))) (w : Fin 4) :
    (Finset.range 19).filter (fun g => IsNewLowMerge 4 4 octInc C g w) = {index w} := by
  have cert : ∀ v : Fin 4, ∀ j : Fin 19, j.val < index v →
      (aliveSet 4 4 C j.val v).card ≤ 1 ∨
      V C v j.val (fun _ : Fin 4 => false) = true ∨
      ∃ p : Fin 4, octInc p v = false ∧ V C v j.val (ind p) = true := by
    rcases shape with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide +kernel
  have hC : IsMonotoneCircuit C := by
    rcases shape with ⟨rfl,_⟩|⟨rfl,_⟩ <;> decide +kernel
  have hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := by
    rcases shape with ⟨rfl,_⟩|⟨rfl,_⟩ <;> decide +kernel
  have hout : ∀ v : Fin 4, ∀ pts, V C v C.output pts = lineSum 4 4 octInc v pts := by
    rcases shape with ⟨rfl,_⟩|⟨rfl,_⟩ <;> decide +kernel
  have size : 4+4+C.gates.length = 19 := by
    rcases shape with ⟨rfl,_⟩|⟨rfl,_⟩ <;> rfl
  have degree : ∀ v : Fin 4, (Finset.univ.filter (fun p : Fin 4 => octInc p v = true)).card = 2 := by
    decide +kernel
  have count := line_identity octInc C w hC hf (hout w)
  rw [size,degree] at count
  obtain ⟨g,hg⟩ := Finset.card_eq_one.mp count
  have hm : g ∈ (Finset.range 19).filter (fun i => IsNewLowMerge 4 4 octInc C i w) := by rw [hg]; simp
  obtain ⟨hr,hn⟩ := Finset.mem_filter.mp hm
  have eq : g=index w := by
    by_contra ng
    by_cases early : g < index w
    · rcases cert w ⟨g,Finset.mem_range.mp hr⟩ early with atMost | zero | ⟨p,off,atP⟩
      · have two := ((new_iff octInc C w g).mp hn).2
        have cap : (labs octInc C w g).card ≤ (aliveSet 4 4 C g w).card := Finset.card_image_le
        change (aliveSet 4 4 C g w).card ≤ 1 at atMost
        omega
      · have bad := hn.1 _ zero
        rw [lineSum_false] at bad
        exact Bool.false_ne_true bad
      · have bad := hn.1 _ atP
        rw [lineSum_ind, off] at bad
        exact Bool.false_ne_true bad
    · have marked : ∀ v : Fin 4, IsLow 4 4 octInc C (index v) v ∧
          ∀ p, octInc p v = true → p ∈ aliveSet 4 4 C (index v) v := by
        rcases shape with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide +kernel
      have sub : aliveSet 4 4 C g w ⊆ aliveSet 4 4 C (index w) w := by
        intro p hp
        exact (marked w).2 _ (Finset.mem_filter.mp (alive_sub_line octInc C g w hn.1 hp)).2
      have one := card_image_le_one octInc C w g _ _ sub
        (const_later octInc C w _ _ (by omega) (marked w).1)
      change (labs octInc C w g).card ≤ 1 at one
      have two := ((new_iff octInc C w g).mp hn).2
      omega
  simpa [eq] using hg

end NewMergeIdentity
