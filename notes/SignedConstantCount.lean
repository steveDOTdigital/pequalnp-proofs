import SignedCofactorBound

namespace PrismSignedFrontier

-- Count distinct live original signals that the row restriction makes constant.
def zeroCount (f : W → W) (s : Finset W) : Nat := (s.filter fun w => f w = 0).card

theorem zeroCount_insert (f : W → W) (w : W) (s : Finset W) :
    zeroCount f (insert w s) ≤ zeroCount f s + (if f w = 0 then 1 else 0) := by
  by_cases h : f w = 0
  · simpa [zeroCount,Finset.filter_insert,h] using
      Finset.card_insert_le w (s.filter fun x => f x = 0)
  · simp only [zeroCount,Finset.filter_insert,if_neg h,Nat.add_zero,le_refl]

theorem zeroCount_erase (f : W → W) (s : Finset W) (w : W) (mem : w ∈ s) :
    zeroCount f (s.erase w) + (if f w = 0 then 1 else 0) = zeroCount f s := by
  have eq : (s.erase w).filter (fun x => f x = 0) = (s.filter fun x => f x = 0).erase w := by
    ext x
    simp [and_assoc,and_comm,and_left_comm]
  unfold zeroCount
  rw [eq]
  by_cases h : f w = 0
  · have hw : w ∈ s.filter (fun x => f x = 0) := by simp [mem,h]
    have pos := Finset.card_pos.mpr ⟨w,hw⟩
    simp only [h,ite_true,Finset.card_erase_of_mem hw]
    omega
  · have hw : w ∉ s.filter (fun x => f x = 0) := fun inside => h (Finset.mem_filter.mp inside).2
    simp only [if_neg h,Nat.add_zero,Finset.erase_eq_of_notMem hw]

-- Skipping a projected gate can introduce at most one extra constant in the
-- backward cone. Keeping a gate requires both of its operands to be nonconstant.
theorem Cone.project_count {g : W} {k : Nat} {s : Finset W} (h : Cone g k s)
    (f : W → W) (hom : ∀ a b w, w ∈ choices a b → f w ∈ choices (f a) (f b))
    (nz : f g ≠ 0) : ∃ j t, j + zeroCount f s ≤ k ∧ Cone (f g) j t ∧ t ⊆ s.image f := by
  induction h with
  | done => exact ⟨0,{f g},by simp only [zeroCount,Finset.filter_singleton,if_neg nz,Finset.card_empty,Nat.zero_add,le_refl],Cone.done,by simp⟩
  | @step k needed a b w rest want a0 b0 ab aw bw form ih =>
    obtain ⟨j,t,le,run,ht⟩ := ih
    let old := insert a (insert b (needed.erase w))
    have aa : f a ∈ old.image f := Finset.mem_image_of_mem _ (by simp [old])
    have bb : f b ∈ old.image f := Finset.mem_image_of_mem _ (by simp [old])
    have former (x : W) (hx : x ∈ needed) (ne : x ≠ w) : f x ∈ old.image f :=
      Finset.mem_image_of_mem _ (by simp [old,hx,ne])
    change ∃ j t, j + zeroCount f old ≤ k+1 ∧ Cone (f g) j t ∧ t ⊆ old.image f
    have ia := zeroCount_insert f a (insert b (needed.erase w))
    have ib := zeroCount_insert f b (needed.erase w)
    have ew := zeroCount_erase f needed w want
    have price : zeroCount f old ≤ zeroCount f needed + 1 := by
      change zeroCount f (insert a (insert b (needed.erase w))) ≤ _
      by_cases ha : f a = 0 <;> by_cases hb : f b = 0
      · have op := hom a b w form
        have hw : f w = 0 := by simpa [choices,ha,hb] using op
        simp only [ha,hb,hw,ite_true] at ia ib ew
        omega
      all_goals split_ifs at ia ib ew <;> omega
    by_cases sub : t ⊆ old.image f
    · exact ⟨j,t,by omega,run,sub⟩
    · have special (x : W) (hx : x ∈ t) : x = f w ∨ x ∈ old.image f := by
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp (ht hx)
        by_cases eq : z = w
        · exact Or.inl (congrArg f eq)
        · exact Or.inr (former z hz eq)
      have used : f w ∈ t := by
        by_contra bad
        exact sub (fun x hx => (special x hx).resolve_left (fun e => bad (e ▸ hx)))
      have fresh : f w ∉ old.image f := fun inside =>
        sub (fun x hx => (special x hx).elim (fun e => e ▸ inside) id)
      have nzW : f w ≠ 0 := fun e => run.noZero nz (e ▸ used)
      have op := hom a b w form
      have good : ¬(f a = 0 ∨ f b = 0 ∨ f a = f b) := by
        intro bad
        rcases constants (f a) (f b) bad _ op with e | e | e
        · exact nzW e
        · exact fresh (e ▸ aa)
        · exact fresh (e ▸ bb)
      let next := insert (f a) (insert (f b) (t.erase (f w)))
      have step : Cone (f g) (j+1) next := Cone.step run used (fun e => good (Or.inl e))
        (fun e => good (Or.inr (Or.inl e))) (fun e => good (Or.inr (Or.inr e)))
        (fun e => fresh (e ▸ aa)) (fun e => fresh (e ▸ bb)) op
      have ha : f a ≠ 0 := fun e => good (Or.inl e)
      have hb : f b ≠ 0 := fun e => good (Or.inr (Or.inl e))
      have cost : zeroCount f old ≤ zeroCount f needed := by
        change zeroCount f (insert a (insert b (needed.erase w))) ≤ _
        simp only [ha,hb,ite_false,Nat.add_zero] at ia ib
        split_ifs at ew <;> omega
      refine ⟨j+1,next,by omega,step,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact aa
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact bb
      have z := Finset.mem_erase.mp hx
      exact (special x z.2).resolve_left z.1

end PrismSignedFrontier
