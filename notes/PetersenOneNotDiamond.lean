import PEqualNP.Defs

namespace PetersenOneNotDiamond

-- Both constant replacements fail. On two input blocks the independently
-- driven NOT output must therefore feed a three-input majority function.
theorem diamond : ∀ (n : ℕ) (f h : (Fin n → Bool) → Bool) (k : (Fin n → Bool) → Bool → Bool),
    Monotone f → Monotone h →
    (∀ x y, x ≤ y → ∀ a b : Bool, a ≤ b → k x a ≤ k y b) →
    (∀ x, k x (!(h x)) = f x) → (∀ b, ∃ x, k x b ≠ f x) →
    ∃ e i : Fin n → Bool, ∀ a b t : Bool, let x := if a then (if b then (fun j => e j || i j) else e)
        else (if b then i else (fun j => e j && i j))
      h x = b ∧ k x t = ((a && b) || ((a || b) && t)) := by
  intro n f h k mf mh mk computes bad
  obtain ⟨e,failE⟩ := bad false
  obtain ⟨i,failI⟩ := bad true
  have lower (x : Fin n → Bool) : k x false ≤ f x := by
    rw [← computes x]
    exact mk x x le_rfl false _ (by cases h x <;> decide)
  have upper (x : Fin n → Bool) : f x ≤ k x true := by
    rw [← computes x]
    exact mk x x le_rfl _ true (by cases h x <;> decide)
  have strict : ∀ a b : Bool, a ≤ b → a ≠ b → a = false ∧ b = true := by decide
  have bot_force : ∀ a : Bool, a ≤ false → a = false := by decide
  have top_force : ∀ a : Bool, true ≤ a → a = true := by decide
  have ec := strict _ _ (lower e) failE
  have ic := (strict _ _ (upper i) (Ne.symm failI)).symm
  have he : h e = false := by
    cases hh : h e with
    | false => rfl
    | true => exact False.elim (failE (by simpa [hh] using computes e))
  have hi : h i = true := by
    cases hh : h i with
    | true => rfl
    | false => exact False.elim (failI (by simpa [hh] using computes i))
  have et : k e true = true := by simpa [he,ec.2] using computes e
  have iz : k i false = false := by simpa [hi,ic.2] using computes i
  let bot := fun j => e j && i j
  let top := fun j => e j || i j
  have bounds : ∀ a b : Bool, (a && b) ≤ a ∧ (a && b) ≤ b ∧ a ≤ (a || b) ∧ b ≤ (a || b) := by decide
  have be : bot ≤ e := fun j => (bounds (e j) (i j)).1
  have bi : bot ≤ i := fun j => (bounds (e j) (i j)).2.1
  have ea : e ≤ top := fun j => (bounds (e j) (i j)).2.2.1
  have ia : i ≤ top := fun j => (bounds (e j) (i j)).2.2.2
  have hb : h bot = false := by
    have le := mh be
    rw [he] at le
    exact bot_force _ le
  have ht : h top = true := by
    have le := mh ia
    rw [hi] at le
    exact top_force _ le
  have fb : f bot = false := by
    have le := mf bi
    rw [ic.2] at le
    exact bot_force _ le
  have ft : f top = true := by
    have le := mf ea
    rw [ec.2] at le
    exact top_force _ le
  have kb (t : Bool) : k bot t = false := by
    have endval : k bot true = false := by simpa [hb,fb] using computes bot
    have le := mk bot bot le_rfl t true (by cases t <;> decide)
    exact bot_force _ (endval ▸ le)
  have kt (t : Bool) : k top t = true := by
    have endval : k top false = true := by simpa [ht,ft] using computes top
    have le := mk top top le_rfl false t (by cases t <;> decide)
    exact top_force _ (endval ▸ le)
  refine ⟨e,i,?_⟩
  intro a b t
  cases a <;> cases b <;> cases t
  · exact ⟨hb,kb false⟩
  · exact ⟨hb,kb true⟩
  · exact ⟨hi,iz⟩
  · exact ⟨hi,ic.1⟩
  · exact ⟨he,ec.1⟩
  · exact ⟨he,et⟩
  · exact ⟨ht,kt false⟩
  · exact ⟨ht,kt true⟩

end PetersenOneNotDiamond
