import PEqualNP.Defs

namespace PetersenFlippedInput

-- On any descending output pair, a monotone suffix must pass the NOT wire
-- through unchanged over the entire interval. This includes both endpoints.
theorem interval {α : Type} [Preorder α] (h : α → Bool) (k : α → Bool → Bool)
    (mk : ∀ x y, x ≤ y → ∀ a b : Bool, a ≤ b → k x a ≤ k y b)
    (v w : α) (vw : v ≤ w) (hi : k v (!(h v)) = true) (lo : k w (!(h w)) = false) :
    h v = false ∧ h w = true ∧ ∀ z, v ≤ z → z ≤ w → ∀ t : Bool, k z t = t := by
  have impossible (ord : (!(h v)) ≤ (!(h w))) : False := by
    have le := mk v w vw _ _ ord
    rw [hi,lo] at le
    exact (by decide : ¬ (true ≤ false)) le
  have flips : h v = false ∧ h w = true := by
    cases hv : h v <;> cases hw : h w <;> simp_all
  refine ⟨flips.1,flips.2,?_⟩
  rw [flips.1] at hi
  rw [flips.2] at lo
  intro z vz zw t
  cases t with
  | false =>
    have le := mk z w zw false false le_rfl
    change k w false = false at lo
    rw [lo] at le
    exact le_antisymm le (by cases k z false <;> decide)
  | true =>
    have le := mk v z vz true true le_rfl
    change k v true = true at hi
    rw [hi] at le
    exact le_antisymm (by cases k z true <;> decide) le

end PetersenFlippedInput
