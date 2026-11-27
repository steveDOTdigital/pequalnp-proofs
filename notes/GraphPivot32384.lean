import Mathlib.Data.Bool.Basic

namespace GraphSynthesis32384

theorem eraseSignOnConnectedPivot {X : Type} [Preorder X]
    (H : X → Bool → Bool) (sign : X → Bool) (pivotal : X → Prop)
    (mono : ∀ {x y : X}, x ≤ y → H x (sign x) ≤ H y (sign y))
    (anti : ∀ {x y : X}, x ≤ y → sign y ≤ sign x)
    (pivot : ∀ x, pivotal x → ∀ b, H x b = b)
    (offPivot : ∀ x, ¬ pivotal x → H x false = H x true)
    (anchor : X) (onAnchor : pivotal anchor)
    (connection : ∀ x, pivotal x → ∃ upper, pivotal upper ∧ x ≤ upper ∧ anchor ≤ upper)
    (x : X) : H x (sign x) = H x (sign anchor) := by
  have sameOnChain {u v : X} (hu : pivotal u) (hv : pivotal v) (ordered : u ≤ v) :
      sign u = sign v := by
    have asc := mono ordered
    rw [pivot u hu, pivot v hv] at asc
    exact le_antisymm asc (anti ordered)
  by_cases onX : pivotal x
  · obtain ⟨upper,upperP,reachX,reachAnchor⟩ := connection x onX
    have same := (sameOnChain onX upperP reachX).trans (sameOnChain onAnchor upperP reachAnchor).symm
    rw [same]
  · have fixed := offPivot x onX
    cases sign x <;> cases sign anchor <;> simp_all

#print axioms eraseSignOnConnectedPivot

end GraphSynthesis32384