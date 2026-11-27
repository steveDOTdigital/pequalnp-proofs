import Mathlib.Data.Bool.Basic

namespace GraphSynthesis32384

theorem positiveDependenceWithSignFixed {Input : Type}
    (afterNot : Input → Bool → Bool) (sign : Input → Bool)
    (signMonotone : ∀ x a b, a ≤ b → afterNot x a ≤ afterNot x b)
    {x y : Input} (signFalls : sign y ≤ sign x)
    (below : afterNot x (sign x) = false) (above : afterNot y (sign y) = true) :
    ∃ fixed : Bool, afterNot x fixed = false ∧ afterNot y fixed = true := by
  refine ⟨sign x, below, ?_⟩
  have greater := signMonotone y (sign y) (sign x) signFalls
  rw [above] at greater
  cases value : afterNot y (sign x) with
  | false => exact ((by decide : ¬ true ≤ false) (value ▸ greater)).elim
  | true => rfl

theorem directInputPathNeeded {Input : Type}
    (afterNot : Input → Bool → Bool) (sign : Input → Bool)
    (signMonotone : ∀ x a b, a ≤ b → afterNot x a ≤ afterNot x b)
    {x y : Input} (signFalls : sign y ≤ sign x)
    (below : afterNot x (sign x) = false) (above : afterNot y (sign y) = true) :
    ¬ ∀ fixed : Bool, afterNot x fixed = afterNot y fixed := by
  intro constant
  obtain ⟨b, low, high⟩ := positiveDependenceWithSignFixed afterNot sign signMonotone signFalls below above
  have same := constant b
  rw [low,high] at same
  contradiction

#print axioms directInputPathNeeded

end GraphSynthesis32384