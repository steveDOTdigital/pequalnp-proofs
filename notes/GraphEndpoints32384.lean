import Mathlib.Data.Bool.Basic

namespace GraphSynthesis32384

theorem reverseEndpointsIsSign {I : Type} (gate : (I → Bool) → Bool → Bool)
    (monotoneInputs : ∀ (x y : I → Bool), (∀ i, x i ≤ y i) → ∀ sign, gate x sign ≤ gate y sign)
    (atZero : gate (fun _ => false) true = true)
    (atOne : gate (fun _ => true) false = false)
    (x : I → Bool) (sign : Bool) : gate x sign = sign := by
  cases sign with
  | false =>
    have bound := monotoneInputs x (fun _ => true) (fun i => by cases x i <;> decide) false
    rw [atOne] at bound
    cases outcome : gate x false with
    | false => rfl
    | true => exact ((by decide : ¬ true ≤ false) (outcome ▸ bound)).elim
  | true =>
    have bound := monotoneInputs (fun _ => false) x (fun i => by cases x i <;> decide) true
    rw [atZero] at bound
    cases outcome : gate x true with
    | false => exact ((by decide : ¬ true ≤ false) (outcome ▸ bound)).elim
    | true => rfl

#print axioms reverseEndpointsIsSign

end GraphSynthesis32384