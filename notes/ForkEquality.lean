import Mathlib.Tactic

namespace Independent.ForkEquality

/-- Count incidences from singleton-hot wires. Every hot wire except the
source has at least one hot incoming operand. -/
theorem exitBudget {hot internal exits reads spare : ℕ}
    (incoming : hot ≤ internal+1) (partition : reads = internal+exits)
    (fanout : reads = hot+spare) : exits ≤ 1+spare := by omega

/-- A first AND distinguishing a pair from both singletons has an operand
on each singleton, in opposite orders. -/
theorem pairBirth (va vb wa wb : Bool)
    (separateV : (va && vb) = false) (separateW : (wa && wb) = false)
    (jointA : (va || wa) = true) (jointB : (vb || wb) = true) :
    (va=true ∧ wb=true) ∨ (wa=true ∧ vb=true) := by
  cases va <;> cases vb <;> cases wa <;> cases wb <;> simp_all

/-- The two-exit bound, summed over a minimum cover, forces equality on
both sides and leaves no internal cover edge. -/
theorem regularAtEquality {inside outside cross incident internal : ℕ}
    (balance : inside ≤ outside) (outsideDegree : 2*outside ≤ cross)
    (capacity : cross+incident ≤ 2*inside)
    (hasInternal : 0 < internal → 0 < incident) :
    inside=outside ∧ cross=2*inside ∧ internal=0 := by omega

end Independent.ForkEquality
