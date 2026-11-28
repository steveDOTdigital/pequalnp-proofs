import PEqualNP.Defs.CircuitLowerBounds

namespace SafeNotReplacement33765

/-- Replacing a single inverted wire by a value in this interval preserves
the output of every context monotone in the wire. -/
theorem eval_eq {α : Type*} (target source choice : α → Bool)
    (context : α → Bool → Bool)
    (mono : ∀ x, context x false = true → context x true = true)
    (correct : ∀ x, context x (!(source x)) = target x)
    (lower : ∀ x, target x = true → source x = false → choice x = true)
    (upper : ∀ x, choice x = true → source x = true → target x = true) :
    ∀ x, context x (choice x) = target x := by
  intro x
  have old := correct x
  cases hs : source x <;> cases hw : choice x
  · have tf : target x = false := by
      cases ht : target x
      · rfl
      · exact False.elim (Bool.false_ne_true (hw.symm.trans (lower x ht hs)))
    have gateOff : context x true = false := by simpa [hs, tf] using old
    have lowOff : context x false = false := by
      cases low : context x false
      · rfl
      · exact False.elim (Bool.false_ne_true (gateOff.symm.trans (mono x low)))
    exact lowOff.trans tf.symm
  · simpa [hs] using old
  · simpa [hs] using old
  · have tt := upper x hw hs
    have gateOn : context x false = true := by simpa [hs, tt] using old
    exact (mono x gateOn).trans tt.symm

#print axioms eval_eq

end SafeNotReplacement33765
