import Mathlib.Tactic

namespace Independent.ForkSurplus

/-- A hot descendant of the first fork is true whenever the fork is true.
The residual context is monotone in the other inputs. At the singleton
all those other inputs are zero, and the context accepts. -/
theorem firstImplies {V : Type*} (g : Finset V → Bool → Bool)
    (rising : ∀ S T, S ⊆ T → ∀ b, g S b = true → g T b = true)
    (hot : g ∅ true = true) : ∀ S, g S true = true := by
  intro S
  exact rising ∅ S (Finset.empty_subset S) true hot

/-- Two incomparable hot wires must both differ from the first fork. -/
theorem extraForks {W R : Type*} (val : W → R → Prop) {h a b : W}
    (firstA : ∀ r, val h r → val a r) (firstB : ∀ r, val h r → val b r)
    (ab : ∃ r, val a r ∧ ¬ val b r) (ba : ∃ r, val b r ∧ ¬ val a r) :
    a≠b ∧ a≠h ∧ b≠h := by
  obtain ⟨r,ar,br⟩ := ab
  obtain ⟨t,bt,at'⟩ := ba
  exact ⟨fun eq => br (eq ▸ ar),fun eq => br (firstB r (eq ▸ ar)),
    fun eq => at' (firstA t (eq ▸ bt))⟩

/-- An obstruction contributes two distinct shared wires outside the cover charges. -/
theorem twoSpare {W : Type*} [DecidableEq W] (charged shared : Finset W) (a b : W)
    (inside : charged ⊆ shared) (ha : a ∈ shared) (hb : b ∈ shared)
    (freshA : a ∉ charged) (freshB : b ∉ charged) (diff : a≠b) :
    charged.card+2 ≤ shared.card := by
  have sub : insert a (insert b charged) ⊆ shared := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ha
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hb
      · exact inside ht
  have count := Finset.card_le_card sub
  simpa [Finset.card_insert_of_notMem, freshA, freshB, diff, Nat.add_assoc] using count

end Independent.ForkSurplus
