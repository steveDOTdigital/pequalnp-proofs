import PlaneSharedFormulas

namespace DegeneratePlaneProfiles

open PlaneSharedFormulas

/-- If all positive earlier terminals are masked, a separating comparison
inside this helper's tree must end at its distinguished raw point. -/
theorem privateSlot {α : Type*} (t : Formula α) (point : α)
    (row mask : α → Bool) (onRow : t.value row = true) (offMask : t.value mask = false)
    (covered : ∀ a, a ≠ point → row a = true → mask a = true) :
    t.label (t.route row mask) = some point := by
  obtain ⟨a, leaf, on, off⟩ := t.separates row mask onRow offMask
  by_cases equal : a = point
  · simpa [equal] using leaf
  · exact False.elim (by simpa [off] using covered a equal on)

/-- A singleton-positive helper always dominates the raw input on the entire cube. -/
theorem rawBelow {α : Type*} (h : Set α → Prop) (mono : Monotone h)
    {p : α} (positive : h {p}) {x : Set α} (active : p ∈ x) : h x :=
  mono (Set.singleton_subset_iff.mpr active) positive

/-- A new partner covers this helper and preserves the coverage of every earlier one. -/
theorem addPartner {α ι : Type*} (read : ι → Set α → Prop)
    (monotoneRead : ∀ i, Monotone (read i)) (previous : Set ι)
    (point partner : α) (mask : Set α) (next : ι)
    (old : ∀ i ∈ previous, read i {point} → read i mask)
    (hot : read next {partner}) :
    ∀ i ∈ insert next previous, read i {point} → read i (insert partner mask) := by
  intro i hi hp
  rcases Set.mem_insert_iff.mp hi with eq | mem
  · subst i
    exact rawBelow _ (monotoneRead _) hot (Set.mem_insert _ _)
  · exact monotoneRead i (Set.subset_insert _ _) (old i mem hp)

/-- An edge of the optional-input graph can be chosen precisely when both
incident maxima have been chosen. This equates the closure condition on all
three levels with the two endpoint tests. -/
inductive Optional (L R E : Type*) where
  | left (l : L) | right (r : R) | edge (e : E)

def optionalLE {L R E : Type*} (l : E → L) (r : E → R) :
    Optional L R E → Optional L R E → Prop
  | .edge e, .left v => l e = v
  | .edge e, .right v => r e = v
  | a, b => a = b

theorem upperChoices {L R E : Type*} (l : E → L) (r : E → R)
    (choose : Optional L R E → Prop) :
    (∀ a b, optionalLE l r a b → choose a → choose b) ↔
    (∀ e, choose (.edge e) → choose (.left (l e)) ∧ choose (.right (r e))) := by
  constructor
  · intro upper e yes
    exact ⟨upper (.edge e) (.left (l e)) rfl yes, upper (.edge e) (.right (r e)) rfl yes⟩
  · intro endpoints a b ext holds
    cases a <;> cases b <;> simp [optionalLE] at ext <;> subst_vars <;> simp_all

/-- Combine the losses from raw operand charges and lost matched edges
without discarding the surplus fanout. -/
theorem retainedBound {g raw excess filterRaw proofRaw flags residual matched
    residualMatching lost : ℕ} (wires : g + 1 = raw + excess)
    (separate : filterRaw + proofRaw ≤ raw)
    (removed : flags ≤ residual + filterRaw)
    (damage : matched ≤ residualMatching + lost)
    (price : residual + residualMatching ≤ proofRaw) :
    flags + matched + excess ≤ g + 1 + lost := by omega

/-- The four cyclic perfect matchings partition the flags. Here the maximum
retained matching and the number of exceptional rows give a gate bound. -/
theorem defectBound {g exceptions retained matching : ℕ}
    (partition : retained + exceptions = 52)
    (averaging : 52 ≤ 4 * matching + exceptions)
    (charge : retained + matching ≤ g + 1) :
    64 ≤ g + exceptions + exceptions / 4 := by omega

end DegeneratePlaneProfiles
