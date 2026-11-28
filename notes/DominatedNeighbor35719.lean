import PEqualNP.Defs.CircuitLowerBounds

namespace DominatedNeighbor35719

def Hits {V : Type*} (adj : V → V → Prop) (S : Finset V) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, adj a b

/-- If all neighbors of z other than p are neighbors of p, adjoining z to an
independent set that avoids p and its neighbors preserves independence. -/
theorem oneStep {V : Type*} [DecidableEq V] (adj : V → V → Prop) (p z : V)
    (symm : ∀ {a b}, adj a b → adj b a)
    (loopless : ∀ a, ¬ adj a a)
    (edge : adj p z)
    (dominated : ∀ t, adj z t → t = p ∨ adj p t)
    (S : Finset V) (absent : p ∉ S)
    (free : ¬ Hits adj S) (quiet : ¬ Hits adj (insert p S)) :
    p ∉ insert z S ∧ ¬ Hits adj (insert z S) ∧ Hits adj (insert p (insert z S)) := by
  have noNeighbor (t : V) (mem : t ∈ S) : ¬ adj p t := by
    intro e
    exact quiet ⟨p, by simp, t, Finset.mem_insert_of_mem mem, e⟩
  have noNew (t : V) (mem : t ∈ S) : ¬ adj z t := by
    intro e
    rcases dominated t e with h | h
    · exact absent (h ▸ mem)
    · exact noNeighbor t mem h
  refine ⟨?_, ?_, ?_⟩
  · intro mem
    rcases Finset.mem_insert.mp mem with same | old
    · exact loopless z (same ▸ edge)
    · exact absent old
  · rintro ⟨a,ma,b,mb,e⟩
    rcases Finset.mem_insert.mp ma with az | oldA
    · subst a
      rcases Finset.mem_insert.mp mb with bz | oldB
      · exact loopless z (bz ▸ e)
      · exact noNew b oldB e
    · rcases Finset.mem_insert.mp mb with bz | oldB
      · subst b
        exact noNew a oldA (symm e)
      · exact free ⟨a,oldA,b,oldB,e⟩
  · exact ⟨p, by simp, z, by simp, edge⟩

/-- A sibling that masks p and is true on a negative input must fall on an
exact quiet-to-exposed pair. Only this neighbor's coordinate needs to vary. -/
theorem siblingFallsOnWitness {V : Type*} [DecidableEq V] (adj : V → V → Prop)
    (p z : V) (symm : ∀ {a b}, adj a b → adj b a)
    (loopless : ∀ a, ¬ adj a a) (edge : adj p z)
    (dominated : ∀ t, adj z t → t = p ∨ adj p t)
    (h : Finset V → Bool)
    (mask : ∀ S, p ∉ S → h S = true → (Hits adj S ↔ Hits adj (insert p S)))
    (counter : ∃ S, p ∉ S ∧ ¬ Hits adj S ∧ h S = true) :
    ∃ S, p ∉ S ∧ z ∉ S ∧ ¬ Hits adj S ∧ ¬ Hits adj (insert p S) ∧
      h S = true ∧ h (insert z S) = false := by
  obtain ⟨S, absent, free, on⟩ := counter
  have quiet : ¬ Hits adj (insert p S) := fun h => free ((mask S absent on).mpr h)
  have nz : z ∉ S := by
    intro zs
    exact quiet ⟨p, by simp, z, Finset.mem_insert_of_mem zs, edge⟩
  obtain ⟨away, negative, positive⟩ := oneStep adj p z symm loopless edge dominated S absent free quiet
  refine ⟨S, absent, nz, free, quiet, on, ?_⟩
  cases next : h (insert z S)
  · rfl
  · exact False.elim (negative ((mask (insert z S) away next).mpr positive))

#print axioms oneStep
#print axioms siblingFallsOnWitness

end DominatedNeighbor35719
