import PEqualNP.Outside.L_meta_950

namespace SixVertexAndCount

-- L-meta-950, already checked upstream, rules out the requested witness.
theorem noWitness : ¬ (∃ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧ ¬ (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)))) := by
  rintro ⟨G, C, wellFormed, onBoundary, noCover⟩
  exact noCover (PEqualNP.Outside.L_meta_950 G C ⟨wellFormed, onBoundary⟩)

end SixVertexAndCount
