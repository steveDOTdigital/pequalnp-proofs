import CliqueFourOnSix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace CliqueFourCatalogue

-- Both posted bounds follow from the original seven-gate witness.
theorem catalogue21922 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (33550 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨CliqueFourOnSix.circuit, CliqueFourOnSix.monotone, ?_, ?_⟩
  · decide
  · decide +kernel

theorem catalogue22536 : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (33550 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  obtain ⟨C, legal, size, correct⟩ := CliqueFourOnSix.seven
  exact ⟨C, legal, by omega, correct⟩

#print axioms catalogue21922
#print axioms catalogue22536
end CliqueFourCatalogue
