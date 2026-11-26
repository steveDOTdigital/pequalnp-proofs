import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace CliqueFourOnSix

def circuit : Circuit :=
  { gates := [⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [6,7]⟩,
              ⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [9,10]⟩,
              ⟨.or, [8,11]⟩], output := 12 }

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem seven : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (33550 : Nat).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

end CliqueFourOnSix
