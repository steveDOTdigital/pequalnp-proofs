import PetersenRawNormal

namespace EightVertex8399
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [8, 3]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.and, [3, 14]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.and, [6, 17]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [19, 15]⟩,
    ⟨.or, [20, 16]⟩,
    ⟨.or, [21, 18]⟩], 22⟩

theorem upper : HasCircuitSize 8 target 15 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro g hg
    simp [witness] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel

/-- It suffices to rule out the single budget immediately below the posted bound. -/
theorem posted_iff : (∀ t, HasCircuitSize 8 target t → 15 ≤ t) ↔
    ¬ HasCircuitSize 8 target 14 := by
  constructor
  · intro h small
    have := h 14 small
    omega
  · intro h t ht
    by_contra! lt
    obtain ⟨C, ok, bound, hit⟩ := ht
    exact h ⟨C, ok, by omega, hit⟩

/-- One step appends an AND and its complement, with free signs on raw inputs and output. -/
def signedValue (p : List (ℕ × ℕ)) (o : ℕ) (x : Fin 8 → Bool) : Bool :=
  (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
    w ++ [z, !z]) ([false, true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false

/-- The two finite lower bounds imply the exact posted proposition. -/
theorem fromSearches
    (signed : ∀ p o, (∀ x, signedValue p o x = target x) → 14 ≤ p.length)
    (monotone : ∀ C : Circuit,
      (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
      (∀ x, circuitFun 8 C x = target x) → 15 ≤ C.size) :
    ∀ t, HasCircuitSize 8 target t → 15 ≤ t := by
  rintro t ⟨C, legal, size, hit⟩
  rcases PetersenRawNormal.normalize 8 C legal with binary | ⟨p, o, shorter, eval⟩
  · exact (monotone C binary hit).trans size
  · have bound := signed p o (fun x => (eval x).trans (hit x))
    omega

end EightVertex8399
