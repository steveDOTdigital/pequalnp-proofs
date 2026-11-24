import Mathlib

namespace HeawoodPortPairing

-- Two input ports supply point 1. Covering its three edges occupies both,
-- and occupies the two ports that could have supplied line 12 to point 5.
theorem four_edges : ∀ f : Fin 10 → Fin 10, (∀ i, f (f i) = i) → ¬ ((f 0 ∈ ([1,8] : List (Fin 10)) ∨ f 6 ∈ ([1,8] : List (Fin 10))) ∧
      (f 0 ∈ ([3,9] : List (Fin 10)) ∨ f 6 ∈ ([3,9] : List (Fin 10))) ∧
      (f 0 ∈ ([2,8] : List (Fin 10)) ∨ f 6 ∈ ([2,8] : List (Fin 10))) ∧
      (f 4 ∈ ([0,8] : List (Fin 10)) ∨ f 7 ∈ ([0,8] : List (Fin 10)))) := by
  intro f inv h
  obtain ⟨h1,h2,h3,h4⟩ := h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h1 h2 h3 h4
  have placements :
      (f 0 = 8 ∧ (f 6 = 3 ∨ f 6 = 9)) ∨ (f 6 = 8 ∧ (f 0 = 3 ∨ f 0 = 9)) := by
    grind
  have rev4 := inv 4
  have rev7 := inv 7
  have rev0 := inv 0
  have rev6 := inv 6
  grind

end HeawoodPortPairing
