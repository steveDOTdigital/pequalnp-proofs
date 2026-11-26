import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds

def mask20348Circuit : Circuit :=
  { gates := [
      ⟨.or, [3, 8]⟩,
      ⟨.or, [6, 11]⟩,
      ⟨.or, [5, 17]⟩,
      ⟨.or, [1, 14]⟩,
      ⟨.or, [0, 15]⟩,
      ⟨.or, [10, 16]⟩,
      ⟨.or, [2, 4]⟩,
      ⟨.or, [18, 19]⟩,
      ⟨.or, [7, 12]⟩,
      ⟨.or, [5, 9]⟩,
      ⟨.or, [6, 20]⟩,
      ⟨.or, [15, 18]⟩,
      ⟨.or, [19, 20]⟩,
      ⟨.or, [16, 27]⟩,
      ⟨.or, [4, 26]⟩,
      ⟨.or, [13, 22]⟩,
      ⟨.and, [30, 25]⟩,
      ⟨.and, [29, 24]⟩,
      ⟨.and, [23, 31]⟩,
      ⟨.and, [21, 28]⟩,
      ⟨.and, [10, 2]⟩,
      ⟨.or, [32, 33]⟩,
      ⟨.or, [37, 34]⟩,
      ⟨.or, [38, 35]⟩,
      ⟨.or, [39, 36]⟩],
    output := 40 }

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem mask20348AtMostTwentyFive :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 8 => (9886157967400379655 : ℕ).testBit (8 * u.val + v.val)) 25 := by
  refine ⟨mask20348Circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [mask20348Circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
