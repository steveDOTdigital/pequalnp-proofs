import PEqualNP.Defs.Represents

/-!
A 19-gate circuit for the six-label inequality matrix in L-meta-9304.
Pair each left input with the right input at its missing edge. A binary
tree on the six presence bits detects whether two different labels occur.
-/
namespace CrownPromise
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def matrix (u v : Fin 6) : Bool := (51404332959 : ℕ).testBit (6 * u.val + v.val)

theorem missingMatching : ∀ u v : Fin 6, matrix u v = decide (u.val ≠ (v.val + 1) % 6) := by
  decide +kernel

def witness : Circuit :=
  ⟨[⟨.or, [0, 11]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.and, [19, 14]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.or, [19, 14]⟩,
    ⟨.and, [15, 16]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [24, 17]⟩,
    ⟨.or, [23, 25]⟩,
    ⟨.or, [24, 17]⟩,
    ⟨.and, [22, 27]⟩,
    ⟨.or, [21, 28]⟩,
    ⟨.or, [26, 29]⟩], 30⟩

theorem upper : RepSizeAtMost matrix 19 := by
  refine ⟨witness, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;>
    first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel

#print axioms upper
end CrownPromise
