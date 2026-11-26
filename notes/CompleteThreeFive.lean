import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
namespace CompleteThreeFive

def graph (u : Fin 3) (v : Fin 5) := (32767 : Nat).testBit (5 * u.val + v.val)

-- Disjoint promised inputs share no true wire, including out-of-range reads.
private theorem disjointReads (o : Nat) :
    (oneEach (0 : Fin 3) (0 : Fin 5)).getD o false = false ∨
    (oneEach (1 : Fin 3) (1 : Fin 5)).getD o false = false := by
  by_cases h : o < 8
  · have check : ∀ i : Fin 8,
        (oneEach (0 : Fin 3) (0 : Fin 5)).getD i.val false = false ∨
        (oneEach (1 : Fin 3) (1 : Fin 5)).getD i.val false = false := by decide +kernel
    exact check ⟨o,h⟩
  · left
    exact List.getD_eq_default _ _ (by change 8 ≤ o; omega)

theorem exactLower : ¬ RepSizeAtMost
    (fun (u : Fin 3) (v : Fin 5) => (32767 : Nat).testBit (5 * u.val + v.val)) 0 := by
  rintro ⟨⟨gs,o⟩, _, hs, he⟩
  change gs.length ≤ 0 at hs
  have hnil : gs = [] := List.length_eq_zero_iff.mp (by omega)
  subst gs
  have h0 := he (0 : Fin 3) (0 : Fin 5)
  have h1 := he (1 : Fin 3) (1 : Fin 5)
  change (oneEach (0 : Fin 3) (0 : Fin 5)).getD o false = true at h0
  change (oneEach (1 : Fin 3) (1 : Fin 5)).getD o false = true at h1
  rcases disjointReads o with h | h <;> simp_all

-- The empty conjunction outputs true on every input.
def circuit : Circuit := { gates := [⟨.and, []⟩], output := 8 }

theorem upper : RepSizeAtMost graph 1 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_singleton] at hg
    subst g
    simp
  · decide
  · decide +kernel

#print axioms exactLower
#print axioms upper
end CompleteThreeFive
