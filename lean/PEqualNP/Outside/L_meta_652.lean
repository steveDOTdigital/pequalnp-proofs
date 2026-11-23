import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Support

namespace PEqualNP.Outside.L_meta_652

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def direct : Circuit :=
  ⟨[⟨.and, [0, 3]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [14, 13]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.and, [2, 4]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [19, 18]⟩], 20⟩

lemma fifteen_suffice : FanInTwo direct ∧ direct.size = 15 ∧
    ∀ x : Fin 6 → Bool, (direct.wires (List.ofFn x)).getD 10 false = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧
      (direct.wires (List.ofFn x)).getD 15 false = ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧
      (direct.wires (List.ofFn x)).getD 20 false = ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4)) := by
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp [direct] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · intro x
    have eq : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5] := by simp [List.ofFn_succ]
    rw [eq]
    simp [direct, Circuit.wires, GateOp.eval]

open PEqualNP.MetaComplexity.Helpers

abbrev Bits := Fin 6 → Bool

def lastMatching (x : Bits) : Bool :=
  (x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4)

private def mate : Fin 6 → Fin 6 := ![5,3,4,1,2,0]

private def single (i : Fin 6) : Bits := fun j => decide (j = mate i)
private def both (i : Fin 6) : Bits := fun j => decide (j = mate i ∨ j = i)

private lemma probes : ∀ i, lastMatching (single i) = false ∧
    lastMatching (both i) = true := by decide

-- Previously computed signals may be given to the suffix for free.
-- If they agree on these six pairs of inputs, all six original bits
-- must still occur in the suffix's own output support.
lemma suffix_needs_five {m : ℕ} (extra : Bits → Fin m → Bool)
    (quiet : ∀ i, extra (single i) = extra (both i)) (D : Circuit) (ok : FanInTwo D)
    (correct : ∀ x, D.eval (List.ofFn (Fin.addCases x (extra x))) = lastMatching x) :
    5 ≤ D.size := by
  classical
  let S := (suppsFrom D.gates (inputSupps (6 + m))).getD D.output ∅
  have included (i : Fin 6) : i.castAdd m ∈ S := by
    by_contra absent
    let u : Fin (6 + m) → Bool := Fin.addCases (single i) (extra (single i))
    let v : Fin (6 + m) → Bool := Fin.addCases (both i) (extra (both i))
    have agree : ∀ j ∈ S, u j = v j := by
      intro j
      refine Fin.addCases (fun k hk => ?_) (fun k hk => ?_) j
      · have diff : k ≠ i := fun eq => absent (eq ▸ hk)
        simp [u, v, single, both, diff]
      · simpa [u, v] using congrFun (quiet i) k
    have eq : D.eval (List.ofFn u) = D.eval (List.ofFn v) :=
      (agree_wiresFrom u v D.gates _ _ _ (agree_inputs u v)).2.2 D.output agree
    have same := (correct (single i)).symm.trans (eq.trans (correct (both i)))
    rw [(probes i).1, (probes i).2] at same
    contradiction
  have sub : Finset.univ.image (fun i : Fin 6 => i.castAdd m) ⊆ S := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact included i
  have injective : Function.Injective (fun i : Fin 6 => i.castAdd m) :=
    fun i j eq => Fin.ext (congrArg (fun k : Fin (6 + m) => k.val) eq)
  have six := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ injective, Finset.card_univ, Fintype.card_fin] at six
  have budget := cnt_suppsFrom D.gates 0 (inputSupps (6 + m)) ok cnt_inputs {D.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at budget
  have h : 6 ≤ D.gates.length + 1 := six.trans budget
  change 5 ≤ D.gates.length
  omega

-- Providing every possible OR of the first two matchings' six products
-- also leaves the lower bound intact: all six products are already zero
-- on both sides of every probe. An arbitrary function of them is quiet.
def earlierProducts (x : Bits) : Fin 6 → Bool :=
  ![x 0 && x 3, x 1 && x 4, x 2 && x 5,
    x 0 && x 4, x 1 && x 5, x 2 && x 3]

lemma earlier_products_free {m : ℕ} (h : Bits → Fin m → Bool)
    (D : Circuit) (ok : FanInTwo D)
    (correct : ∀ x, D.eval (List.ofFn (Fin.addCases x (h (earlierProducts x)))) = lastMatching x) :
    5 ≤ D.size := by
  apply suffix_needs_five (fun x => h (earlierProducts x)) _ D ok correct
  have quiet : ∀ i, earlierProducts (single i) = earlierProducts (both i) := by decide
  exact fun i => congrArg h (quiet i)

end PEqualNP.Outside.L_meta_652

