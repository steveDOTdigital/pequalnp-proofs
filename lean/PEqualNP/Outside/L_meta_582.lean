import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Support

namespace PEqualNP.Outside.L_meta_582

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers

-- Repeated copies and constants may be supplied freely, but a circuit on
-- this restricted input family still has to connect the essential variables.
private lemma projection_bound {d n : ℕ} (label : Fin n → Option (Fin d))
    (f : (Fin d → Bool) → Bool) (D : Circuit) (ok : FanInTwo D)
    (correct : ∀ x, D.eval (List.ofFn (fun j => ((label j).map x).getD true)) = f x)
    (depends : ∀ i, ∃ x y, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y) :
    d ≤ D.size + 1 := by
  classical
  let S := (suppsFrom D.gates (inputSupps n)).getD D.output ∅
  have incl : Finset.univ.image (@some (Fin d)) ⊆ S.image label := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    by_contra absent
    obtain ⟨x, y, same, diff⟩ := depends i
    apply diff
    rw [← correct, ← correct]
    apply (agree_wiresFrom _ _ D.gates _ _ _ (agree_inputs _ _)).2.2
    intro j hj
    cases h : label j with
    | none => simp
    | some k =>
      have ne : k ≠ i := by
        intro eq
        exact absent (Finset.mem_image.mpr ⟨j, hj, eq ▸ h⟩)
      simp [same k ne]
  have size := (Finset.card_le_card incl).trans (Finset.card_image_le)
  rw [Finset.card_image_of_injective _ (Option.some_injective (Fin d)), Finset.card_univ,
    Fintype.card_fin] at size
  have lim := cnt_suppsFrom D.gates 0 (inputSupps n) ok cnt_inputs {D.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at lim
  exact size.trans lim

abbrev Input := Fin 14 → Bool

def edgeFunction (z : Input) : Bool :=
  (z 7 && (z 0 || z 1 || z 3)) ||
  (z 8 && (z 0 || z 2 || z 6)) ||
  (z 9 && (z 1 || z 5 || z 6)) ||
  (z 10 && (z 0 || z 4 || z 5)) ||
  (z 11 && (z 3 || z 4 || z 6)) ||
  (z 12 && (z 2 || z 3 || z 5)) ||
  (z 13 && (z 1 || z 2 || z 4))

-- Six completed line stars, with every two-point partial OR and the
-- full three-point OR available for each of the six. This gives the
-- suffix more signals than any one choice of parenthesization.
def freeInputs (z : Input) : Fin 44 → Bool :=
  ![z 0, z 1, z 2, z 3, z 4, 
    z 5, z 6, z 7, z 8, z 9, 
    z 10, z 11, z 12, z 13, z 0 || z 2, 
    z 2 || z 6, z 6 || z 0, (z 0 || z 2 || z 6), (z 8 && (z 0 || z 2 || z 6)), z 1 || z 5, 
    z 5 || z 6, z 6 || z 1, (z 1 || z 5 || z 6), (z 9 && (z 1 || z 5 || z 6)), z 0 || z 4, 
    z 4 || z 5, z 5 || z 0, (z 0 || z 4 || z 5), (z 10 && (z 0 || z 4 || z 5)), z 3 || z 4, 
    z 4 || z 6, z 6 || z 3, (z 3 || z 4 || z 6), (z 11 && (z 3 || z 4 || z 6)), z 2 || z 3, 
    z 3 || z 5, z 5 || z 2, (z 2 || z 3 || z 5), (z 12 && (z 2 || z 3 || z 5)), z 1 || z 2, 
    z 2 || z 4, z 4 || z 1, (z 1 || z 2 || z 4), (z 13 && (z 1 || z 2 || z 4))]

private def restriction (x : Fin 10 → Bool) : Input :=
  ![x 0, x 1, true, x 2, true, true, true, x 3, x 4, x 5, x 6, x 7, x 8, x 9]

private def labels : Fin 44 → Option (Fin 10) :=
  ![some 0, some 1, none, some 2, none, 
    none, none, some 3, some 4, some 5, 
    some 6, some 7, some 8, some 9, none, 
    none, none, none, some 4, none, 
    none, none, none, some 5, none, 
    none, none, none, some 6, none, 
    none, none, none, some 7, none, 
    none, none, none, some 8, none, 
    none, none, none, some 9]

private def reduced (x : Fin 10 → Bool) : Bool :=
  (x 3 && (x 0 || x 1 || x 2)) || x 4 || x 5 || x 6 || x 7 || x 8 || x 9

private lemma signals (x : Fin 10 → Bool) :
    freeInputs (restriction x) = fun j => ((labels j).map x).getD true := by
  funext j
  fin_cases j <;> simp [freeInputs, restriction, labels]

private lemma restricted_target (x : Fin 10 → Bool) :
    edgeFunction (restriction x) = reduced x := by
  simp [edgeFunction, restriction, reduced]

private def start (i j : Fin 10) := decide ((i.val < 3 ∧ j = 3) ∨ (i = 3 ∧ j = 0))
private def finish (i j : Fin 10) := start i j || decide (j = i)

private lemma probes : ∀ i, reduced (start i) = false ∧ reduced (finish i) = true := by decide

-- In particular, six canonical stars cost 18 gates and an arbitrary
-- suffix needs at least nine, even when it may use NOT gates.
lemma six_stars_need_nine (D : Circuit) (ok : FanInTwo D)
    (correct : ∀ z, D.eval (List.ofFn (freeInputs z)) = edgeFunction z) :
    9 ≤ D.size := by
  have bound := projection_bound labels reduced D ok (fun x => by
    rw [← signals x, correct, restricted_target]) (fun i => by
      refine ⟨start i, finish i, ?_, ?_⟩
      · intro j ne
        simp [finish, ne]
      · rw [(probes i).1, (probes i).2]
        decide)
  omega

end PEqualNP.Outside.L_meta_582
