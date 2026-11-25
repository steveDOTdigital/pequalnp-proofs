import NineVertexDeletion

namespace NineVertexTableTwo
open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_8451

/-- Keep the certified deletion and allow any choice of neighbors for the new vertex. -/
def extension (neighbors : Fin 9 → Bool) (x : Fin 9 → Bool) : Bool :=
  target (Function.update x 2 false) ||
    (x 2 && (List.ofFn fun i : Fin 9 => neighbors i && x i).any id)

private theorem pinnedExtension (neighbors : Fin 9 → Bool) (x : Fin 9 → Bool) :
    extension neighbors (Function.update x 2 false) = target (Function.update x 2 false) := by
  simp [extension, Function.update_idem]

theorem extensionLower (neighbors : Fin 9 → Bool) (w : Fin 9)
    (separate : w ≠ 2) (edge : neighbors w = true) (s : ℕ)
    (h : HasCircuitSize 9 (extension neighbors) s) : 15 ≤ s := by
  let x := fun i : Fin 9 => decide (i = w)
  have zero : x 2 = false := by simp [x, Ne.symm separate]
  have empty : target (Function.update x 2 false) = false := by
    have fact : ∀ j : Fin 9,
        target (Function.update (fun i : Fin 9 => decide (i = j)) 2 false) = false := by decide +kernel
    exact fact w
  have before : extension neighbors x = false := by simp [extension, zero, empty]
  let y := Function.update x 2 true
  have on : y w = true := by simp [y, x, Function.update_of_ne separate]
  have after : extension neighbors y = true := by
    have hit : (List.ofFn fun i : Fin 9 => neighbors i && y i).any id = true := by
      exact List.any_eq_true.mpr ⟨true, List.mem_ofFn.mpr ⟨w, by simp [edge,on]⟩, rfl⟩
    have bit : y 2 = true := Function.update_self ..
    simp only [extension, hit, bit, Bool.and_true, Bool.or_true]
  have depends : ∃ z, extension neighbors (Function.update z 2 (!z 2)) ≠ extension neighbors z := by
    refine ⟨x, ?_⟩
    rw [zero, before]
    exact Bool.ne_false_iff.mpr after
  have varies : ∃ u v, extension neighbors (Function.update u 2 false) ≠
      extension neighbors (Function.update v 2 false) := by
    refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 4), ?_⟩
    rw [pinnedExtension, pinnedExtension]
    decide +kernel
  obtain ⟨t, savings, cofactor⟩ := Bow.one_gate_at 8 _ 2 false s depends varies h
  have same : (fun x => extension neighbors (Function.update x 2 false)) =
      (fun x => target (Function.update x 2 false)) := funext (pinnedExtension neighbors)
  rw [same] at cofactor
  have := deletionFourteen t cofactor
  omega

end NineVertexTableTwo
