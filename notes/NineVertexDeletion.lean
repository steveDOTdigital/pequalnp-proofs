import PEqualNP.Outside.L_meta_8451
import NineVertexTableTwo

namespace NineVertexTableTwo
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8451

private theorem dependsTwo : Maj.Helpers.Readers.Dep target 2 :=
  ⟨fun i => decide (i = 6), by decide +kernel⟩

private theorem variesTwo (b : Bool) : ∃ x y : Fin 9 → Bool,
    target (Function.update x 2 b) ≠ target (Function.update y 2 b) := by
  cases b <;> exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 4), by decide +kernel⟩

/-- Deleting input 2 leaves the certified eight-vertex graph of L-meta-8451. -/
theorem deletionFourteen (t : ℕ)
    (small : HasCircuitSize 9 (fun x => target (Function.update x 2 false)) t) : 14 ≤ t := by
  let labels : Fin 9 → Fin 8 := ![5, 2, 0, 3, 6, 1, 4, 7, 0]
  have reduced := Bow.relabel_size labels _ t small
  have same : (fun x : Fin 8 → Bool => target (Function.update (x ∘ labels) 2 false)) =
      (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
        (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6) ||
        (x 5 && x 7) || (x 6 && x 7)) := by
    funext x
    simp [target, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [same] at reduced
  exact PEqualNP.Outside.L_meta_8451 t reduced

theorem ordinaryFifteen (s : ℕ) (h : HasCircuitSize 9 target s) : 15 ≤ s := by
  obtain ⟨t, saving, small⟩ := Bow.one_gate_at 8 target 2 false s dependsTwo (variesTwo false) h
  have := deletionFourteen t small
  omega

open PEqualNP.CircuitLowerBounds Maj.Helpers Maj.Helpers.Readers

/-- At budget 15 precisely one gate may read input 2, and its operation must be OR. -/
theorem uniqueOr {gs : List Gate} {o : ℕ} (L : Least 9 target gs o) (size : gs.length ≤ 15) :
    ∃ p g, gs[p]? = some g ∧ (2 : ℕ) ∈ g.inputs ∧ g.op = .or ∧
      ∀ q, Reads gs q 2 → q = p := by
  obtain ⟨p, hp⟩ := L.dep_read 2 dependsTwo variesTwo
  have impossible (q : ℕ) (other : p ≠ q) (rc : RC 8 gs 2 false q) : False := by
    obtain ⟨s, saving, small⟩ := L.save2 2 false (variesTwo false) p q other (rc_input false hp) rc
    have := deletionFourteen s small
    omega
  obtain ⟨g, hg, raw⟩ := hp
  refine ⟨p, g, hg, raw, ?_, ?_⟩
  · by_contra nonOr
    have fb : fixBit g = false := by
      unfold fixBit
      split <;> simp_all
    have fixed := const_read 8 gs L.hcl 2 false p g hg 2 raw (by rw [fb]; exact stF_self 8 gs 2 false)
    obtain ⟨q, later, _, rc⟩ := L.next 2 false (variesTwo false) p
      (List.getElem?_eq_some_iff.mp hg).1 fixed
    exact impossible q (by omega) rc
  · intro q hq
    by_contra neq
    exact impossible q (Ne.symm neq) (rc_input false hq)


/-- A raw companion to the unique OR reader would mask a genuine change of the target. -/
theorem noRawMate {gs : List Gate} {o p : ℕ} {g : Gate}
    (L : Least 9 target gs o) (atGate : gs[p]? = some g) (isOr : g.op = .or)
    (unique : ∀ q, Reads gs q 2 → q = p) (w : Fin 9) (other : w ≠ 2) :
    (w : ℕ) ∉ g.inputs := by
  intro readsMate
  have rows : ∀ j : Fin 9, j ≠ 2 → ∃ r : Fin 512,
      let x := fun i : Fin 9 => r.val.testBit i.val
      x j = true ∧ target (Function.update x 2 false) ≠ target (Function.update x 2 true) := by
    decide +kernel
  obtain ⟨r, hrow⟩ := rows w other
  let x := fun i : Fin 9 => r.val.testBit i.val
  change x w = true ∧ _ at hrow
  let lo := Function.update x 2 false
  let hi := Function.update x 2 true
  have bitL : lo w = true := by simpa [lo, Function.update_of_ne other] using hrow.1
  have bitH : hi w = true := by simpa [hi, Function.update_of_ne other] using hrow.1
  have forced (y : Fin 9 → Bool) (bit : y w = true) : vl gs y (9+p) = true := by
    rw [vl_gate gs L.hcl y p g atGate, isOr]
    change (g.inputs.map (vl gs y)).any id = true
    apply List.any_eq_true.mpr
    exact ⟨true, List.mem_map.mpr ⟨w.val, readsMate, (vl_input gs y w.val w.isLt).trans bit⟩, rfl⟩
  have agree := agree_B gs L.hcl lo hi (fun i => i = 2) (o+1)
    (by
      intro j hj away
      rw [vl_input gs lo j hj, vl_input gs hi j hj]
      have ne : (⟨j,hj⟩ : Fin 9) ≠ 2 := by intro e; exact away (congrArg Fin.val e)
      simp [lo,hi,Function.update_of_ne ne])
    (by
      rintro q gate pos _ _ ⟨a, mem, rfl⟩ _
      have eq : q = p := unique q ⟨gate, pos, mem⟩
      subst q
      exact (forced lo bitL).trans (forced hi bitH).symm)
  have out : o ≠ 2 := by
    intro eq
    obtain ⟨u, v, diff⟩ := variesTwo false
    apply diff
    rw [← L.hev, ← L.hev, eq, vl_input gs _ 2 (by decide), vl_input gs _ 2 (by decide)]
    simp
  exact hrow.2 ((L.hev lo).symm.trans ((agree o (by omega) out).trans (L.hev hi)))

end NineVertexTableTwo
