import SignedCofactorPrefixes
import SignedConstantCount

namespace PrismSignedFrontier

def countedCut (mask : W) (patterns : List W) (bound budget : Nat) (s : List W) : Bool :=
  s.all (fun w => patterns.contains (w &&& mask)) &&
    decide (budget < bound + (s.filter (fun w => (w &&& mask) == 0 || (w &&& mask) == mask)).toFinset.card)

structure CountCertificate (g : W) where
  mask : W
  patterns : List W
  bound : Nat
  sound : ∀ budget s {k}, k ≤ budget → Cone g k s.toFinset →
    countedCut mask patterns bound budget s = false

theorem countedCut_sound (f : Fin 64 → Fin 64) (mask : W) (base raw : List W)
    (g : W) (bound budget : Nat) (s : List W)
    (cover : ∀ i, mask.getLsbD (f i).val = true)
    (stock : ∀ w ∈ base, signedMap f w ∈ raw)
    (nz : signedMap f g ≠ 0) (low : signedLower (signedMap f g) raw bound)
    {k : Nat} (small : k ≤ budget) (run : Cone g k s.toFinset) :
    countedCut mask (base.map (· &&& mask)) bound budget s = false := by
  by_contra! fail
  have yes : countedCut mask (base.map (· &&& mask)) bound budget s = true := by simpa using fail
  obtain ⟨pattern, cutoff⟩ := Bool.and_eq_true_iff.mp yes
  have sub : s.toFinset.image (signedMap f) ⊆ insert 0 raw.toFinset := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    have test := List.all_eq_true.mp pattern v (List.mem_toFinset.mp hv)
    obtain ⟨u,hu,eq⟩ := List.mem_map.mp (List.contains_iff_mem.mp test)
    have close := signedMap_eq_of_mask f mask u v cover eq
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (close ▸ stock u hu))
  have constant : (s.filter (fun w => (w &&& mask) == 0 || (w &&& mask) == mask)).toFinset ⊆
      s.toFinset.filter (fun w => signedMap f w = 0) := by
    intro w hw
    obtain ⟨inside,bit⟩ := List.mem_filter.mp (List.mem_toFinset.mp hw)
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr inside,?_⟩
    rcases Bool.or_eq_true_iff.mp bit with a | b
    · have eq : w &&& mask = (0 : W) &&& mask := by simpa using a
      exact (signedMap_eq_of_mask f mask w 0 cover eq).trans (signedMap_zero f)
    · have eq : w &&& mask = (~~~(0 : W)) &&& mask := by
        change w &&& mask = BitVec.allOnes 64 &&& mask
        rw [BitVec.allOnes_and]
        exact beq_iff_eq.mp b
      exact (signedMap_eq_of_mask f mask w _ cover eq).trans (signedMap_ones f)
  obtain ⟨j,t,price,exec,inside⟩ := run.project_count (signedMap f) (signedMap_choice f) nz
  have lb := low exec (inside.trans sub)
  have cc := Finset.card_le_card constant
  unfold zeroCount at price
  have threshold := of_decide_eq_true cutoff
  omega

def countedPrefixCertificate (g goal mask : W) (f : Fin 64 → Fin 64) (base raw : List W)
    (n : Nat) (low : signedLower goal raw n) (nz : goal ≠ 0)
    (cover : ∀ i, mask.getLsbD (f i).val = true) (goalEq : signedMap f g = goal)
    (start : available (base.map (rowMap f)) ⊆ insert 0 raw.toFinset)
    (p : List (Nat × Nat)) : CountCertificate g :=
  let ws := p.foldl add base
  let supplied := ws.map (signedMap f)
  { mask := mask
    patterns := ws.map (· &&& mask)
    bound := n - p.length
    sound := by
      intro budget s k le run
      apply countedCut_sound f mask ws supplied g _ budget s cover _ _ _ le run
      · intro w hw
        exact List.mem_map_of_mem hw
      · rw [goalEq]
        exact nz
      · rw [goalEq]
        apply signedLower_after_prefix goal raw _ supplied n (@low) start p
        rw [←rowMap_prefix]
        simp only [available,List.map_map]
        rfl }

end PrismSignedFrontier
