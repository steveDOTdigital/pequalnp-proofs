import PetersenSignedSlice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenSignedSlice
namespace PetersenSignedInputs

theorem compile : ∀ (α : Type) (C : Circuit) (_hc : FanInTwo C) (s v : List (α → Bool)),
      (∀ b : Bool, (fun _ : α => b) ∈ s) →
      (∀ u ∈ v, u ∈ s ∧ (fun x => !(u x)) ∈ s) →
      ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ C.size ∧ ∀ x : α,
        (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) (s.map fun u => u x)).getD o false = C.eval (v.map fun u => u x) := by
  intro α C hc s v constants pins
  let a := v.map (fun f => (⟨f,false,false⟩ : Wire α))
  have base (b : Bool) : Good s (K b) := ⟨constants b,constants (!b)⟩
  have old : ∀ u ∈ a, Good s u := by
    intro u hu
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hu
    exact pins f hf
  have cap (gs : List Gate) : (gs.map Paid).sum ≤ gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have one : Paid g ≤ 1 := by unfold Paid; split <;> (first | decide | split <;> decide)
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
  obtain ⟨k,t,run,limit,good,_⟩ := fold C.gates (fun g hg => ⟨(hc g hg).1,(hc g hg).2⟩) s base a old
  let out := (C.gates.foldl step a).getD C.output (K false)
  have defaultValue : Good t (K false) := ⟨run.keep _ (base false).1,run.keep _ (base false).2⟩
  have output : Good t out := get_property _ _ _ _ defaultValue good
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem output.1
  obtain ⟨p,len,sim⟩ := run.program
  refine ⟨p,o,by rw [len]; exact limit.trans (cap C.gates),?_⟩
  intro x
  change (p.foldl addPair _).getD o false = _
  rw [sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  simpa only [out,a,List.map_map,Function.comp_def] using
    outputMap (fun u : Wire α => u.f x) rfl (fun _ _ => rfl) C a

end PetersenSignedInputs
