import PetersenSignedSlice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenSignedSlice
namespace PetersenRawNormal

private theorem count (gs : List Gate) (legal : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (gs.map Paid).sum ≤ gs.length ∧ ((gs.map Paid).sum = gs.length →
      ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨limit,saturated⟩ := ih (fun k hk => legal k (List.mem_cons_of_mem g hk))
    have cap : Paid g ≤ 1 := by unfold Paid; split <;> (first | decide | split <;> decide)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    refine ⟨by omega,?_⟩
    intro eq k hk
    rcases List.mem_cons.mp hk with rfl | tail
    · have unit : Paid k = 1 := by omega
      obtain ha | ho | hn := legal k (by simp)
      · exact ⟨Or.inl ha, by simpa [Paid,ha,GateOp.eval] using unit⟩
      · exact ⟨Or.inr ho, by simpa [Paid,ho,GateOp.eval] using unit⟩
      · simp [Paid,hn,GateOp.eval] at unit
    · exact saturated (by omega) k tail

theorem normalize (n : ℕ) (C : Circuit) (hc : FanInTwo C) :
    (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length < C.size ∧ ∀ x : Fin n → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false =
      circuitFun n C x := by
  obtain ⟨cap,saturated⟩ := count C.gates (fun g hg => (hc g hg).1)
  by_cases eq : (C.gates.map Paid).sum = C.size
  · exact Or.inl (saturated eq)
  right
  let raws := List.ofFn (fun j : Fin n => fun x : Fin n → Bool => x j)
  let s := [(fun _ : Fin n → Bool => false),(fun _ : Fin n → Bool => true)] ++ raws ++ raws.map inv
  let a := List.ofFn (fun j : Fin n => (⟨fun x : Fin n → Bool => x j,false,false⟩ : Wire (Fin n → Bool)))
  have memK (b : Bool) : (fun _ : Fin n → Bool => b) ∈ s := by cases b <;> simp [s]
  have constants (b : Bool) : Good s (K b) := ⟨memK b,memK (!b)⟩
  have old : ∀ u ∈ a, Good s u := by
    intro u hu
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hu
    have pos : (fun x : Fin n → Bool => x j) ∈ raws := List.mem_ofFn.mpr ⟨j,rfl⟩
    exact ⟨List.mem_append_left _ (List.mem_append_right _ pos),List.mem_append_right _ (List.mem_map_of_mem pos)⟩
  obtain ⟨k,t,run,le,ok,_⟩ := fold C.gates (fun g hg => ⟨(hc g hg).1,(hc g hg).2⟩) s constants a old
  let out := (C.gates.foldl step a).getD C.output (K false)
  have base : Good t (K false) := ⟨run.keep _ (constants false).1,run.keep _ (constants false).2⟩
  have found : Good t out := get_property _ _ _ _ base ok
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem found.1
  obtain ⟨p,len,sim⟩ := run.program
  refine ⟨p,o,by rw [len]; change (C.gates.map Paid).sum ≠ C.gates.length at eq; change k < C.gates.length; omega,?_⟩
  intro x
  have pool : s.map (fun f => f x) = [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not := by
    simp only [s,raws,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  change (p.foldl addPair _).getD o false = _
  rw [← pool,sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  have h := outputMap (fun u : Wire (Fin n → Bool) => u.f x) rfl (fun _ _ => rfl) C a
  simpa only [out,a,List.map_ofFn,Function.comp_def,circuitFun] using h

end PetersenRawNormal
