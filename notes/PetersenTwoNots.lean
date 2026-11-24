import PetersenRawFirstErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenSignedSlice
namespace PetersenTwoNots

private theorem simulate : ∀ (α : Type) (C : Circuit) (_hc : FanInTwo C) (s v : List (α → Bool)),
      (∀ b : Bool, (fun _ : α => b) ∈ s) →
      (∀ u ∈ v, u ∈ s ∧ (fun x => !(u x)) ∈ s) →
      ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ (C.gates.map Paid).sum ∧ ∀ x : α,
        (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) (s.map fun u => u x)).getD o false = C.eval (v.map fun u => u x) := by
  intro α C hc s v constants pins
  let a := v.map (fun f => (⟨f,false,false⟩ : Wire α))
  have base (b : Bool) : Good s (K b) := ⟨constants b,constants (!b)⟩
  have old : ∀ u ∈ a, Good s u := by
    intro u hu
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hu
    exact pins f hf
  obtain ⟨k,t,run,limit,good,_⟩ := fold C.gates (fun g hg => ⟨(hc g hg).1,(hc g hg).2⟩) s base a old
  let out := (C.gates.foldl step a).getD C.output (K false)
  have defaultValue : Good t (K false) := ⟨run.keep _ (base false).1,run.keep _ (base false).2⟩
  have output : Good t out := get_property _ _ _ _ defaultValue good
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem output.1
  obtain ⟨p,len,sim⟩ := run.program
  refine ⟨p,o,by rw [len]; exact limit,?_⟩
  intro x
  change (p.foldl addPair _).getD o false = _
  rw [sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  simpa only [out,a,List.map_map,Function.comp_def] using
    outputMap (fun u : Wire α => u.f x) rfl (fun _ _ => rfl) C a


private theorem unitBound (g : PEqualNP.CircuitLowerBounds.Gate) : Paid g ≤ 1 := by
  unfold Paid; split <;> (first | decide | split <;> decide)

private theorem free (g : PEqualNP.CircuitLowerBounds.Gate) (h : g.op = .not) : Paid g = 0 := by
  simp [Paid,h,GateOp.eval]

private theorem allBound (gs : List PEqualNP.CircuitLowerBounds.Gate) :
    (gs.map Paid).sum ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; have := unitBound g; omega

private theorem oneFree (gs : List PEqualNP.CircuitLowerBounds.Gate) (i : Fin gs.length)
    (hi : (gs.get i).op = .not) : (gs.map Paid).sum + 1 ≤ gs.length := by
  induction gs with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    obtain ⟨k,hk⟩ := i
    cases k with
    | zero =>
      have z := free g hi
      have := allBound gs
      omega
    | succ k =>
      have e := ih ⟨k,by simpa using hk⟩ hi
      have := unitBound g
      omega

private theorem twoFree (gs : List PEqualNP.CircuitLowerBounds.Gate) (i j : Fin gs.length)
    (lt : i < j) (hi : (gs.get i).op = .not) (hj : (gs.get j).op = .not) :
    (gs.map Paid).sum + 2 ≤ gs.length := by
  induction gs with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    obtain ⟨u,hu⟩ := i
    obtain ⟨v,hv⟩ := j
    change u<v at lt
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    cases v with
    | zero => omega
    | succ v =>
      have vv : v < gs.length := by simpa using hv
      cases u with
      | zero =>
        have z := free g hi
        have e := oneFree gs ⟨v,vv⟩ hj
        omega
      | succ u =>
        have uu : u < gs.length := by simpa using hu
        have e := ih ⟨u,uu⟩ ⟨v,vv⟩ (show u<v by omega) hi hj
        have := unitBound g
        omega

theorem compile : ∀ (n : ℕ) (C : Circuit), FanInTwo C →
      (∃ i j : Fin C.gates.length, i < j ∧ (C.gates.get i).op = .not ∧ (C.gates.get j).op = .not) →
      ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length + 2 ≤ C.size ∧ ∀ x : Fin n → Bool,
        (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false = C.eval (List.ofFn x) := by
  intro n C hc ⟨i,j,lt,hi,hj⟩
  let inputs := List.ofFn (fun k : Fin n => fun x : Fin n → Bool => x k)
  let raw := [(fun _ : Fin n → Bool => false),(fun _ : Fin n → Bool => true)] ++ inputs ++ inputs.map (fun u x => !(u x))
  have constants (b : Bool) : (fun _ : Fin n → Bool => b) ∈ raw := by
    cases b <;> simp [raw]
  have pins : ∀ u ∈ inputs, u ∈ raw ∧ (fun x => !(u x)) ∈ raw := by
    intro u hu
    exact ⟨List.mem_append_left _ (List.mem_append_right _ hu),
      List.mem_append_right _ (List.mem_map.mpr ⟨u,hu,rfl⟩)⟩
  obtain ⟨p,o,cap,good⟩ := simulate (Fin n → Bool) C hc raw inputs constants pins
  have bound := twoFree C.gates i j lt hi hj
  refine ⟨p,o,by unfold Circuit.size; omega,?_⟩
  intro x
  have val := good x
  simpa [raw,inputs,List.map_ofFn,List.map_map,Function.comp_def] using val

open PetersenFirstSignedCut PetersenRawFirstErase in
theorem restrict : let can := fun (n : ℕ) (f : (Fin 9 → Bool) → Bool) =>
      ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ n ∧ ∀ x : Fin 9 → Bool,
        (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false = f x
      can 13 (fun x => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      can 10 (fun x => ([(1,2),(2,3),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) := by
  dsimp only
  rintro ⟨p,o,sz,hit⟩
  have h : Can pool 13 graph := ⟨p,o,sz,fun x => by rw [poolAt]; exact hit x⟩
  obtain ⟨v,low⟩ := restriction 13 h
  obtain ⟨q,k,cap,good⟩ := thetaOfDeletion v low
  refine ⟨q,k,cap,fun x => ?_⟩
  have g := good x
  rw [poolAt] at g
  apply g.trans
  simp [theta,deletion,graph,fixed,Function.update]

end PetersenTwoNots
