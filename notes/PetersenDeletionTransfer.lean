import PetersenBinaryBudget
import PetersenSignedSlice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- At least two gates disappear between the original circuit and a signed
-- program for vertex deletion. Any improved deletion bound transfers directly.
set_option maxHeartbeats 4000000 in
theorem PetersenDeletionTransfer.flipped (limit : ℕ)
    (lower : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ limit → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(2,7),(3,8),(5,7),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ limit + 2 → ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval ((List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ))]).set ↑x2 !x8 x2) ≠ x1 x8 := by
  let budget := PetersenBinaryBudget.strict
  let slice := PetersenSignedSlice.compile
  let graph := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let deleted := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(2,7),(3,8),(5,7),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let pins := fun (i : Fin 9) (x : Fin 9 → Bool) => (List.ofFn x ++ [x 0 || x 6]).set i.val (!(x i))
  intro target i C nz ns hc tiny
  change ∃ x : Fin 9 → Bool, C.eval (pins i x) ≠ graph x
  by_contra! correct
  let neighbor : Fin 9 → Fin 9 := ![1,0,1,2,0,0,1,2,3]
  let point := fun j : Fin 9 => decide (j=neighbor i)
  let edge := fun j : Fin 9 => decide (j=i ∨ j=neighbor i)
  have yes : graph edge = true := by
    fin_cases i <;> decide
  have no : graph point = false := by
    fin_cases i <;> decide
  let wire := fun (x : Fin 9 → Bool) (j : Fin 10) =>
    if h : j.val < 9 then (if j.val = i.val then !(x i) else x ⟨j.val,h⟩) else (x 0 || x 6)
  have pinList (x : Fin 9 → Bool) : List.ofFn (wire x) = pins i x := by
    fin_cases i <;> simp [pins,wire,List.set]
  have inc : ∀ j : Fin 10, wire edge j = true → wire point j = true := by
    fin_cases i <;> first | contradiction | decide
  have ordered (j : ℕ) : (pins i edge).getD j false = true → (pins i point).getD j false = true := by
    rw [← pinList edge,← pinList point]
    by_cases hj : j < 10
    · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getD_eq_getElem _ _ (by simpa using hj)]
      simpa only [List.getElem_ofFn] using inc ⟨j,hj⟩
    · rw [List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt hj)),List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt hj))]
      exact id
  have less := budget C hc (pins i edge) (pins i point) (by simp [pins]) ordered
    ((correct edge).trans yes) ((correct point).trans no)
  let erase := fun (x : Fin 9 → Bool) (v : Fin 9) => if v=6 then false else x v
  let a := fun j : Fin 9 => decide (j=0 ∨ j=8)
  let b := fun j : Fin 9 => decide (j=0 ∨ j=6 ∨ j=8)
  let v := List.ofFn (fun j : Fin 10 => ((fun x : Fin 9 → Bool => wire (erase x) j),wire a j,wire b j))
  let raws := List.ofFn (fun j : Fin 9 => (fun x : Fin 9 → Bool => x j))
  let s := [(fun _ : Fin 9 → Bool => false),(fun _ : Fin 9 → Bool => true)] ++ raws ++ raws.map (fun f x => !(f x))
  have constants (bit : Bool) : (fun _ : Fin 9 → Bool => bit) ∈ s := by
    cases bit <;> simp [s]
  have pos (j : Fin 9) : (fun x : Fin 9 → Bool => x j) ∈ s := by
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  have neg (j : Fin 9) : (fun x : Fin 9 → Bool => !(x j)) ∈ s := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,rfl⟩
  have data : ∀ t ∈ v, t.1 ∈ s ∧ (fun x => !(t.1 x)) ∈ s ∧
      ((∃ bit, ∀ x, t.1 x=bit) ∨ t.2.1=t.2.2) := by
    intro t ht
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    by_cases last : j.val < 9
    · by_cases same : j.val = i.val
      · have hi : i ≠ 6 := ns
        simp only [wire,same,i.isLt,↓reduceDIte,ite_true,erase,hi,ite_false,Bool.not_not]
        exact ⟨neg i,pos i,Or.inr (by simp [a,b,hi])⟩
      · let k : Fin 9 := ⟨j.val,last⟩
        by_cases six : k = 6
        · have j6 : (⟨j.val,last⟩ : Fin 9) = 6 := six
          simp only [wire,last,↓reduceDIte,same,ite_false,erase,j6,ite_true,Bool.not_false]
          exact ⟨constants false,constants true,Or.inl ⟨false,fun _ => rfl⟩⟩
        · change (⟨j.val,last⟩ : Fin 9) ≠ 6 at six
          simp only [wire,last,↓reduceDIte,same,ite_false,erase,six]
          exact ⟨pos k,neg k,Or.inr (by simp [a,b,six])⟩
    · simp [wire,last,erase,a,b]
      exact ⟨pos 0,neg 0⟩
  have mapped (x : Fin 9 → Bool) : v.map (fun t => t.1 x) = pins i (erase x) := by
    rw [← pinList]; simp only [v,List.map_ofFn]; rfl
  have lo : v.map (fun t => t.2.1) = pins i a := by
    rw [← pinList]; simp only [v,List.map_ofFn]; rfl
  have hi : v.map (fun t => t.2.2) = pins i b := by
    rw [← pinList]; simp only [v,List.map_ofFn]; rfl
  have varies : ¬∃ bit : Bool, ∀ x : Fin 9 → Bool, C.eval (v.map fun t => t.1 x) = bit := by
    rintro ⟨bit,values⟩
    have h0 := values (fun _ => false)
    have h1 := values (fun _ => true)
    rw [mapped,correct] at h0 h1
    change false = bit at h0
    change true = bit at h1
    exact Bool.false_ne_true (h0.trans h1.symm)
  have sens : C.eval (v.map fun t => t.2.1) ≠ C.eval (v.map fun t => t.2.2) := by
    rw [lo,hi,correct,correct]
    decide
  obtain ⟨p,o,cost,computes⟩ := slice (Fin 9 → Bool) C hc s v constants data varies sens
  obtain ⟨x,miss⟩ := lower p o (by omega)
  have pool : s.map (fun f => f x) = [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not := by
    simp only [s,raws,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  have matched := computes x
  rw [pool,mapped,correct] at matched
  apply miss
  apply matched.trans
  simp [graph,erase]
