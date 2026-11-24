import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

namespace CubicBatch

-- Looking only at a prefix computes the same values on its existing wires.
private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private theorem run_len (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (_ ++ [_])).length = _
    rw [ih]
    simp
    omega

private theorem run_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem at_prefix (a b : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + a.length) :
    (run (a ++ b) x).getD i false = (run a x).getD i false := by
  change (List.foldl _ x (a ++ b)).getD i false = _
  rw [List.foldl_append]
  exact run_old b (run a x) i (by rwa [run_len])

private theorem before (n : ℕ) (C : Circuit) (t p i : ℕ) (ht : t < C.size)
    (hi : i < n+t) (x : Fin n → Bool) :
    ((eraseGate n C t p).wires (List.ofFn x)).getD i false =
      (C.wires (List.ofFn x)).getD i false := by
  have ht' : t < C.gates.length := ht
  have bound : i < (List.ofFn x).length + (C.gates.take t).length := by
    simpa [Nat.min_eq_left (Nat.le_of_lt ht')] using hi
  change (run (eraseGate n C t p).gates _).getD i false = (run C.gates _).getD i false
  conv_rhs => rw [← List.take_append_drop t C.gates, at_prefix _ _ _ i bound]
  simp only [eraseGate,ite_eq_left ht']
  exact at_prefix _ _ _ i bound

private theorem redirect_ne (n t p m i : ℕ) (hmt : m < t)
    (hp : p ≠ n+m) (hi : i ≠ n+m) : eraseRedirect n t p i ≠ n+m := by
  unfold eraseRedirect
  split <;> (first | exact hp | split <;> omega)

-- A semantic mark has a fixed, earlier representative on the prescribed rows.
-- A garbage mark can be read only by other marked gates and cannot be the output.
def Static (n : ℕ) (row : (Fin n → Bool) → (Fin n → Bool))
    (C : Circuit) (S : Finset ℕ) (p : ℕ → ℕ) : Prop :=
  ∀ m ∈ S, m < C.size ∧ p m < n+m ∧ (∀ j ∈ S, p m ≠ n+j) ∧
    ((∀ x, let w := C.wires (List.ofFn (row x)); w.getD (n+m) false = w.getD (p m) false) ∨
     (C.output ≠ n+m ∧ ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → j ∉ S → n+m ∉ g.inputs))

def Move (n : ℕ) (row : (Fin n → Bool) → (Fin n → Bool)) (C D : Circuit) : Prop :=
  ∃ m p, m < C.size ∧ p < n+m ∧ D = eraseGate n C m p ∧
    ((∀ x, let w := C.wires (List.ofFn (row x)); w.getD (n+m) false = w.getD p false) ∨
      (C.output ≠ n+m ∧ ∀ g ∈ C.gates.drop (m+1), n+m ∉ g.inputs))

-- With the largest mark gone, every earlier mark still has its original certificate.
private theorem peel (n : ℕ) (row : (Fin n → Bool) → (Fin n → Bool))
    (C : Circuit) (S : Finset ℕ) (p : ℕ → ℕ) (cert : Static n row C S p)
    (t : ℕ) (ht : t ∈ S) (top : ∀ j ∈ S, j ≤ t) :
    Move n row C (eraseGate n C t (p t)) ∧
    Static n row (eraseGate n C t (p t)) (S.erase t) p := by
  obtain ⟨bound,anchor,avoid,site⟩ := cert t ht
  have bt : t < C.gates.length := bound
  have len : (C.gates.take t).length = t := by simp [Nat.min_eq_left (Nat.le_of_lt bt)]
  constructor
  · refine ⟨t,p t,bound,anchor,rfl,?_⟩
    rcases site with eq | ⟨out,dead⟩
    · exact Or.inl eq
    · refine Or.inr ⟨out,?_⟩
      intro g hg
      obtain ⟨j,hj,hg'⟩ := List.getElem_of_mem hg
      apply dead (t+1+j) g
      · have e := (List.getElem?_eq_getElem hj).trans (congrArg some hg')
        simpa using e
      · intro h
        have := top _ h
        omega
  · intro m hm
    obtain ⟨hne,hs⟩ := Finset.mem_erase.mp hm
    have mt : m < t := lt_of_le_of_ne (top m hs) hne
    obtain ⟨_,pm,pmAvoid,cond⟩ := cert m hs
    refine ⟨?_,pm,(fun j hj => pmAvoid j (Finset.mem_of_mem_erase hj)),?_⟩
    · change m < (eraseGate n C t (p t)).gates.length
      simp [eraseGate,bt,len]
      omega
    rcases cond with eq | ⟨out,dead⟩
    · left
      intro x
      exact (before n C t (p t) (n+m) bound (by omega) (row x)).trans
        ((eq x).trans (before n C t (p t) (p m) bound (by omega) (row x)).symm)
    · right
      have avoidM := avoid m hs
      constructor
      · simpa [eraseGate,bt] using redirect_ne n t (p t) m C.output mt avoidM out
      · intro j g read clean
        simp only [eraseGate,ite_eq_left bt] at read
        by_cases hj : j < t
        · rw [List.getElem?_append_left (by simpa [len] using hj)] at read
          apply dead j g
          · simpa [List.getElem?_take,hj] using read
          · intro h
            exact clean (Finset.mem_erase.mpr ⟨by omega,h⟩)
        · rw [List.getElem?_append_right (by simp [len]; omega),len,
              List.getElem?_map,List.getElem?_drop] at read
          cases orig : C.gates[t+1+(j-t)]? with
          | none => simp [orig] at read
          | some original =>
            simp [orig] at read
            subst g
            have noRead := dead (t+1+(j-t)) original orig (by
              intro h
              have := top _ h
              omega)
            intro bad
            obtain ⟨i,mem,hit⟩ := List.mem_map.mp bad
            exact redirect_ne n t (p t) m i mt avoidM (by rintro rfl; exact noRead mem) hit

theorem batch (n : ℕ) (row : (Fin n → Bool) → (Fin n → Bool))
    (C : Circuit) (S : Finset ℕ) (p : ℕ → ℕ) (cert : Static n row C S p) :
    ∃ D : ℕ → Circuit, D 0 = C ∧ ∀ j < S.card, Move n row (D j) (D (j+1)) := by
  suffices claim : ∀ k (T : Finset ℕ) (B : Circuit), T.card = k → Static n row B T p →
      ∃ D : ℕ → Circuit, D 0 = B ∧ ∀ j < k, Move n row (D j) (D (j+1)) from
    claim _ S C rfl cert
  intro k
  induction k with
  | zero =>
    intro T B _ _
    exact ⟨fun _ => B,rfl,by omega⟩
  | succ k ih =>
    intro T B card ok
    have nonempty : T.Nonempty := Finset.card_pos.mp (by omega)
    let t := T.max' nonempty
    obtain ⟨first,rest⟩ := peel n row B T p ok t (T.max'_mem nonempty) (fun j hj => T.le_max' j hj)
    have remaining : (T.erase t).card = k := by
      rw [Finset.card_erase_of_mem (T.max'_mem nonempty),card]
      omega
    obtain ⟨tail,start,steps⟩ := ih (T.erase t) _ remaining rest
    refine ⟨fun j => Nat.casesOn j B tail,rfl,?_⟩
    intro j h
    cases j with
    | zero => simpa [start] using first
    | succ i => exact steps i (by omega)

end CubicBatch
