import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PlaneTerminalCover

def combine (isAnd a b : Bool) := if isAnd then a && b else a || b

def grow (n : ℕ) (isAnd : Bool) (C : Circuit) (w : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨if isAnd then .and else .or,[C.output,w]⟩], n+C.size⟩

theorem wire_length (C : Circuit) (x : List Bool) : (C.wires x).length = x.length+C.size := by
  obtain ⟨gs,o⟩ := C
  induction gs generalizing x with
  | nil => simp [Circuit.wires,Circuit.size]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs,o⟩ (x++[_])).length = _
    rw [ih]
    simp [Circuit.size,Nat.add_comm,Nat.add_left_comm]

theorem grow_wires (n : ℕ) (b : Bool) (C : Circuit) (w : ℕ) (x : List Bool) :
    (grow n b C w).wires x = C.wires x ++ [combine b (C.eval x) ((C.wires x).getD w false)] := by
  cases b <;> simp [grow,Circuit.eval,Circuit.wires,List.foldl_append,GateOp.eval,combine]

theorem grow_mono (n : ℕ) (b : Bool) (C : Circuit) (w : ℕ) (h : Monotone2 C) :
    Monotone2 (grow n b C w) := by
  intro g hg
  change g ∈ C.gates ++ [_] at hg
  rcases List.mem_append.mp hg with old|last
  · exact h g old
  · obtain rfl := List.mem_singleton.mp last
    cases b <;> simp

theorem grow_size (n : ℕ) (b : Bool) (C : Circuit) (w : ℕ) : (grow n b C w).size = C.size+1 := by
  simp [grow,Circuit.size]

theorem fold_same (ws : List ℕ) (f g : ℕ → Bool) (b a : Bool)
    (same : ∀ v ∈ ws, f v = g v) :
    ws.foldl (fun s v => combine b s (f v)) a = ws.foldl (fun s v => combine b s (g v)) a := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons,same w (by simp)]
    exact ih _ (fun v hv => same v (List.mem_cons_of_mem _ hv))

theorem gather (n : ℕ) (b : Bool) (C : Circuit) (ws : List ℕ)
    (mono : Monotone2 C) (valid : ∀ w ∈ ws, w < n+C.size) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size+ws.length ∧
      ∀ x : List Bool, x.length=n →
        D.eval x = ws.foldl (fun a w => combine b a ((C.wires x).getD w false)) (C.eval x) := by
  induction ws generalizing C with
  | nil => exact ⟨C,mono,by simp,fun _ _ => rfl⟩
  | cons w ws ih =>
    let E := grow n b C w
    have sz : E.size=C.size+1 := grow_size _ _ _ _
    have bound : ∀ v ∈ ws, v<n+E.size := by
      intro v hv
      have := valid v (List.mem_cons_of_mem _ hv)
      omega
    obtain ⟨D,md,sd,eq⟩ := ih E (grow_mono _ _ _ _ mono) bound
    refine ⟨D,md,by rw [sd,sz,List.length_cons]; omega,?_⟩
    intro x hx
    have len : (C.wires x).length = n+C.size := by rw [wire_length,hx]
    have val : E.eval x = combine b (C.eval x) ((C.wires x).getD w false) := by
      change ((grow n b C w).wires x).getD (n+C.size) false = _
      rw [grow_wires,← len]
      simp
    have same : ∀ v ∈ ws, (E.wires x).getD v false = (C.wires x).getD v false := by
      intro v hv
      change ((grow n b C w).wires x).getD v false = _
      rw [grow_wires,List.getD_append _ _ _ _ (by rw [len]; exact valid v (List.mem_cons_of_mem _ hv))]
    rw [eq x hx,val,List.foldl_cons]
    exact fold_same ws _ _ _ _ same

theorem assemble : ∀ (n : ℕ) (C : Circuit) (ws : List ℕ) (b : Bool),
    Monotone2 C → ws ≠ [] → (∀ i ∈ ws, i < n+C.size) →
    ∃ D : Circuit, Monotone2 D ∧ D.size+1 = C.size+ws.length ∧ ∀ x : List Bool, x.length=n →
      D.eval x = if b then ws.all (fun i => (C.wires x).getD i false)
        else ws.any (fun i => (C.wires x).getD i false) := by
  intro n C ws b mono nonempty valid
  cases ws with
  | nil => contradiction
  | cons a ws =>
    let E : Circuit := ⟨C.gates,a⟩
    have h := gather n b E ws mono (fun v hv => valid v (List.mem_cons_of_mem _ hv))
    obtain ⟨D,md,sz,eq⟩ := h
    refine ⟨D,md,?_,?_⟩
    · change D.size+1 = C.size+(ws.length+1)
      change D.size=C.size+ws.length at sz
      omega
    intro x hx
    rw [eq x hx]
    let f := fun i => (C.wires x).getD i false
    change ws.foldl (fun z i => combine b z (f i)) (f a) =
      if b then (a::ws).all f else (a::ws).any f
    have fold (ys : List ℕ) (z : Bool) :
        ys.foldl (fun val i => combine b val (f i)) z =
        if b then z && ys.all f else z || ys.any f := by
      induction ys generalizing z with
      | nil => cases b <;> simp [combine]
      | cons y ys ih => rw [List.foldl_cons,ih]; cases b <;> simp [combine,Bool.and_assoc,Bool.or_assoc]
    rw [fold]
    cases b <;> rfl

end PlaneTerminalCover
