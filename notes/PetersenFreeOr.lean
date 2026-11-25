import PetersenSignedSlice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenSignedSlice

namespace PetersenFreeOr

abbrev Input := Fin 10 → Bool

def graph (x : Input) : Bool :=
  ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any
      (fun e => x e.1 && x e.2)

def initial (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not

-- On the legal basis this predicate recognizes exactly NOT, with any arity.
def notCount (gs : List Gate) := gs.countP fun g => g.op.eval [false]

private theorem paidAndNot (gs : List Gate) :
    (gs.map Paid).sum + notCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [notCount]
  | cons g gs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    unfold notCount at *
    simp only [List.countP_cons]
    by_cases neg : g.op.eval [false] = true
    · simp [neg, Paid] at *
      omega
    · by_cases two : g.inputs.length = 2 <;> simp [neg, two, Paid] at * <;> omega

-- Give the free OR one paid signed gate, retaining arbitrary input wiring.
theorem compileHint (C : Circuit) (wiring : Fin 10 → Fin 10) (legal : FanInTwo C) :
    ∃ (p : List (ℕ × ℕ)) (o : ℕ),
      p.length + notCount C.gates ≤ C.size + 1 ∧
      ∀ x : Input, (p.foldl addPair (initial x)).getD o false =
        C.eval (List.ofFn (x ∘ wiring) ++ [x 0 || x 2]) := by
  let coord := fun (j : Fin 10) (x : Input) => x j
  let raws := List.ofFn coord
  let s := [(fun _ : Input => false),(fun _ : Input => true)] ++ raws ++ raws.map inv
  have pos (j : Fin 10) : coord j ∈ s :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
  have negMem (j : Fin 10) : inv (coord j) ∈ s :=
    List.mem_append_right _ (List.mem_map_of_mem (List.mem_ofFn.mpr ⟨j,rfl⟩))
  let nor := meet (inv (coord 0)) (inv (coord 2))
  let pool := s ++ [nor, inv nor]
  have first : Run s 1 pool := Run.gate Run.nil (negMem 0) (negMem 2)
  let raw := fun (j : Fin 10) => (⟨coord (wiring j),false,false⟩ : Wire Input)
  let hint := (⟨fun x : Input => x 0 || x 2,false,false⟩ : Wire Input)
  let pins := List.ofFn raw ++ [hint]
  have constants (b : Bool) : Good pool (K b) := by
    have mem (t : Bool) : (fun _ : Input => t) ∈ s := by cases t <;> simp [s]
    exact ⟨first.keep _ (mem b),first.keep _ (mem (!b))⟩
  have hintPos : hint.f = inv nor := by funext x; simp [hint,nor,meet,inv,coord]
  have hintNeg : inv hint.f = nor := by funext x; simp [hint,nor,meet,inv,coord]
  have old : ∀ u ∈ pins, Good pool u := by
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
      exact ⟨first.keep _ (pos _),first.keep _ (negMem _)⟩
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨List.mem_append_right _ (by simp [hintPos]),List.mem_append_right _ (by simp [hintNeg])⟩
  obtain ⟨k,t,run,le,ok,_⟩ := fold C.gates legal pool constants pins old
  let out := (C.gates.foldl step pins).getD C.output (K false)
  have base : Good t (K false) := ⟨run.keep _ (constants false).1,run.keep _ (constants false).2⟩
  have usable : Good t out := get_property _ _ _ _ base ok
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem usable.1
  obtain ⟨p,len,sim⟩ := (first.comp run).program
  have budget := paidAndNot C.gates
  refine ⟨p,o,by rw [len]; change 1 + k + notCount C.gates ≤ C.gates.length + 1; omega,?_⟩
  intro x
  have start : s.map (fun f => f x) = initial x := by
    simp only [s,raws,initial,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← start,sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  simpa only [out,pins,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,raw,coord,hint,
    Function.comp_def] using outputMap (fun u : Wire Input => u.f x) rfl (fun _ _ => rfl) C pins

theorem atMostTwoNots
    (lower : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 16 → ∃ x : Input,
      (p.foldl addPair (initial x)).getD o false ≠ graph x)
    (C : Circuit) (wiring : Fin 10 → Fin 10) (legal : FanInTwo C) (size : C.size ≤ 18)
    (correct : ∀ x : Input, C.eval (List.ofFn (x ∘ wiring) ++ [x 0 || x 2]) = graph x) :
    notCount C.gates ≤ 2 := by
  obtain ⟨p,o,budget,eval⟩ := compileHint C wiring legal
  by_contra! many
  obtain ⟨x,miss⟩ := lower p o (by omega)
  exact miss ((eval x).trans (correct x))

end PetersenFreeOr
