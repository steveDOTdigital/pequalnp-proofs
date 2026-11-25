import PetersenFreeOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PetersenSignedSlice PetersenFreeOr

namespace PetersenUnaryInput

theorem unaryChoices (f : Bool → Bool) :
    f = (fun _ => false) ∨ f = (fun _ => true) ∨ f = id ∨ f = Bool.not := by
  cases a : f false <;> cases b : f true
  · left; funext x; cases x <;> assumption
  · right; right; left; funext x; cases x <;> assumption
  · right; right; right; funext x; cases x <;> assumption
  · right; left; funext x; cases x <;> assumption

private theorem pay (gs : List Gate) : (gs.map Paid).sum + notCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [notCount]
  | cons g gs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    unfold notCount at *
    simp only [List.countP_cons]
    by_cases h : g.op.eval [false] = true
    · simp [h,Paid] at *
      omega
    · by_cases t : g.inputs.length = 2 <;> simp [h,t,Paid] at * <;> omega

theorem compileUnary (C : Circuit) (w : Fin 10 → Fin 10) (f : Bool → Bool)
    (legal : FanInTwo C) :
    ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length + notCount C.gates ≤ C.size ∧
      ∀ x : Input, (p.foldl addPair (initial x)).getD o false =
        C.eval (List.ofFn (x ∘ w) ++ [f (x 0)]) := by
  let coord := fun (j : Fin 10) (x : Input) => x j
  let raws := List.ofFn coord
  let s := [(fun _ : Input => false),(fun _ : Input => true)] ++ raws ++ raws.map inv
  have pos (j : Fin 10) : coord j ∈ s :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
  have negMem (j : Fin 10) : inv (coord j) ∈ s :=
    List.mem_append_right _ (List.mem_map_of_mem (List.mem_ofFn.mpr ⟨j,rfl⟩))
  have constants (b : Bool) : Good s (K b) := by
    have mem (t : Bool) : (fun _ : Input => t) ∈ s := by cases t <;> simp [s]
    exact ⟨mem b,mem (!b)⟩
  let raw := fun (j : Fin 10) => (⟨coord (w j),false,false⟩ : Wire Input)
  let hint := (⟨fun x : Input => f (x 0),false,false⟩ : Wire Input)
  let pins := List.ofFn raw ++ [hint]
  have old : ∀ u ∈ pins, Good s u := by
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
      exact ⟨pos _,negMem _⟩
    · obtain rfl := List.mem_singleton.mp h
      rcases unaryChoices f with hf | hf | hf | hf
      · exact ⟨by simpa [hint,hf,PetersenSignedSlice.K,PetersenSignedSlice.inv] using (constants false).1,
          by simpa [hint,hf,PetersenSignedSlice.K,PetersenSignedSlice.inv] using (constants false).2⟩
      · exact ⟨by simpa [hint,hf,PetersenSignedSlice.K,PetersenSignedSlice.inv] using (constants true).1,
          by simpa [hint,hf,PetersenSignedSlice.K,PetersenSignedSlice.inv] using (constants true).2⟩
      · exact ⟨by simpa [hint,hf,coord] using pos 0,
          by simpa [hint,hf,coord] using negMem 0⟩
      · have ep : hint.f = PetersenSignedSlice.inv (coord 0) := by funext x; simp [hint,hf,coord,PetersenSignedSlice.inv]
        have en : PetersenSignedSlice.inv hint.f = coord 0 := by funext x; simp [hint,hf,coord,PetersenSignedSlice.inv]
        exact ⟨ep ▸ negMem 0,en ▸ pos 0⟩
  obtain ⟨k,t,run,le,ok,_⟩ := fold C.gates legal s constants pins old
  let out := (C.gates.foldl step pins).getD C.output (K false)
  have base : Good t (K false) := ⟨run.keep _ (constants false).1,run.keep _ (constants false).2⟩
  have usable : Good t out := get_property _ _ _ _ base ok
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem usable.1
  obtain ⟨p,len,sim⟩ := run.program
  have budget := pay C.gates
  refine ⟨p,o,by rw [len]; change k + notCount C.gates ≤ C.gates.length; omega,?_⟩
  intro x
  have start : s.map (fun h => h x) = initial x := by
    simp only [s,raws,initial,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← start,sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  simpa only [out,pins,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,raw,coord,hint,
    Function.comp_def] using outputMap (fun u : Wire Input => u.f x) rfl (fun _ _ => rfl) C pins

def canonical (x : Input) := List.ofFn x ++ [!x 0,false,true]

def renumber (w : Fin 10 → Fin 10) (f : Bool → Bool) (i : ℕ) : ℕ :=
  if h : i < 10 then (w ⟨i,h⟩).val else if i = 10 then
    if f false then (if f true then 12 else 10) else (if f true then 0 else 11)
  else 13 + (i-11)

def rewriteGate (w : Fin 10 → Fin 10) (f : Bool → Bool) (g : Gate) : Gate :=
  { g with inputs := g.inputs.map (renumber w f) }

def rewriteCircuit (w : Fin 10 → Fin 10) (f : Bool → Bool) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rewriteGate w f), renumber w f C.output⟩

private theorem readWire (x : Input) (w : Fin 10 → Fin 10) (f : Bool → Bool)
    (tail : List Bool) (i : ℕ) :
    (canonical x ++ tail).getD (renumber w f i) false =
      ((List.ofFn (x ∘ w) ++ [f (x 0)]) ++ tail).getD i false := by
  by_cases h : i < 10
  · have hw := (w ⟨i,h⟩).isLt
    simp only [canonical,renumber,dite_eq_left h,List.append_assoc]
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hw),
        List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using h)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    simp [h,hw]
  · by_cases j : i = 10
    · subst i
      rcases unaryChoices f with rfl | rfl | rfl | rfl <;>
        simp [renumber,canonical,List.getD_eq_getElem?_getD,
          Function.comp_def]
    · rw [List.getD_append_right _ _ _ _ (by simp [canonical,renumber,h,j]),
          List.getD_append_right _ _ _ _ (by simp; omega)]
      simp [canonical,renumber,h,j]

private def advance (xs : List Bool) (g : Gate) :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private theorem appendFold (x : Input) (w : Fin 10 → Fin 10) (f : Bool → Bool)
    (gs : List Gate) (tail : List Bool) :
    ∃ ys, (gs.map (rewriteGate w f)).foldl advance (canonical x ++ tail) = canonical x ++ ys ∧
      gs.foldl advance ((List.ofFn (x ∘ w) ++ [f (x 0)]) ++ tail) =
        (List.ofFn (x ∘ w) ++ [f (x 0)]) ++ ys := by
  induction gs generalizing tail with
  | nil => exact ⟨tail,rfl,rfl⟩
  | cons g gs ih =>
    let val := g.op.eval (g.inputs.map fun i =>
      ((List.ofFn (x ∘ w) ++ [f (x 0)]) ++ tail).getD i false)
    have same : advance (canonical x ++ tail) (rewriteGate w f g) = canonical x ++ (tail ++ [val]) := by
      simp only [advance,rewriteGate,List.map_map,Function.comp_def,readWire,List.append_assoc,val]
    have orig : advance ((List.ofFn (x ∘ w) ++ [f (x 0)]) ++ tail) g =
        (List.ofFn (x ∘ w) ++ [f (x 0)]) ++ (tail ++ [val]) := by simp [advance,val]
    simpa only [List.map_cons,List.foldl_cons,same,orig] using ih (tail ++ [val])

theorem rewriteEval (C : Circuit) (w : Fin 10 → Fin 10) (f : Bool → Bool) (x : Input) :
    (rewriteCircuit w f C).eval (canonical x) = C.eval (List.ofFn (x ∘ w) ++ [f (x 0)]) := by
  obtain ⟨ys,h,k⟩ := appendFold x w f C.gates []
  simp only [List.append_nil] at h k
  change ((C.gates.map (rewriteGate w f)).foldl advance _).getD _ _ =
    (C.gates.foldl advance _).getD _ _
  rw [h,k]
  exact readWire x w f ys C.output

theorem deskFromSearches
    (signed : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 17 → ∃ x : Input,
      (p.foldl addPair (initial x)).getD o false ≠ graph x)
    (positive : ∀ D : Circuit, Monotone2 D → D.size ≤ 18 → ∃ x : Input,
      D.eval (canonical x) ≠ graph x)
    (C : Circuit) (w : Fin 10 → Fin 10) (f : Bool → Bool)
    (legal : FanInTwo C) (size : C.size ≤ 18) :
    ∃ x : Input, C.eval (List.ofFn (x ∘ w) ++ [f (x 0)]) ≠ graph x := by
  by_contra! correct
  obtain ⟨p,o,budget,eval⟩ := compileUnary C w f legal
  have nopaid : notCount C.gates = 0 := by
    by_contra! paid
    obtain ⟨x,h⟩ := signed p o (by omega)
    exact h ((eval x).trans (correct x))
  have mono : Monotone2 (rewriteCircuit w f C) := by
    intro g hg
    obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hg
    obtain ⟨kind,arity⟩ := legal old mem
    have off : old.op.eval [false] ≠ true := by
      intro on
      have hh : 0 < C.gates.countP (fun g => g.op.eval [false]) :=
        List.countP_pos_iff.mpr ⟨old,mem,on⟩
      change C.gates.countP _ = 0 at nopaid
      omega
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at kind ⊢
    rcases kind with h | h | h
    · exact ⟨Or.inl h,by simpa [rewriteGate] using arity⟩
    · exact ⟨Or.inr h,by simpa [rewriteGate] using arity⟩
    · exact False.elim (off (by simp [h,GateOp.eval]))
  obtain ⟨x,bad⟩ := positive (rewriteCircuit w f C) mono (by simpa [Circuit.size,rewriteCircuit] using size)
  exact bad ((rewriteEval C w f x).trans (correct x))

/-- Once the single increasing occurrence of a distinguished raw input is
cut, both remaining evaluations are ordered in the opposite direction. -/
theorem solePositiveMustRise (suffix : Bool → Bool → Bool) (lo hi : Bool)
    (mon : ∀ a b c d : Bool, (a = true → c = true) → (b = true → d = true) →
      suffix a b = true → suffix c d = true)
    (off : suffix lo true = false) (on : suffix hi false = true) :
    lo = false ∧ hi = true := by
  cases lo <;> cases hi <;> simp_all

def normalized (p q a b : Bool) := ((xor a p && xor b q) ^^ (p && q))

/-- The two legal physical versions of a normalized signed gate are dual. -/
theorem twoOrientations (p q a b : Bool) :
    (xor a p && xor b q) = xor (normalized p q a b) (p && q) ∧
    (xor a (!p) || xor b (!q)) = xor (normalized p q a b) (!(p && q)) := by
  cases p <;> cases q <;> cases a <;> cases b <;> decide

theorem postedFromSearches
    (signed : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 17 → ∃ x : Input,
      (p.foldl addPair (initial x)).getD o false ≠ graph x)
    (positive : ∀ D : Circuit, Monotone2 D → D.size ≤ 18 → ∃ x : Input,
      D.eval (canonical x) ≠ graph x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C w f legal size
  obtain ⟨x,h⟩ := deskFromSearches signed positive C w f legal size
  exact ⟨x,by simpa [PetersenFreeOr.graph,Bool.or_assoc] using h⟩

end PetersenUnaryInput
