import OrderFourErasure18057

namespace SingleNotPinErasure34187

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

private theorem runLength (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

private theorem readAppend (w : List Bool) (v : Bool) (i : Nat) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (by omega)]
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)]
    by_cases eq : i = w.length
    · subst i
      rw [ite_eq_left rfl, Nat.sub_self]
      rfl
    · rw [ite_eq_right eq]
      have i1 : 1 ≤ i - w.length := by omega
      have i2 : w.length ≤ i := by omega
      have singleton : [v].length ≤ i - w.length := by simpa using i1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none singleton,
        List.getElem?_eq_none i2]

private theorem runOld (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem runAppend (L R : List Gate) (x : List Bool) :
    run (L ++ R) x = run R (run L x) := by
  unfold run
  exact List.foldl_append

private theorem orPairCopy (q r width : Nat) (hq : q < width) :
    ∃ p < width, ∀ w : List Bool, w.length = width → w.getD q false = false →
      (w.getD q false || w.getD r false) = w.getD p false := by
  by_cases inside : r < width
  · refine ⟨r,inside,?_⟩
    intro w _ zero
    rw [zero]
    rfl
  · refine ⟨q,hq,?_⟩
    intro w len zero
    have out : w.length ≤ r := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none out]

private theorem readerCopy (g : Gate) (q width : Nat) (hq : q < width)
    (mono : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (mem : q ∈ g.inputs) :
    ∃ p < width, ∀ (w : List Bool), w.length = width → w.getD q false = false →
      g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD p false := by
  have modes : g.op = .and ∨ g.op = .or := by simpa using mono.1
  rcases modes with andOp | orOp
  · refine ⟨q,hq,?_⟩
    intro w _ zero
    rw [andOp, GateOp.eval, zero]
    cases h : (g.inputs.map fun i => w.getD i false).all id
    · rfl
    · have present : false ∈ g.inputs.map (fun i => w.getD i false) :=
        List.mem_map.mpr ⟨q,mem,zero⟩
      have bad := List.all_eq_true.mp h false present
      contradiction
  · rw [orOp]
    rcases args : g.inputs with _ | ⟨a,tail⟩
    · simp [args] at mem
    · rcases tail with _ | ⟨b,tail⟩
      · have aq : q=a := by simpa [args] using mem
        subst a
        refine ⟨q,hq,?_⟩
        intro w _ _
        simp [GateOp.eval]
      · have cap := mono.2
        simp only [args,List.length_cons] at cap
        cases tail with
        | cons c rest => simp at cap
        | nil =>
          have pair : q=a ∨ q=b := by simpa [args] using mem
          rcases pair with qa | qb
          · subst a
            obtain ⟨p,bound,proof⟩ := orPairCopy q b width hq
            exact ⟨p,bound,fun w len zero => by simpa [GateOp.eval] using proof w len zero⟩
          · subst b
            obtain ⟨p,bound,proof⟩ := orPairCopy q a width hq
            exact ⟨p,bound,fun w len zero => by
              simpa [GateOp.eval,Bool.or_comm] using proof w len zero⟩

theorem erasePaidReader (n : Nat) (C : Circuit) (m q : Nat)
    (bound : m < C.gates.length) (raw : q < n)
    (mode : C.gates[m].op = .and ∨ C.gates[m].op = .or)
    (cap : C.gates[m].inputs.length ≤ 2) (reads : q ∈ C.gates[m].inputs) :
    ∃ p < n+m, ∀ x : List Bool, x.length = n → x.getD q false = false →
      (eraseGate n C m p).eval x = C.eval x := by
  let L := C.gates.take m
  let R := C.gates.drop (m+1)
  let g := C.gates[m]
  have allGates : C.gates = L ++ g :: R := by
    conv_lhs => rw [← List.take_append_drop m C.gates]
    exact congrArg (L ++ ·) (List.drop_eq_getElem_cons bound)
  have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    ⟨by simpa using mode, cap⟩
  obtain ⟨p,hp,copy⟩ := readerCopy g q (n+m) (by omega) hg reads
  refine ⟨p,hp,?_⟩
  intro x len zero
  let tape := run L x
  have width : tape.length = n+m := by
    change (run L x).length = _
    rw [runLength,len]
    simp [L,Nat.min_eq_left (Nat.le_of_lt bound)]
  have qval : tape.getD q false = false := by
    change (run L x).getD q false = _
    rw [runOld _ _ _ (by omega),zero]
  let v := g.op.eval (g.inputs.map fun i => tape.getD i false)
  have old : C.wires x = run R (tape ++ [v]) := by
    change run C.gates x = _
    rw [allGates,runAppend]
    rfl
  have extended : (tape ++ [v]).length = tape.length+1 := by simp
  apply OrderFourErasure18057.eraseEval n C m p x len bound hp
  left
  rw [old,runOld _ _ _ (by omega),runOld _ _ _ (by omega),readAppend,
    readAppend,width,ite_eq_left rfl,ite_eq_right (by omega)]
  exact copy tape width qval


private def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

private theorem countRename (gs : List Gate) (f : Nat → Nat) :
    ((gs.map fun g => (⟨g.op, g.inputs.map f⟩ : Gate)).filter isNot).length =
      (gs.filter isNot).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have mark : isNot (⟨g.op, g.inputs.map f⟩ : Gate) = isNot g := rfl
    cases h : isNot g <;> simp [List.filter_cons, mark, h, ih]

theorem erasePaidKeepsNotCount (n : Nat) (C : Circuit) (m p : Nat)
    (bound : m < C.gates.length)
    (mode : C.gates[m].op = .and ∨ C.gates[m].op = .or) :
    (((eraseGate n C m p).gates).filter isNot).length = (C.gates.filter isNot).length := by
  let L := C.gates.take m
  let R := C.gates.drop (m+1)
  let g := C.gates[m]
  have allGates : C.gates = L ++ g :: R := by
    conv_lhs => rw [← List.take_append_drop m C.gates]
    exact congrArg (L ++ ·) (List.drop_eq_getElem_cons bound)
  have skip : isNot g = false := by
    change g.op = .and ∨ g.op = .or at mode
    rcases mode with a | a <;> simp [isNot, a]
  have shorter : (eraseGate n C m p).gates =
      L ++ R.map (fun u => ⟨u.op, u.inputs.map (eraseRedirect n m p)⟩) := by
    simp [eraseGate, bound, L, R]
  conv_rhs => rw [allGates]
  rw [shorter, List.filter_append, List.filter_append, List.length_append,
    List.length_append, countRename]
  simp [List.filter_cons, skip]

#print axioms erasePaidReader
#print axioms erasePaidKeepsNotCount

end SingleNotPinErasure34187
