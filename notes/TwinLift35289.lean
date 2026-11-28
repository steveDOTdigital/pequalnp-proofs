import OrderFourErasure18057

/-!
An output-absorbed disjunct can move from an internal OR to the final OR.
The argument uses the evaluator directly and allows a later NOT.
-/

namespace TwinLift35289

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

private theorem runLength (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

private theorem runOld (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem runAppend (L R : List Gate) (x : List Bool) :
    run (L ++ R) x = run R (run L x) := List.foldl_append

private theorem appendOr (D : Circuit) (x : List Bool) (h : Nat) :
    (⟨D.gates ++ [⟨.or, [D.output, h]⟩], x.length + D.gates.length⟩ : Circuit).eval x =
      (D.eval x || (D.wires x).getD h false) := by
  change (run (D.gates ++ [⟨.or, [D.output, h]⟩]) x).getD
    (x.length + D.gates.length) false = _
  rw [runAppend, ← runLength D.gates x]
  change ((run D.gates x) ++ [_]).getD (run D.gates x).length false = _
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
  change ([GateOp.or.eval [((run D.gates x).getD D.output false),
    ((run D.gates x).getD h false)]] : List Bool).getD 0 false = _
  change _ = ((run D.gates x).getD D.output false || (run D.gates x).getD h false)
  simp [GateOp.eval]

/-- A wire earlier than the moved OR may be an input or a gate. Its implication
to the output is the only semantic assumption on the surrounding circuit. -/
theorem liftEval (n : Nat) (C : Circuit) (m p h : Nat) (x : List Bool)
    (len : x.length = n) (idx : m < C.gates.length)
    (hp : p < n+m) (hh : h < n+m)
    (gate : C.gates[m] = ⟨.or, [p, h]⟩ ∨ C.gates[m] = ⟨.or, [h, p]⟩)
    (below : (C.wires x).getD h false = true → C.eval x = true) :
    (liftAt n C m p h).eval x = C.eval x := by
  let D := eraseGate n C m p
  let L := C.gates.take m
  let R := C.gates.drop (m+1)
  let g := C.gates[m]
  let tape := run L x
  have width : tape.length = n+m := by
    change (run L x).length = _
    rw [runLength, len]
    simp [L, Nat.min_eq_left (Nat.le_of_lt idx)]
  have splitGates : C.gates = L ++ g :: R := by
    conv_lhs => rw [← List.take_append_drop m C.gates]
    exact congrArg (L ++ ·) (List.drop_eq_getElem_cons idx)
  have old : C.wires x = run (g :: R) tape := by
    change run C.gates x = _
    rw [splitGates, runAppend]
  have shorter : D.wires x =
      run (R.map fun k => ⟨k.op, k.inputs.map (eraseRedirect n m p)⟩) tape := by
    change run (eraseGate n C m p).gates x = _
    simp only [eraseGate, ite_eq_left idx]
    exact runAppend L _ x
  have beforeOld (i : Nat) (hi : i < n+m) :
      (C.wires x).getD i false = tape.getD i false := by
    rw [old, runOld _ _ _ (by omega)]
  have hUnchanged : (D.wires x).getD h false = (C.wires x).getD h false := by
    rw [shorter, runOld _ _ _ (by omega), beforeOld h hh]
  have atGate : (C.wires x).getD (n+m) false =
      ((C.wires x).getD p false || (C.wires x).getD h false) := by
    rw [beforeOld p hp, beforeOld h hh, old]
    change (run R (step tape g)).getD (n+m) false = _
    have room : n+m < (step tape g).length := by simp [step, width]
    rw [runOld _ _ _ room]
    unfold step
    rw [List.getD_append_right _ _ _ _ (by omega : tape.length ≤ n+m),
      width, Nat.sub_self]
    change g = _ ∨ g = _ at gate
    rcases gate with e | e
    · simp [e, GateOp.eval]
    · simp [e, GateOp.eval, Bool.or_comm]
  have lifted : (liftAt n C m p h).eval x =
      (D.eval x || (D.wires x).getD h false) := by
    simpa only [liftAt, len] using appendOr D x h
  rw [lifted, hUnchanged]
  cases hval : (C.wires x).getD h false with
  | false =>
    rw [hval, Bool.or_false] at atGate
    have same := OrderFourErasure18057.eraseEval n C m p x len idx hp (Or.inl atGate)
    rw [Bool.or_false]
    exact same
  | true => simp [below hval]

theorem relationPreservesEval (n : Nat) (C D : Circuit) (move : Lift n C D)
    (x : Fin n → Bool) : D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨m, idx, p, hp, h, hh, _, gate, below, rfl⟩ := move
  have orientations : C.gates[m] = ⟨.or, [p,h]⟩ ∨ C.gates[m] = ⟨.or, [h,p]⟩ := by
    simpa only [List.getElem?_eq_getElem idx, Option.some.injEq] using gate
  exact liftEval n C m p h (List.ofFn x) (by simp) idx hp hh orientations (below x)

theorem liftSize (n : Nat) (C : Circuit) (m p h : Nat) (bound : m < C.size) :
    (liftAt n C m p h).size = C.size := by
  have erased := OrderFourErasure18057.eraseSize n C m p bound
  change (eraseGate n C m p).gates.length = C.size - 1 at erased
  simp only [liftAt, Circuit.size, List.length_append, List.length_cons, List.length_nil]
  change m < C.gates.length at bound
  change (eraseGate n C m p).gates.length = C.gates.length - 1 at erased
  omega

/-- With the outside edge detector false, the other twin can be chosen so the
full detector reads exactly the designated twin. -/
theorem exposeTwin (u neighbors : Bool) :
    ((u && !neighbors) || ((u || !neighbors) && neighbors)) = u := by
  cases u <;> cases neighbors <;> decide

#print axioms liftEval
#print axioms relationPreservesEval
#print axioms liftSize
#print axioms exposeTwin

end TwinLift35289
