import PEqualNP.Defs.CircuitLowerBounds

namespace SingleNotPaidReader34187

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def bin (g : Gate) : Prop :=
  g.op = GateOp.and ∨ g.op = GateOp.or

private def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

private def notCount (gs : List Gate) : Nat := (gs.filter isNot).length

private def EqAway (q : Nat) (hi lo : List Bool) : Prop :=
  ∀ i, i ≠ q → hi.getD i false = lo.getD i false

private def LeAway (q : Nat) (hi lo : List Bool) : Prop :=
  ∀ i, i ≠ q → hi.getD i false = true → lo.getD i false = true

private theorem appendRead (w : List Bool) (v : Bool) (i : Nat) :
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

private theorem binStepEq (q : Nat) (hi lo : List Bool) (g : Gate)
    (hlen : hi.length = lo.length) (eq : EqAway q hi lo) (quiet : q ∉ g.inputs) :
    EqAway q (step hi g) (step lo g) := by
  have reads : (g.inputs.map fun i => hi.getD i false) =
      (g.inputs.map fun i => lo.getD i false) :=
    List.map_congr_left (fun i mem => eq i (fun e => quiet (e ▸ mem)))
  intro i away
  unfold step
  rw [appendRead, appendRead, hlen, reads, eq i away]

private theorem binOutputLe (q : Nat) (hi lo : List Bool) (g : Gate)
    (mon : bin g) (order : LeAway q hi lo) (quiet : q ∉ g.inputs)
    (trueHi : g.op.eval (g.inputs.map fun i => hi.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => lo.getD i false) = true := by
  rcases mon with andOp | orOp
  · rw [andOp, GateOp.eval] at trueHi ⊢
    apply List.all_eq_true.mpr
    intro b mem
    obtain ⟨i, inside, rfl⟩ := List.mem_map.mp mem
    exact order i (fun e => quiet (e ▸ inside))
      (List.all_eq_true.mp trueHi _ (List.mem_map_of_mem inside))
  · rw [orOp, GateOp.eval] at trueHi ⊢
    obtain ⟨_, mem, yes⟩ := List.any_eq_true.mp trueHi
    obtain ⟨i, inside, rfl⟩ := List.mem_map.mp mem
    exact List.any_eq_true.mpr ⟨_, List.mem_map_of_mem inside,
      order i (fun e => quiet (e ▸ inside)) yes⟩

private theorem stepLe (q : Nat) (hi lo : List Bool) (g : Gate)
    (hlen : hi.length = lo.length) (order : LeAway q hi lo)
    (gate : g.op.eval (g.inputs.map fun i => hi.getD i false) = true →
      g.op.eval (g.inputs.map fun i => lo.getD i false) = true) :
    LeAway q (step hi g) (step lo g) := by
  intro i away
  unfold step
  rw [appendRead, appendRead, hlen]
  split
  · exact gate
  · exact order i away

private theorem binaryTailLe (q : Nat) (gs : List Gate) (hi lo : List Bool)
    (hlen : hi.length = lo.length) (order : LeAway q hi lo)
    (legal : ∀ g ∈ gs, bin g ∧ q ∉ g.inputs) :
    LeAway q (gs.foldl step hi) (gs.foldl step lo) := by
  induction gs generalizing hi lo with
  | nil => exact order
  | cons g gs ih =>
    have ok := legal g (by simp)
    exact ih _ _ (by simp [step, hlen]) (stepLe q hi lo g hlen order
      (binOutputLe q hi lo g ok.1 order ok.2))
      fun u hu => legal u (List.mem_cons_of_mem _ hu)

private theorem notOutputLe (q : Nat) (hi lo : List Bool) (g : Gate)
    (eq : EqAway q hi lo) (high : hi.getD q false = true)
    (op : g.op = GateOp.not)
    (trueHi : g.op.eval (g.inputs.map fun i => hi.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => lo.getD i false) = true := by
  rw [op, GateOp.eval] at trueHi ⊢
  cases args : g.inputs with
  | nil => simp
  | cons a rest =>
    have value : (!(hi.getD a false)) = true := by
      simpa only [args, List.map_cons, List.headD_cons] using trueHi
    change (!(lo.getD a false)) = true
    by_cases atQ : a = q
    · subst a
      rw [high] at value
      contradiction
    · rwa [← eq a atQ]

private theorem oneNotLe (q : Nat) (gs : List Gate) (hi lo : List Bool)
    (hlen : hi.length = lo.length) (raw : q < hi.length)
    (eq : EqAway q hi lo) (high : hi.getD q false = true)
    (count : notCount gs ≤ 1)
    (legal : ∀ g ∈ gs, (bin g ∧ q ∉ g.inputs) ∨ g.op = GateOp.not) :
    LeAway q (gs.foldl step hi) (gs.foldl step lo) := by
  induction gs generalizing hi lo with
  | nil => exact fun i ne value => (eq i ne).symm.trans value
  | cons g gs ih =>
    have rest : ∀ u ∈ gs, (bin u ∧ q ∉ u.inputs) ∨ u.op = GateOp.not :=
      fun u hu => legal u (List.mem_cons_of_mem _ hu)
    have newLength : (step hi g).length = (step lo g).length := by simp [step, hlen]
    rcases legal g (by simp) with ordinary | negation
    · rcases ordinary with ⟨how, quiet⟩
      have unchanged : (step hi g).getD q false = true := by
        unfold step
        rwa [List.getD_append _ _ _ _ raw]
      have cap : notCount gs ≤ 1 := by
        rcases how with op | op <;> simpa [notCount, isNot, op] using count
      exact ih _ _ newLength (by simp [step]; omega)
        (binStepEq q hi lo g hlen eq quiet) unchanged cap rest
    · have empty : gs.filter isNot = [] := by
        have marked : isNot g = true := by simp [isNot, negation]
        have count' : (gs.filter isNot).length + 1 ≤ 1 := by
          simpa only [notCount, List.filter_cons, marked, ite_true, List.length_cons] using count
        have lengthZero : (gs.filter isNot).length = 0 := by omega
        simpa using lengthZero
      have onlyBinary : ∀ u ∈ gs, bin u ∧ q ∉ u.inputs := by
        intro u hu
        rcases rest u hu with ok | bad
        · exact ok
        · have existsInFilter : u ∈ gs.filter isNot :=
            List.mem_filter.mpr ⟨hu, by simp [isNot, bad]⟩
          rw [empty] at existsInFilter
          cases existsInFilter
      have order : LeAway q hi lo := fun i ne value => (eq i ne).symm.trans value
      exact binaryTailLe q gs _ _ newLength
        (stepLe q hi lo g hlen order (notOutputLe q hi lo g eq high negation))
        onlyBinary


private theorem marked_iff (g : Gate) : isNot g = true ↔ g.op = GateOp.not := by
  cases h : g.op <;> simp [isNot, h]

private theorem atMostOneMark (gs : List Gate)
    (single : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) : notCount gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    have tail : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
        (gs.get j).op = GateOp.not → i = j := by
      intro i j ni nj
      have same := single i.succ j.succ ni nj
      exact Fin.succ_inj.mp same
    cases marked : isNot g with
    | false =>
      simpa only [notCount, List.filter_cons, marked, Bool.false_eq_true, ite_false] using ih tail
    | true =>
      have n : g.op = GateOp.not := (marked_iff g).mp marked
      have empty : gs.filter isNot = [] := by
        cases view : gs.filter isNot with
        | nil => rfl
        | cons u us =>
          exfalso
          have hu : u ∈ gs.filter isNot := by simp [view]
          obtain ⟨mem, mark⟩ := List.mem_filter.mp hu
          obtain ⟨i, ii, eq⟩ := List.mem_iff_getElem.mp mem
          have notTail : (gs.get ⟨i, ii⟩).op = GateOp.not := by
            change gs[i].op = GateOp.not
            rw [eq]
            exact (marked_iff u).mp mark
          have impossible := single ⟨0, by simp⟩ (Fin.succ ⟨i, ii⟩) n notTail
          have indices := congrArg Fin.val impossible
          simp at indices
      simp only [notCount, List.filter_cons, marked, ite_true, empty,
        List.length_cons, List.length_nil, Nat.zero_add, le_refl]

/-- An increasing output witness at a raw input forces a direct paid reader
when the output is elsewhere and at most one gate is a NOT. -/
theorem paidReaderExists (C : Circuit) (q : Nat) (hi lo : List Bool)
    (hlen : hi.length = lo.length) (raw : q < hi.length)
    (eq : ∀ i, i ≠ q → hi.getD i false = lo.getD i false)
    (high : hi.getD q false = true) (out : C.output ≠ q)
    (single : ∀ i j : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      (C.gates.get j).op = GateOp.not → i = j)
    (legal : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (yes : C.eval hi = true) (no : C.eval lo = false) :
    ∃ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ q ∈ g.inputs := by
  by_contra! absent
  have quieter : ∀ g ∈ C.gates,
      (bin g ∧ q ∉ g.inputs) ∨ g.op = GateOp.not := by
    intro g mem
    rcases legal g mem with a | o | n
    · exact Or.inl ⟨Or.inl a, fun h => absent g mem (Or.inl a) h⟩
    · exact Or.inl ⟨Or.inr o, fun h => absent g mem (Or.inr o) h⟩
    · exact Or.inr n
  have ordered := oneNotLe q C.gates hi lo hlen raw eq high
    (atMostOneMark C.gates single) quieter
  have comesDown : C.eval lo = true := ordered C.output out yes
  rw [no] at comesDown
  contradiction

#print axioms paidReaderExists

end SingleNotPaidReader34187
