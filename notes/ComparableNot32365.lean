import PEqualNP.Defs.CircuitLowerBounds

namespace ComparableNot32365

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def tapeLe (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

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

private theorem appendLe (a b : List Bool) (u v : Bool) (same : a.length = b.length)
    (old : tapeLe a b) (new : u = true → v = true) : tapeLe (a ++ [u]) (b ++ [v]) := by
  intro i hi
  rw [appendRead, same] at hi
  rw [appendRead]
  by_cases boundary : i = b.length
  · simp only [boundary, ite_true] at hi ⊢
    exact new hi
  · simp only [boundary, ite_false] at hi ⊢
    exact old i hi

private theorem bitLe (a b : List Bool) (g : Gate) (old : tapeLe a b)
    (legal : g.op = .and ∨ g.op = .or)
    (hi : g.op.eval (g.inputs.map fun i => a.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases legal with h | h
  · rw [h, GateOp.eval] at hi ⊢
    apply List.all_eq_true.mpr
    intro x mem
    obtain ⟨i, inG, rfl⟩ := List.mem_map.mp mem
    exact old i (List.all_eq_true.mp hi _ (List.mem_map_of_mem inG))
  · rw [h, GateOp.eval] at hi ⊢
    obtain ⟨_, mem, hOn⟩ := List.any_eq_true.mp hi
    obtain ⟨i, inG, rfl⟩ := List.mem_map.mp mem
    exact List.any_eq_true.mpr ⟨_,List.mem_map_of_mem inG,old i hOn⟩

private theorem foldLe (gates : List Gate) (a b : List Bool)
    (same : a.length = b.length) (old : tapeLe a b)
    (legal : ∀ g ∈ gates, g.op = .and ∨ g.op = .or) :
    tapeLe (gates.foldl step a) (gates.foldl step b) := by
  induction gates generalizing a b with
  | nil => exact old
  | cons g tail ih =>
    have t : ∀ u ∈ tail, u.op = .and ∨ u.op = .or :=
      fun u hu => legal u (List.mem_cons_of_mem _ hu)
    exact ih _ _ (by simp [step, same]) (appendLe _ _ _ _ same old
      (bitLe a b g old (legal g (by simp)))) t

def original (pre post : List Gate) (args : List Nat) (out : Nat) : Circuit :=
  ⟨pre ++ ⟨GateOp.not,args⟩ :: post, out⟩

def replaced (pre post : List Gate) (value : Bool) (out : Nat) : Circuit :=
  ⟨pre ++ ⟨if value then GateOp.and else GateOp.or, []⟩ :: post, out⟩

def source (pre : List Gate) (args : List Nat) (x : List Bool) : Bool :=
  (args.map fun i => (pre.foldl step x).getD i false).headD false

private def context (pre post : List Gate) (out : Nat) (x : List Bool) (s : Bool) : Bool :=
  (post.foldl step (pre.foldl step x ++ [s])).getD out false

private theorem originalEval (pre post : List Gate) (args : List Nat) (out : Nat) (x : List Bool) :
    (original pre post args out).eval x = context pre post out x (!(source pre args x)) := by
  change ((pre ++ ⟨GateOp.not,args⟩ :: post).foldl step x).getD out false = _
  rw [List.foldl_append]
  rfl

private theorem replacedEval (pre post : List Gate) (out : Nat) (x : List Bool) (b : Bool) :
    (replaced pre post b out).eval x = context pre post out x b := by
  change ((pre ++ ⟨if b then GateOp.and else GateOp.or, []⟩ :: post).foldl step x).getD out false = _
  rw [List.foldl_append]
  cases b <;> rfl

private theorem contextLe (pre post : List Gate) (out : Nat) (x : List Bool)
    (legal : ∀ g ∈ post, g.op = .and ∨ g.op = .or) :
    context pre post out x false = true → context pre post out x true = true := by
  apply foldLe post (pre.foldl step x ++ [false]) (pre.foldl step x ++ [true]) _ _ legal out
  · simp
  · exact appendLe _ _ _ _ rfl (fun _ h => h) (by decide)

theorem drop_when_source_below (pre post : List Gate) (args : List Nat) (out : Nat)
    (legal : ∀ g ∈ post, g.op = .and ∨ g.op = .or)
    (below : ∀ x, source pre args x = true → (original pre post args out).eval x = true) :
    ∀ x, (replaced pre post true out).eval x = (original pre post args out).eval x := by
  intro x
  rw [replacedEval, originalEval]
  cases h : source pre args x
  · rfl
  · have on := below x h
    rw [originalEval, h] at on
    change context pre post out x true = context pre post out x false
    exact (contextLe pre post out x legal on).trans (show context pre post out x false = true from on).symm

theorem drop_when_output_below (pre post : List Gate) (args : List Nat) (out : Nat)
    (legal : ∀ g ∈ post, g.op = .and ∨ g.op = .or)
    (below : ∀ x, (original pre post args out).eval x = true → source pre args x = true) :
    ∀ x, (replaced pre post false out).eval x = (original pre post args out).eval x := by
  intro x
  rw [replacedEval, originalEval]
  cases h : source pre args x
  · change context pre post out x false = context pre post out x true
    have highFalse : context pre post out x true = false := by
      cases high : context pre post out x true
      · rfl
      · have orig : (original pre post args out).eval x = true := by
          rw [originalEval, h]
          exact high
        exact False.elim (Bool.false_ne_true (h.symm.trans (below x orig)))
    have lowFalse : context pre post out x false = false := by
      cases low : context pre post out x false
      · rfl
      · exact False.elim
          (Bool.false_ne_true (highFalse.symm.trans (contextLe pre post out x legal low)))
    exact lowFalse.trans highFalse.symm
  · rfl

theorem sameSize (pre post : List Gate) (args : List Nat) (out : Nat) (b : Bool) :
    (replaced pre post b out).size = (original pre post args out).size := by
  simp [Circuit.size, replaced, original]

#print axioms drop_when_source_below
#print axioms drop_when_output_below
#print axioms sameSize

end ComparableNot32365
