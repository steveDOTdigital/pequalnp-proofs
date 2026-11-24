import PEqualNP.Defs

namespace FanoCollision

def combine (isAnd left right : Bool) : Bool :=
  if isAnd then left && right else left || right

def linear (isAnd a b da db : Bool) : Bool :=
  if isAnd then (a && db) || (da && b) else da || db

-- If both input wires are explained, an unexplained true output must be a
-- conjunction whose operands both change from false to true.
theorem local_step : ∀ op a b da db x y : Bool,
    (x = true → a = true ∨ da = true) →
    (y = true → b = true ∨ db = true) →
    combine op x y = true → combine op a b = false → linear op a b da db = false →
    op = true ∧ x = true ∧ y = true ∧ a = false ∧ b = false ∧ da = true ∧ db = true := by
  intro op a b da db x y
  cases op <;> cases a <;> cases b <;> cases da <;> cases db <;> cases x <;> cases y <;>
    simp [combine,linear]

theorem locate (n m out : ℕ) (op : ℕ → Bool) (l r : ℕ → ℕ)
    (base pair trace : ℕ → Bool)
    (earlier : ∀ j < m, l j < n+j ∧ r j < n+j)
    (raw : ∀ i < n, pair i = true → base i = true ∨ trace i = true)
    (rec : ∀ j < m,
      base (n+j) = combine (op j) (base (l j)) (base (r j)) ∧
      pair (n+j) = combine (op j) (pair (l j)) (pair (r j)) ∧
      trace (n+j) = linear (op j) (base (l j)) (base (r j)) (trace (l j)) (trace (r j)))
    (inRange : out < n+m) (hit : pair out = true)
    (miss : base out = false) (lost : trace out = false) :
    ∃ j < m, op j = true ∧ pair (l j) = true ∧ pair (r j) = true ∧
      base (l j) = false ∧ base (r j) = false ∧ trace (l j) = true ∧ trace (r j) = true := by
  classical
  by_contra absent
  have explain : ∀ w, w < n+m → pair w = true → base w = true ∨ trace w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hp
      by_cases input : w < n
      · exact raw w input hp
      let j := w-n
      have ew : w = n+j := by dsimp [j]; omega
      have hj : j < m := by omega
      obtain ⟨hl,hr⟩ := earlier j hj
      obtain ⟨hb,hy,hd⟩ := rec j hj
      by_contra failed
      have bz : base w = false := by cases b : base w <;> simp_all
      have dz : trace w = false := by cases d : trace w <;> simp_all
      have lx := ih (l j) (by omega) (by omega)
      have rx := ih (r j) (by omega) (by omega)
      have row : combine (op j) (pair (l j)) (pair (r j)) = true := hy.symm.trans (ew ▸ hp)
      have zero : combine (op j) (base (l j)) (base (r j)) = false := hb.symm.trans (ew ▸ bz)
      have dzero : linear (op j) (base (l j)) (base (r j)) (trace (l j)) (trace (r j)) = false :=
        hd.symm.trans (ew ▸ dz)
      exact absent ⟨j,hj,local_step _ _ _ _ _ _ _ lx rx row zero dzero⟩
  rcases explain out inRange hit with b|d <;> simp_all

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def fold (gs : List Gate) (w : List Bool) := gs.foldl step w

theorem fold_length (gs : List Gate) (w : List Bool) : (fold gs w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [fold]
  | cons g gs ih =>
    change (fold gs (step w g)).length = _
    rw [ih]
    simp [step,Nat.add_comm,Nat.add_left_comm]

theorem kept (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i<w.length) :
    (fold gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (fold gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem computed (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (back : ∀ i ∈ gs[j].inputs, i < w.length+j) :
    (fold gs w).getD (w.length+j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (fold gs w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero,Nat.add_zero] at back ⊢
      change (fold gs (step w g)).getD w.length false =
        g.op.eval (g.inputs.map fun i => (fold gs (step w g)).getD i false)
      rw [kept gs _ _ (by simp [step])]
      have preserve : g.inputs.map (fun i => (fold gs (step w g)).getD i false) =
          g.inputs.map (fun i => w.getD i false) := by
        apply List.map_congr_left
        intro i hi
        have hb := back i hi
        rw [kept gs _ _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hb
      rw [preserve]
      simp [step]
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have le : (step w g).length = w.length+1 := by simp [step]
      have eq : w.length+(j+1) = (step w g).length+j := by omega
      have hb : ∀ i ∈ gs[j].inputs, i < (step w g).length+j := by
        simpa [le,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using back
      simpa [fold,eq] using ih (step w g) j hj' hb

theorem two_inputs (xs : List ℕ) (hl : xs.length=2) :
    xs = [xs.getD 0 0,xs.getD 1 0] := by
  rcases xs with _|⟨a,xs⟩ <;> simp_all
  rcases xs with _|⟨b,xs⟩ <;> simp_all

def val (C : Circuit) (x : Fin 14 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false

def op (C : Circuit) (j : ℕ) : Bool := match (gateAt C j).op with
  | .and => true
  | _ => false

theorem gateInfo (C : Circuit) (ao : IsAO2 14 C) (j : ℕ) (hj : j<C.size) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0,opnd C j 1] ∧
    (opnd C j 0 < 14+j ∧ opnd C j 1 < 14+j) := by
  have hm : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have eq := two_inputs _ (ao.2.2 _ hm)
  change (gateAt C j).inputs = [opnd C j 0,opnd C j 1] at eq
  refine ⟨ao.1 _ hm,eq,ao.2.1 j hj _ ?_,ao.2.1 j hj _ ?_⟩ <;> rw [eq] <;> simp

theorem val_rec (C : Circuit) (ao : IsAO2 14 C) (x : Fin 14 → Bool) (j : ℕ) (hj : j<C.size) :
    val C x (14+j) = combine (op C j) (val C x (opnd C j 0)) (val C x (opnd C j 1)) := by
  obtain ⟨kind,ins,_,_⟩ := gateInfo C ao j hj
  have atJ : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hb : ∀ i ∈ C.gates[j].inputs, i < (List.ofFn x).length+j := by
    simpa [← atJ] using ao.2.1 j hj
  have eq := computed C.gates (List.ofFn x) j hj hb
  change (fold C.gates (List.ofFn x)).getD (14+j) false = _
  simp only [List.length_ofFn,← atJ,ins,List.map_cons,List.map_nil] at eq
  rw [eq]
  change (gateAt C j).op.eval [val C x (opnd C j 0),val C x (opnd C j 1)] = _
  unfold op
  rcases kind with h|h <;> simp [h,combine,GateOp.eval]


theorem collision_child : ∀ (C : Circuit), IsAO2 14 C → ∀ b : Bool,
      let s := fun i : Fin 14 => decide (i = if b = true then (0 : Fin 14) else 7)
      let t := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7
      let w := C.wires (List.ofFn s)
      let y := C.wires (List.ofFn t)
      ∀ d : ℕ → Bool,
        (∀ i < 14, d i = decide (i = if b = true then (7 : ℕ) else 0)) →
        (∀ j < C.size, let g := gateAt C j; let a := opnd C j 0; let k := opnd C j 1
          (g.op = GateOp.and → d (14+j) = ((w.getD a false && d k) || (d a && w.getD k false))) ∧
          (g.op = GateOp.or → d (14+j) = (d a || d k))) →
        d C.output = false → C.eval (List.ofFn s) = false → C.eval (List.ofFn t) = true →
        ∃ j < C.size, (gateAt C j).op = GateOp.and ∧
          ∀ k : Fin 2, y.getD (opnd C j k) false = true ∧ w.getD (opnd C j k) false = false := by
  intro C ao b s t w y d raw rec lost baseZero pairTrue
  have rawVal (x : Fin 14 → Bool) (i : ℕ) (hi : i<14) :
      val C x i = x ⟨i,hi⟩ := by
    change (fold C.gates (List.ofFn x)).getD i false = _
    rw [kept _ _ _ (by simpa),List.getD_eq_getElem _ _ (by simpa),List.getElem_ofFn]
  have starts (i : ℕ) (hi : i<14) (hit : val C t i=true) : val C s i=true ∨ d i=true := by
    rw [rawVal _ _ hi] at hit ⊢
    rw [raw i hi]
    have check : ∀ (flag : Bool) (k : Fin 14),
        PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 k = true →
        decide (k = if flag=true then (0 : Fin 14) else 7) = true ∨
        decide (k.val = if flag=true then (7 : ℕ) else 0) = true := by
      intro flag
      cases flag <;> decide +kernel
    exact check b ⟨i,hi⟩ hit
  have stepEq (j : ℕ) (hj : j<C.size) :
      d (14+j) = linear (op C j) (val C s (opnd C j 0)) (val C s (opnd C j 1))
        (d (opnd C j 0)) (d (opnd C j 1)) := by
    obtain ⟨ha,ho⟩ := rec j hj
    rcases (gateInfo C ao j hj).1 with h|h
    · simpa [linear,op,h,val,w] using ha h
    · simpa [linear,op,h,val,w] using ho h
  have bound : C.output < 14+C.size := by
    by_contra! outside
    have ln : (C.wires (List.ofFn t)).length = 14+C.size := by
      change (fold C.gates _).length = _
      rw [fold_length,List.length_ofFn,Circuit.size]
    change (C.wires (List.ofFn t)).getD C.output false = true at pairTrue
    rw [List.getD_eq_default _ _ (by omega)] at pairTrue
    contradiction
  obtain ⟨j,hj,kind,pa,pb,za,zb,_,_⟩ := locate 14 C.size C.output (op C)
    (fun j => opnd C j 0) (fun j => opnd C j 1) (val C s) (val C t) d
    (fun j hj => (gateInfo C ao j hj).2.2) starts
    (fun j hj => ⟨val_rec C ao s j hj,val_rec C ao t j hj,stepEq j hj⟩)
    bound pairTrue baseZero lost
  refine ⟨j,hj,?_,?_⟩
  · rcases (gateInfo C ao j hj).1 with h|h
    · exact h
    · simp [op,h] at kind
  · intro k
    fin_cases k
    · exact ⟨pa,za⟩
    · exact ⟨pb,zb⟩

end FanoCollision
