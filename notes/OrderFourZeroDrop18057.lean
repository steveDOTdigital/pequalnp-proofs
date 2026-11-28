import OrderFourErasure18057

namespace OrderFourZeroDrop18057

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
open OrderFourErasure18057

def Below (x y : List Bool) : Prop :=
  ∀ i, x.getD i false = true → y.getD i false = true

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl step x

private theorem runLength (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step x g)).length = _
    rw [ih]
    simp [step]
    omega

private theorem runAppend (L R : List Gate) (x : List Bool) :
    run (L ++ R) x = run R (run L x) := by
  unfold run
  exact List.foldl_append

private theorem runOld (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step x g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem appendBelow (x y : List Bool) (a b : Bool)
    (width : x.length = y.length) (inputs : Below x y) (result : a = true → b = true) :
    Below (x ++ [a]) (y ++ [b]) := by
  intro i hi
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact inputs i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega),← width]
    by_cases equal : i = x.length
    · simp only [equal,Nat.sub_self] at hi ⊢
      exact result hi
    · have out : [a].length ≤ i-x.length := by simp; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none out] at hi

private theorem gateBelow (g : Gate) (x y : List Bool) (compare : Below x y)
    (op : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
      g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  have h : g.op = .and ∨ g.op = .or := by simpa using op
  rcases h with andOp | orOp
  · simp only [andOp,GateOp.eval,List.all_eq_true,id_eq]
    intro hx yv hy
    obtain ⟨i,hm,rfl⟩ := List.mem_map.mp hy
    exact compare i (hx _ (List.mem_map.mpr ⟨i,hm,rfl⟩))
  · simp only [orOp,GateOp.eval,List.any_eq_true,id_eq]
    rintro ⟨xv,hx,one⟩
    obtain ⟨i,hm,rfl⟩ := List.mem_map.mp hx
    exact ⟨_,List.mem_map.mpr ⟨i,hm,rfl⟩,compare i one⟩

private theorem runBelow (gs : List Gate) (x y : List Bool)
    (width : x.length = y.length) (inputs : Below x y)
    (mono : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    Below (run gs x) (run gs y) := by
  induction gs generalizing x y with
  | nil => exact inputs
  | cons g gs ih =>
    change Below (run gs (step x g)) (run gs (step y g))
    apply ih
    · simp [step,width]
    · exact appendBelow _ _ _ _ width inputs (gateBelow g x y inputs (mono g (by simp)))
    · intro h mem
      exact mono h (by simp [mem])

theorem evalBelow (C : Circuit) (x y : List Bool) (mono : Monotone2 C)
    (width : x.length = y.length) (inputs : Below x y) :
    C.eval x = true → C.eval y = true := by
  exact runBelow C.gates x y width inputs (fun g mem => (mono g mem).1) C.output

theorem zeroEraseBelow (n : Nat) (C : Circuit) (m q : Nat) (x : List Bool)
    (mono : Monotone2 C) (len : x.length = n) (bound : m < C.size)
    (raw : q < n) (pinned : x.getD q false = false) :
    (eraseGate n C m q).eval x = true → C.eval x = true := by
  have index : m < C.gates.length := bound
  let L := C.gates.take m
  let R := C.gates.drop (m+1)
  let gate := C.gates[m]
  have original : C.gates = L ++ gate :: R := by
    conv_lhs => rw [← List.take_append_drop m C.gates]
    exact congrArg (L ++ ·) (List.drop_eq_getElem_cons index)
  let z : Gate := ⟨.or,[]⟩
  let Z : Circuit := ⟨L ++ z :: R,C.output⟩
  let w := run L x
  let v := gate.op.eval (gate.inputs.map fun i => w.getD i false)
  have front : L.length = m := by simp [L,Nat.min_eq_left (Nat.le_of_lt index)]
  have width : w.length = n+m := by
    change (run L x).length = _
    rw [runLength,len,front]
  have old : C.wires x = run R (w ++ [v]) := by
    change run C.gates x = _
    rw [original,runAppend]
    rfl
  have made : Z.wires x = run R (w ++ [false]) := by
    change run (L ++ z :: R) x = _
    rw [runAppend]
    rfl
  have point : Below (w ++ [false]) (w ++ [v]) := by
    apply appendBelow _ _ _ _ rfl (fun _ h => h)
    simp
  have order : Below (Z.wires x) (C.wires x) := by
    rw [made,old]
    exact runBelow R _ _ (by simp) point (fun g mem => (mono g (List.mem_of_mem_drop mem)).1)
  have outs : (Z.wires x).getD (n+m) false = false := by
    rw [made,runOld _ _ _ (by simp; omega)]
    rw [List.getD_append_right _ _ _ _ (by omega),width,Nat.sub_self]
    rfl
  have dest : (Z.wires x).getD q false = false := by
    change (run Z.gates x).getD q false = _
    rw [runOld _ _ _ (by omega),pinned]
  have valid : m < Z.gates.length := by
    change m < (L ++ z :: R).length
    simp [front]
  have eq : (eraseGate n Z m q).eval x = Z.eval x :=
    eraseEval n Z m q x len valid (by omega) (Or.inl (outs.trans dest.symm))
  have taken : Z.gates.take m = L := by
    change (L ++ z :: R).take m = L
    rw [← front]
    simp
  have dropped : Z.gates.drop (m+1) = R := by
    change (L ++ z :: R).drop (m+1) = R
    rw [← front]
    simp
  have erased : eraseGate n Z m q = eraseGate n C m q := by
    simp only [eraseGate,ite_eq_left valid,ite_eq_left index,taken,dropped]
    rfl
  intro yes
  rw [erased] at eq
  exact order C.output (eq.symm.trans yes)

theorem exactFromPositiveBasis (C D : Circuit) (n : Nat) (rows basis : List Bool → Prop)
    (mono : Monotone2 D)
    (sound : ∀ x, x.length = n → rows x → D.eval x = true → C.eval x = true)
    (covers : ∀ x, x.length = n → rows x → C.eval x = true →
      ∃ y, y.length = n ∧ basis y ∧ Below y x)
    (tests : ∀ y, y.length = n → basis y → D.eval y = true) :
    ∀ x, x.length = n → rows x → D.eval x = C.eval x := by
  intro x len allowed
  cases hD : D.eval x <;> cases hC : C.eval x
  · rfl
  · obtain ⟨y,ly,member,point⟩ := covers x len allowed hC
    have yes := evalBelow D y x mono (ly.trans len.symm) point (tests y ly member)
    rw [hD] at yes
    contradiction
  · have yes := sound x len allowed hD
    rw [hC] at yes
    contradiction
  · rfl

#print axioms evalBelow
#print axioms zeroEraseBelow
#print axioms exactFromPositiveBasis

theorem eraseColdAtMaximum (n : Nat) (C : Circuit) (m q : Nat) (high x : List Bool)
    (mono : Monotone2 C) (width : x.length = n) (hwidth : high.length = n)
    (bound : m < C.size) (raw : q < n) (zero : x.getD q false = false)
    (supported : Below x high) (cold : (C.wires high).getD (n+m) false = false) :
    (eraseGate n C m q).eval x = C.eval x := by
  have same : (C.wires x).getD (n+m) false = false := by
    cases hv : (C.wires x).getD (n+m) false
    · rfl
    · have hot := runBelow C.gates x high (width.trans hwidth.symm) supported
          (fun g mem => (mono g mem).1) (n+m) hv
      change (C.wires high).getD (n+m) false = true at hot
      rw [cold] at hot
      contradiction
  have pin : (C.wires x).getD q false = false := by
    change (run C.gates x).getD q false = false
    rw [runOld _ _ _ (by omega),zero]
  exact eraseEval n C m q x width bound (by omega) (Or.inl (same.trans pin.symm))

def certifiedMixed (n q : Nat) (rows : List Bool → Prop) :
    Circuit → List (Nat × Nat) → Prop
  | _, [] => True
  | C, op :: tail =>
    (op.2 = q ∨
      ∀ x, x.length = n → rows x →
        (C.wires x).getD (n+op.1) false = (C.wires x).getD op.2 false ∨
        (C.output ≠ n+op.1 ∧ ∀ g ∈ C.gates.drop (op.1+1), n+op.1 ∉ g.inputs)) ∧
    certifiedMixed n q rows (eraseGate n C op.1 op.2) tail

theorem mixedStepsBelow (n : Nat) (C : Circuit) (q : Nat) (ops : List (Nat × Nat))
    (rows : List Bool → Prop) (raw : q < n) (mono : Monotone2 C)
    (pinned : ∀ x, rows x → x.getD q false = false)
    (valid : validSteps n C ops) (certificate : certifiedMixed n q rows C ops) :
    Monotone2 (eraseSteps n C ops) ∧
    ∀ x : List Bool, x.length = n → rows x →
      (eraseSteps n C ops).eval x = true → C.eval x = true := by
  induction ops generalizing C with
  | nil => exact ⟨mono,fun _ _ _ hit => hit⟩
  | cons op tail ih =>
    let E := eraseGate n C op.1 op.2
    obtain ⟨well,preserved⟩ := ih E (eraseMono n C op.1 op.2 mono) valid.2.2 certificate.2
    refine ⟨well,?_⟩
    intro x width allowed yes
    have ok : E.eval x = true := preserved x width allowed yes
    dsimp [E] at ok
    rcases certificate.1 with redirect | exactCopy
    · rw [redirect] at ok
      exact zeroEraseBelow n C op.1 q x mono width valid.1 raw (pinned x allowed) ok
    · exact (eraseEval n C op.1 op.2 x width valid.1 valid.2.1
        (exactCopy x width allowed)).symm.trans ok

theorem mixedStepsExact (n : Nat) (C : Circuit) (q : Nat) (ops : List (Nat × Nat))
    (rows basis : List Bool → Prop)
    (raw : q < n) (mono : Monotone2 C) (valid : validSteps n C ops)
    (certificate : certifiedMixed n q rows C ops)
    (pinned : ∀ x, rows x → x.getD q false = false)
    (covers : ∀ x, x.length = n → rows x → C.eval x = true →
      ∃ y, y.length = n ∧ basis y ∧ Below y x)
    (tests : ∀ y, y.length = n → basis y → (eraseSteps n C ops).eval y = true) :
    ∀ x, x.length = n → rows x → (eraseSteps n C ops).eval x = C.eval x := by
  obtain ⟨well,weak⟩ := mixedStepsBelow n C q ops rows raw mono pinned valid certificate
  exact exactFromPositiveBasis C _ n rows basis well weak covers tests

private theorem zeroRedirectCertificate (n : Nat) (C : Circuit) (q : Nat)
    (ops : List (Nat × Nat)) (rows : List Bool → Prop)
    (redirects : ∀ op ∈ ops, op.2 = q) :
    certifiedMixed n q rows C ops := by
  induction ops generalizing C with
  | nil => trivial
  | cons op tail ih =>
    exact ⟨Or.inl (redirects op (by simp)),ih _ (fun next mem => redirects next (by simp [mem]))⟩

theorem zeroStepsBelow (n : Nat) (C : Circuit) (q : Nat) (ops : List (Nat × Nat))
    (raw : q < n) (mono : Monotone2 C) (valid : validSteps n C ops)
    (redirects : ∀ op ∈ ops, op.2 = q) :
    Monotone2 (eraseSteps n C ops) ∧
    ∀ x : List Bool, x.length = n → x.getD q false = false →
      (eraseSteps n C ops).eval x = true → C.eval x = true :=
  mixedStepsBelow n C q ops (fun x => x.getD q false = false) raw mono
    (fun _ h => h) valid (zeroRedirectCertificate n C q ops _ redirects)

theorem zeroStepsExact (n : Nat) (C : Circuit) (q : Nat) (ops : List (Nat × Nat))
    (rows basis : List Bool → Prop)
    (raw : q < n) (mono : Monotone2 C) (valid : validSteps n C ops)
    (redirects : ∀ op ∈ ops, op.2 = q) (pinned : ∀ x, rows x → x.getD q false = false)
    (covers : ∀ x, x.length = n → rows x → C.eval x = true →
      ∃ y, y.length = n ∧ basis y ∧ Below y x)
    (tests : ∀ y, y.length = n → basis y → (eraseSteps n C ops).eval y = true) :
    ∀ x, x.length = n → rows x → (eraseSteps n C ops).eval x = C.eval x := by
  obtain ⟨well,weak⟩ := zeroStepsBelow n C q ops raw mono valid redirects
  exact exactFromPositiveBasis C _ n rows basis well
    (fun x width mem => weak x width (pinned x mem)) covers tests

#print axioms eraseColdAtMaximum
#print axioms mixedStepsExact
#print axioms zeroStepsBelow
#print axioms zeroStepsExact

end OrderFourZeroDrop18057
