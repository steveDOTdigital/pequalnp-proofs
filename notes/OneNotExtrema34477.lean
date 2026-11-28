import OrderFourZeroDrop18057

namespace OneNotExtrema34477

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open OrderFourZeroDrop18057

def prefixTape (C : Circuit) (m : Nat) (x : List Bool) : List Bool :=
  (⟨C.gates.take m,0⟩ : Circuit).wires x

def tail (C : Circuit) (m : Nat) : Circuit :=
  ⟨C.gates.drop (m+1), C.output⟩

def constant (b : Bool) : Gate :=
  ⟨if b then .and else .or,[]⟩

def forced (C : Circuit) (m : Nat) (b : Bool) : Circuit :=
  ⟨C.gates.take m ++ constant b :: C.gates.drop (m+1),C.output⟩

def value (C : Circuit) (m : Nat) (bound : m < C.gates.length) (x : List Bool) : Bool :=
  let g := C.gates[m]
  g.op.eval (g.inputs.map fun i => (prefixTape C m x).getD i false)

def allowedOutside (C : Circuit) (m : Nat) : Prop :=
  ∀ j (h : j < C.gates.length), j ≠ m →
    C.gates[j].op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ C.gates[j].inputs.length ≤ 2

theorem forcedSize (C : Circuit) (m : Nat) (b : Bool) (bound : m < C.gates.length) :
    (forced C m b).size = C.size := by
  simp only [forced,Circuit.size,List.length_append,List.length_cons,List.length_take,
    List.length_drop,Nat.min_eq_left (Nat.le_of_lt bound)]
  omega

private theorem allowedHead (C : Circuit) (m : Nat) (hyp : allowedOutside C m) :
    Monotone2 (⟨C.gates.take m,0⟩ : Circuit) := by
  intro g mg
  obtain ⟨i,hi,atI⟩ := List.getElem_of_mem mg
  have short : i < m := by simp at hi; omega
  have bound : i < C.gates.length := by simp at hi; omega
  have pos : C.gates[i] = g := by simpa using atI
  simpa only [pos] using hyp i bound (by omega)

theorem allowedTail (C : Circuit) (m : Nat) (hyp : allowedOutside C m) :
    Monotone2 (tail C m) := by
  intro g mg
  change g ∈ C.gates.drop (m+1) at mg
  obtain ⟨i,hi,get⟩ := List.getElem_of_mem mg
  have bound : m+1+i < C.gates.length := by simp at hi; omega
  have pos : C.gates[m+1+i] = g := by simpa using get
  simpa only [pos] using hyp (m+1+i) bound (by omega)

theorem forcedMono (C : Circuit) (m : Nat) (b : Bool) (hyp : allowedOutside C m) :
    Monotone2 (forced C m b) := by
  intro g mem
  change g ∈ C.gates.take m ++ constant b :: C.gates.drop (m+1) at mem
  rcases List.mem_append.mp mem with front | back
  · exact allowedHead C m hyp g front
  rcases List.mem_cons.mp back with rfl | last
  · cases b <;> simp [constant]
  · exact allowedTail C m hyp g last

theorem forcedEval (C : Circuit) (m : Nat) (b : Bool) (x : List Bool) :
    (forced C m b).eval x = (tail C m).eval (prefixTape C m x ++ [b]) := by
  unfold Circuit.eval Circuit.wires forced tail prefixTape
  rw [List.foldl_append]
  cases b <;> rfl

theorem originalEval (C : Circuit) (m : Nat) (x : List Bool)
    (bound : m < C.gates.length) :
    C.eval x = (tail C m).eval (prefixTape C m x ++ [value C m bound x]) := by
  have parts : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m+1) := by
    conv_lhs => rw [← List.take_append_drop m C.gates]
    exact congrArg (C.gates.take m ++ ·) (List.drop_eq_getElem_cons bound)
  conv_lhs =>
    unfold Circuit.eval Circuit.wires
    rw [parts,List.foldl_append]
  rfl

private theorem appendBits (w : List Bool) (a b : Bool)
    (order : a = true → b = true) : Below (w ++ [a]) (w ++ [b]) := by
  intro i one
  by_cases old : i < w.length
  · rw [List.getD_append _ _ _ _ old] at one ⊢
    exact one
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt old)] at one ⊢
    by_cases atEnd : i = w.length
    · simp only [atEnd,Nat.sub_self] at one ⊢
      exact order one
    · have outside : [a].length ≤ i-w.length := by simp; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none outside] at one

theorem forceEqual (C : Circuit) (m : Nat) (x : List Bool) (b : Bool)
    (bound : m < C.gates.length) (atGate : value C m bound x = b) :
    (forced C m b).eval x = C.eval x := by
  rw [forcedEval,originalEval C m x bound,atGate]

theorem forceSandwich (C : Circuit) (m : Nat) (x : List Bool)
    (bound : m < C.gates.length) (hyp : allowedOutside C m) :
    ((forced C m false).eval x = true → C.eval x = true) ∧
      (C.eval x = true → (forced C m true).eval x = true) := by
  rw [forcedEval,forcedEval,originalEval C m x bound]
  constructor
  · exact evalBelow _ _ _ (allowedTail C m hyp) (by simp)
      (appendBits _ _ _ (by simp))
  · exact evalBelow _ _ _ (allowedTail C m hyp) (by simp)
      (appendBits _ _ _ (by simp))

theorem lowerReplacement (C : Circuit) (m n : Nat) (basis : List Bool → Prop)
    (bound : m < C.gates.length) (good : allowedOutside C m)
    (positive : ∀ x, x.length = n → C.eval x = true →
      ∃ y, y.length = n ∧ basis y ∧ Below y x)
    (tests : ∀ y, y.length = n → basis y → C.eval y = true ∧ value C m bound y = false) :
    ∀ x, x.length = n → (forced C m false).eval x = C.eval x := by
  have proof := exactFromPositiveBasis C (forced C m false) n (fun _ => True) basis
    (forcedMono C m false good)
    (fun x _ _ => (forceSandwich C m x bound good).1)
    (fun x hx _ yes => positive x hx yes)
    (fun y hy mem => (forceEqual C m y false bound (tests y hy mem).2).trans (tests y hy mem).1)
  exact fun x width => proof x width trivial

theorem upperReplacement (C : Circuit) (m n : Nat) (basis : List Bool → Prop)
    (bound : m < C.gates.length) (good : allowedOutside C m)
    (negative : ∀ x, x.length = n → C.eval x = false →
      ∃ y, y.length = n ∧ basis y ∧ Below x y)
    (tests : ∀ y, y.length = n → basis y → C.eval y = false ∧ value C m bound y = true) :
    ∀ x, x.length = n → (forced C m true).eval x = C.eval x := by
  intro x width
  cases out : C.eval x
  · obtain ⟨y,hy,member,compare⟩ := negative x width out
    have atY := (forceEqual C m y true bound (tests y hy member).2).trans (tests y hy member).1
    cases hit : (forced C m true).eval x
    · rfl
    · have rises := evalBelow (forced C m true) x y (forcedMono C m true good)
        (width.trans hy.symm) compare hit
      rw [atY] at rises
      contradiction
  · exact (forceSandwich C m x bound good).2 out

#print axioms forcedMono
#print axioms forceSandwich
#print axioms lowerReplacement
#print axioms upperReplacement

end OneNotExtrema34477
