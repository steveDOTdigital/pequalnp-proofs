import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PlaneSharedPencil

abbrev Bits (n : ℕ) := Fin n → Bool

def near (p w : Fin 13) := ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = w+d
instance (p w : Fin 13) : Decidable (near p w) := by unfold near; infer_instance

def pins (x : Bits 26) (i : Fin 20) :=
  if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val+8 else i.val+9))
  else ((decide (i.val ≠ 18) && (x 16 || x 18)) || (decide (i.val ≠ 17) && (x 19 || x 23)))

def o (i j : ℕ) : Gate := ⟨.or,[i,j]⟩
def a (i j : ℕ) : Gate := ⟨.and,[i,j]⟩
def ok (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def fold (gs : List Gate) (w : List Bool) := gs.foldl step w

-- Each group computes one four-line neighborhood and gates it with its point.
-- The last seven ORs combine the eight point stars.
def fixed : List Gate :=
  [o 18 17, o 15 22, o 26 27, a 5 28,
   o 16 18, o 19 23, o 30 31, a 6 32,
   o 20 19, o 17 24, o 34 35, a 7 36,
   o 21 20, o 18 25, o 38 39, a 8 40,
   o 22 21, o 19 13, o 42 43, a 9 44,
   o 23 22, o 20 14, o 46 47, a 10 48,
   o 24 23, o 21 15, o 50 51, a 11 52,
   o 25 24, o 22 16, o 54 55, a 12 56,
   o 29 33, o 58 37, o 59 41, o 60 45, o 61 49, o 62 53, o 63 57]

def rows : List (Fin 13 × List (Fin 13)) :=
  [(5,[5,4,2,9]),(6,[3,5,6,10]),(7,[7,6,4,11]),(8,[8,7,5,12]),(9,[9,8,6,0]),(10,[10,9,7,1]),(11,[11,10,8,2]),(12,[12,11,9,3])]

theorem coverage : ∀ p w : Fin 13, (∃ r ∈ rows, r.1=p ∧ w∈r.2) ↔ 5 ≤ p.val ∧ near p w := by
  decide +kernel

def outside (x : Bits 26) := decide (∃ p w : Fin 13, 5 ≤ p.val ∧ near p w ∧
  x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)

theorem outside_rows (x : Bits 26) : rows.any (fun r => x (Fin.castAdd 13 r.1) &&
    r.2.any (fun w => x (Fin.natAdd 13 w))) = outside x := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, outside, decide_eq_true_eq]
  constructor
  · rintro ⟨r,hr,hp,w,hw,hw'⟩
    obtain ⟨bound,inc⟩ := (coverage r.1 w).mp ⟨r,hr,rfl,hw⟩
    exact ⟨r.1,w,bound,inc,hp,hw'⟩
  · rintro ⟨p,w,bound,inc,hp,hw'⟩
    obtain ⟨r,hr,eq,hw⟩ := (coverage p w).mpr ⟨bound,inc⟩
    exact ⟨r,hr,eq.symm ▸ hp,w,hw,hw'⟩

abbrev base (x : Bits 26) := fold fixed (List.ofFn x)

inductive Formula where
  | var (i : Fin 26)
  | zero
  | conj (a b : Formula)
  | disj (a b : Formula)
  deriving DecidableEq

def Formula.value (x : Bits 26) : Formula → Bool
  | .var i => x i
  | .zero => false
  | .conj a b => a.value x && b.value x
  | .disj a b => a.value x || b.value x

def binary (g : Gate) := ∃ i j : ℕ, g=o i j ∨ g=a i j

theorem fixedBinary : ∀ g ∈ fixed, binary g := by
  have orB (i j : ℕ) : binary (o i j) := ⟨i,j,Or.inl rfl⟩
  have andB (i j : ℕ) : binary (a i j) := ⟨i,j,Or.inr rfl⟩
  simp only [fixed,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,
    orB,andB,true_and,implies_true]

def symStep (w : List Formula) (g : Gate) :=
  let i := w.getD (g.inputs.getD 0 0) .zero
  let j := w.getD (g.inputs.getD 1 0) .zero
  w ++ [match g.op with | .and => .conj i j | _ => .disj i j]

theorem symbolic (gs : List Gate) (legal : ∀ g ∈ gs, binary g) (w : List Formula) (x : Bits 26) :
    (gs.foldl symStep w).map (Formula.value x) = fold gs (w.map (Formula.value x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl symStep (symStep w g)).map (Formula.value x) = fold gs (step (w.map (Formula.value x)) g)
    rw [ih (fun z hz => legal z (by simp [hz]))]
    congr 1
    have rd (j : ℕ) : (w.map (Formula.value x)).getD j false = (w.getD j .zero).value x :=
      List.getD_map w Formula.zero (Formula.value x)
    rcases legal g (by simp) with ⟨i,j,rfl|rfl⟩ <;>
      simp only [symStep,step,o,a,List.map_append,List.map_cons,List.map_nil,GateOp.eval,
        List.any_cons,List.any_nil,List.all_cons,List.all_nil,id_eq,Bool.or_false,Bool.and_true,rd] <;> rfl

def trace := fixed.foldl symStep (List.ofFn Formula.var)

theorem lookup (x : Bits 26) (i : ℕ) : (base x).getD i false = (trace.getD i .zero).value x := by
  have h := symbolic fixed fixedBinary (List.ofFn Formula.var) x
  have eq : (List.ofFn Formula.var).map (Formula.value x) = List.ofFn x := by rw [List.map_ofFn]; rfl
  rw [eq] at h
  change (trace.map (Formula.value x)) = base x at h
  rw [← h]
  exact List.getD_map trace Formula.zero (Formula.value x)

theorem fixedOutput (x : Bits 26) : (base x).getD 64 false = outside x := by
  have cert : trace.getD 64 .zero = (.disj (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var 5) (.disj (.disj (.var 18) (.var 17)) (.disj (.var 15) (.var 22)))) (.conj (.var 6) (.disj (.disj (.var 16) (.var 18)) (.disj (.var 19) (.var 23))))) (.conj (.var 7) (.disj (.disj (.var 20) (.var 19)) (.disj (.var 17) (.var 24))))) (.conj (.var 8) (.disj (.disj (.var 21) (.var 20)) (.disj (.var 18) (.var 25))))) (.conj (.var 9) (.disj (.disj (.var 22) (.var 21)) (.disj (.var 19) (.var 13))))) (.conj (.var 10) (.disj (.disj (.var 23) (.var 22)) (.disj (.var 20) (.var 14))))) (.conj (.var 11) (.disj (.disj (.var 24) (.var 23)) (.disj (.var 21) (.var 15))))) (.conj (.var 12) (.disj (.disj (.var 25) (.var 24)) (.disj (.var 22) (.var 16))))) := by decide +kernel
  rw [lookup,cert,← outside_rows]
  simp only [Formula.value,rows,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  rfl

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

theorem base_length (x : Bits 26) : (base x).length = 65 := by rw [fold_length,List.length_ofFn]; rfl

-- Physical wires 30, 31 and 32 already exist inside the star centered at point six.
def wire (j : ℕ) := if j < 17 then (if j < 5 then j else if j < 14 then j+8 else j+9)
  else if j < 20 then j+13 else j+45

theorem smallWire (j : Fin 20) : wire j.val < 65 := by unfold wire; split_ifs <;> omega


theorem helperBits (x : Bits 26) :
    (base x).getD 30 false = (x 16 || x 18) ∧
    (base x).getD 31 false = (x 19 || x 23) ∧
    (base x).getD 32 false = ((x 16 || x 18) || (x 19 || x 23)) := by
  have cert : trace.getD 30 .zero = .disj (.var 16) (.var 18) ∧
      trace.getD 31 .zero = .disj (.var 19) (.var 23) ∧
      trace.getD 32 .zero = .disj (.disj (.var 16) (.var 18)) (.disj (.var 19) (.var 23)) := by decide +kernel
  simp only [lookup,cert.1,cert.2.1,cert.2.2,Formula.value,and_self]

theorem basePins (x : Bits 26) (i : Fin 20) : (base x).getD (wire i.val) false = pins x i := by
  by_cases hi : i.val<17
  · have hj : wire i.val<26 := by unfold wire; split_ifs <;> omega
    rw [kept _ _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_ofFn,pins,hi,↓reduceIte]
    congr 1
    apply Fin.ext
    change wire i.val = _ % 26
    rw [← show wire i.val = (if i.val < 5 then i.val else if i.val < 14 then i.val+8 else i.val+9) by simp [wire,hi]]
    omega
  · have cases3 : i = 17 ∨ i = 18 ∨ i = 19 := by omega
    rcases cases3 with rfl|rfl|rfl
    · change (base x).getD 30 false = ((true && (x 16 || x 18)) || (false && (x 19 || x 23)))
      simpa using (helperBits x).1
    · change (base x).getD 31 false = ((false && (x 16 || x 18)) || (true && (x 19 || x 23)))
      simpa using (helperBits x).2.1
    · change (base x).getD 32 false = ((true && (x 16 || x 18)) || (true && (x 19 || x 23)))
      simpa using (helperBits x).2.2

def liftGate (g : Gate) : Gate := ⟨g.op,g.inputs.map wire⟩

theorem read_append (w : List Bool) (b : Bool) (i : ℕ) :
    (w++[b]).getD i false = if i=w.length then b else w.getD i false := by
  by_cases h : i<w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default w _ (by omega)]
    by_cases he : i=w.length
    · simp [he]
    · rw [List.getD_eq_default _ _ (by simp; omega),ite_eq_right he]

theorem simulate (gs : List Gate) (w v : List Bool) (hw : 20 ≤ w.length) (hv : v.length=w.length+45)
    (rel : ∀ i, w.getD i false = v.getD (wire i) false) (i : ℕ) :
    (fold gs w).getD i false = (fold (gs.map liftGate) v).getD (wire i) false := by
  induction gs generalizing w v with
  | nil => exact rel i
  | cons g gs ih =>
    change (fold gs (step w g)).getD i false = (fold (gs.map liftGate) (step v (liftGate g))).getD (wire i) false
    apply ih
    · simp [step]; omega
    · simp [step,hv]
    · intro j
      have hg : (liftGate g).op.eval ((liftGate g).inputs.map fun k => v.getD k false) =
          g.op.eval (g.inputs.map fun k => w.getD k false) := by simp only [liftGate,List.map_map,Function.comp_def,rel]
      have he : wire j = v.length ↔ j=w.length := by
        by_cases hj : j<20
        · have hh := smallWire ⟨j,hj⟩
          change wire j < 65 at hh
          omega
        · simp [wire,show ¬j<17 by omega,hj,hv]
      simp only [step,read_append,hg,he,rel]

theorem assemble : let pins (x : Fin 26 → Bool) (i : Fin 20) :=
        if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val+8 else i.val+9))
        else ((decide (i.val ≠ 18) && (x 16 || x 18)) || (decide (i.val ≠ 17) && (x 19 || x 23)))
      let near (p w : Fin 13) := ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = w+d
      ∀ D : Circuit, Monotone2 D → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size+40 ∧
        ∀ x : Fin 26 → Bool, circuitFun 26 C x =
          (decide (∃ p w : Fin 13, 5 ≤ p.val ∧ near p w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true) ||
          circuitFun 20 D (pins x)) := by
  change ∀ D : Circuit, Monotone2 D → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size+40 ∧
    ∀ x : Bits 26, circuitFun 26 C x = (outside x || circuitFun 20 D (pins x))
  intro D hD
  let rest := D.gates.map liftGate
  let joined := o 64 (wire D.output)
  let C : Circuit := ⟨fixed ++ rest ++ [joined],65+D.gates.length⟩
  have fm : ∀ g ∈ fixed, ok g := by
    intro g hg
    rcases fixedBinary g hg with ⟨i,j,rfl|rfl⟩ <;> simp [ok,o,a]
  have hm : Monotone2 C := by
    intro g h
    change g ∈ fixed ++ rest ++ [joined] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · exact fm g h
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
        obtain ⟨ho,hlen⟩ := hD z hz
        exact ⟨ho,by simpa [liftGate] using hlen⟩
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨Or.inr rfl,by change 2 ≤ 2; decide⟩
  refine ⟨C,hm,?_,?_⟩
  · change (fixed ++ rest ++ [joined]).length ≤ D.gates.length+40
    have ln : fixed.length=39 := rfl
    simp [rest,ln]; omega
  · intro x
    let v := fold rest (base x)
    have len : v.length=65+D.gates.length := by rw [show v.length = (base x).length + rest.length from fold_length _ _,base_length]; simp [rest]
    have init (i : ℕ) : (List.ofFn (pins x)).getD i false = (base x).getD (wire i) false := by
      by_cases hi : i<20
      · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]
        exact (basePins x ⟨i,hi⟩).symm
      · have hi' : 65 ≤ wire i := by simp [wire,show ¬i<17 by omega,hi]; omega
        rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by rw [base_length]; exact hi')]
    have carry : v.getD 64 false = outside x := (kept rest _ 64 (by rw [base_length]; decide)).trans (fixedOutput x)
    have core : v.getD (wire D.output) false = circuitFun 20 D (pins x) :=
      (simulate D.gates (List.ofFn (pins x)) (base x) (by simp) (by simp [base_length]) init D.output).symm
    change (fold (fixed ++ rest ++ [joined]) (List.ofFn x)).getD (65+D.gates.length) false = _
    simp only [fold,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (step v joined).getD (65+D.gates.length) false = _
    rw [step,read_append,ite_eq_left len.symm]
    change (v.getD 64 false || (v.getD (wire D.output) false || false)) = _
    rw [carry,core,Bool.or_false]

end PlaneSharedPencil
