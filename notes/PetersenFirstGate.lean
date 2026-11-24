import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenFirstGate

abbrev Bits := Fin 9 → Bool
def target : Bits → Bool := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def reps : List (Fin 9 × Fin 9) := ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9))

inductive Expr (α : Type) where
  | lit (b : Bool)
  | copy (i : α)
  | neg (i : α)
  | pair (b : Bool) (i j : α)

def val (f : α → Bool) : Bool ⊕ α → Bool := Sum.elim id f
def op (b x y : Bool) := if b then x && y else x || y

def Expr.eval (e : Expr α) (f : α → Bool) : Bool :=
  match e with
  | .lit b => b
  | .copy i => f i
  | .neg i => !(f i)
  | .pair b i j => op b (f i) (f j)

def combine (b : Bool) : Bool ⊕ α → Bool ⊕ α → Expr α
  | .inl x,.inl y => .lit (op b x y)
  | .inl x,.inr j => if x == b then .copy j else .lit x
  | .inr i,.inl y => if y == b then .copy i else .lit y
  | .inr i,.inr j => .pair b i j

theorem combine_eval (b) (a c : Bool ⊕ α) (f : α → Bool) :
    (combine b a c).eval f = op b (val f a) (val f c) := by
  rcases a with a|i <;> rcases c with c|j
  · cases b <;> cases a <;> cases c <;> rfl
  · cases b <;> cases a <;> simp [combine,Expr.eval,val,op]
  · cases b <;> cases c <;> simp [combine,Expr.eval,val,op]
  · rfl

def fromPins (g : Gate) (ρ : ℕ → Bool ⊕ α) : Expr α :=
  let xs := g.inputs.map ρ
  let binary (b : Bool) := combine b (xs[0]?.getD (.inl b)) (xs[1]?.getD (.inl b))
  match g.op with
  | .and => binary true
  | .or => binary false
  | .not => match xs.head?.getD (.inl false) with
    | .inl b => .lit (!b)
    | .inr i => .neg i
  | _ => .lit false

def ok (g : Gate) := g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem fromPins_eval (g : Gate) (hg : ok g) (ρ : ℕ → Bool ⊕ α) (f : α → Bool) :
    (fromPins g ρ).eval f = g.op.eval (g.inputs.map fun j => val f (ρ j)) := by
  obtain ⟨o,pins⟩ := g
  obtain ⟨ho,hl⟩ := hg
  change o = .and ∨ o = .or ∨ o = .not at ho
  change pins.length ≤ 2 at hl
  rcases ho with rfl|rfl|rfl <;> cases pins with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases h : ρ a <;> simp [fromPins, h, combine_eval, val, op, GateOp.eval] <;> rfl
    | cons b xs =>
      obtain rfl : xs = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      cases h : ρ a <;> simp [fromPins, h, combine_eval, val, op, GateOp.eval] <;> rfl

def Expr.gate (e : Expr α) (idx : α → ℕ) : Gate :=
  match e with
  | .lit true => ⟨.and,[]⟩
  | .lit false => ⟨.or,[]⟩
  | .copy i => ⟨.or,[idx i]⟩
  | .neg i => ⟨.not,[idx i]⟩
  | .pair b i j => ⟨if b then .and else .or,[idx i,idx j]⟩

theorem Expr.gate_ok (e : Expr α) (idx : α → ℕ) : ok (e.gate idx) := by
  cases e with
  | lit b => cases b <;> simp [ok, Expr.gate]
  | pair b i j => cases b <;> simp [ok, Expr.gate]
  | _ => simp [ok, Expr.gate]

theorem Expr.gate_eval (e : Expr α) (idx : α → ℕ) (f : ℕ → Bool) :
    (e.gate idx).op.eval ((e.gate idx).inputs.map f) = e.eval (fun i => f (idx i)) := by
  cases e with
  | lit b => cases b <;> rfl
  | pair b i j => cases b <;> simp [Expr.gate, Expr.eval, op, GateOp.eval]
  | _ => simp [Expr.gate, Expr.eval, GateOp.eval]

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def fold (gs : List Gate) (w : List Bool) := gs.foldl step w
def recode (ρ : ℕ → Bool ⊕ ℕ) (g : Gate) := (fromPins g ρ).gate id

theorem read_append (w : List Bool) (a : Bool) (i : ℕ) :
    (w++[a]).getD i false = if i = w.length then a else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default w _ (by omega)]
    by_cases h' : i=w.length
    · simp [h']
    · rw [List.getD_eq_default _ _ (by simp; omega), ite_eq_right h']

theorem fold_length (gs : List Gate) (w : List Bool) : (fold gs w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [fold]
  | cons g gs ih =>
    change (fold gs (step w g)).length = _
    rw [ih]
    simp [step, Nat.add_comm, Nat.add_left_comm]

theorem fold_kept (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i<w.length) :
    (fold gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (fold gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

-- Indices above the first gate are unchanged. Earlier wires can be constants or renamed inputs.
theorem simulate (ρ : ℕ → Bool ⊕ ℕ) (high : ∀ j, 10 ≤ j → ρ j = .inr j)
    (low : ∀ i j, i<10 → ρ i = .inr j → j<10) (gs : List Gate) (legal : ∀ g ∈ gs, ok g)
    (w v : List Bool) (hw : 10 ≤ w.length) (hlen : v.length=w.length)
    (rel : ∀ j, w.getD j false = val (fun i => v.getD i false) (ρ j)) (j : ℕ) :
    (fold gs w).getD j false = val (fun i => (fold (gs.map (recode ρ)) v).getD i false) (ρ j) := by
  induction gs generalizing w v with
  | nil => exact rel j
  | cons g gs ih =>
    change (fold gs (step w g)).getD j false =
      val (fun i => (fold (gs.map (recode ρ)) (step v (recode ρ g))).getD i false) (ρ j)
    apply ih (fun z hz => legal z (by simp [hz]))
    · simp [step]; omega
    · simp [step, hlen]
    · have he : (recode ρ g).op.eval ((recode ρ g).inputs.map fun i => v.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [recode, Expr.gate_eval, fromPins_eval g (legal g (by simp))]
        simp only [id_eq, ← rel]
      intro i
      simp only [step, he, read_append, hlen]
      by_cases hi : 10 ≤ i
      · rw [high i hi]
        have hr := rel i
        rw [high i hi] at hr
        simp [val] at hr ⊢
        rw [hr]
      · rw [ite_eq_right (by omega : i ≠ w.length), rel]
        cases hm : ρ i with
        | inl b => rfl
        | inr k =>
          have hk := low i k (by omega) hm
          simp [val, show k ≠ w.length by omega]


def perm : Fin 12 → Fin 9 → Fin 9 :=
  ![![0,1,2,3,4,5,6,7,8],
    ![1,2,3,8,6,0,7,4,5],
    ![2,3,8,5,7,1,4,6,0],
    ![3,8,5,0,4,2,6,7,1],
    ![8,5,0,1,6,3,7,4,2],
    ![5,0,1,2,7,8,4,6,3],
    ![0,5,8,3,4,1,7,6,2],
    ![1,0,5,8,6,2,4,7,3],
    ![2,1,0,5,7,3,6,4,8],
    ![3,2,1,0,4,8,7,6,5],
    ![8,3,2,1,6,5,4,7,0],
    ![5,8,3,2,7,0,6,4,1]]

theorem preserves (h : Fin 12) (x : Bits) : target (fun i => x (perm h i)) = target x := by
  fin_cases h
  · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 2 && x 7) || (x 3 && x 4) || (x 8 && x 5) || (x 0 && x 4) || (x 7 && x 5) || (x 5 && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 1) || (x 3 && x 4) || (x 8 && x 6) || (x 5 && x 0) || (x 1 && x 6) || (x 4 && x 0) || (x 0 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 8 && x 6) || (x 5 && x 7) || (x 0 && x 1) || (x 2 && x 7) || (x 6 && x 1) || (x 1 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 8 && x 5) || (x 5 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 3) || (x 5 && x 7) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 7 && x 2) || (x 2 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 5 && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 8 && x 6) || (x 4 && x 3) || (x 3 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 2 && x 7) || (x 4 && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 3 && x 4) || (x 6 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 8 && x 6) || (x 7 && x 5) || (x 5 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 8 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 3 && x 4) || (x 2 && x 7) || (x 1 && x 0) || (x 5 && x 7) || (x 4 && x 0) || (x 0 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl
  · change ((x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 8 && x 6) || (x 3 && x 4) || (x 2 && x 1) || (x 0 && x 4) || (x 6 && x 1) || (x 1 && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    ac_rfl

theorem unaryOrbit : ∀ i : Fin 9, ∃ h : Fin 12, perm h i ∈ ([0,4] : List (Fin 9)) := by decide

theorem pairOrbit : ∀ i j : Fin 9, i ≠ j → ∃ h : Fin 12,
    (perm h i,perm h j) ∈ reps ∨ (perm h j,perm h i) ∈ reps := by decide

def Allowed (e : Expr (Fin 9)) : Prop :=
  (∃ i ∈ ([0,4] : List (Fin 9)), e = .neg i) ∨
  (∃ p ∈ reps, ∃ b, e = .pair b p.1 p.2)

abbrev Seed := Bool ⊕ Option (Fin 9)
def seedValue (x : Bits) (b : Bool) : Seed → Bool
  | .inl c => c
  | .inr none => b
  | .inr (some i) => x i

-- A constant or copy frees the first slot. It can hold a canonical NOT because
-- the remaining gates can use the original constant or raw input directly.
theorem choose (e : Expr (Fin 9)) : ∃ (π : Fin 9 → Fin 9) (g : Expr (Fin 9)) (s : Seed),
    (∀ x, target (fun i => x (π i)) = target x) ∧ Allowed g ∧
    ∀ x, e.eval (fun i => x (π i)) = seedValue x (g.eval x) s := by
  have defaultOK : Allowed (.neg 0) := Or.inl ⟨0,by decide,rfl⟩
  cases e with
  | lit b => exact ⟨id,.neg 0,.inl b,fun _ => rfl,defaultOK,fun _ => rfl⟩
  | copy i => exact ⟨id,.neg 0,.inr (some i),fun _ => rfl,defaultOK,fun _ => rfl⟩
  | neg i =>
    obtain ⟨h,hi⟩ := unaryOrbit i
    exact ⟨perm h,.neg (perm h i),.inr none,preserves h,Or.inl ⟨_,hi,rfl⟩,fun _ => rfl⟩
  | pair b i j =>
    by_cases he : i = j
    · subst j
      refine ⟨id,.neg 0,.inr (some i),fun _ => rfl,defaultOK,?_⟩
      intro x
      cases b <;> simp [Expr.eval,op,seedValue]
    · obtain ⟨h,hp|hp⟩ := pairOrbit i j he
      · exact ⟨perm h,.pair b (perm h i) (perm h j),.inr none,preserves h,
          Or.inr ⟨_,hp,b,rfl⟩,fun _ => rfl⟩
      · refine ⟨perm h,.pair b (perm h j) (perm h i),.inr none,preserves h,
          Or.inr ⟨_,hp,b,rfl⟩,?_⟩
        intro x
        cases b <;> simp [Expr.eval,op,seedValue,Bool.and_comm,Bool.or_comm]

def raw (i : ℕ) : Bool ⊕ Fin 9 := if h : i < 9 then .inr ⟨i,h⟩ else .inl false
theorem readRaw (x : Bits) (i : ℕ) : (List.ofFn x).getD i false = val x (raw i) := by
  by_cases hi : i < 9
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn,raw,hi, ↓reduceDIte,val,Sum.elim_inr]
  · exact (List.getD_eq_default _ _ (by simp; omega)).trans (by simp [raw,hi,val])

def codeSeed : Seed → Bool ⊕ ℕ
  | .inl b => .inl b
  | .inr none => .inr 9
  | .inr (some i) => .inr i.val

def rename (π : Fin 9 → Fin 9) (s : Seed) (i : ℕ) : Bool ⊕ ℕ :=
  if h : i<9 then .inr (π ⟨i,h⟩).val else if i=9 then codeSeed s else .inr i

theorem renameHigh (π : Fin 9 → Fin 9) (s : Seed) (j : ℕ) (hj : 10≤j) :
    rename π s j = .inr j := by simp [rename,show ¬ j<9 by omega,show j≠9 by omega]

theorem renameLow (π : Fin 9 → Fin 9) (s : Seed) (i j : ℕ) (hi : i<10)
    (hr : rename π s i = .inr j) : j<10 := by
  by_cases h : i<9
  · simp [rename,h] at hr
    omega
  · obtain rfl : i=9 := by omega
    cases s with
    | inl c => simp [rename,codeSeed] at hr
    | inr o =>
      cases o <;> simp [rename,codeSeed] at hr <;> omega

theorem seedRead (x : Bits) (b : Bool) (s : Seed) :
    seedValue x b s = val (fun i => (List.ofFn x ++ [b]).getD i false) (codeSeed s) := by
  cases s with
  | inl c => rfl
  | inr o =>
    cases o with
    | none => simp [seedValue, val, codeSeed]
    | some i =>
      simp only [seedValue, val, codeSeed, Sum.elim_inr, read_append, List.length_ofFn]
      rw [ite_eq_right (by omega : i.val ≠ 9), List.getD_eq_getElem _ _ (by simp)]
      simp only [List.getElem_ofFn]

theorem initialRel (π : Fin 9 → Fin 9) (s : Seed) (x : Bits) (b : Bool) (j : ℕ) :
    (List.ofFn (fun i => x (π i)) ++ [seedValue x b s]).getD j false =
    val (fun i => (List.ofFn x ++ [b]).getD i false) (rename π s j) := by
  by_cases hj : j<9
  · simp only [read_append, List.length_ofFn]
    simp only [rename,hj, ↓reduceDIte,val,Sum.elim_inr]
    rw [ite_eq_right (by omega : j≠9), ite_eq_right (by omega : (π ⟨j,hj⟩).val ≠9),
      List.getD_eq_getElem _ _ (by simpa using hj),List.getD_eq_getElem _ _ (by simp)]
    simp only [List.getElem_ofFn]
  · by_cases hj' : j=9
    · subst j
      simpa [rename, read_append] using seedRead x b s
    · rw [renameHigh _ _ _ (by omega)]
      change _ = (List.ofFn x ++ [b]).getD j false
      rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

theorem singleFalse (i : Fin 9) : target (fun j => decide (j=i)) = false := by
  fin_cases i <;> decide

theorem normalize : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ circuitFun 9 D = circuitFun 9 C ∧
        ((∃ i ∈ ([0,4] : List (Fin 9)), ∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = !(x i)) ∨
        (∃ p ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)), ∃ b : Bool, ∀ x : Fin 9 → Bool,
          (D.wires (List.ofFn x)).getD 9 false = if b then x p.1 && x p.2 else x p.1 || x p.2)) := by
  intro C legal hc
  change circuitFun 9 C = target at hc
  obtain ⟨gates,out⟩ := C
  cases gates with
  | nil =>
    exfalso
    have hfun (x : Bits) : (List.ofFn x).getD out false = target x := congrFun hc x
    by_cases ho : out < 9
    · let i : Fin 9 := ⟨out,ho⟩
      have h := hfun (fun j => decide (j=i))
      rw [singleFalse, List.getD_eq_getElem _ _ (by simpa using ho)] at h
      simp only [List.getElem_ofFn, i, decide_true] at h
      contradiction
    · have h := hfun (fun _ => true)
      rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction
  | cons g gs =>
    have hg : ok g := legal g (by simp)
    have hgs (z) (hz : z ∈ gs) : ok z := legal z (by simp [hz])
    let e := fromPins g raw
    obtain ⟨π,b,s,hπ,hb,he⟩ := choose e
    let ρ := rename π s
    let first := b.gate Fin.val
    let tail := gs.map (recode ρ)
    let D : Circuit := ⟨first :: tail, (ρ out).elim (fun _ => 0) id⟩
    have hD : FanInTwo D := by
      intro z hz
      change z ∈ first :: gs.map (recode ρ) at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact b.gate_ok _
      · obtain ⟨old,_,rfl⟩ := List.mem_map.mp hz
        exact Expr.gate_ok _ _
    have hsiz : D.size ≤ (Circuit.mk (g::gs) out).size := by simp [Circuit.size,D,tail]
    have newstep (x : Bits) : step (List.ofFn x) first = List.ofFn x ++ [b.eval x] := by
      have inputs (j : Fin 9) : (List.ofFn x).getD j.val false = x j := by
        rw [List.getD_eq_getElem _ _ (by simp)]
        simp only [List.getElem_ofFn]
      simp only [step,first,Expr.gate_eval,inputs]
    have newW (x : Bits) : D.wires (List.ofFn x) = fold tail (List.ofFn x ++ [b.eval x]) := by
      change fold tail (step (List.ofFn x) first) = _
      rw [newstep]
    have oldstep (x : Bits) :
        step (List.ofFn (fun i => x (π i))) g =
          List.ofFn (fun i => x (π i)) ++ [seedValue x (b.eval x) s] := by
      have h := (fromPins_eval g hg raw (fun i => x (π i))).symm
      rw [← he x]
      simpa only [step,e,← readRaw] using congrArg (fun v => List.ofFn (fun i => x (π i)) ++ [v]) h
    have same (x : Bits) : target x = val (fun i => (D.wires (List.ofFn x)).getD i false) (ρ out) := by
      rw [← hπ x, ← congrFun hc (fun i => x (π i))]
      change (fold gs (step (List.ofFn (fun i => x (π i))) g)).getD out false = _
      rw [oldstep,newW]
      exact simulate ρ (renameHigh π s) (renameLow π s) gs hgs _ _ (by simp) (by simp)
        (initialRel π s x (b.eval x)) out
    have comp : circuitFun 9 D = target := by
      cases h : ρ out with
      | inr i =>
        funext x
        have ht := same x
        rw [h] at ht
        simpa only [circuitFun,Circuit.eval,D,h,Sum.elim_inr,id_eq,val] using ht.symm
      | inl c =>
        have ha := same (fun _ => true)
        have hz := same (fun _ => false)
        rw [h] at ha hz
        change true = c at ha
        change false = c at hz
        cases c <;> contradiction
    have atFirst (x : Bits) : (D.wires (List.ofFn x)).getD 9 false = b.eval x := by
      rw [newW,fold_kept _ _ _ (by simp),read_append]
      simp
    refine ⟨D,hD,hsiz,comp.trans hc.symm,?_⟩
    rcases hb with ⟨i,hi,rfl⟩ | ⟨p,hp,t,rfl⟩
    · exact Or.inl ⟨i,hi,atFirst⟩
    · exact Or.inr ⟨p,hp,t,atFirst⟩

end PetersenFirstGate
