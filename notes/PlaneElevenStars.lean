import Mathlib

namespace PlaneElevenStars

-- Bits 0 through 4 are the common point, two private points, and the two lines.
-- An optional sixth bit is one completed star that can fire on its own.
def path (r : ℕ) : Bool :=
  (r.testBit 3 && (r.testBit 0 || r.testBit 1)) ||
  (r.testBit 4 && (r.testBit 0 || r.testBit 2))
def target (alarm : Bool) (r : ℕ) := (alarm && r.testBit 5) || path r
def join (m i j : ℕ) := (i &&& m) ||| (j &&& (63-m))
def relevant (m : Fin 64) : Prop :=
  (m.val < 31 ∧ 1 < (List.range 5).countP m.val.testBit) ∨ (32 < m.val ∧ m.val < 63)
instance (m : Fin 64) : Decidable (relevant m) := inferInstanceAs (Decidable
  ((m.val < 31 ∧ 1 < (List.range 5).countP m.val.testBit) ∨ (32 < m.val ∧ m.val < 63)))

-- For each relevant block the six base-64 digits give three assignments inside
-- and three outside assignments distinguishing their three pairs of cofactors.
def evidence : List ℕ := [0,0,0,17316192320,0,8860483648,8860483712,17316192320,0,2185265216,303616,4231232,1094746368,2185265216,1094746368,4231232,0,4364238912,1092681856,4364238912,345088,2166848,1092681856,2166848,2164589056,561664,303616,67174976,2164589056,561664,303616,0,0,2228288,2228352,17316192320,4325632,8860483648,8860483712,17316192320,393728,2185265216,303616,4231232,1094746368,2185265216,1094746368,4231232,394240,4364238912,1092681856,4364238912,345088,2166848,1092681856,2166848,2164589056,561664,303616,67174976,2164589056,561664,303616,0]
def part (m : Fin 64) (j : ℕ) := (evidence.getD m.val 0 >>> (6*j)) % 64
def result (m : Fin 64) (a z : ℕ) := target (32 ≤ m.val) (join m.val (part m a) (part m z))

set_option maxRecDepth 12000 in
theorem separated : ∀ m : Fin 64, relevant m →
    result m 0 3 ≠ result m 1 3 ∧ result m 0 4 ≠ result m 2 4 ∧
    result m 1 5 ≠ result m 2 5 := by decide +kernel

theorem noSingleSignal (m : Fin 64) (hm : relevant m)
    (inside : ℕ → Bool) (outside : Bool → ℕ → Bool) :
    ¬∀ a z, outside (inside a) z = target (32 ≤ m.val) (join m.val a z) := by
  intro h
  have distinguish (a b z) (ne : result m a z ≠ result m b z) : inside (part m a) ≠ inside (part m b) := by
    intro eq
    apply ne
    unfold result
    rw [←h,←h,eq]
  obtain ⟨xy,xz,yz⟩ := separated m hm
  have hxy := distinguish 0 1 3 xy
  have hxz := distinguish 0 2 4 xz
  have hyz := distinguish 1 2 5 yz
  have two : ∀ a b c : Bool, a ≠ b → a ≠ c → b ≠ c → False := by decide
  exact two _ _ _ hxy hxz hyz

-- On either internal edge of the five-vertex path, fixing the other three
-- bits gives both AND and OR as two-variable restrictions.
def switched (j : Fin 2) (external a b : Bool) : ℕ :=
  if j=0 then a.toNat + 2*external.toNat + 8*b.toNat + 16*external.toNat
  else a.toNat + 4*external.toNat + 8*external.toNat + 16*b.toNat
theorem pairSwitches : ∀ (j : Fin 2) (a b : Bool),
    path (switched j false a b) = (a && b) ∧ path (switched j true a b) = (a || b) := by decide

inductive Formula where
  | pin (i : ℕ)
  | both (f g : Formula)
  | either (f g : Formula)

def Formula.eval (inputs : ℕ → Bool) : Formula → Bool
  | .pin i => inputs i
  | .both f g => f.eval inputs && g.eval inputs
  | .either f g => f.eval inputs || g.eval inputs

def Formula.slope (inputs : ℕ → Bool) (i : ℕ) : Formula → Bool
  | .pin j => decide (j=i)
  | .both f g => (f.eval inputs && g.slope inputs i) || (f.slope inputs i && g.eval inputs)
  | .either f g => f.slope inputs i || g.slope inputs i

def Formula.uses (i : ℕ) : Formula → ℕ
  | .pin j => if j=i then 1 else 0
  | .both f g | .either f g => f.uses i + g.uses i

theorem absent (f : Formula) (i) (x) (h : f.uses i=0) : f.slope x i = false := by
  induction f with
  | pin j => by_cases eq : j=i <;> simp [Formula.uses,Formula.slope,eq] at *
  | both f g hf hg =>
    obtain ⟨lf,lg⟩ := Nat.add_eq_zero_iff.mp h
    simp [Formula.slope,hf lf,hg lg]
  | either f g hf hg =>
    obtain ⟨lf,lg⟩ := Nat.add_eq_zero_iff.mp h
    simp [Formula.slope,hf lf,hg lg]

theorem singleRead (f : Formula) (i : ℕ) (x : ℕ → Bool) (h : f.uses i ≤ 1) :
    f.eval (fun j => x j || decide (j=i)) = (f.eval x || f.slope x i) := by
  induction f with
  | pin j => rfl
  | either f g hf hg =>
    change f.uses i + g.uses i ≤ 1 at h
    simp only [Formula.eval,Formula.slope,hf (by omega),hg (by omega)]
    generalize f.eval x = a; generalize g.eval x = b
    generalize f.slope x i = c; generalize g.slope x i = d
    cases a <;> cases b <;> cases c <;> cases d <;> decide
  | both f g hf hg =>
    change f.uses i + g.uses i ≤ 1 at h
    simp only [Formula.eval,Formula.slope,hf (by omega),hg (by omega)]
    have one : f.uses i=0 ∨ g.uses i=0 := by omega
    have law : ∀ a b c d : Bool, (c=false ∨ d=false) →
        ((a || c) && (b || d)) = ((a && b) || ((a && d) || (c && b))) := by decide
    exact law _ _ _ _ (one.imp (absent f i x) (absent g i x))

theorem essentialRead (f : Formula) (i) (x) (once : f.uses i ≤ 1)
    (low : f.eval x=false) (high : f.eval (fun j => x j || decide (j=i))=true) :
    f.slope x i = true := by simpa [singleRead f i x once,low] using high

end PlaneElevenStars
