import Mathlib.Tactic

namespace GenericHelperPrice

-- Any proposed nonnegative integer weights can certify a raw-leaf bound.
-- The feature capacities count compulsory reports and eligible dominations.
theorem weightedPrice {V I : Type} [Fintype V] [Fintype I]
    (scale : ℕ) (raw localMin : V → ℕ) (charge : V → I → ℕ) (weights cap : I → ℕ)
    (lower : ∀ v, localMin v ≤ scale*raw v + ∑ i, weights i * charge v i)
    (upper : ∀ i, (∑ v, charge v i) ≤ cap i) :
    (∑ v, localMin v) ≤ scale*(∑ v, raw v) + ∑ i, weights i * cap i := by
  calc
    (∑ v, localMin v) ≤ ∑ v, (scale*raw v + ∑ i, weights i * charge v i) :=
      Finset.sum_le_sum (fun v _ => lower v)
    _ = scale*(∑ v, raw v) + ∑ i, weights i*(∑ v, charge v i) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_comm (f := fun v i => weights i * charge v i)]
      simp only [Finset.mul_sum]
    _ ≤ _ := Nat.add_le_add_left (Finset.sum_le_sum (fun i _ =>
      Nat.mul_le_mul_left _ (upper i))) _

inductive Expr (n : ℕ) where
  | raw (v : Fin n)
  | gate (isOr : Bool) (left right : Expr n)

def op (isOr a b : Bool) := if isOr then a || b else a && b

def Expr.val {n} : Expr n → (Fin n → Bool) → Bool
  | .raw v,x => x v
  | .gate k a b,x => op k (a.val x) (b.val x)

def Expr.size {n} : Expr n → ℕ
  | .raw _ => 1
  | .gate _ a b => a.size+b.size

def Expr.removed {n} (S : Finset (Fin n)) : Expr n → ℕ
  | .raw i => if i ∈ S then 1 else 0
  | .gate _ a b => a.removed S + b.removed S

def merge {n} (k : Bool) (a b : Option (Expr n)) : Option (Expr n) :=
  match a,b with
  | some t,some u => some (.gate k t u)
  | some t,none => if k then some t else none
  | none,some u => if k then some u else none
  | none,none => none

def Expr.cut {n} (S : Finset (Fin n)) : Expr n → Option (Expr n)
  | .raw i => if i ∈ S then none else some (.raw i)
  | .gate k a b => merge k (a.cut S) (b.cut S)

def sizeOpt {n} : Option (Expr n) → ℕ
  | some a => a.size
  | none => 0

def valOpt {n} (x : Fin n → Bool) : Option (Expr n) → Bool
  | some a => a.val x
  | none => false

theorem mergeSize {n} (k : Bool) (a b : Option (Expr n)) :
    sizeOpt (merge k a b) ≤ sizeOpt a+sizeOpt b := by
  cases a <;> cases b <;> cases k <;> simp [merge,sizeOpt,Expr.size]

theorem cutSize {n} (S : Finset (Fin n)) (t : Expr n) :
    sizeOpt (t.cut S) + t.removed S ≤ t.size := by
  induction t with
  | raw i => by_cases h : i ∈ S <;> simp [Expr.cut,Expr.removed,Expr.size,sizeOpt,h]
  | gate k a b ha hb =>
    have h := mergeSize k (a.cut S) (b.cut S)
    simp only [Expr.cut,Expr.removed,Expr.size]
    omega

theorem mergeVal {n} (x : Fin n → Bool) (k : Bool) (a b : Option (Expr n)) :
    valOpt x (merge k a b) = op k (valOpt x a) (valOpt x b) := by
  cases a <;> cases b <;> cases k <;> simp [merge,valOpt,Expr.val,op]

theorem cutVal {n} (S : Finset (Fin n)) (t : Expr n) (x : Fin n → Bool) :
    valOpt x (t.cut S) = t.val (fun i => if i ∈ S then false else x i) := by
  induction t with
  | raw i => by_cases h : i ∈ S <;> simp [Expr.cut,Expr.val,valOpt,h]
  | gate k a b ha hb => simp only [Expr.cut,mergeVal,Expr.val,ha,hb]

theorem rising {n} (t : Expr n) (x y : Fin n → Bool) (xy : ∀ i, x i=true → y i=true) :
    t.val x=true → t.val y=true := by
  induction t with
  | raw i => exact xy i
  | gate k a b ha hb => cases k <;> simp [Expr.val,op] at * <;> tauto

theorem extract {n} (S : Finset (Fin n)) (t : Expr n)
    (singles : ∀ i ∈ S, t.val (fun j => decide (j=i))=true) (x : Fin n → Bool) :
    t.val x=true ↔ (∃ i ∈ S, x i=true) ∨ valOpt x (t.cut S)=true := by
  by_cases hx : ∃ i ∈ S, x i=true
  · obtain ⟨i,hi,xi⟩ := hx
    have h := rising t (fun j => decide (j=i)) x (fun j hj => by simpa using (of_decide_eq_true hj ▸ xi)) (singles i hi)
    exact ⟨fun _ => Or.inl ⟨i,hi,xi⟩,fun _ => h⟩
  · have e : (fun i => if i ∈ S then false else x i)=x := by
      funext i
      by_cases hi : i ∈ S
      · have z : x i=false := by cases h : x i <;> first | rfl | exact (hx ⟨i,hi,h⟩).elim
        simp [hi,z]
      · simp [hi]
    rw [cutVal,e]
    simp [hx]


-- A subterm that never fires on a negative row may be moved to the output.
theorem moveCertificate (outer : Bool → Bool) (a e target : Bool)
    (correct : outer (a || e)=target) (safe : e=true → target=true) :
    (outer a || e)=target := by
  cases e <;> simp_all

-- Safe replacements of a helper's value act together on the two test classes.
theorem shrink (outer : Bool → Bool) (old smaller answer : Bool)
    (correct : outer old=answer) (pos : answer=true → old=true → smaller=true)
    (neg : answer=false → smaller=true → old=true) (mono : outer false=true → outer true=true) :
    outer smaller=answer := by
  cases old <;> cases smaller <;> cases answer <;> cases h : outer false <;>
    cases j : outer true <;> simp_all

theorem outerBudget (g t raw : ℕ) (two : 2 ≤ t) (cost : g + (raw+t-1) ≤ 63) :
    raw ≤ 62-g := by omega


-- A signal depending monotonically on only two raw coordinates can be
-- replaced on the promised rows by one primitive gate, projection or constant.
theorem classifyTwo (f : Bool → Bool → Bool)
    (riseLeft : ∀ b, f false b=true → f true b=true)
    (riseRight : ∀ a, f a false=true → f a true=true) :
    f=(fun _ _ => false) ∨ f=(fun _ _ => true) ∨
    f=(fun a _ => a) ∨ f=(fun _ b => b) ∨
    f=(fun a b => a && b) ∨ f=(fun a b => a || b) := by
  have casesAt (g : Bool → Bool → Bool) (h00 : f false false=g false false)
      (h01 : f false true=g false true) (h10 : f true false=g true false)
      (h11 : f true true=g true true) : f=g := by
    funext a b
    cases a <;> cases b <;> assumption
  cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true
  all_goals first
    | exact Or.inl (casesAt _ h00 h01 h10 h11)
    | exact Or.inr (Or.inl (casesAt _ h00 h01 h10 h11))
    | exact Or.inr (Or.inr (Or.inl (casesAt _ h00 h01 h10 h11)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (casesAt _ h00 h01 h10 h11))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (casesAt _ h00 h01 h10 h11)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (casesAt _ h00 h01 h10 h11)))))
    | exfalso; first
      | exact Bool.noConfusion ((riseLeft _ h00).symm.trans h10)
      | exact Bool.noConfusion ((riseRight _ h00).symm.trans h01)
      | exact Bool.noConfusion ((riseLeft _ h01).symm.trans h11)
      | exact Bool.noConfusion ((riseRight _ h10).symm.trans h11)

theorem pairBudget (h t raw : ℕ) (shared : 2*h≤t)
    (cost : h + (raw+t-1) ≤ 63) : raw≤64-3*h := by omega

end GenericHelperPrice
