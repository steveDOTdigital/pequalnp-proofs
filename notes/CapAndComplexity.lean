import PEqualNP.Defs

namespace CapAndComplexity

-- An AND identifier may occur repeatedly when a circuit is unfolded.
inductive Expr (V I : Type) where
  | raw (v : V)
  | bot
  | disj (a b : Expr V I)
  | conj (i : I) (a b : Expr V I)

def Expr.value {V I} : Expr V I → (V → Bool) → Bool
  | .raw v,x => x v
  | .bot,_ => false
  | .disj a b,x => a.value x || b.value x
  | .conj _ a b,x => a.value x && b.value x

def Expr.branch {V I} (s : I → Bool) : Expr V I → (V → Bool) → Bool
  | .raw v,x => x v
  | .bot,_ => false
  | .disj a b,x => a.branch s x || b.branch s x
  | .conj i a b,x => if s i then a.branch s x else b.branch s x

theorem upper {V I} (e : Expr V I) (s : I → Bool) (x : V → Bool)
    (h : e.value x=true) : e.branch s x=true := by
  induction e with
  | raw => exact h
  | bot => exact h
  | disj a b ia ib =>
    simp only [Expr.value,Bool.or_eq_true] at h
    rcases h with h|h
    · simp [Expr.branch,ia h]
    · simp [Expr.branch,ib h]
  | conj i a b ia ib =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    cases w : s i <;> simp [Expr.branch,w,ia ha,ib hb]

theorem branch_union {V I} (e : Expr V I) (s : I → Bool) (x y : V → Bool) :
    e.branch s (fun v => x v || y v)=(e.branch s x || e.branch s y) := by
  induction e with
  | raw => rfl
  | bot => rfl
  | disj a b ia ib => simp [Expr.branch,ia,ib,Bool.or_assoc,Bool.or_left_comm]
  | conj i a b ia ib => cases h : s i <;> simp [Expr.branch,h,ia,ib]

theorem distinct_false {V I} (e : Expr V I) (s : I → Bool) (x y : V → Bool)
    (accept : e.value (fun v => x v || y v)=true) :
    ¬ (e.branch s x=false ∧ e.branch s y=false) := by
  rintro ⟨hx,hy⟩
  have h := upper e s _ accept
  rw [branch_union,hx,hy] at h
  contradiction

def Expr.consistent {V I} (s : I → Bool) (x : V → Bool) : Expr V I → Prop
  | .raw _ | .bot => True
  | .disj a b => a.consistent s x ∧ b.consistent s x
  | .conj i a b => a.consistent s x ∧ b.consistent s x ∧
    (if s i then a.value x else b.value x)=(a.value x && b.value x)

theorem exact_branch {V I} (e : Expr V I) (s : I → Bool) (x : V → Bool)
    (h : e.consistent s x) : e.branch s x=e.value x := by
  induction e with
  | raw => rfl
  | bot => rfl
  | disj a b ia ib => simp [Expr.branch,Expr.value,ia h.1,ib h.2]
  | conj i a b ia ib =>
    rcases h with ⟨ha,hb,hw⟩
    simpa [Expr.branch,Expr.value,ia ha,ib hb] using hw

theorem choice_capacity {V T : Type} [Fintype T] (k : ℕ)
    (e : Expr V (Fin k)) (input : T → V → Bool) (A : T → Finset (Fin k → Bool))
    (accept : ∀ t u, t≠u → e.value (fun v => input t v || input u v)=true)
    (reject : ∀ t, e.value (input t)=false)
    (works : ∀ t s, s∈A t → e.consistent s (input t)) :
    (∑ t, (A t).card) ≤ 2^k := by
  classical
  have dis : (↑(Finset.univ : Finset T) : Set T).PairwiseDisjoint A := by
    intro t _ u _ ne
    apply Finset.disjoint_left.mpr
    intro s hs ht
    apply distinct_false e s (input t) (input u) (accept t u ne)
    exact ⟨(exact_branch e s _ (works t s hs)).trans (reject t),
      (exact_branch e s _ (works u s ht)).trans (reject u)⟩
  have small := Finset.card_le_card (Finset.subset_univ ((Finset.univ : Finset T).biUnion A))
  rw [Finset.card_biUnion dis] at small
  simpa using small

-- The two counting steps in the 22-port obstruction.
theorem eight_triples (removed remaining slots two three : ℕ)
    (raw : removed+remaining=26) (budget : slots+removed≤22)
    (ports : slots=two+three) (handshake : 2*remaining=2*two+3*three)
    (independent : 3*three≤remaining) : three=8 ∧ removed≤2 ∧ two≤14 := by omega

theorem mutual_count (a b common available : ℕ) (pointUses : a=12)
    (lineUses : b=12) (available_le : available≤14)
    (union_le : a+b≤available+common) : 10≤common := by omega


-- If a raw input occurs at r normalized ANDs, setting it high removes r
-- paid gates. The sharp one- and two-pin bounds limit these multiplicities.
theorem full_multiplicity (k r residual : ℕ) (cost : r+residual≤k)
    (limit : k≤11) (fixed : 9≤residual) : r≤2 := by omega
theorem line_multiplicity (k r residual : ℕ) (cost : r+residual≤k)
    (limit : k≤9) (fixed : 8≤residual) : r≤1 := by omega
theorem point_multiplicity (k r residual : ℕ) (cost : r+residual≤k)
    (limit : k≤9) (fixed : 6≤residual) : r≤3 := by omega

end CapAndComplexity
