import PEqualNP.Defs

namespace PlaneCrossRestrictions

/-- A subset of the raw inputs is held at one. A gate is forced when at
least one of its two operands is already true at that assignment. -/
def Forced {G V : Type*} (hit : G → Bool → Finset V → Bool) (g : G) (U : Finset V) :=
  ∃ b, hit g b U = true

theorem stabilize {G V : Type*} [DecidableEq G] [DecidableEq V]
    (valid : Finset V → Prop) (hit : G → Bool → Finset V → Bool)
    (mono : ∀ g b S T, S ⊆ T → hit g b S = true → hit g b T = true)
    (budget : ℕ) (marked : Finset G) (start : Finset V) (feasible : valid start) :
    ∃ U, start ⊆ U ∧ valid U ∧ U.card ≤ start.card + budget*marked.card ∧
      ∀ g ∈ marked, Forced hit g U ∨
        ∀ D : Finset V, D.card ≤ budget → valid (U ∪ D) → ¬Forced hit g (U ∪ D) := by
  classical
  have go : ∀ t (M : Finset G), M.card=t → ∀ S : Finset V, valid S →
      ∃ U, S ⊆ U ∧ valid U ∧ U.card ≤ S.card+budget*t ∧
        ∀ g ∈ M, Forced hit g U ∨
          ∀ D : Finset V, D.card ≤ budget → valid (U ∪ D) → ¬Forced hit g (U ∪ D) := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro M size S ok
      by_cases active : ∃ g ∈ M, ∃ D : Finset V, D.card ≤ budget ∧ valid (S ∪ D) ∧ Forced hit g (S ∪ D)
      · obtain ⟨g,hg,D,small,good,b,w⟩ := active
        have shrink : (M.erase g).card < t := by
          have h := Finset.card_erase_lt_of_mem hg
          omega
        obtain ⟨U,sub,vu,count,others⟩ := ih _ shrink (M.erase g) rfl (S ∪ D) good
        refine ⟨U,(Finset.subset_union_left).trans sub,vu,?_,?_⟩
        · have add := Finset.card_union_le S D
          have eq : t = (M.erase g).card+1 := by simpa [size] using (Finset.card_erase_add_one hg).symm
          rw [eq,Nat.mul_add,Nat.mul_one]
          omega
        · intro h hh
          by_cases eq : h=g
          · subst h; exact Or.inl ⟨b,mono g b _ _ sub w⟩
          · exact others _ (Finset.mem_erase.mpr ⟨eq,hh⟩)
      · refine ⟨S,Finset.Subset.rfl,ok,by omega,?_⟩
        exact fun g hg => Or.inr (fun D hd vd f => active ⟨g,hg,D,hd,vd,f⟩)
  exact go _ marked rfl start feasible

/-- On the surviving negative rows one fixed input can replace a selected
AND simultaneously. On other rows replacement by either input only increases it. -/
theorem choose_operand {G V : Type*} [DecidableEq V] (valid : Finset V → Prop)
    (hit : G → Bool → Finset V → Bool)
    (mono : ∀ g b S T, S ⊆ T → hit g b S = true → hit g b T = true)
    (U : Finset V) (g : G) (d : ℕ)
    (status : Forced hit g U ∨ ∀ D : Finset V, D.card ≤ d → valid (U ∪ D) → ¬Forced hit g (U ∪ D)) :
    ∃ choice : Bool, ∀ D : Finset V, D.card ≤ d → valid (U ∪ D) →
      (hit g false (U ∪ D) && hit g true (U ∪ D)) = hit g choice (U ∪ D) := by
  rcases status with ⟨b,hot⟩|off
  · cases b
    · exact ⟨true,fun D _ _ => by simp [mono g false U (U ∪ D) Finset.subset_union_left hot]⟩
    · exact ⟨false,fun D _ _ => by simp [mono g true U (U ∪ D) Finset.subset_union_left hot]⟩
  · refine ⟨false,?_⟩
    intro D small feasible
    have cold : hit g false (U ∪ D) = false := by
      cases h : hit g false (U ∪ D)
      · rfl
      · exact False.elim ((off D small feasible) ⟨false,h⟩)
    simp [cold]

section Roles
variable {P L : Type*} [PartialOrder P] [OrderBot P] [OrderTop P]
    [PartialOrder L] [OrderBot L] [OrderTop L]

def pointOnly (f : P → L → Bool) := ∀ p l, f p l = f p ⊥
def lineOnly (f : P → L → Bool) := ∀ p l, f p l = f ⊥ l
def lineChange (f : P → L → Bool) := ∃ p, f p ⊥ ≠ f p ⊤
def pointChange (f : P → L → Bool) := ∃ l, f ⊥ l ≠ f ⊤ l

omit [PartialOrder P] [OrderBot P] [OrderTop P] in
theorem pointOnly_of_no_line (f : P → L → Bool) (mono : ∀ p, Monotone (f p))
    (h : ¬lineChange f) : pointOnly f := by
  intro p l
  have same : f p ⊥ = f p ⊤ := by by_contra ne; exact h ⟨p,ne⟩
  exact le_antisymm (same ▸ mono p (show l ≤ ⊤ from le_top)) (mono p bot_le)

omit [PartialOrder L] [OrderBot L] [OrderTop L] in
theorem lineOnly_of_no_point (f : P → L → Bool) (mono : ∀ l, Monotone fun p => f p l)
    (h : ¬pointChange f) : lineOnly f := by
  intro p l
  have same : f ⊥ l = f ⊤ l := by by_contra ne; exact h ⟨l,ne⟩
  exact le_antisymm (same ▸ mono l (show p ≤ ⊤ from le_top)) (mono l bot_le)

theorem cannot_both (f : P → L → Bool) (nonconstant : f ⊥ ⊥ ≠ f ⊤ ⊤)
    (p : pointOnly f) (l : lineOnly f) : False :=
  nonconstant ((p ⊤ ⊤).trans (l ⊤ ⊥)).symm

theorem opposite (f g : P → L → Bool) (mf : ∀ p, Monotone (f p))
    (nf : ∀ l, Monotone fun p => f p l) (mg : ∀ p, Monotone (g p))
    (ng : ∀ l, Monotone fun p => g p l)
    (cf : f ⊥ ⊥ ≠ f ⊤ ⊤) (cg : g ⊥ ⊥ ≠ g ⊤ ⊤)
    (outside : ¬((lineChange f ∧ lineChange g) ∨ (pointChange f ∧ pointChange g))) :
    (pointOnly f ∧ lineOnly g) ∨ (lineOnly f ∧ pointOnly g) := by
  by_cases a : lineChange f
  · have b : ¬lineChange g := fun x => outside (Or.inl ⟨a,x⟩)
    have only := pointOnly_of_no_line g mg b
    have c : pointChange g := by
      by_contra t
      exact cannot_both g cg only (lineOnly_of_no_point g ng t)
    exact Or.inr ⟨lineOnly_of_no_point f nf (fun x => outside (Or.inr ⟨x,c⟩)),only⟩
  · have only := pointOnly_of_no_line f mf a
    have c : pointChange f := by
      by_contra t
      exact cannot_both f cf only (lineOnly_of_no_point f nf t)
    exact Or.inl ⟨only,lineOnly_of_no_point g ng (fun x => outside (Or.inr ⟨c,x⟩))⟩

omit [OrderTop P] [OrderTop L] in
theorem split_and (f g : P → L → Bool) (baseF : f ⊥ ⊥ = false) (baseG : g ⊥ ⊥ = false)
    (side : pointOnly f ∧ lineOnly g) (p : P) (l : L) :
    (f p l && g p l) = (f p ⊥ && g ⊥ l) ∧
    (f p ⊥ && g p ⊥) = false ∧ (f ⊥ l && g ⊥ l) = false := by
  refine ⟨by rw [side.1 p l,side.2 p l],?_,?_⟩
  · rw [side.2 p ⊥,baseG]; simp
  · rw [side.1 ⊥ l,baseF]; simp
end Roles

/-- A single selected signal suffices for every AND reading it. At the
terminal restriction it has the same value on the base and all surviving
negative tests. The same holds for any function of selected signals. -/
theorem stabilize_signals {G V : Type*} [DecidableEq G] [DecidableEq V]
    (valid : Finset V → Prop) (hit : G → Finset V → Bool)
    (mono : ∀ g S T, S ⊆ T → hit g S = true → hit g T = true)
    (budget : ℕ) (marked : Finset G) (start : Finset V) (feasible : valid start) :
    ∃ U, start ⊆ U ∧ valid U ∧ U.card ≤ start.card+budget*marked.card ∧
      ∀ g ∈ marked, ∀ D : Finset V, D.card ≤ budget → valid (U ∪ D) →
        hit g (U ∪ D) = hit g U := by
  obtain ⟨U,sub,vu,count,status⟩ := stabilize valid (fun g _ => hit g)
    (fun g _ => mono g) budget marked start feasible
  refine ⟨U,sub,vu,count,?_⟩
  intro g hg D small good
  rcases status g hg with ⟨_,on⟩|off
  · change hit g U = true at on
    exact (mono g U (U ∪ D) Finset.subset_union_left on).trans on.symm
  · cases h : hit g (U ∪ D) <;> cases b : hit g U
    · rfl
    · exact False.elim (Bool.noConfusion (h.symm.trans (mono g U (U ∪ D) Finset.subset_union_left b)))
    · exact False.elim ((off D small good) ⟨false,h⟩)
    · rfl

theorem decoder_constant {ι α β : Type*} (read : ι → α → Bool) (a b : α)
    (eq : ∀ i, read i a = read i b) (decoder : (ι → Bool) → β) :
    decoder (fun i => read i a) = decoder (fun i => read i b) :=
  congrArg decoder (funext eq)

section Rebase
variable {P L : Type*}
def tracks (f : P → L → Bool) (p₀ : P) (l₀ : L) (p : P) (l : L) :=
  (f p l, f p l₀, f p₀ l)

theorem rebased_product (f g : P → L → Bool) (p₀ : P) (l₀ : L)
    (onlyP : ∀ p l, f p l = f p l₀) (onlyL : ∀ p l, g p l = g p₀ l) (p : P) (l : L) :
    tracks (fun x y => f x y && g x y) p₀ l₀ p l =
      (f p l₀ && g p₀ l, f p l₀ && g p₀ l₀, f p₀ l₀ && g p₀ l) := by
  simp only [tracks]
  rw [onlyP p l,onlyL p l,onlyL p l₀,onlyP p₀ l]

theorem same_selection (A B : P → L → Bool) (p₀ : P) (l₀ : L) (p : P) (l : L)
    (same : A p l=A p₀ l₀ ∧ A p l₀=A p₀ l₀ ∧ A p₀ l=A p₀ l₀) :
    tracks (fun x y => A x y && B x y) p₀ l₀ p l =
      tracks (if A p₀ l₀ then B else A) p₀ l₀ p l := by
  rcases same with ⟨one,two,three⟩
  cases h : A p₀ l₀ <;> simp [tracks,h,one,two,three]

end Rebase

section Comparison
/-- Simultaneous replacements may be tested against the original tape. -/
theorem agree_prefix (n s : ℕ) (old new : ℕ → Bool)
    (raw : ∀ i < n, new i=old i)
    (step : ∀ j < s, (∀ i < n+j, new i=old i) → new (n+j)=old (n+j)) :
    ∀ i < n+s, new i=old i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases h : i < n
    · exact raw i h
    · have eq : n+(i-n)=i := by omega
      have f := step (i-n) (by omega)
      rw [eq] at f
      exact f (fun u hu => ih u hu (by omega))

theorem increase_prefix (n s : ℕ) (old new : ℕ → Bool)
    (raw : ∀ i < n, old i=true → new i=true)
    (step : ∀ j < s, (∀ i < n+j, old i=true → new i=true) →
      old (n+j)=true → new (n+j)=true) :
    ∀ i < n+s, old i=true → new i=true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases h : i < n
    · exact raw i h
    · have eq : n+(i-n)=i := by omega
      have f := step (i-n) (by omega)
      rw [eq] at f
      exact f (fun u hu => ih u hu (by omega))
end Comparison

section SingletonPayments
variable {V : Type*} [DecidableEq V]

def singletonPart (f : Finset V → Bool) (choices : Finset V) (x : Finset V) :=
  decide (∃ v ∈ choices, v ∈ x ∧ f {v} = true)

theorem singleton_sound (f : Finset V → Bool)
    (mono : ∀ A B, A ⊆ B → f A=true → f B=true) (choices x : Finset V) :
    singletonPart f choices x = true → f x = true := by
  intro h
  obtain ⟨v,_,hx,hot⟩ := of_decide_eq_true h
  exact mono {v} x (by simpa using hx) hot

theorem unpaid (f : Finset V → Bool) (choices : Finset V) (p l : V)
    (hp : p ∈ choices) (hl : l ∈ choices) :
    singletonPart f choices {p,l} = false ↔ f {p}=false ∧ f {l}=false := by
  simp [singletonPart,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨h p hp (Or.inl rfl),h l hl (Or.inr rfl)⟩
  · rintro ⟨a,b⟩ v _ (h|h)
    · simpa [h] using a
    · simpa [h] using b

end SingletonPayments

section Counting
/-- The flags lost by reserving a vertex are covered by the flags at its
neighbors. The bound permits repeated charges for different reserved inputs. -/
theorem damage {V E : Type*} [DecidableEq E] (U : Finset V) (lost : V → Finset E)
    (m : ℕ) (limit : ∀ x ∈ U, (lost x).card ≤ m) :
    (U.biUnion lost).card ≤ U.card*m := by
  calc
    _ ≤ ∑ x ∈ U, (lost x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ U, m := Finset.sum_le_sum limit
    _ = _ := by simp [Nat.mul_comm]

theorem few_cross (q N s h : ℕ) (large : 100 < q) (order : N=q^2+q+1)
    (few : 7*h ≤ q) (afterPins : N*(q+1) ≤ 3*s+6*h*(q+1)^2) : N*q ≤ 100*s := by
  have loss := Nat.mul_le_mul_right ((q+1)^2) few
  have pos : 0 ≤ (q:ℤ)-101 := by omega
  have cube := mul_nonneg pos (sq_nonneg (q:ℤ))
  have square := sq_nonneg (q:ℤ)
  rw [order] at afterPins ⊢
  exact_mod_cast (show ((q:ℤ)^2+q+1)*q ≤ 100*(s:ℤ) by
    have a : ((q:ℤ)^2+q+1)*(q+1) ≤ 3*s+6*h*(q+1)^2 := by exact_mod_cast afterPins
    have b : 7*(h:ℤ)*(q+1)^2 ≤ q*(q+1)^2 := by exact_mod_cast loss
    nlinarith)

theorem guarded_bound (q N s u : ℕ) (large : 100 < q) (order : N=q^2+q+1)
    (few : 100*u ≤ 49*q) (estimate : N*(q+1) ≤ 2*s+2*u*(q+1)^2) :
    2*u+2 ≤ q ∧ N*q ≤ 100*s := by
  refine ⟨by omega,?_⟩
  have price := Nat.mul_le_mul_right ((q+1)^2) few
  rw [order] at estimate ⊢
  exact_mod_cast (show ((q:ℤ)^2+q+1)*q ≤ 100*(s:ℤ) by
    have a : ((q:ℤ)^2+q+1)*(q+1) ≤ 2*s+2*u*(q+1)^2 := by exact_mod_cast estimate
    have b : 100*(u:ℤ)*(q+1)^2 ≤ 49*q*(q+1)^2 := by exact_mod_cast price
    nlinarith [sq_nonneg (q:ℤ)])

end Counting


section LineWitness
/-- Propagate the contribution of exactly one occurrence of a line input.
The other child of an AND has to be true with all line inputs switched off. -/
def linAnd (a₀ b₀ da db : Bool) := (da && b₀) || (a₀ && db)

theorem lin_sound (a₀ b₀ a b da db : Bool) (ha : a₀ ≤ a) (hb : b₀ ≤ b)
    (hda : da ≤ a) (hdb : db ≤ b) : linAnd a₀ b₀ da db ≤ (a && b) := by
  revert ha hb hda hdb
  cases a₀ <;> cases b₀ <;> cases a <;> cases b <;> cases da <;> cases db <;> decide

theorem lin_or_exact (a₀ b₀ da db : Bool) :
    ((a₀ || da) || (b₀ || db)) = ((a₀ || b₀) || (da || db)) := by
  cases a₀ <;> cases b₀ <;> cases da <;> cases db <;> rfl

theorem lin_missing (a₀ b₀ da db : Bool) :
    (((a₀ || da) && (b₀ || db)) && !((a₀ && b₀) || linAnd a₀ b₀ da db)) =
      (!a₀ && !b₀ && da && db) := by
  cases a₀ <;> cases b₀ <;> cases da <;> cases db <;> rfl

/-- One reverse step conserves every line coefficient in the linear expression,
even when both predecessor accumulators already have nonzero contributions. -/
theorem transpose_step (rest w wa wb ka kb da db : Bool) :
    (rest || (wa && da) || (wb && db) || (w && ((ka && da) || (kb && db)))) =
    (rest || ((wa || (w && ka)) && da) || ((wb || (w && kb)) && db)) := by
  cases rest <;> cases w <;> cases wa <;> cases wb <;> cases ka <;> cases kb <;>
    cases da <;> cases db <;> rfl

theorem transpose_cost (s a n live compiled saved : ℕ)
    (ands : a ≤ s) (edgeCount : live + (s-1) + 2*n = 2*s)
    (nonempty : 1 ≤ s) (cost : compiled ≤ s+2*a+live)
    (price : saved ≤ compiled+n) : saved+n ≤ 4*s+1 := by omega

theorem collision_bound (s n q loss kept : ℕ) (npos : 1 ≤ n)
    (total : n*(q+1) ≤ kept+loss) (compile : kept+n ≤ 4*s+1)
    (budget : loss ≤ 96*s) : n*q ≤ 100*s := by
  rw [Nat.mul_add,Nat.mul_one] at total
  omega

theorem affine_sweep_cost (i a b merges : ℕ) (leaves : 1 ≤ b)
    (internal : 1 ≤ i) (edges : merges+(i-1+b)=2*i-a) : merges+a ≤ i := by omega

theorem raise_const (original base exactValue rest : Bool) (lo : original ≤ base)
    (hi : base ≤ exactValue) (rule : exactValue = (original || rest)) :
    exactValue = (base || rest) := by
  revert lo hi rule
  cases original <;> cases base <;> cases exactValue <;> cases rest <;> decide

theorem cut_cost (s N q k : ℕ) (small : k ≤ 11) (order : 380 < q)
    (price : N*q ≤ (2*k+2)*s+(2*k*k+3*k+1)*N) : N*q ≤ 100*s := by
  have k2 := Nat.mul_le_mul small small
  have c : 2*k+2 ≤ 24 := by omega
  have d : 2*k*k+3*k+1 ≤ 276 := by nlinarith
  have b := Nat.mul_le_mul_right s c
  have e := Nat.mul_le_mul_right N d
  have f := Nat.mul_le_mul_left N order
  by_contra h
  omega

end LineWitness
theorem small_order (q N g : ℕ) (lo : 101 ≤ q) (hi : q ≤ 380)
    (order : N = q^2+q+1)
    (bound : (4*N : ℤ) * 20 ≤ (g:ℤ)*20 + 2*19*(q+1)*20 + 2*(q:ℤ)*(q-19)) :
    N*q ≤ 100*g := by
  have arith : ∀ j : Fin 381, 101 ≤ j.val →
      let n : ℤ := (j.val:ℤ)^2+j.val+1
      20*n*j.val ≤ 100*(4*n*20-2*19*(j.val+1)*20-2*(j.val:ℤ)*(j.val-19)) := by
    decide +kernel
  obtain h := arith ⟨q,by omega⟩ lo
  simp only at h
  rw [order] at bound ⊢
  push_cast at bound ⊢
  exact_mod_cast (show ((q:ℤ)^2+q+1)*(q:ℤ) ≤ 100*(g:ℤ) by nlinarith)

end PlaneCrossRestrictions
