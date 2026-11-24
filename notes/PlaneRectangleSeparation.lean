import PEqualNP.Defs

namespace PlaneRectangleSeparation

/-- A binary rectangle cover can split one coordinate or copy one child. -/
theorem rectangle_split {α β : Type*} (A U V : Set α) (B W Z : Set β)
    (aNonempty : A.Nonempty) (bNonempty : B.Nonempty)
    (h : A ×ˢ B ⊆ (U ×ˢ W) ∪ (V ×ˢ Z)) :
    (A ⊆ U ∧ B ⊆ W) ∨ (A ⊆ V ∧ B ⊆ Z) ∨
    (A ⊆ U ∪ V ∧ B ⊆ W ∧ B ⊆ Z) ∨ (A ⊆ U ∧ A ⊆ V ∧ B ⊆ W ∪ Z) := by
  classical
  have atxy (x : α) (y : β) (hx : x ∈ A) (hy : y ∈ B) :
      (x ∈ U ∧ y ∈ W) ∨ (x ∈ V ∧ y ∈ Z) := @h (x,y) ⟨hx,hy⟩
  by_cases au : A ⊆ U <;> by_cases av : A ⊆ V
  · right; right; right
    refine ⟨au,av,?_⟩
    obtain ⟨x,hx⟩ := aNonempty
    intro y hy
    rcases atxy x y hx hy with z|z
    · exact Or.inl z.2
    · exact Or.inr z.2
  · obtain ⟨x,hx,nv⟩ := Set.not_subset.mp av
    exact Or.inl ⟨au, fun y hy => ((atxy x y hx hy).resolve_right (fun z => nv z.1)).2⟩
  · obtain ⟨x,hx,nu⟩ := Set.not_subset.mp au
    exact Or.inr (Or.inl ⟨av, fun y hy => ((atxy x y hx hy).resolve_left (fun z => nu z.1)).2⟩)
  · obtain ⟨x,hx,nu⟩ := Set.not_subset.mp au
    obtain ⟨z,hz,nv⟩ := Set.not_subset.mp av
    right; right; left
    refine ⟨?_,fun y hy => ((atxy z y hz hy).resolve_right (fun k => nv k.1)).2,
      fun y hy => ((atxy x y hx hy).resolve_left (fun k => nu k.1)).2⟩
    intro w hw
    obtain ⟨y,hy⟩ := bNonempty
    rcases atxy w y hw hy with k|k
    · exact Or.inl k.1
    · exact Or.inr k.1

def Realizes {α β X : Type*} (pos : α → X) (neg : β → X) (A : Set α) (B : Set β)
    (f : X → Bool) : Prop :=
  (∀ a ∈ A, f (pos a) = true) ∧ (∀ b ∈ B, f (neg b) = false)

def BinaryStep {X : Type*} (a b f : X → Bool) : Prop :=
  f=a ∨ f=b ∨ f=(fun x => a x || b x) ∨ f=(fun x => a x && b x)

theorem realize_merge {α β X : Type*} (pos : α → X) (neg : β → X)
    (A U V : Set α) (B W Z : Set β) (f g : X → Bool)
    (a : A.Nonempty) (b : B.Nonempty)
    (cover : A ×ˢ B ⊆ (U ×ˢ W) ∪ (V ×ˢ Z))
    (hf : Realizes pos neg U W f) (hg : Realizes pos neg V Z g) :
    ∃ v, BinaryStep f g v ∧ Realizes pos neg A B v := by
  rcases rectangle_split A U V B W Z a b cover with ⟨r,c⟩|⟨r,c⟩|⟨r,c,d⟩|⟨r,t,c⟩
  · exact ⟨f,Or.inl rfl,fun x hx => hf.1 x (r hx),fun y hy => hf.2 y (c hy)⟩
  · exact ⟨g,Or.inr (Or.inl rfl),fun x hx => hg.1 x (r hx),fun y hy => hg.2 y (c hy)⟩
  · refine ⟨_,Or.inr (Or.inr (Or.inl rfl)),?_,?_⟩
    · intro x hx
      rcases r hx with hu|hv
      · simp [hf.1 x hu]
      · simp [hg.1 x hv]
    · intro y hy
      simp [hf.2 y (c hy),hg.2 y (d hy)]
  · refine ⟨_,Or.inr (Or.inr (Or.inr rfl)),?_,?_⟩
    · intro x hx
      simp [hf.1 x (r hx),hg.1 x (t hx)]
    · intro y hy
      rcases c hy with hw|hz
      · simp [hf.2 y hw]
      · simp [hg.2 y hz]

/-- Initial nonempty rectangles give the two independent obligations on a raw wire. -/
theorem realize_leaf {α β X : Type*} (pos : α → X) (neg : β → X) (A : Set α) (B : Set β)
    (f : X → Bool) (a : A.Nonempty) (b : B.Nonempty)
    (h : ∀ x ∈ A, ∀ y ∈ B, f (pos x) = true ∧ f (neg y) = false) :
    Realizes pos neg A B f :=
  ⟨fun x hx => (h x hx _ b.choose_spec).1, fun y hy => (h _ a.choose_spec y hy).2⟩

/-- Choose all wires in one topological order. An empty rectangle may be
represented by a Boolean constant, and each nonempty gate costs at most one. -/
theorem program {α β X : Type*} (pos : α → X) (neg : β → X) (n s : ℕ)
    (A : ℕ → Set α) (B : ℕ → Set β) (raw : ℕ → X → Bool)
    (leaf : ∀ i < n, ∀ x ∈ A i, ∀ y ∈ B i,
      raw i (pos x) = true ∧ raw i (neg y) = false)
    (gates : ∀ j < s, ∃ u v, u < v ∧ v < n+j ∧
      A (n+j) ×ˢ B (n+j) ⊆ (A u ×ˢ B u) ∪ (A v ×ˢ B v)) :
    ∃ F : ℕ → X → Bool,
      (∀ i < n+s, Realizes pos neg (A i) (B i) (F i)) ∧
      (∀ i < n, F i = raw i ∨ F i = (fun _ => false) ∨ F i = (fun _ => true)) ∧
      ∀ j < s, F (n+j) = (fun _ => false) ∨ F (n+j) = (fun _ => true) ∨
        ∃ u v, u < v ∧ v < n+j ∧ BinaryStep (F u) (F v) (F (n+j)) := by
  classical
  let Init (F : ℕ → X → Bool) (i : ℕ) :=
    F i = raw i ∨ F i = (fun _ => false) ∨ F i = (fun _ => true)
  let Internal (F : ℕ → X → Bool) (i : ℕ) :=
    F i = (fun _ => false) ∨ F i = (fun _ => true) ∨
      ∃ u v, u < v ∧ v < i ∧ BinaryStep (F u) (F v) (F i)
  let St (F : ℕ → X → Bool) (i : ℕ) := Realizes pos neg (A i) (B i) (F i) ∧
      (i < n → Init F i) ∧ (n ≤ i → Internal F i)
  have buildTape : ∀ t, t ≤ n+s → ∃ F, ∀ i < t, St F i := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨fun _ _ => false, by simp⟩
    | succ t ih =>
      intro limit
      obtain ⟨F,old⟩ := ih (by omega)
      have next : ∃ f : X → Bool, Realizes pos neg (A t) (B t) f ∧
          (t < n → f=raw t ∨ f=(fun _ => false) ∨ f=(fun _ => true)) ∧
          (n ≤ t → f=(fun _ => false) ∨ f=(fun _ => true) ∨
            ∃ u v, u < v ∧ v < t ∧ BinaryStep (F u) (F v) f) := by
        by_cases a : (A t).Nonempty
        · by_cases b : (B t).Nonempty
          · by_cases ht : t < n
            · exact ⟨raw t,realize_leaf pos neg _ _ _ a b (leaf _ ht),
                fun _ => Or.inl rfl, fun hn => False.elim (by omega)⟩
            · obtain ⟨u,v,hu,hv,cov⟩ := gates (t-n) (by omega)
              have eq : n+(t-n)=t := by omega
              rw [eq] at hv cov
              obtain ⟨f,op,yes⟩ := realize_merge pos neg _ _ _ _ _ _ _ _ a b cov
                (old u (by omega)).1 (old v hv).1
              exact ⟨f,yes,fun h => False.elim (ht h),
                fun _ => Or.inr (Or.inr ⟨u,v,hu,hv,op⟩)⟩
          · refine ⟨fun _ => true,⟨by simp,?_⟩,fun _ => Or.inr (Or.inr rfl),
              fun _ => Or.inr (Or.inl rfl)⟩
            exact fun y hy => False.elim (b ⟨y,hy⟩)
        · refine ⟨fun _ => false,⟨?_,by simp⟩,fun _ => Or.inr (Or.inl rfl),
            fun _ => Or.inl rfl⟩
          exact fun x hx => False.elim (a ⟨x,hx⟩)
      obtain ⟨f,hf,hi,hg⟩ := next
      let G := Function.update F t f
      have same (i : ℕ) (h : i < t) : G i=F i := Function.update_of_ne (by omega) _ _
      have last : G t=f := Function.update_self ..
      refine ⟨G,?_⟩
      intro i bound
      by_cases lt : i < t
      · obtain ⟨valid,ini,gate⟩ := old i lt
        refine ⟨(same i lt).symm ▸ valid,?_,?_⟩
        · simpa only [Init,same i lt] using ini
        · intro large
          rcases gate large with a|b|⟨u,v,hu,hv,op⟩
          · exact Or.inl ((same i lt).trans a)
          · exact Or.inr (Or.inl ((same i lt).trans b))
          · exact Or.inr (Or.inr ⟨u,v,hu,hv,by rwa [same i lt,same u (by omega),same v (by omega)]⟩)
      · have eq : i=t := by omega
        subst i
        refine ⟨last.symm ▸ hf,?_,?_⟩
        · simpa only [Init,last] using hi
        · intro large
          rcases hg large with a|b|⟨u,v,hu,hv,op⟩
          · exact Or.inl (last.trans a)
          · exact Or.inr (Or.inl (last.trans b))
          · exact Or.inr (Or.inr ⟨u,v,hu,hv,by rwa [last,same u (by omega),same v hv]⟩)
  obtain ⟨F,ok⟩ := buildTape (n+s) (le_refl _)
  exact ⟨F,fun i hi => (ok i hi).1,fun i hi => (ok i (by omega)).2.1 hi,
    fun j hj => (ok (n+j) (by omega)).2.2 (by omega)⟩

/-- The reverse implication uses the rectangle of every wire that is true on
its positive input and false on its negative input. No depth expansion occurs. -/
theorem reverse_step {α β X : Type*} (pos : α → X) (neg : β → X) (a b f : X → Bool)
    (step : BinaryStep a b f) :
    {e | f (pos e) = true} ×ˢ {T | f (neg T) = false} ⊆
      ({e | a (pos e) = true} ×ˢ {T | a (neg T) = false}) ∪
      ({e | b (pos e) = true} ×ˢ {T | b (neg T) = false}) := by
  rintro ⟨e,T⟩ ⟨hp,hn⟩
  rcases step with h|h|h|h
  · exact Or.inl ⟨h ▸ hp,h ▸ hn⟩
  · exact Or.inr ⟨h ▸ hp,h ▸ hn⟩
  · change f (pos e)=true at hp
    change f (neg T)=false at hn
    rw [h] at hp hn
    cases ha : a (pos e) <;> cases na : a (neg T) <;>
      cases hb : b (pos e) <;> cases nb : b (neg T) <;>
      simp_all [Set.mem_prod]
  · change f (pos e)=true at hp
    change f (neg T)=false at hn
    rw [h] at hp hn
    cases ha : a (pos e) <;> cases na : a (neg T) <;>
      cases hb : b (pos e) <;> cases nb : b (neg T) <;>
      simp_all [Set.mem_prod]

section Desk
variable {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]

def positiveBits (e : Fin n × Fin n) (i : Fin (n+n)) : Bool :=
  decide (i=Fin.castAdd n e.1 ∨ i=Fin.natAdd n e.2)

def negativeBits (T : Finset (Fin n)) (i : Fin (n+n)) : Bool :=
  decide (¬ ((∃ p, i=Fin.castAdd n p ∧ ∃ l ∈ T, I p l) ∨
    ∃ l, i=Fin.natAdd n l ∧ l ∉ T))

def rawBit (j : ℕ) (x : Fin (n+n) → Bool) : Bool :=
  if h : j < n+n then x ⟨j,h⟩ else false

/-- Apply the reconstruction to the exact terminal and cover conditions of 5086. -/
theorem desk_separator (q s o : ℕ) (D : ℕ → Set (Fin n × Fin n) × Set (Finset (Fin n)))
    (out : o < n+n+s)
    (leaf : ∀ i : Fin (n+n), ∀ p l T, ((p,l),T) ∈ (D i).1 ×ˢ (D i).2 →
      (i=Fin.castAdd n p ∧ ∃ m ∈ T, I p m) ∨ i=Fin.natAdd n l ∧ l ∉ T)
    (gate : ∀ j < s, ∃ u v, u < v ∧ v < n+n+j ∧
      (D (n+n+j)).1 ×ˢ (D (n+n+j)).2 ⊆
        ((D u).1 ×ˢ (D u).2) ∪ ((D v).1 ×ˢ (D v).2))
    (root : {e : Fin n × Fin n | I e.1 e.2} ×ˢ {T : Finset (Fin n) | T.card ≤ q} ⊆
      (D o).1 ×ˢ (D o).2)
    (anyFlag : ∃ e : Fin n × Fin n, I e.1 e.2) :
    ∃ F : ℕ → (Fin (n+n) → Bool) → Bool,
      (∀ j < n+n, F j = rawBit j ∨ F j = (fun _ => false) ∨ F j = (fun _ => true)) ∧
      (∀ j < s, F (n+n+j) = (fun _ => false) ∨ F (n+n+j) = (fun _ => true) ∨
        ∃ u v, u < v ∧ v < n+n+j ∧ BinaryStep (F u) (F v) (F (n+n+j))) ∧
      (∀ p l, I p l → F o (positiveBits (p,l)) = true) ∧
      ∀ T, T.card ≤ q → F o (negativeBits I T) = false := by
  have leaves : ∀ i < n+n, ∀ e ∈ (D i).1, ∀ T ∈ (D i).2,
      rawBit i (positiveBits e) = true ∧ rawBit i (negativeBits I T) = false := by
    intro i hi e he T hT
    let j : Fin (n+n) := ⟨i,hi⟩
    rcases leaf j e.1 e.2 T ⟨he,hT⟩ with ⟨pt,hit⟩|⟨ln,off⟩
    · have no : (∃ p, j=Fin.castAdd n p ∧ ∃ l ∈ T, I p l) ∨
          ∃ l, j=Fin.natAdd n l ∧ l ∉ T := Or.inl ⟨e.1,pt,hit⟩
      simp only [rawBit,dite_eq_left hi,positiveBits,negativeBits,decide_eq_true_eq,decide_eq_false_iff_not]
      exact ⟨Or.inl pt,fun h => h no⟩
    · have no : (∃ p, j=Fin.castAdd n p ∧ ∃ l ∈ T, I p l) ∨
          ∃ l, j=Fin.natAdd n l ∧ l ∉ T := Or.inr ⟨e.2,ln,off⟩
      simp only [rawBit,dite_eq_left hi,positiveBits,negativeBits,decide_eq_true_eq,decide_eq_false_iff_not]
      exact ⟨Or.inr ln,fun h => h no⟩
  obtain ⟨F,fits,init,internal⟩ := program positiveBits (negativeBits I) (n+n) s
    (fun j => (D j).1) (fun j => (D j).2) rawBit leaves gate
  refine ⟨F,init,internal,?_,?_⟩
  · intro p l h
    have hr := @root ((p,l),∅) ⟨h,by simp⟩
    exact (fits o out).1 _ hr.1
  · intro T ht
    obtain ⟨e,he⟩ := anyFlag
    have hr := @root (e,T) ⟨he,ht⟩
    exact (fits o out).2 _ hr.2
end Desk

section Monotone
variable {n : ℕ}
def LessBits (x y : Fin n → Bool) := ∀ i, x i = true → y i = true
def Increasing (f : (Fin n → Bool) → Bool) :=
  ∀ x y, LessBits x y → f x = true → f y = true

theorem increasing_step (a b f : (Fin n → Bool) → Bool)
    (ha : Increasing a) (hb : Increasing b) (step : BinaryStep a b f) : Increasing f := by
  rcases step with h|h|h|h
  · exact h ▸ ha
  · exact h ▸ hb
  · subst f
    intro x y le hx
    change (a x || b x) = true at hx
    rcases Bool.or_eq_true_iff.mp hx with h|h
    · simp [ha x y le h]
    · simp [hb x y le h]
  · subst f
    intro x y le hx
    change (a x && b x) = true at hx
    obtain ⟨h,k⟩ := Bool.and_eq_true_iff.mp hx
    simp [ha x y le h,hb x y le k]

theorem increasing_tape (inputs s : ℕ) (raw F : ℕ → (Fin n → Bool) → Bool)
    (rawMono : ∀ i < inputs, Increasing (raw i))
    (init : ∀ i < inputs, F i = raw i ∨ F i = (fun _ => false) ∨ F i = (fun _ => true))
    (gate : ∀ j < s, F (inputs+j) = (fun _ => false) ∨ F (inputs+j) = (fun _ => true) ∨
      ∃ u v, u < v ∧ v < inputs+j ∧ BinaryStep (F u) (F v) (F (inputs+j))) :
    ∀ i < inputs+s, Increasing (F i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases rawNode : i < inputs
    · rcases init i rawNode with a|a|a
      · exact a ▸ rawMono _ rawNode
      · simp [a,Increasing]
      · simp [a,Increasing]
    · have add : inputs+(i-inputs)=i := by omega
      have st := gate (i-inputs) (by omega)
      rw [add] at st
      rcases st with a|a|⟨u,v,hu,hv,op⟩
      · simp [a,Increasing]
      · simp [a,Increasing]
      · exact increasing_step _ _ _ (ih u (by omega) (by omega)) (ih v hv (by omega)) op
end Monotone

section Promise
variable {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]

def selected (P L : Finset (Fin n)) : Fin (n+n) → Bool :=
  Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))

theorem independent_below (P L : Finset (Fin n)) (free : ∀ p ∈ P, ∀ l ∈ L, ¬I p l) :
    LessBits (selected P L) (negativeBits I L) := by
  intro i
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · intro on
    have hp : p ∈ P := by simpa [selected] using on
    apply decide_eq_true
    rintro (⟨u,eq,v,hv,uv⟩|⟨v,eq,_⟩)
    · have val := congrArg Fin.val eq
      have same : p=u := by apply Fin.ext; simpa using val
      exact free p hp v hv (same.symm ▸ uv)
    · have := congrArg Fin.val eq
      simp at this
      omega
  · intro on
    have hl : l ∈ L := by simpa only [selected, Fin.addCases_right, decide_eq_true_eq] using on
    apply decide_eq_true
    rintro (⟨u,eq,_⟩|⟨v,eq,off⟩)
    · have := congrArg Fin.val eq
      simp at this
      omega
    · have h := congrArg Fin.val eq
      have same : l=v := by apply Fin.ext; simpa using h
      exact off (same ▸ hl)

theorem flag_below (P L : Finset (Fin n)) (p l : Fin n) (hp : p ∈ P) (hl : l ∈ L) :
    LessBits (positiveBits (p,l)) (selected P L) := by
  intro i hi
  obtain e|e := of_decide_eq_true hi
  · subst i; simpa [selected] using hp
  · subst i; simpa only [selected, Fin.addCases_right, decide_eq_true_eq] using hl

theorem exact_sparse (q : ℕ) (f : (Fin (n+n) → Bool) → Bool)
    (inc : Increasing f) (pos : ∀ p l, I p l → f (positiveBits (p,l))=true)
    (neg : ∀ T, T.card ≤ q → f (negativeBits I T)=false)
    (P L : Finset (Fin n)) (small : L.card ≤ q) :
    f (selected P L)=true ↔ ∃ p ∈ P, ∃ l ∈ L, I p l := by
  constructor
  · intro h
    by_contra! free
    have yes := inc _ _ (independent_below I P L free) h
    rw [neg L small] at yes
    contradiction
  · rintro ⟨p,hp,l,hl,edge⟩
    exact inc _ _ (flag_below P L p l hp hl) (pos _ _ edge)
end Promise

section Readers
/-- A singly OR-read vertex cannot be masked by a one-signal wire on the
opposite shore. One or two active opposite vertices suffice for the test. -/
theorem no_or_mask {β : Type*} [DecidableEq β] (y z : β)
    (W : Finset β → Bool) (K : Bool → Finset β → Bool)
    (F : Bool → Finset β → Bool) (on : W {z} = true)
    (monoW : ∀ S T, S ⊆ T → W S = true → W T = true)
    (factor : ∀ x T, F x T = K (x || W T) T)
    (pos : F true {y} = true)
    (monoF : ∀ S T, S ⊆ T → F true S = true → F true T = true)
    (neg : ∀ T, T.card ≤ 2 → F false T = false) : False := by
  have m : W {y,z} = true := monoW {z} {y,z} (by simp) on
  have p := monoF {y} {y,z} (by simp) pos
  have hcard : ({y,z} : Finset β).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  have n := neg {y,z} hcard
  simp [factor,m] at p n
  rw [p] at n
  contradiction
end Readers

/-- Re-minimization is allowed between pins. This telescope needs only the
existence of one affordable next choice on each surviving subset. -/
theorem telescope {α : Type*} [DecidableEq α] (U : Finset α) (cost : Finset α → ℕ)
    (stop payment : ℕ) (enough : stop ≤ U.card)
    (step : ∀ S ⊆ U, stop < S.card → ∃ x ∈ S, cost (S.erase x) + payment ≤ cost S) :
    ∃ R ⊆ U, R.card=stop ∧ cost R + payment*(U.card-stop) ≤ cost U := by
  have build : ∀ m (S : Finset α), S.card=m → S ⊆ U → stop ≤ m →
      ∃ R ⊆ S, R.card=stop ∧ cost R + payment*(m-stop) ≤ cost S := by
    intro m
    induction m with
    | zero =>
      intro S eq sub hn
      refine ⟨S,Finset.Subset.rfl,by omega,by simp⟩
    | succ m ih =>
      intro S eq sub hn
      by_cases last : stop = m+1
      · exact ⟨S,Finset.Subset.rfl,eq.trans last.symm,by simp [last]⟩
      · obtain ⟨x,hx,pay⟩ := step S sub (by omega)
        have size : (S.erase x).card=m := by rw [Finset.card_erase_of_mem hx,eq]; omega
        obtain ⟨R,rs,card,old⟩ := ih (S.erase x) size (Finset.Subset.trans (Finset.erase_subset _ _) sub) (by omega)
        refine ⟨R,rs.trans (Finset.erase_subset _ _),card,?_⟩
        rw [show m+1-stop = (m-stop)+1 by omega,Nat.mul_add,Nat.mul_one]
        omega
  exact build U.card U rfl Finset.Subset.rfl enough

section Geometry
variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def entry (p l : Fin N) : ℤ := if I p l then 1 else 0

theorem column_total (q : ℕ) (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (l : Fin N) : ∑ p, entry I p l = (q:ℤ)+1 := by
  have d := degree l
  simp only [Fintype.card_subtype] at d
  simpa [entry,Finset.sum_boole] using (show ((Finset.univ.filter fun p => I p l).card : ℤ) = q+1 by exact_mod_cast d)

theorem row_dot (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) (p r : Fin N) :
    ∑ l, entry I p l * entry I r l = if p=r then ∑ l, entry I p l else 1 := by
  classical
  by_cases eq : p=r
  · subst r
    simp only [ite_true]
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : I p l <;> simp [entry,h]
  · rw [ite_eq_right eq]
    obtain ⟨u,hu,one⟩ := unique p r eq
    rw [Finset.sum_eq_single u]
    · simp [entry,hu.1,hu.2]
    · intro v _ diff
      by_cases a : I p v <;> by_cases b : I r v <;> simp_all [entry]
    · simp

theorem point_total (q : ℕ) (hq : 0 < q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) (p : Fin N) :
    ∑ l, entry I p l = (q:ℤ)+1 := by
  let t := ∑ l, entry I p l
  have diag : ∀ r : Fin N, (if p=r then t else 1) = 1+(if r=p then t-1 else 0) := by
    intro r
    by_cases eq : r=p
    · subst r; simp
    · simp [eq,Ne.symm eq]
  have area : t*((q:ℤ)+1) = N + (t-1) := by
    calc
      _ = ∑ l, entry I p l * (∑ r, entry I r l) := by
        simp only [column_total I q degree,Finset.sum_mul,t]
      _ = ∑ r, ∑ l, entry I p l * entry I r l := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = _ := by
        simp only [row_dot I unique,← show t = ∑ l, entry I p l from rfl,diag,
          Finset.sum_add_distrib]
        simp
  have cast : (N:ℤ)=(q:ℤ)^2+q+1 := by exact_mod_cast order
  change t=_
  have zero : (q:ℤ)*(t-((q:ℤ)+1))=0 := by nlinarith
  have hn : (q:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have := (mul_eq_zero.mp zero).resolve_left hn
  omega

def meetCount (R : Finset (Fin N)) (l : Fin N) : ℤ := ∑ p ∈ R, entry I p l

theorem moments (q : ℕ) (hq : 0 < q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) (R : Finset (Fin N)) :
    (∑ l, meetCount I R l = (R.card:ℤ)*(q+1)) ∧
    ∑ l, meetCount I R l*(meetCount I R l-1) = (R.card:ℤ)*(R.card-1) := by
  have pt := point_total I q hq order degree unique
  have first : ∑ l, meetCount I R l = (R.card:ℤ)*(q+1) := by
    unfold meetCount
    rw [Finset.sum_comm]
    simp [pt]
  have diag (p r : Fin N) :
      (if p=r then ∑ l, entry I p l else 1) = 1+(if r=p then (q:ℤ) else 0) := by
    by_cases eq : r=p
    · subst r; simp [pt,add_comm]
    · simp [eq,Ne.symm eq]
  have squares : ∑ l, meetCount I R l * meetCount I R l = (R.card:ℤ)*(R.card+q) := by
    calc
      _ = ∑ p ∈ R, ∑ r ∈ R, ∑ l, entry I p l * entry I r l := by
        simp only [meetCount,Finset.sum_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_comm]
        simp only [mul_comm]
      _ = _ := by
        simp only [row_dot I unique,diag,Finset.sum_add_distrib]
        simp [mul_add]
  refine ⟨first,?_⟩
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,squares,first]
  ring

end Geometry

section Counts

/-- A quadratic nonnegative on the integers pays twice for empty lines and
once for tangent lines. A tangent meets the retained point set once. -/
theorem penalty_pointwise (k d : ℤ) (hk : 3 ≤ k) (hd : 0 ≤ d) :
    (if d=0 then 2 else if d=1 then 1 else 0) * (k*(k+1)) ≤
      2*((d-k)*(d-k-1)) := by
  split_ifs with a b
  · subst d; ring_nf; omega
  · subst d
    have t : 0 ≤ k*(k-3) := mul_nonneg (by omega) (by omega)
    nlinarith
  · by_cases h : d ≤ k
    · have t := mul_nonneg (show 0 ≤ k-d by omega) (show 0 ≤ k+1-d by omega)
      nlinarith
    · have t := mul_nonneg (show 0 ≤ d-k by omega) (show 0 ≤ d-k-1 by omega)
      nlinarith

/-- The first two incidence moments give the entire quadratic sum. -/
theorem quadratic_moment {N : ℕ} (d : Fin N → ℤ) (q k : ℤ)
    (order : (N:ℤ) = q*q+q+1)
    (total : ∑ l, d l = (k*(q+1))*(q+1))
    (pairs : ∑ l, d l*(d l-1) = (k*(q+1))*(k*(q+1)-1)) :
    ∑ l, (d l-k)*(d l-k-1) = q*k*(q-k) := by
  calc
    _ = ∑ l, (d l*(d l-1) - (2*k)*d l + k*(k+1)) := by
      apply Finset.sum_congr rfl
      intro l _; ring
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,pairs,total]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,order]
      ring

theorem total_penalty {N : ℕ} (d : Fin N → ℤ) (q k : ℤ)
    (hk : 3 ≤ k) (hd : ∀ l, 0 ≤ d l)
    (order : (N:ℤ) = q*q+q+1)
    (total : ∑ l, d l = (k*(q+1))*(q+1))
    (pairs : ∑ l, d l*(d l-1) = (k*(q+1))*(k*(q+1)-1)) :
    (∑ l, (if d l=0 then 2 else if d l=1 then 1 else 0)) * (k*(k+1)) ≤
      2*(q*k*(q-k)) := by
  rw [Finset.sum_mul,← quadratic_moment d q k order total pairs,Finset.mul_sum]
  exact Finset.sum_le_sum fun l _ => penalty_pointwise k (d l) hk (hd l)

theorem numerical (q N g : ℕ) (lo : 250 ≤ q) (hi : q ≤ 380)
    (order : N = q^2+q+1)
    (bound : (4*N : ℤ) * 20 ≤ (g:ℤ)*20 + 2*19*(q+1)*20 + 2*(q:ℤ)*(q-19)) :
    N*q ≤ 100*g := by
  have arith : ∀ j : Fin 381, 250 ≤ j.val →
      let n : ℤ := (j.val:ℤ)^2+j.val+1
      20*n*j.val ≤ 100*(4*n*20-2*19*(j.val+1)*20-2*(j.val:ℤ)*(j.val-19)) := by
    decide +kernel
  obtain h := arith ⟨q,by omega⟩ lo
  simp only at h
  rw [order] at bound ⊢
  push_cast at bound ⊢
  exact_mod_cast (show ((q:ℤ)^2+q+1)*(q:ℤ) ≤ 100*(g:ℤ) by nlinarith)

/-- For an arbitrary retained point set, the deletion inequality alone
implies the desk target in the indicated range. -/
theorem range_from_payment {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (q g : ℕ) (lo : 250 ≤ q) (hi : q ≤ 380) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) (R : Finset (Fin N))
    (kept : R.card=19*(q+1))
    (payment : 4*(N:ℤ) ≤ g+2*(R.card:ℤ) +
      ∑ l, (if meetCount I R l=0 then 2 else if meetCount I R l=1 then 1 else 0)) :
    N*q ≤ 100*g := by
  obtain ⟨total,pairs⟩ := moments I q (by omega) order degree unique R
  have size : (R.card:ℤ)=19*((q:ℤ)+1) := by exact_mod_cast kept
  rw [size] at total pairs payment
  have hd (l : Fin N) : 0 ≤ meetCount I R l := by
    apply Finset.sum_nonneg
    intro p _
    by_cases h : I p l <;> simp [entry,h]
  have orderZ : (N:ℤ)=(q:ℤ)*q+q+1 := by exact_mod_cast (by simpa [pow_two] using order : N=q*q+q+1)
  have penalty := total_penalty (meetCount I R) q 19 (by decide) hd orderZ total pairs
  apply numerical q N g lo hi order
  nlinarith

end Counts
section ClauseProducts

theorem cube_cover (m k : ℕ) (miss : Fin k → (Fin m → Bool) → Prop)
    (cover : ∀ b, ∃ c, miss c b)
    (alone : ∀ c b d, miss c b → miss c d → b=d) : 2^m ≤ k := by
  classical
  choose f hf using cover
  have inj : Function.Injective f := by
    intro b d eq
    exact alone (f d) b d (eq ▸ hf b) (hf d)
  simpa using Fintype.card_le_of_injective f inj

theorem cube_power (j : ℕ) (hj : 10 ≤ j) : j^3 ≤ 2^j := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    have a : 0 ≤ (j:ℤ)-10 := by omega
    have b := mul_nonneg a (sq_nonneg ((j:ℤ)+1))
    have c := sq_nonneg ((j:ℤ)-5)
    have growth : (j+1)^3 ≤ 2*j^3 := by
      exact_mod_cast (show ((j:ℤ)+1)^3 ≤ 2*(j:ℤ)^3 by nlinarith)
    rw [pow_succ]
    exact growth.trans (by omega)

/-- The five geometric and connectivity estimates for one clause product
collapse to a uniform cost of at least one gate per three flags, up to one. -/
theorem term_cost (e v k j x : ℕ) (vertices : v ≤ x) (terminals : 2*k ≤ x)
    (components : v+k ≤ x+2) (dyadic : 2^j ≤ k)
    (degree : 2*e ≤ max 2 j * v) (matching : e ≤ v+4*j^3) : e ≤ 3*x := by
  by_cases small : j ≤ 6
  · have h := Nat.mul_le_mul_right v (show max 2 j ≤ 6 by omega)
    omega
  by_cases large : 10 ≤ j
  · have power := cube_power j large
    omega
  interval_cases j <;> norm_num at * <;> omega

/-- Choosing one outside literal per missed clause produces a forbidden
input unless some clause has no outside literal on the projected shore. -/
theorem projected_terminal {α β : Type*} [DecidableEq β] (W : Finset α)
    (outside : Set β) (C : α → Set β)
    (reject : ∀ S : Finset β, (∀ b ∈ S, b ∈ outside) → S.card ≤ W.card →
      ∃ c ∈ W, ∀ b ∈ S, b ∉ C c) :
    ∃ c ∈ W, ∀ b ∈ outside, b ∉ C c := by
  classical
  by_contra! bad
  have select (c : ↥W) : ∃ b ∈ outside, b ∈ C c.val := bad c.val c.property
  choose f hf hg using select
  let S := Finset.univ.image f
  have n : S.card ≤ W.card := by simpa [S] using (Finset.card_image_le (f:=f) (s:=Finset.univ))
  obtain ⟨c,hc,no⟩ := reject S (by
    intro b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    exact hf i) n
  let i : ↥W := ⟨c,hc⟩
  exact no (f i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) (hg i)

theorem cover_per_and (j k : ℕ) (dyadic : 2^j ≤ k) : 4*j^2 ≤ 6*(k-1) := by
  have small : ∀ t : Fin 4, 4*t.val^2 ≤ 6*(2^t.val-1) := by decide
  have aux : ∀ t, 3 ≤ t → 4*t^2 ≤ 6*(2^t-1) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => decide
    | succ t ht ih =>
      have grows : (t+1)^2 ≤ 2*t^2 := by
        have prod := Nat.mul_le_mul_left t (show 3 ≤ t by omega)
        nlinarith
      have nz : 0 < (2:ℕ)^t := Nat.pow_pos (by decide)
      rw [show (2:ℕ)^(t+1)=2^t*2 by exact pow_succ ..]
      omega
  by_cases h : 3 ≤ j
  · have bound := aux j h
    omega
  · have bound := small ⟨j,by omega⟩
    change 4*j^2 ≤ 6*(2^j-1) at bound
    omega

theorem shared_product_bound (N q s r uses : ℕ) (big : 99 ≤ N)
    (flags : N*(q+1) ≤ 3*(uses+r)) (overlap : uses ≤ 33*(s+1-r))
    (top : r ≤ s+1) : N*q ≤ 100*s := by
  rw [Nat.mul_add,Nat.mul_one] at flags
  omega

end ClauseProducts

end PlaneRectangleSeparation
