import PEqualNP.Defs

namespace SingletonFrontier

variable {W R : Type} (V : W → R → Bool)

-- An OR on the terminal wires of a private OR tree.
def fires (xs : List W) (z : R) : Prop := ∃ w ∈ xs, V w z = true

def feeds (w : W) (side : List W) : Prop := ∀ z, V w z = true → fires V side z

def covered (xs other : List W) (z : R) : Prop :=
  ∀ w ∈ xs, V w z = true → feeds V w other

noncomputable def selected (other : List W) (w : W) : Bool := by
  classical
  exact decide (feeds V w other)

theorem selected_iff (other : List W) (w : W) :
    selected V other w = true ↔ feeds V w other := by
  classical
  simp [selected]

theorem partition (xs other : List W) (z : R) :
    fires V xs z ↔ fires V (xs.filter (selected V other)) z ∨
      fires V (xs.filter (fun w => !(selected V other w))) z := by
  constructor
  · rintro ⟨w,h,hv⟩
    cases e : selected V other w with
    | true => exact Or.inl ⟨w,List.mem_filter.mpr ⟨h,e⟩,hv⟩
    | false => exact Or.inr ⟨w,List.mem_filter.mpr ⟨h,by simp [e]⟩,hv⟩
  · rintro (⟨w,h,hv⟩|⟨w,h,hv⟩) <;> exact ⟨w,(List.mem_filter.mp h).1,hv⟩

theorem regroup (xs other : List W) (z : R) :
    (fires V xs z ∧ fires V other z) ↔
      fires V (xs.filter (selected V other)) z ∨
      (fires V (xs.filter (fun w => !(selected V other w))) z ∧ fires V other z) := by
  constructor
  · rintro ⟨h,k⟩
    rcases (partition V xs other z).mp h with a|b
    · exact Or.inl a
    · exact Or.inr ⟨b,k⟩
  · rintro (h|⟨h,k⟩)
    · obtain ⟨w,hm,v⟩ := h
      obtain ⟨mem,sel⟩ := List.mem_filter.mp hm
      exact ⟨⟨w,mem,v⟩,(selected_iff V other w).mp sel z v⟩
    · exact ⟨(partition V xs other z).mpr (Or.inr h),k⟩

theorem clears (xs other : List W) (x : R) (h : covered V xs other x) :
    ¬ fires V (xs.filter (fun w => !(selected V other w))) x := by
  rintro ⟨w,hm,v⟩
  obtain ⟨mem,off⟩ := List.mem_filter.mp hm
  have on := (selected_iff V other w).mpr (h w mem v)
  simp [on] at off

theorem splitCost (p q : ℕ) (hp : 0<p) (hq : 0<q) :
    (p-1)+(q-1)+2 = (p+q-1)+1 := by omega

-- The two incompatible shared wires are distinguished by actual assignments.
theorem alternative (A B : List W) (x : R) (shared : W → Prop)
    (left : ∀ w ∈ A, V w x = true → ¬ shared w → feeds V w B)
    (right : ∀ w ∈ B, V w x = true → ¬ shared w → feeds V w A) :
    covered V A B x ∨ covered V B A x ∨
      ∃ u ∈ A, ∃ v ∈ B, shared u ∧ shared v ∧ V u x = true ∧ V v x = true ∧
        (∃ t, V u t = true ∧ V v t = false) ∧ (∃ t, V v t = true ∧ V u t = false) := by
  classical
  by_cases ha : covered V A B x
  · exact Or.inl ha
  by_cases hb : covered V B A x
  · exact Or.inr (Or.inl hb)
  right; right
  simp only [covered,not_forall] at ha hb
  obtain ⟨u,ua,ux,nu⟩ := ha
  obtain ⟨v,vb,vx,nv⟩ := hb
  have su : shared u := by by_contra no; exact nu (left u ua ux no)
  have sv : shared v := by by_contra no; exact nv (right v vb vx no)
  simp only [feeds,not_forall] at nu nv
  obtain ⟨t,ut,nt⟩ := nu
  obtain ⟨z,vz,nz⟩ := nv
  have vt : V v t = false := by
    cases e : V v t with
    | false => rfl
    | true => exact False.elim (nt ⟨v,vb,e⟩)
  have uz : V u z = false := by
    cases e : V u z with
    | false => rfl
    | true => exact False.elim (nz ⟨u,ua,e⟩)
  exact ⟨u,ua,v,vb,su,sv,ux,vx,⟨t,ut,vt⟩,⟨z,vz,uz⟩⟩


-- Regard an assignment on the old variables as a set. A wire W may be used
-- to restore a deleted vertex as long as it agrees with its neighbor alarm
-- wherever the old graph function is false.
theorem repair {old alarm W : R → Prop} (ok : ∀ z, ¬old z → (W z ↔ alarm z))
    (z : R) (x : Prop) :
    (old z ∨ (x ∧ W z)) ↔ (old z ∨ (x ∧ alarm z)) := by
  by_cases h : old z
  · simp [h]
  · simp [h,ok z h]

theorem independentTests {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Finset ι) (ind W : Finset ι → Prop)
    (mono : ∀ s t, s ⊆ t → W s → W t)
    (single : ∀ i ∈ K, W {i})
    (maxneg : ∀ t, ind t → Disjoint t K →
      (∀ u, t ⊆ u → ind u → Disjoint u K → u = t) → ¬ W t) :
    ∀ s, ind s → (W s ↔ ∃ i ∈ K, i ∈ s) := by
  classical
  intro s hs
  constructor
  · intro hw
    by_contra miss
    have dis : Disjoint s K := Finset.disjoint_left.mpr (by
      intro i hi hk; exact miss ⟨i,hk,hi⟩)
    let fam : Finset (Finset ι) := Finset.univ.filter (fun t => s ⊆ t ∧ ind t ∧ Disjoint t K)
    have ins : s ∈ fam := by simp [fam,hs,dis]
    obtain ⟨t,mem,largest⟩ := Finset.exists_max_image fam Finset.card ⟨s,ins⟩
    obtain ⟨st,it,dt⟩ := (Finset.mem_filter.mp mem).2
    have mt : ∀ u, t ⊆ u → ind u → Disjoint u K → u=t := by
      intro u tu iu du
      exact (Finset.eq_of_subset_of_card_le tu (largest u
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,st.trans tu,iu,du⟩))).symm
    exact (maxneg t it dt mt) (mono s t st hw)
  · rintro ⟨i,hi,mem⟩
    exact mono {i} s (Finset.singleton_subset_iff.mpr mem) (single i hi)

-- This three-bit example forces an extra gate if both shared ORs must stay
-- and the value at the selected output must agree on singleton and edge rows.
def available (w : Fin 5) (x a b : Bool) : Bool :=
  [x,a,b,x || a,x || b].getD w.val false

def forkValue (x a b : Bool) := (x || a) && (x || b)

theorem forkForm (x a b : Bool) : forkValue x a b = (x || (a && b)) := by
  cases x <;> cases a <;> cases b <;> rfl

theorem forkLower :
    ∀ u v : Fin 5, ∀ op : Bool,
      (let f := fun x a b =>
        if op then (available u x a b && available v x a b)
        else (available u x a b || available v x a b)
       (op = true → f true false false = false) →
       ¬ (f true false false = true ∧ f false true false = false ∧
          f false false true = false ∧ f false true true = true)) := by decide


def containsEdge {ι : Type} (E : Finset (Finset ι)) (s : Finset ι) :=
  ∃ e ∈ E, e ⊆ s

-- K fixes all wires independent of the replaced signal. Its second input is
-- the signal value. E lists the minimal positive assignments.
theorem spliceCorrect {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Finset (Finset ι)) (a b : Finset ι → Prop) (K : Finset ι → Prop → Prop)
    (port : ∀ s u v, (u → v) → K s u → K s v)
    (mono : ∀ s t, s ⊆ t → K s (b s) → K t (b t))
    (old : ∀ s, K s (a s) ↔ containsEdge E s)
    (pos : ∀ e ∈ E, a e → b e)
    (neg : ∀ t, ¬ containsEdge E t →
      (∀ u, t ⊆ u → ¬containsEdge E u → u=t) → K t True → b t → a t) :
    ∀ s, K s (b s) ↔ containsEdge E s := by
  classical
  intro s
  constructor
  · intro yes
    by_contra no
    let fam := Finset.univ.filter (fun t : Finset ι => s ⊆ t ∧ ¬containsEdge E t)
    have mem : s ∈ fam := by simp [fam,no]
    obtain ⟨t,tm,largest⟩ := Finset.exists_max_image fam Finset.card ⟨s,mem⟩
    obtain ⟨st,nt⟩ := (Finset.mem_filter.mp tm).2
    have mx : ∀ u, t ⊆ u → ¬containsEdge E u → u=t := by
      intro u tu nu
      exact (Finset.eq_of_subset_of_card_le tu (largest u
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,st.trans tu,nu⟩))).symm
    have hit := mono s t st yes
    have force := port t (b t) True (fun _ => True.intro) hit
    exact nt ((old t).mp (port t _ _ (neg t nt mx force) hit))
  · rintro ⟨e,he,sub⟩
    exact mono e s sub (port e _ _ (pos e he) ((old e).mpr ⟨e,he,by rfl⟩))

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def original : Circuit := ⟨[
  ⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.and,[4,5]⟩,⟨.and,[1,2]⟩,
  ⟨.or,[3,7]⟩,⟨.and,[6,8]⟩,⟨.or,[4,5]⟩,⟨.and,[9,10]⟩],11⟩

def repaired : Circuit := ⟨[
  ⟨.and,[1,2]⟩,⟨.and,[1,2]⟩,⟨.or,[3,5]⟩,⟨.and,[4,6]⟩,
  ⟨.or,[1,2]⟩,⟨.and,[7,8]⟩,⟨.and,[0,3]⟩,⟨.or,[9,10]⟩],11⟩

attribute [local instance] gateOpDecEq

theorem matchingControl :
    original.size = 8 ∧ repaired.size = 8 ∧
    (∀ z : Fin 4 → Bool, original.eval (List.ofFn z) = ((z 0 && z 3) || (z 1 && z 2)) ∧
      repaired.eval (List.ofFn z) = original.eval (List.ofFn z)) ∧
    (original.wires [true,false,false,false]).getD 6 false = true ∧
    (∀ j : Fin 8, (gateAt repaired j).op = GateOp.and → ∀ i : Fin 4,
      (repaired.wires (List.ofFn (fun v : Fin 4 => decide (v=i)))).getD (4+j.val) false = false) := by
  decide


def increases (xs ys : List Bool) :=
  xs.length = ys.length ∧ ∀ i, xs.getD i false = true → ys.getD i false = true

theorem snoc {xs ys : List Bool} {a b : Bool} (h : increases xs ys) (ab : a=true → b=true) :
    increases (xs++[a]) (ys++[b]) := by
  obtain ⟨len,ord⟩ := h
  refine ⟨by simp [len],?_⟩
  intro i
  by_cases hi : i<xs.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (len ▸ hi)]
    exact ord i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),← len]
    cases i-xs.length with
    | zero => exact ab
    | succ j => simp [List.getD_eq_getElem?_getD]

def advance (xs : List Bool) (g : Gate) :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

theorem advanceMono (xs ys : List Bool) (g : Gate) (op : g.op=.and ∨ g.op=.or)
    (h : increases xs ys) : increases (advance xs g) (advance ys g) := by
  apply snoc h
  rcases op with e|e
  · simp only [e, GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro all w hw
    exact h.2 w (all w hw)
  · simp only [e, GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨w,hw,hit⟩
    exact ⟨w,hw,h.2 w hit⟩

theorem foldMono (gs : List Gate) (ops : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (xs ys : List Bool) (h : increases xs ys) :
    increases (gs.foldl advance xs) (gs.foldl advance ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g tail ih =>
    exact ih (fun k hk => ops k (List.mem_cons_of_mem _ hk)) _ _
      (advanceMono xs ys g (ops g List.mem_cons_self) h)

theorem suffixMono (C : Circuit) (mono : Monotone2 C) (xs ys : List Bool) (h : increases xs ys) :
    increases (C.wires xs) (C.wires ys) := by
  apply foldMono C.gates _ xs ys h
  exact fun g hg => (mono g hg).1


-- R can consist solely of the maximal negatives on which the circuit would
-- change if the chosen AND wire were forced high. x is tested separately.
theorem twoTestRows (A B : List W) (atX : W → Prop) (shared : W → Prop)
    (left : ∀ w ∈ A, atX w → ¬shared w → feeds V w B)
    (right : ∀ w ∈ B, atX w → ¬shared w → feeds V w A)
    (noL : ¬ ∀ w ∈ A, atX w → feeds V w B)
    (noR : ¬ ∀ w ∈ B, atX w → feeds V w A) :
    ∃ u ∈ A, ∃ v ∈ B, shared u ∧ shared v ∧ atX u ∧ atX v ∧
      ∃ r s : R, r ≠ s ∧ V u r = true ∧ V v r = false ∧ V u s = false ∧ V v s = true := by
  classical
  simp only [not_forall] at noL noR
  obtain ⟨u,ua,ux,nu⟩ := noL
  obtain ⟨v,vb,vx,nv⟩ := noR
  have su : shared u := by by_contra no; exact nu (left u ua ux no)
  have sv : shared v := by by_contra no; exact nv (right v vb vx no)
  simp only [feeds,not_forall] at nu nv
  obtain ⟨r,ur,nr⟩ := nu
  obtain ⟨s,vs,ns⟩ := nv
  have vr : V v r = false := by
    cases e : V v r <;> first | rfl | exact False.elim (nr ⟨v,vb,e⟩)
  have us : V u s = false := by
    cases e : V u s <;> first | rfl | exact False.elim (ns ⟨u,ua,e⟩)
  exact ⟨u,ua,v,vb,su,sv,ux,vx,r,s,by intro h; subst s; simp_all,ur,vr,us,vs⟩

theorem crossing {ι : Type} [DecidableEq ι] (G : SimpleGraph ι) (I J : Finset ι)
    (maxI : ∀ w, w ∉ I → ∃ u ∈ I, G.Adj w u)
    (indJ : ∀ u ∈ J, ∀ v ∈ J, ¬G.Adj u v)
    (j : ι) (hj : j ∈ J) (out : j ∉ I) :
    ∃ i ∈ I, i ∉ J ∧ G.Adj i j := by
  obtain ⟨i,hi,edge⟩ := maxI j out
  exact ⟨i,hi,fun h => indJ j hj i h edge,edge.symm⟩


theorem sensitiveRows (lo hi old replacement target : Bool)
    (monotone : lo=true → hi=true) (correct : (if old then hi else lo)=target) :
    ((if replacement then hi else lo)=target) ↔
      ((target=true ∧ lo=false) → replacement=true) ∧
      ((target=false ∧ hi=true) → replacement=false) := by
  cases lo <;> cases hi <;> cases old <;> cases replacement <;> cases target <;> simp_all


theorem chainPeel (A B : List W) (atX shared : W → Prop)
    (left : ∀ w ∈ A, atX w → ¬shared w → feeds V w B)
    (right : ∀ w ∈ B, atX w → ¬shared w → feeds V w A)
    (chain : ∀ u v, shared u → shared v → atX u → atX v →
      (∀ t, V u t = true → V v t = true) ∨ (∀ t, V v t = true → V u t = true)) :
    (∀ w ∈ A, atX w → feeds V w B) ∨ (∀ w ∈ B, atX w → feeds V w A) := by
  classical
  by_cases ha : ∀ w ∈ A, atX w → feeds V w B
  · exact Or.inl ha
  by_cases hb : ∀ w ∈ B, atX w → feeds V w A
  · exact Or.inr hb
  exfalso
  obtain ⟨u,_,v,_,hu,hv,ux,vx,r,s,_,ur,vr,us,vs⟩ :=
    twoTestRows V A B atX shared left right ha hb
  rcases chain u v hu hv ux vx with uv|vu
  · have := uv r ur; simp_all
  · have := vu s vs; simp_all

theorem legalControl : Monotone2 original ∧ ReadsBack 4 original ∧ Monotone2 repaired ∧ ReadsBack 4 repaired := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [Monotone2,original]
  · intro j hj
    change j<8 at hj
    interval_cases j <;> decide
  · simp [Monotone2,repaired]
  · intro j hj
    change j<8 at hj
    interval_cases j <;> decide

end SingletonFrontier
