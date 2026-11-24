import PEqualNP.Defs

namespace HeawoodPartition

def raw : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
def left : Fin 21 → Fin 14 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6]
def right : Fin 21 → Fin 14 := ![7, 8, 10, 7, 9, 13, 8, 12, 13, 7, 11, 12, 10, 11, 13, 9, 10, 12, 8, 9, 11]
def edgeAt : Fin 14 → Fin 3 → Fin 21 := ![![0, 1, 2], ![3, 4, 5], ![6, 7, 8], ![9, 10, 11], ![12, 13, 14], ![15, 16, 17], ![18, 19, 20], ![0, 3, 9], ![1, 6, 18], ![4, 15, 19], ![2, 12, 16], ![10, 13, 20], ![7, 11, 17], ![5, 8, 14]]
def negBit (v : Fin 14) (t : Fin 37) := (raw.getD v.val 0).testBit (21+t.val)

theorem row_labels : ∀ e : Fin 21, ∀ v : Fin 14,
    (raw.getD v.val 0).testBit e.val = decide (left e=v ∨ right e=v) := by decide +kernel

theorem local_injective : ∀ v : Fin 14, Function.Injective (edgeAt v) := by decide +kernel

theorem forcing : ∀ v : Fin 14, ∃ t : Fin 37, ∀ i : Fin 3,
    (if v.val<7 then negBit (right (edgeAt v i)) t else negBit (left (edgeAt v i)) t)=true := by
  decide +kernel

theorem distinguish : ∀ e f : Fin 21, left e ≠ left f → right e ≠ right f →
    ∃ t : Fin 37, (negBit (left e) t=true ∧ negBit (right f) t=true) ∨
      (negBit (right e) t=true ∧ negBit (left f) t=true) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem outer_edges : ∀ (v w : Fin 14) (i j : Fin 3), v≠w → edgeAt v i=edgeAt w j →
    ∀ a b : Fin 3, a≠i → b≠j →
      left (edgeAt v a) ≠ left (edgeAt w b) ∧ right (edgeAt v a) ≠ right (edgeAt w b) := by
  decide +kernel

def tied (z : Fin 3 → Fin 37 → Bool) : Finset (Fin 3) :=
  Finset.univ.filter fun i => ∃ j, j≠i ∧ z i=z j

-- Two rectangles which together cover a whole column use at most two row patterns.
theorem two_patterns :
    ∀ (A B : Fin 3 → Bool) (a b : Bool),
      (∀ i, ((A i && a) || (B i && b))=true) →
      (∀ i, ((A i && a) && (B i && b))=false) →
      ∃ i j, i≠j ∧ A i=A j ∧ B i=B j := by decide +kernel

theorem local_price (k : ℕ) (z : Fin 3 → Fin 37 → Bool)
    (R : Fin k → Fin 3 → Bool) (C : Fin k → Fin 37 → Bool)
    (exactly : ∀ i t, z i t=true ↔ ∃ b, R b i=true ∧ C b t=true)
    (unique : ∀ i t a b, R a i=true → C a t=true → R b i=true → C b t=true → a=b)
    (full : ∃ t, ∀ i, z i t=true) : 9 ≤ 3*k+2*(tied z).card := by
  classical
  obtain ⟨t,all⟩ := full
  have equal (i j : Fin 3) (h : ∀ b, R b i=R b j) : z i=z j := by
    funext c
    apply Bool.eq_iff_iff.mpr
    rw [exactly,exactly]
    simp only [h]
  cases k with
  | zero =>
    obtain ⟨i,_,_⟩ := (exactly 0 t).mp (all 0)
    exact Fin.elim0 i
  | succ k =>
    cases k with
    | zero =>
      have on (i : Fin 3) : R 0 i=true := by
        obtain ⟨b,yes,_⟩ := (exactly i t).mp (all i)
        fin_cases b; exact yes
      have every : tied z=Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro i
        obtain ⟨j,ne⟩ := exists_ne i
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,ne,
          equal i j (fun b => by fin_cases b; exact (on i).trans (on j).symm)⟩
      simp [every]
    | succ k =>
      cases k with
      | zero =>
        have both (i : Fin 3) : ((R 0 i && C 0 t) || (R 1 i && C 1 t))=true := by
          obtain ⟨b,h,c⟩ := (exactly i t).mp (all i)
          fin_cases b <;> simp_all
        have dis (i : Fin 3) : ((R 0 i && C 0 t) && (R 1 i && C 1 t))=false := by
          cases x : R 0 i <;> cases y : C 0 t <;> cases a : R 1 i <;> cases b : C 1 t <;> try rfl
          exact False.elim ((by decide : (0 : Fin 2)≠1) (unique i t 0 1 x y a b))
        obtain ⟨i,j,ne,a,b⟩ := two_patterns (R 0) (R 1) (C 0 t) (C 1 t) both dis
        have eq := equal i j (fun r => by fin_cases r <;> assumption)
        have sub : ({i,j} : Finset (Fin 3)) ⊆ tied z := by
          intro x hx
          rcases Finset.mem_insert.mp hx with h|h
          · subst x; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,ne.symm,eq⟩
          · have e := Finset.mem_singleton.mp h
            subst x; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,ne,eq.symm⟩
        have size := Finset.card_le_card sub
        rw [Finset.card_pair ne] at size
        omega
      | succ k => omega

def takeAt (orient : Fin 21 → Fin 37 → Bool) (v : Fin 14) (i : Fin 3) (t : Fin 37) :=
  if v.val<7 then orient (edgeAt v i) t else !(orient (edgeAt v i) t)

theorem taken_eq (orient : Fin 21 → Fin 37 → Bool) (v : Fin 14) (i j : Fin 3)
    (h : takeAt orient v i=takeAt orient v j) : orient (edgeAt v i)=orient (edgeAt v j) := by
  funext t
  have eq := congrFun h t
  by_cases side : v.val<7
  · simpa [takeAt,side] using eq
  · simpa [takeAt,side] using eq

theorem partition_lower (orient : Fin 21 → Fin 37 → Bool)
    (l : ∀ e t, negBit (left e) t=true → orient e t=false)
    (r : ∀ e t, negBit (right e) t=true → orient e t=true)
    (k : Fin 14 → ℕ) (R : ∀ v, Fin (k v) → Fin 3 → Bool)
    (C : ∀ v, Fin (k v) → Fin 37 → Bool)
    (rep : ∀ v i t, takeAt orient v i t=true ↔ ∃ b, R v b i=true ∧ C v b t=true)
    (unique : ∀ v i t a b, R v a i=true → C v a t=true → R v b i=true → C v b t=true → a=b) :
    28 ≤ ∑ v, k v := by
  classical
  let A (v : Fin 14) := (tied (takeAt orient v)).image (edgeAt v)
  have card (v : Fin 14) : (A v).card=(tied (takeAt orient v)).card :=
    Finset.card_image_of_injOn (local_injective v).injOn
  have dis : ∀ v ∈ (Finset.univ : Finset (Fin 14)), ∀ w ∈ (Finset.univ : Finset (Fin 14)), v≠w → Disjoint (A v) (A w) := by
    intro v _ w _ ne
    apply Finset.disjoint_left.mpr
    intro e h1 h2
    obtain ⟨i,ti,ei⟩ := Finset.mem_image.mp h1
    obtain ⟨j,tj,ej⟩ := Finset.mem_image.mp h2
    obtain ⟨a,na,qa⟩ := (Finset.mem_filter.mp ti).2
    obtain ⟨b,nb,qb⟩ := (Finset.mem_filter.mp tj).2
    have dif := outer_edges v w i j ne (ei.trans ej.symm) a b na nb
    have same := (taken_eq orient v i a qa).symm.trans
      ((congrArg orient (ei.trans ej.symm)).trans (taken_eq orient w j b qb))
    obtain ⟨t,hit|hit⟩ := distinguish _ _ dif.1 dif.2
    · exact Bool.noConfusion ((l _ t hit.1).symm.trans ((congrFun same t).trans (r _ t hit.2)))
    · exact Bool.noConfusion ((r _ t hit.1).symm.trans ((congrFun same t).trans (l _ t hit.2)))
  have small : (∑ v, (A v).card) ≤ 21 := by
    have h := Finset.card_le_card (Finset.subset_univ ((Finset.univ : Finset (Fin 14)).biUnion A))
    rw [Finset.card_biUnion] at h
    · simpa using h
    · intro i hi j hj ne
      exact dis i hi j hj ne
  have each (v : Fin 14) : 9 ≤ 3*k v+2*(A v).card := by
    rw [card]
    apply local_price (k v) _ (R v) (C v) (rep v) (unique v)
    obtain ⟨t,ht⟩ := forcing v
    refine ⟨t,fun i => ?_⟩
    by_cases h : v.val<7
    · exact (by simpa [takeAt,h] using r (edgeAt v i) t (by simpa [h] using ht i))
    · simp [takeAt,h,l (edgeAt v i) t (by simpa [h] using ht i)]
  have bound := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => each v)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Finset.sum_add_distrib,
    ←Finset.mul_sum] at bound
  omega


theorem channels : ∀ (v : Fin 14) (i : Fin 3),
    if v.val<7 then left (edgeAt v i)=v ∧ right (edgeAt v i)≠v
    else right (edgeAt v i)=v ∧ left (edgeAt v i)≠v := by decide +kernel

theorem raw_partition {ι : Type} [Fintype ι] [DecidableEq ι] (label : ι → Fin 14)
    (select : Fin 21 → Fin 37 → ι) (R : ι → Fin 21 → Bool) (C : ι → Fin 37 → Bool)
    (rect : ∀ e t b, select e t=b ↔ R b e=true ∧ C b t=true)
    (on : ∀ e t, label (select e t)=left e ∨ label (select e t)=right e)
    (off : ∀ e t, negBit (label (select e t)) t=false) : 28 ≤ Fintype.card ι := by
  classical
  let pick e t := label (select e t)
  let ori e t := decide (pick e t=left e)
  let k v := Fintype.card {b : ι // label b=v}
  let idx (v : Fin 14) := (Fintype.equivFin {b : ι // label b=v}).symm
  have role (v : Fin 14) (i : Fin 3) (t : Fin 37) :
      takeAt ori v i t=true ↔ pick (edgeAt v i) t=v := by
    have side := channels v i
    have endpoints := on (edgeAt v i) t
    change pick (edgeAt v i) t=_ ∨ pick (edgeAt v i) t=_ at endpoints
    by_cases h : v.val<7
    · simp [h] at side
      simp [takeAt,h,ori,side.1]
    · simp [h] at side
      simp [takeAt,h,ori]
      rcases endpoints with a|b
      · rw [a]; simp [side.2]
      · rw [b,side.1]; simp [Ne.symm side.2]
  have total := partition_lower ori
    (fun e t h => by
      have miss : pick e t ≠ left e := by
        intro eq; have bad := off e t; change negBit (pick e t) t=false at bad; rw [eq,h] at bad; contradiction
      simp [ori,miss])
    (fun e t h => by
      rcases on e t with eq|eq
      · exact decide_eq_true eq
      · have bad := off e t; rw [eq,h] at bad; contradiction)
    k (fun v b i => R (idx v b).val (edgeAt v i)) (fun v b t => C (idx v b).val t)
    (fun v i t => by
      rw [role]
      constructor
      · intro eq
        let w : {b : ι // label b=v} := ⟨select (edgeAt v i) t,eq⟩
        refine ⟨(idx v).symm w,?_⟩
        simpa only [Equiv.apply_symm_apply] using (rect (edgeAt v i) t w.val).mp rfl
      · rintro ⟨b,h⟩
        exact congrArg label ((rect _ _ _).mpr h) |>.trans (idx v b).property)
    (fun v i t a b ra ca rb cb => by
      apply (idx v).injective
      apply Subtype.ext
      exact ((rect _ _ _).mpr ⟨ra,ca⟩).symm.trans ((rect _ _ _).mpr ⟨rb,cb⟩))
  have sum : (∑ v, k v)=Fintype.card ι := by
    change (∑ v, Fintype.card {b : ι // label b=v})=_
    rw [←Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv label)
  simpa [sum] using total

inductive Tree where
  | raw (v : Fin 14)
  | gate (isOr : Bool) (a b : Tree)

def Tree.val : Tree → (Fin 14 → Bool) → Bool
  | .raw v,x => x v
  | .gate op a b,x => if op then a.val x || b.val x else a.val x && b.val x

def Tree.leaves : Tree → ℕ
  | .raw _ => 1
  | .gate _ a b => a.leaves+b.leaves

structure Protocol (X Y : Type) where
  size : ℕ
  label : Fin size → Fin 14
  start : X → Y → Fin size
  row : Fin size → X → Bool
  col : Fin size → Y → Bool
  block : ∀ x y b, start x y=b ↔ row b x=true ∧ col b y=true

-- Row and column tests are independent. This construction permits two
-- disjoint occurrences of the same raw variable to carry different blocks.
theorem tree_protocol (T : Tree) (px : Fin 21 → Fin 14 → Bool) (ny : Fin 37 → Fin 14 → Bool) :
    ∃ P : Protocol (Fin 21) (Fin 37), P.size=T.leaves ∧
      ∀ e t, T.val (px e)=true → T.val (ny t)=false →
        px e (P.label (P.start e t))=true ∧ ny t (P.label (P.start e t))=false := by
  induction T with
  | raw v =>
    exact ⟨⟨1,fun _ => v,fun _ _ => 0,fun _ _ => true,fun _ _ => true,
      fun e t b => by fin_cases b; simp⟩,rfl,fun _ _ h q => ⟨h,q⟩⟩
  | gate op a b ia ib =>
    obtain ⟨A,sa,ha⟩ := ia
    obtain ⟨B,sb,hb⟩ := ib
    let E := finSumFinEquiv (m:=A.size) (n:=B.size)
    let onA := fun e t => if op then a.val (px e) else !(a.val (ny t))
    let start := fun e t => E (if onA e t then Sum.inl (A.start e t) else Sum.inr (B.start e t))
    let lab := fun i => Sum.elim A.label B.label (E.symm i)
    let row := fun i e => Sum.elim (fun j => A.row j e && (!op || a.val (px e)))
      (fun j => B.row j e && (!op || !(a.val (px e)))) (E.symm i)
    let col := fun i t => Sum.elim (fun j => A.col j t && (op || !(a.val (ny t))))
      (fun j => B.col j t && (op || a.val (ny t))) (E.symm i)
    have rect : ∀ e t i, start e t=i ↔ row i e=true ∧ col i t=true := by
      intro e t i
      obtain ⟨u,rfl⟩ := E.surjective i
      cases u with
      | inl j =>
        cases op <;> cases x : a.val (px e) <;> cases y : a.val (ny t) <;>
          simp [start,onA,row,col,x,y,A.block]
      | inr j =>
        cases op <;> cases x : a.val (px e) <;> cases y : a.val (ny t) <;>
          simp [start,onA,row,col,x,y,B.block]
    refine ⟨⟨A.size+B.size,lab,start,row,col,rect⟩,by simp [Tree.leaves,sa,sb],?_⟩
    intro e t on off
    change px e (lab (start e t))=true ∧ ny t (lab (start e t))=false
    cases op <;> cases x : a.val (px e) <;> cases y : a.val (ny t) <;>
      simp_all [Tree.val,lab,start,onA]

theorem formula_lower (T : Tree)
    (yes : ∀ e : Fin 21, T.val (fun v => (raw.getD v.val 0).testBit e.val)=true)
    (no : ∀ t : Fin 37, T.val (fun v => negBit v t)=false) : 28 ≤ T.leaves := by
  obtain ⟨P,len,ok⟩ := tree_protocol T (fun e v => (raw.getD v.val 0).testBit e.val)
    (fun t v => negBit v t)
  have h := raw_partition P.label P.start P.row P.col P.block
    (fun e t => by
      have yes := (ok e t (yes e) (no t)).1
      rw [row_labels] at yes
      rcases of_decide_eq_true yes with l|r
      · exact Or.inl l.symm
      · exact Or.inr r.symm)
    (fun e t => (ok e t (yes e) (no t)).2)
  simpa [len] using h


-- The 27-step control uses the same no-duplicate and prefix legality
-- conditions as the desk. The witness includes operand indices for each gate.
def upperWords : List ℕ := [191866593364673099, 193001360500003407, 7, 264171595797922329, 288167337562522425, 56, 281826563967027394, 288230119687211490, 448, 265911111072622089, 283937879088049801, 3584, 269151924997141508, 288221854669305124, 28672, 256193051121782804, 274226965962791060, 229376, 228319279526477906, 232840552945329234, 1835008, 63, 511, 4095, 32767, 262143, 2097151]
def upperWires : List (Bool × ℕ × ℕ) := [(true, 7, 8), (true, 14, 10), (false, 0, 15), (true, 7, 9), (true, 17, 13), (false, 1, 18), (true, 8, 12), (true, 20, 13), (false, 2, 21), (true, 7, 11), (true, 23, 12), (false, 3, 24), (true, 10, 11), (true, 26, 13), (false, 4, 27), (true, 9, 10), (true, 29, 12), (false, 5, 30), (true, 8, 9), (true, 32, 11), (false, 6, 33), (true, 16, 19), (true, 35, 22), (true, 36, 25), (true, 37, 28), (true, 38, 31), (true, 39, 34)]

theorem upper_control : upperWords.length=27 ∧ upperWords.Nodup ∧
    (∀ x ∈ upperWords, x ∉ raw) ∧ 2097151 ∈ upperWords ∧
    ∀ i : Fin upperWords.length,
      let w := upperWires.getD i.val (false,0,0)
      let avail := raw ++ upperWords.take i.val
      w.2.1<avail.length ∧ w.2.2<avail.length ∧
      upperWords.get i=(if w.1 then avail.getD w.2.1 0 ||| avail.getD w.2.2 0
        else avail.getD w.2.1 0 &&& avail.getD w.2.2 0) := by decide +kernel

end HeawoodPartition
