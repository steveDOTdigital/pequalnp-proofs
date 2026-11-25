import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace FlagCrossRank

open scoped BigOperators Matrix

-- At a vertex, a cross column forces its label on every other incident edge.
-- The diagonal is zero when the central edge reports the opposite endpoint.
def crossMatrix {i : Type*} [DecidableEq i] (reported : i → Bool) : Matrix i i ℚ :=
  fun a b => 1 - (if a = b ∧ reported a = false then 1 else 0)

theorem rowSum {i : Type*} [Fintype i] [DecidableEq i] (rep : i → Bool) (x : i → ℚ) (a : i) :
    ((crossMatrix rep).mulVec x) a = (∑ b, x b) - (if rep a then 0 else x a) := by
  classical
  simp only [Matrix.mulVec, dotProduct, crossMatrix, sub_mul, one_mul, Finset.sum_sub_distrib]
  cases rep a <;> simp [ite_mul, Finset.sum_ite_eq]

theorem fullRank {i : Type*} [Fintype i] [DecidableEq i] (rep : i → Bool)
    (atMostOne : ∀ a b, rep a = true → rep b = true → a = b)
    (enough : (∃ a, rep a = true) ∨ Fintype.card i ≠ 1) :
    (crossMatrix rep).rank = Fintype.card i := by
  classical
  have zero : ∀ x : i → ℚ, (crossMatrix rep).mulVec x = 0 → x = 0 := by
    intro x hx
    let total := ∑ b, x b
    have eq (a : i) : total - (if rep a then 0 else x a) = 0 := by
      simpa only [rowSum, Pi.zero_apply, total] using congrFun hx a
    by_cases ex : ∃ j, rep j = true
    · obtain ⟨j, hj⟩ := ex
      have hz : total = 0 := by simpa [hj] using eq j
      have off (a : i) (h : a ≠ j) : x a = 0 := by
        have r : rep a = false := by
          cases h' : rep a with
          | false => rfl
          | true => exact False.elim (h (atMostOne a j h' hj))
        simpa [r,hz] using eq a
      have hj0 : x j = 0 := by
        change (∑ b, x b) = 0 at hz
        rw [Finset.sum_eq_single j (fun b _ h => off b h) (by simp)] at hz
        exact hz
      funext a
      by_cases a = j
      · subst a; exact hj0
      · exact off a (by assumption)
    · have every (a : i) : x a = total := by
        cases ha : rep a with
        | false => have h := eq a; simp [ha] at h; linarith
        | true => exact False.elim (ex ⟨a,ha⟩)
      have self : total = (Fintype.card i : ℚ) * total := by
        calc
          total = ∑ b : i, x b := rfl
          _ = ∑ _b : i, total := Finset.sum_congr rfl (fun b _ => every b)
          _ = _ := by simp [nsmul_eq_mul]
      have ne : (Fintype.card i : ℚ) ≠ 1 := by exact_mod_cast enough.resolve_left ex
      have prod : ((Fintype.card i : ℚ) - 1) * total = 0 := by linarith
      have hz := (mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr ne)
      funext a; simpa [hz] using every a
  have inj : Function.Injective (crossMatrix rep).mulVecLin := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    exact zero
  rw [Matrix.rank, LinearMap.finrank_range_of_inj inj, Module.finrank_fintype_fun_eq_card]

-- Each leaf labelled by this vertex contributes one outer product. Restrict
-- to the missing diagonal positions and at most one reported representative.
theorem localPrice {i leaf : Type*} [Fintype i] [DecidableEq i] [Fintype leaf]
    (rep : i → Bool) (R : Matrix i leaf ℚ) (C : Matrix leaf i ℚ)
    (factor : R * C = crossMatrix rep)
    (one : ∀ a b, rep a = true → rep b = true → a = b)
    (enough : (∃ a, rep a = true) ∨ Fintype.card i ≠ 1) :
    Fintype.card i ≤ Fintype.card leaf := by
  rw [← fullRank rep one enough, ← factor]
  exact (Matrix.rank_mul_le_left R C).trans R.rank_le_card_width

-- The two open neighborhoods with the opposite endpoint removed form an
-- independent input. This uses only absence of a four-cycle.
theorem crossNegative {P L : Type*} (I : P → L → Prop)
    (squareFree : ∀ p a l b, p ≠ a → l ≠ b → I p l → I p b → I a l → ¬ I a b)
    {p a : P} {l b : L} (edge : I p l) (point : I a l ∧ a ≠ p)
    (line : I p b ∧ b ≠ l) : ¬ I a b :=
  squareFree p a l b point.2.symm line.2.symm edge line.1 point.1

-- One absent endpoint per edge is charged. The opposite endpoints used on the
-- diagonal form a cover, recorded here by their image.
theorem aggregate {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (miss report : E → V) (price : V → ℕ)
    (localBound : ∀ v, Fintype.card {e // miss e = v} +
      (if v ∈ Finset.univ.image report then 1 else 0) ≤ price v) :
    Fintype.card E + (Finset.univ.image report).card ≤ ∑ v, price v := by
  classical
  have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => localBound v)
  rw [Finset.sum_add_distrib] at h
  have hm : (∑ v, Fintype.card {e // miss e = v}) = Fintype.card E := by
    rw [← Fintype.card_sigma]; exact Fintype.card_congr (Equiv.sigmaFiberEquiv miss)
  simpa [hm, Finset.sum_boole] using h

-- A rectangle partition has an exact zero-one product factorization at each label.
theorem rectangleEntry {E V T B : Type*} [Fintype B] [DecidableEq V]
    (label : B → V) (select : E → T → B) (row : B → E → Bool) (col : B → T → Bool)
    (rect : ∀ e t b, select e t = b ↔ row b e = true ∧ col b t = true)
    (v : V) (e : E) (t : T) :
    (∑ b : {b // label b = v}, (if row b.val e then (1:ℚ) else 0) *
      (if col b.val t then 1 else 0)) = (if label (select e t) = v then 1 else 0) := by
  classical
  have term (b : {b // label b = v}) (ne : select e t ≠ b.val) :
      (if row b.val e then (1:ℚ) else 0) * (if col b.val t then 1 else 0) = 0 := by
    cases hr : row b.val e <;> cases hc : col b.val t <;> simp
    exact False.elim (ne ((rect e t b.val).mpr ⟨hr,hc⟩))
  by_cases hv : label (select e t) = v
  · let w : {b // label b = v} := ⟨select e t, hv⟩
    rw [Finset.sum_eq_single w]
    · obtain ⟨r,c⟩ := (rect e t (select e t)).mp rfl
      simp [w,r,c,hv]
    · intro b _ ne
      exact term b (fun eq => ne (Subtype.ext eq.symm))
    · simp
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro b _
    exact term b (fun eq => hv ((congrArg label eq).trans b.property))

-- Keep any set of incident edges with at most one positive diagonal entry.
theorem restrictedPrice {E V T B : Type*} [DecidableEq E] [DecidableEq V] [Fintype B]
    (label : B → V) (select : E → T → B) (row : B → E → Bool) (col : B → T → Bool)
    (rect : ∀ e t b, select e t = b ↔ row b e = true ∧ col b t = true)
    (cross : E → T) (v : V) (s : Finset E)
    (off : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → label (select a (cross b)) = v)
    (one : ∀ a ∈ s, ∀ b ∈ s, label (select a (cross a)) = v →
      label (select b (cross b)) = v → a = b)
    (single : ∀ e ∈ s, ∃ t, label (select e t) = v) :
    s.card ≤ Fintype.card {b // label b = v} := by
  classical
  by_cases hs : s.card = 1
  · obtain ⟨e,he⟩ := Finset.card_eq_one.mp hs
    have mem : e ∈ s := by simp [he]
    obtain ⟨t, ht⟩ := single e mem
    have : Nonempty {b // label b = v} := ⟨⟨select e t,ht⟩⟩
    rw [hs]; exact Fintype.card_pos
  let rep (a : s) := decide (label (select a.val (cross a.val)) = v)
  let R : Matrix s {b // label b = v} ℚ := fun a b => if row b.val a.val then 1 else 0
  let C : Matrix {b // label b = v} s ℚ := fun b a => if col b.val (cross a.val) then 1 else 0
  have fac : R * C = crossMatrix rep := by
    ext a b
    rw [Matrix.mul_apply]
    change (∑ w : {w // label w = v}, (if row w.val a.val then (1:ℚ) else 0) *
      (if col w.val (cross b.val) then 1 else 0)) = _
    rw [rectangleEntry label select row col rect]
    by_cases eq : a = b
    · subst b; by_cases h : label (select a.val (cross a.val)) = v <;>
        simp [crossMatrix, rep, h]
    · have force := off a a.property b b.property (fun h => eq (Subtype.ext h))
      simp [crossMatrix, eq, force]
  have bound := localPrice rep R C fac (by
    intro a b ha hb
    exact Subtype.ext (one a a.property b b.property (of_decide_eq_true ha) (of_decide_eq_true hb)))
    (Or.inr (by simpa using hs))
  simpa using bound

theorem partitionCover {E V T B : Type*} [Fintype E] [Fintype V] [Fintype B]
    [DecidableEq E] [DecidableEq V]
    (label : B → V) (select : E → T → B) (row : B → E → Bool) (col : B → T → Bool)
    (rect : ∀ e t b, select e t = b ↔ row b e = true ∧ col b t = true)
    (cross : E → T) (miss : E → V) (report : E → V)
    (diag : ∀ e, label (select e (cross e)) = report e)
    (distinct : ∀ e, miss e ≠ report e)
    (force : ∀ a b v, a ≠ b → (miss a = v ∨ report a = v) →
      (miss b = v ∨ report b = v) → label (select a (cross b)) = v)
    (base : ∀ e v, (miss e = v ∨ report e = v) → ∃ t, label (select e t) = v) :
    Fintype.card E + (Finset.univ.image report).card ≤ Fintype.card B := by
  classical
  let price (v : V) := Fintype.card {b // label b = v}
  have cost (v : V) : Fintype.card {e // miss e = v} +
      (if v ∈ Finset.univ.image report then 1 else 0) ≤ price v := by
    let M := Finset.univ.filter fun e => miss e = v
    have card : M.card = Fintype.card {e // miss e = v} := by simp [M,Fintype.card_subtype]
    have member {e} : e ∈ M ↔ miss e = v := by simp [M]
    have use (s : Finset E) (ends : ∀ e ∈ s, miss e = v ∨ report e = v)
        (atMost : ∀ a ∈ s, ∀ b ∈ s, report a = v → report b = v → a = b) :
        s.card ≤ price v :=
      restrictedPrice label select row col rect cross v s
        (fun a ha b hb ne => force a b v ne (ends a ha) (ends b hb))
        (fun a ha b hb ar br => atMost a ha b hb ((diag a).symm.trans ar)
          ((diag b).symm.trans br))
        (fun e he => base e v (ends e he))
    by_cases hv : v ∈ Finset.univ.image report
    · obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hv
      have notM : r ∉ M := fun m => distinct r ((member.mp m).trans hr.symm)
      have unique (a : E) (h : a ∈ insert r M) (ar : report a = v) : a = r := by
        rcases Finset.mem_insert.mp h with eq | mem
        · exact eq
        · exact False.elim (distinct a ((member.mp mem).trans ar.symm))
      have h := use (insert r M) (fun a mem => by
        rcases Finset.mem_insert.mp mem with rfl | hm
        · exact Or.inr hr
        · exact Or.inl (member.mp hm))
        (fun a ha b hb ar br => (unique a ha ar).trans (unique b hb br).symm)
      simpa [hv,Finset.card_insert_of_notMem notM,card] using h
    · have h := use M (fun _ hm => Or.inl (member.mp hm))
        (fun a ha _ _ ar _ => False.elim (distinct a ((member.mp ha).trans ar.symm)))
      simpa [hv,card] using h
  have h := aggregate miss report price cost
  have sum : (∑ v, price v) = Fintype.card B := by
    rw [← Fintype.card_sigma]; exact Fintype.card_congr (Equiv.sigmaFiberEquiv label)
  simpa [sum] using h

inductive Tree (V : Type) where
  | raw (v : V)
  | gate (isOr : Bool) (a b : Tree V)

def Tree.val {V : Type} : Tree V → (V → Bool) → Bool
  | .raw v,x => x v
  | .gate op a b,x => if op then a.val x || b.val x else a.val x && b.val x

def Tree.leaves {V : Type} : Tree V → ℕ
  | .raw _ => 1
  | .gate _ a b => a.leaves+b.leaves

structure Protocol (V X Y : Type) where
  size : ℕ
  label : Fin size → V
  start : X → Y → Fin size
  row : Fin size → X → Bool
  col : Fin size → Y → Bool
  block : ∀ x y b, start x y=b ↔ row b x=true ∧ col b y=true

-- Row and column tests are independent. This construction permits two
-- disjoint occurrences of the same raw variable to carry different blocks.
theorem tree_protocol {V X Y : Type} (T : Tree V) (px : X → V → Bool) (ny : Y → V → Bool) :
    ∃ P : Protocol V X Y, P.size=T.leaves ∧
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

-- Interface to the negative tests: at the cross of f, every other row meeting
-- f at v must report v. The extra witness is only needed for singleton fibers.
theorem formulaCover {V E Y : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (T : Tree V) (left right : E → V) (sep : ∀ e, left e ≠ right e)
    (neg : Y → V → Bool) (cross : E → Y)
    (yes : ∀ e, T.val (fun v => decide (v = left e ∨ v = right e)) = true)
    (no : ∀ y, T.val (neg y) = false)
    (sides : ∀ a b v w, a ≠ b → (v = left a ∨ v = right a) →
      (v = left b ∨ v = right b) → (w = left a ∨ w = right a) → w ≠ v →
      neg (cross b) w = true)
    (single : ∀ e v, (v = left e ∨ v = right e) → ∃ y, ∀ w,
      (w = left e ∨ w = right e) → w ≠ v → neg y w = true) :
    ∃ K : Finset V, (∀ e, left e ∈ K ∨ right e ∈ K) ∧ Fintype.card E + K.card ≤ T.leaves := by
  classical
  obtain ⟨P,length,truth⟩ := tree_protocol T
    (fun e v => decide (v = left e ∨ v = right e)) neg
  let pick e y := P.label (P.start e y)
  have ends (e : E) (y : Y) : pick e y = left e ∨ pick e y = right e :=
    of_decide_eq_true (truth e y (yes e) (no y)).1
  have absent (e : E) (y : Y) : neg y (pick e y) = false :=
    (truth e y (yes e) (no y)).2
  let report e := pick e (cross e)
  let miss e := if report e = left e then right e else left e
  have both (e : E) : (miss e = right e ∧ report e = left e) ∨
      (miss e = left e ∧ report e = right e) := by
    rcases ends e (cross e) with h | h
    · left; change report e = left e at h; simp [miss,h]
    · right; change report e = right e at h; simp [miss,h,(sep e).symm]
  have atEnd (e : E) (v : V) (h : miss e = v ∨ report e = v) :
      v = left e ∨ v = right e := by
    rcases both e with h' | h' <;> rcases h with h | h <;> grind
  have bound := partitionCover P.label P.start P.row P.col P.block cross miss report
    (fun _ => rfl) (fun e => by rcases both e with h | h <;> have := sep e <;> grind)
    (by
      intro a b v ab av bv
      by_contra bad
      have on := sides a b v (pick a (cross b)) ab (atEnd a v av)
        (atEnd b v bv) (ends a (cross b)) bad
      exact Bool.noConfusion ((absent a (cross b)).symm.trans on))
    (by
      intro e v ev
      obtain ⟨y,hy⟩ := single e v (atEnd e v ev)
      refine ⟨y, ?_⟩
      by_contra bad
      exact Bool.noConfusion ((absent e y).symm.trans (hy _ (ends e y) bad)))
  refine ⟨Finset.univ.image report, ?_, ?_⟩
  · intro e
    have mem := Finset.mem_image_of_mem report (Finset.mem_univ e)
    rcases both e with h | h
    · exact Or.inl (h.2 ▸ mem)
    · exact Or.inr (h.2 ▸ mem)
  · simpa [length] using bound

abbrev Flag {P L : Type} (I : P → L → Prop) := {z : P × L // I z.1 z.2}

def edgeBits {P L : Type} [DecidableEq P] [DecidableEq L] (f : P × L) (v : P ⊕ L) :=
  decide (v = Sum.inl f.1 ∨ v = Sum.inr f.2)

def crossBits {P L : Type} [DecidableEq P] [DecidableEq L]
    (I : P → L → Prop) [DecidableRel I] (f : P × L) : P ⊕ L → Bool
  | .inl x => decide (I x f.2 ∧ x ≠ f.1)
  | .inr y => decide (I f.1 y ∧ y ≠ f.2)

-- The positive rows may be an arbitrary subset J of the actual incidences I.
-- One negative cross per retained flag plus negative singleton tests suffice.
theorem bipartiteFormula {P L : Type} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
    (I J : P → L → Prop) [DecidableRel I] [DecidableRel J] (sub : ∀ p l, J p l → I p l)
    (T : Tree (P ⊕ L)) (yes : ∀ e : Flag J, T.val (edgeBits e.val) = true)
    (noCross : ∀ e : Flag J, T.val (crossBits I e.val) = false)
    (noSingle : ∀ v : P ⊕ L, T.val (fun w => decide (w = v)) = false) :
    ∃ K : Finset (P ⊕ L), (∀ e : Flag J, Sum.inl e.val.1 ∈ K ∨ Sum.inr e.val.2 ∈ K) ∧
      Fintype.card (Flag J) + K.card ≤ T.leaves := by
  classical
  let neg : Flag J ⊕ (P ⊕ L) → (P ⊕ L) → Bool :=
    Sum.elim (fun e => crossBits I e.val) (fun v w => decide (w = v))
  apply formulaCover T (fun e : Flag J => Sum.inl e.val.1) (fun e => Sum.inr e.val.2)
    (fun _ => Sum.inl_ne_inr) neg Sum.inl yes (fun y => by
      cases y with
      | inl e => exact noCross e
      | inr v => exact noSingle v)
  · intro a b v w ne va vb wa wv
    obtain ⟨⟨p,l⟩, ae⟩ := a
    obtain ⟨⟨p',l'⟩, be⟩ := b
    have diff : p ≠ p' ∨ l ≠ l' := by
      by_contra! both
      exact ne (Subtype.ext (Prod.ext both.1 both.2))
    rcases va with rfl | rfl <;> rcases vb with eq | eq <;>
      rcases wa with rfl | rfl <;> simp_all [neg,crossBits]
    all_goals subst_vars; exact sub _ _ ae
  · intro e v ev
    rcases ev with rfl | rfl
    · refine ⟨Sum.inr (Sum.inr e.val.2), ?_⟩
      rintro w (rfl | rfl) ne <;> simp_all [neg]
    · refine ⟨Sum.inr (Sum.inl e.val.1), ?_⟩
      rintro w (rfl | rfl) ne <;> simp_all [neg]

theorem planeSquareFree {P L : Type} (I : P → L → Prop)
    (line : ∀ p a, p ≠ a → ∃! b, I p b ∧ I a b)
    (p a : P) (l b : L) (ne : p ≠ a) (diff : l ≠ b)
    (pl : I p l) (pb : I p b) (al : I a l) : ¬ I a b := by
  intro ab
  obtain ⟨only,_,unique⟩ := line p a ne
  exact diff ((unique l ⟨pl,al⟩).trans (unique b ⟨pb,ab⟩).symm)

theorem pencilDegree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (order : N = q^2 + q + 1) (hq : 2 ≤ q)
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (unique : ∀ p a, p ≠ a → ∃! l, I p l ∧ I a l) (p : Fin N) :
    (Finset.univ.filter (I p)).card = q+1 := by
  classical
  let lines := Finset.univ.filter (I p)
  let block (l : Fin N) := (Finset.univ.filter (fun a => I a l)).erase p
  have blocks : lines.biUnion block = Finset.univ.erase p := by
    ext a
    simp only [Finset.mem_biUnion,Finset.mem_erase,Finset.mem_univ,true_and,and_true,
      lines,block,Finset.mem_filter]
    constructor
    · rintro ⟨_,_,ne,_⟩; exact ne
    · intro ne
      obtain ⟨l,hl,_⟩ := unique p a ne.symm
      exact ⟨l,hl.1,ne,hl.2⟩
  have dis : (lines : Set (Fin N)).PairwiseDisjoint block := by
    intro a ha b hb ne
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    have ax := Finset.mem_erase.mp hxa
    have bx := Finset.mem_erase.mp hxb
    obtain ⟨u,_,only⟩ := unique p x ax.1.symm
    exact ne ((only a ⟨(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp ax.2).2⟩).trans
      (only b ⟨(Finset.mem_filter.mp hb).2,(Finset.mem_filter.mp bx.2).2⟩).symm)
  have size (l) (hl : l ∈ lines) : (block l).card = q := by
    have mem : p ∈ Finset.univ.filter (fun a => I a l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    dsimp only [block]
    rw [Finset.card_erase_of_mem mem,degree]; omega
  have h := congrArg Finset.card blocks
  rw [Finset.card_biUnion dis,Finset.sum_congr rfl size,
      Finset.card_erase_of_mem (Finset.mem_univ p)] at h
  simp [Finset.sum_const] at h
  change lines.card = _
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q by omega)
  rw [h,order]; simp [pow_two,Nat.add_mul]

theorem degreeCover {E V : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (K : Finset V) (fiber : V → Finset E) (d : ℕ)
    (bound : ∀ v ∈ K, (fiber v).card ≤ d)
    (covers : ∀ e, ∃ v ∈ K, e ∈ fiber v) :
    Fintype.card E ≤ K.card*d := by
  have all : K.biUnion fiber = Finset.univ := by
    ext e; simp only [Finset.mem_biUnion,Finset.mem_univ,iff_true]; exact covers e
  have h := Finset.card_biUnion_le_card_mul K fiber d bound
  simpa [all] using h

theorem planeFormula (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (order : N = q^2 + q + 1) (hq : 2 ≤ q)
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (unique : ∀ p a, p ≠ a → ∃! l, I p l ∧ I a l)
    (T : Tree (Fin N ⊕ Fin N)) (yes : ∀ e : Flag I, T.val (edgeBits e.val) = true)
    (noCross : ∀ e : Flag I, T.val (crossBits I e.val) = false)
    (noSingle : ∀ v : Fin N ⊕ Fin N, T.val (fun w => decide (w = v)) = false) :
    N*(q+2) ≤ T.leaves := by
  classical
  obtain ⟨K,cover,lower⟩ := bipartiteFormula I I (fun _ _ h => h) T yes noCross noSingle
  let fiber : (Fin N ⊕ Fin N) → Finset (Flag I) := Sum.elim
    (fun p => Finset.univ.filter (fun e => e.val.1 = p))
    (fun l => Finset.univ.filter (fun e => e.val.2 = l))
  let rightEq (l : Fin N) : {e : Flag I // e.val.2 = l} ≃ {p : Fin N // I p l} :=
    { toFun := fun e => ⟨e.1.val.1,Eq.mp (congrArg (I e.1.val.1) e.property) e.1.property⟩
      invFun := fun p => ⟨⟨(p.val,l),p.property⟩,rfl⟩
      left_inv := fun ⟨⟨⟨p,_⟩,_⟩,rfl⟩ => rfl
      right_inv := fun _ => rfl }
  have rightCard (l) : Fintype.card {e : Flag I // e.val.2 = l} = q+1 := by
    rw [Fintype.card_congr (rightEq l),Fintype.card_subtype]; exact degree l
  have leftCard (p : Fin N) : Fintype.card {e : Flag I // e.val.1 = p} = q+1 := by
    let F : {e : Flag I // e.val.1 = p} ≃ {l : Fin N // I p l} :=
      { toFun := fun e => ⟨e.1.val.2,
          Eq.mp (congrArg (fun p' => I p' e.1.val.2) e.property) e.1.property⟩
        invFun := fun l => ⟨⟨(p,l.val),l.property⟩,rfl⟩
        left_inv := fun ⟨⟨⟨_,l⟩,_⟩,rfl⟩ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr F,Fintype.card_subtype]; exact pencilDegree q N I order hq degree unique p
  have edgeCount : Fintype.card (Flag I) = N*(q+1) := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun e : Flag I => e.val.2)),
      Fintype.card_sigma]; simp [rightCard]
  have enough := degreeCover K fiber (q+1) (by
    rintro (p | l) _
    · simpa [fiber,Fintype.card_subtype] using (leftCard p).le
    · simpa [fiber,Fintype.card_subtype] using (rightCard l).le) (by
    intro e
    rcases cover e with hp | hl
    · exact ⟨_,hp,by simp [fiber]⟩
    · exact ⟨_,hl,by simp [fiber]⟩)
  rw [edgeCount] at lower enough
  have coverSize := Nat.le_of_mul_le_mul_right enough (show 0 < q+1 by omega)
  calc N*(q+2) = N*(q+1)+N := by ring
       _ ≤ _ := by omega

theorem treeMono {V : Type} (T : Tree V) (a b : V → Bool)
    (le : ∀ v, a v = true → b v = true) (on : T.val a = true) : T.val b = true := by
  induction T with
  | raw v => exact le v on
  | gate op x y hx hy =>
    cases op
    · simp [Tree.val] at on ⊢; exact ⟨hx on.1,hy on.2⟩
    · simp [Tree.val] at on ⊢; exact on.imp hx hy

theorem planeCrossOnly (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (order : N = q^2 + q + 1) (hq : 2 ≤ q)
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (unique : ∀ p a, p ≠ a → ∃! l, I p l ∧ I a l)
    (T : Tree (Fin N ⊕ Fin N)) (yes : ∀ e : Flag I, T.val (edgeBits e.val) = true)
    (noCross : ∀ e : Flag I, T.val (crossBits I e.val) = false) :
    N*(q+2) ≤ T.leaves := by
  classical
  apply planeFormula q N I order hq degree unique T yes noCross
  intro v
  have witness : ∃ e : Flag I, crossBits I e.val v = true := by
    cases v with
    | inl p =>
      obtain ⟨l,hl⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (I p)).card by
        rw [pencilDegree q N I order hq degree unique]; omega)
      obtain ⟨a,ha,ne⟩ := Finset.exists_mem_ne (s := Finset.univ.filter fun x => I x l)
        (by rw [degree]; omega) p
      exact ⟨⟨(a,l),(Finset.mem_filter.mp ha).2⟩,by
        simp [crossBits,(Finset.mem_filter.mp hl).2,ne.symm]⟩
    | inr l =>
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun a => I a l)).card by
        rw [degree]; omega)
      obtain ⟨b,hb,ne⟩ := Finset.exists_mem_ne (s := Finset.univ.filter (I p))
        (by rw [pencilDegree q N I order hq degree unique]; omega) l
      exact ⟨⟨(p,b),(Finset.mem_filter.mp hb).2⟩,by
        simp [crossBits,(Finset.mem_filter.mp hp).2,ne.symm]⟩
  obtain ⟨e,he⟩ := witness
  cases s : T.val (fun w => decide (w = v)) with
  | false => rfl
  | true =>
    have on := treeMono T (fun w => decide (w = v)) (crossBits I e.val) (by
      intro w hw; have eq : w = v := of_decide_eq_true hw; simpa [eq] using he) s
    exact Bool.noConfusion ((noCross e).symm.trans on)

end FlagCrossRank
