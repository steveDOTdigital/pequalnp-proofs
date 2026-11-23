import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_958_aux

open PEqualNP.AndCount AndCountCircuit

variable {n : Nat}

def left (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def right (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

private theorem side_congr {k : Nat} (I B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) {a b : Fin k → Bool} (h : ∀ j, j < i → a j = b j) :
    sideTrue I B F i a = sideTrue I B F i b := by
  unfold sideTrue
  congr 1
  apply propext
  constructor <;> rintro (raw | ⟨j, hj, lt, val⟩)
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt) ▸ val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt).symm ▸ val⟩

private theorem stable (C : AndCountCircuit n) (I : Finset (Fin n)) (m : Nat) :
    ∀ i : Fin C.size, i.val < m → ∀ a b : Nat, i.val < a → i.val < b →
    C.gateValFuel I a i = C.gateValFuel I b i := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi a b ha hb
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [gateValFuel]
        have eq (j : Fin C.size) (lt : j < i) :
            C.gateValFuel I a j = C.gateValFuel I b j :=
          ih j (by change j.val < i.val at lt; omega) a b
            (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
        rw [side_congr I _ _ i eq, side_congr I _ _ i eq]

theorem gate_eq (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal I i = (left C I i && right C I i) := by
  have h := stable C I C.size i i.isLt C.size (C.size + 1) i.isLt (by omega)
  exact h

def vars (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightVars i else C.leftVars i

def parents (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightGates i else C.leftGates i

def support (C : AndCountCircuit n) (q : Fin C.size → Bool) :
    Nat → Fin C.size → Finset (Fin n)
  | 0, _ => ∅
  | d+1, i => vars C q i ∪ ((parents C q i).filter (· < i)).biUnion (support C q d)

def hits (I S : Finset (Fin n)) := ∃ v ∈ S, v ∈ I

theorem hit_step (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i : Fin C.size) (I : Finset (Fin n)) :
    hits I (support C q (d+1) i) ↔ hits I (vars C q i) ∨
      ∃ j ∈ parents C q i, j < i ∧ hits I (support C q d j) := by
  simp only [hits, support, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv | ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩
    · exact Or.inl ⟨v, hv, hI⟩
    · exact Or.inr ⟨j, hj, lt, v, hv, hI⟩
  · rintro (⟨v, hv, hI⟩ | ⟨j, hj, lt, v, hv, hI⟩)
    · exact ⟨v, Or.inl hv, hI⟩
    · exact ⟨v, Or.inr ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩

def clause (C : AndCountCircuit n) (q : Fin C.size → Bool) :=
  C.outVars ∪ C.outGates.biUnion (support C q C.size)

theorem clause_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n)) :
    hits I (clause C q) ↔ hits I C.outVars ∨ ∃ j ∈ C.outGates, hits I (support C q C.size j) := by
  simp only [hits, clause, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv | ⟨j, hj, hv⟩, hi⟩
    · exact Or.inl ⟨v, hv, hi⟩
    · exact Or.inr ⟨j, hj, v, hv, hi⟩
  · rintro (⟨v, hv, hi⟩ | ⟨j, hj, v, hv, hi⟩)
    · exact ⟨v, Or.inl hv, hi⟩
    · exact ⟨v, Or.inr ⟨j, hj, hv⟩, hi⟩

theorem dominates (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (d : Nat) (i : Fin C.size) (hd : i.val < d) :
    C.gateVal I i = true → hits I (support C q d i) := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    rw [gate_eq, Bool.and_eq_true] at h
    apply (hit_step C q d i I).2
    have hs : sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = true := by
      cases e : q i <;> simp [vars, parents, e]
      · exact h.1
      · exact h.2
    rw [sideTrue, decide_eq_true_eq] at hs
    rcases hs with raw | ⟨j, hj, lt, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩

theorem chosen (C : AndCountCircuit n) (I : Finset (Fin n)) (d : Nat)
    (i : Fin C.size) (hd : i.val < d) :
    hits I (support C (left C I) d i) → C.gateVal I i = true := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    have hs : sideTrue I (vars C (left C I) i) (parents C (left C I) i) i (C.gateVal I) = true := by
      rw [sideTrue, decide_eq_true_eq]
      rcases (hit_step _ _ _ _ _).1 h with raw | ⟨j, hj, lt, val⟩
      · exact Or.inl raw
      · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩
    rw [gate_eq, Bool.and_eq_true]
    cases hl : left C I i with
    | false =>
      simp [vars, parents, hl] at hs
      change left C I i = true at hs
      simp [hl] at hs
    | true =>
      exact ⟨rfl, by simpa [vars, parents, hl, right] using hs⟩

theorem gives_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (h : C.eval I = true) : hits I (clause C q) := by
  rw [eval, decide_eq_true_eq] at h
  apply (clause_hit _ _ _).2
  rcases h with raw | ⟨j, hj, val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, dominates C q I C.size j j.isLt val⟩

theorem avoids (C : AndCountCircuit n) (I : Finset (Fin n)) (h : C.eval I = false) :
    ¬ hits I (clause C (left C I)) := by
  intro hit
  have ht : C.eval I = true := by
    rw [eval, decide_eq_true_eq]
    rcases (clause_hit _ _ _).1 hit with raw | ⟨j, hj, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, chosen C I C.size j j.isLt val⟩
  simp [h] at ht

theorem complement_clause (C : AndCountCircuit n) (I : Finset (Fin n))
    (h : C.eval I = false) (positive : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∀ u, u ∈ I ↔ u ∉ clause C (left C I) := by
  intro u
  constructor
  · intro hu hc
    exact avoids C I h ⟨u, hc, hu⟩
  · intro absent
    by_contra missing
    obtain ⟨v, hv, hin⟩ := gives_hit C (left C I) _ (positive u missing)
    rcases Finset.mem_insert.mp hin with rfl | inside
    · exact absent hv
    · exact avoids C I h ⟨v, hv, inside⟩

def indep (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :=
  ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b

def maximalIndep (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :=
  indep G I ∧ ∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v

theorem extend_indep (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (hU : indep G U) :
    ∃ I, U ⊆ I ∧ maximalIndep G I := by
  classical
  let sets := Finset.univ.filter fun I : Finset (Fin n) => U ⊆ I ∧ indep G I
  have hm : U ∈ sets := by simp [sets, hU]
  obtain ⟨I, hi, biggest⟩ := Finset.exists_max_image sets Finset.card ⟨U, hm⟩
  obtain ⟨sub, ind⟩ := (Finset.mem_filter.mp hi).2
  refine ⟨I, sub, ind, ?_⟩
  intro u hu
  by_contra h
  have miss : ∀ v ∈ I, ¬ G.Adj u v := by grind
  have ind' : indep G (insert u I) := by
    intro a ha b hb
    simp only [Finset.mem_insert] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · subst a; subst b; exact G.loopless.irrefl _
    · subst a; exact miss _ hb
    · subst b; exact fun e => miss _ ha e.symm
    · exact ind _ ha _ hb
  have larger : insert u I ∈ sets :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub.trans (Finset.subset_insert _ _), ind'⟩
  have := biggest _ larger
  rw [Finset.card_insert_of_notMem hu] at this
  omega

noncomputable def corners (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) :
    Finset (Fin C.size → Bool) := by
  classical
  exact (Finset.univ.filter (maximalIndep G)).image (left C)

noncomputable def profile (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (v : Fin n) :=
  (corners C G).filter fun q => v ∉ clause C q

def correctOn (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) :=
  ∀ I, maximalIndep G I → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

theorem enclosed_iff (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (U : Finset (Fin n)) :
    indep G U ↔ ∃ q ∈ corners C G, ∀ v ∈ U, q ∈ profile C G v := by
  classical
  constructor
  · intro hu
    obtain ⟨I, incl, maximal⟩ := extend_indep G U hu
    have inC : left C I ∈ corners C G :=
      Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ _, maximal⟩, rfl⟩
    refine ⟨left C I, inC, fun v hv => Finset.mem_filter.mpr ⟨inC, ?_⟩⟩
    exact (complement_clause C I (h I maximal).1 (h I maximal).2 v).mp (incl hv)
  · rintro ⟨q, hq, contains⟩
    obtain ⟨I, hi, rfl⟩ := Finset.mem_image.mp hq
    have maximal : maximalIndep G I := (Finset.mem_filter.mp hi).2
    have incl (v) (hv : v ∈ U) : v ∈ I :=
      (complement_clause C I (h I maximal).1 (h I maximal).2 v).mpr
        (Finset.mem_filter.mp (contains v hv)).2
    exact fun a ha b hb => maximal.1 a (incl a ha) b (incl b hb)

theorem profile_adj (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (a b : Fin n) : G.Adj a b ↔ Disjoint (profile C G a) (profile C G b) := by
  classical
  have e := enclosed_iff C G h {a,b}
  have eq : indep G {a,b} ↔ ¬ G.Adj a b := by
    constructor
    · exact fun t => t a (by simp) b (by simp)
    · intro t v hv w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
      · exact G.loopless.irrefl _
      · exact t
      · exact fun bad => t bad.symm
      · exact G.loopless.irrefl _
  rw [eq] at e
  constructor
  · intro adj
    rw [Finset.disjoint_left]
    intro q ha hb
    apply e.mpr _ adj
    refine ⟨q, (Finset.mem_filter.mp ha).1, ?_⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ha
    · exact hb
  · intro disj
    by_contra missing
    obtain ⟨q, _, hp⟩ := e.mp missing
    exact (Finset.disjoint_left.mp disj) (hp a (by simp)) (hp b (by simp))

theorem class_star {α : Type} [Nonempty (Fin n)] (f : Fin n → α) (G : SimpleGraph (Fin n))
    (same : ∀ a b v, f a = f b → (G.Adj a v ↔ G.Adj b v))
    (square : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (t : α) : ∃ z : Fin n, ∀ a b, f a = t → G.Adj a b → z = a ∨ z = b := by
  classical
  by_cases edge : ∃ a b, f a = t ∧ G.Adj a b
  · obtain ⟨a, b, atype, ab⟩ := edge
    by_cases second : ∃ c, f c = t ∧ c ≠ a
    · obtain ⟨c, ctype, ca⟩ := second
      refine ⟨b, ?_⟩
      intro u v ut uv
      right
      by_contra ne
      have av := (same u a v (ut.trans atype.symm)).mp uv
      have cv := (same u c v (ut.trans ctype.symm)).mp uv
      have cb := (same a c b (atype.trans ctype.symm)).mp ab
      exact square a b c v (Ne.symm ca) ne ab cb.symm cv av.symm
    · exact ⟨a, fun u _ ut _ => Or.inl (by by_contra h; exact second ⟨u, ut, Ne.symm h⟩)⟩
  · exact ⟨Classical.choice inferInstance, fun a b ha hb => False.elim (edge ⟨a,b,ha,hb⟩)⟩

theorem lift_cover {α : Type} [DecidableEq α] [Nonempty (Fin n)] (f : Fin n → α)
    (G : SimpleGraph (Fin n)) (star : ∀ t, ∃ z : Fin n, ∀ a b, f a = t → G.Adj a b → z = a ∨ z = b)
    (T : Finset α) (covers : ∀ a b, G.Adj a b → f a ∈ T ∨ f b ∈ T) :
    ∃ Q : Finset (Fin n), Q.card ≤ T.card ∧ ∀ a b, G.Adj a b → a ∈ Q ∨ b ∈ Q := by
  classical
  choose center hc using star
  refine ⟨T.image center, Finset.card_image_le, ?_⟩
  intro a b edge
  rcases covers a b edge with ha | hb
  · rcases hc (f a) a b rfl edge with e | e
    · exact Or.inl (Finset.mem_image.mpr ⟨f a, ha, e⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨f a, ha, e⟩)
  · rcases hc (f b) b a rfl edge.symm with e | e
    · exact Or.inr (Finset.mem_image.mpr ⟨f b, hb, e⟩)
    · exact Or.inl (Finset.mem_image.mpr ⟨f b, hb, e⟩)

abbrev maskCover (A T : Finset Nat) :=
  ∀ a ∈ A, ∀ b ∈ A, a &&& b = 0 → a ∈ T ∨ b ∈ T

abbrev forbidden (four : Bool) (a b c d : Nat) :=
  if four then a ≠ c ∧ b ≠ d ∧ a &&& b = 0 ∧ b &&& c = 0 ∧ c &&& d = 0 ∧ d &&& a = 0
  else a &&& b ≠ 0 ∧ b &&& c ≠ 0 ∧ c &&& a ≠ 0 ∧ a &&& b &&& c = 0

def blockSet (four : Bool) (a b c d : Nat) : Finset Nat :=
  if four then {a,b,c,d} else {a,b,c}

def admissible (X : Finset Nat) :=
  ∀ four a b c d, forbidden four a b c d → ¬ blockSet four a b c d ⊆ X

def arg (H : Array Nat) (word slot : Nat) :=
  H[(word >>> (2 + 5*slot)) % 32]?.getD 0

def leafSet (H : Array Nat) (w : Nat) : Finset Nat :=
  {arg H w 0, arg H w 1, arg H w 2}

def block (H : Array Nat) (w : Nat) :=
  blockSet (decide (w % 4 = 3)) (arg H w 0) (arg H w 1) (arg H w 2) (arg H w 3)

abbrev badWord (H : Array Nat) (w : Nat) :=
  forbidden (decide (w % 4 = 3)) (arg H w 0) (arg H w 1) (arg H w 2) (arg H w 3)

def wordAt (code : Array Nat) (pc : Nat) :=
  (code[pc / 32]?.getD 0 >>> (24 * (pc % 32))) % 16777216

def checked (H code : Array Nat) : Nat → Nat → Finset Nat → Finset Nat → Bool
  | 0, _, _, _ => false
  | fuel+1, pc, A, P =>
    let w := wordAt code pc
    let v := arg H w 0
    if w % 4 = 0 then decide (maskCover A (leafSet H w))
    else if w % 4 = 1 then
      checked H code fuel (pc+1) (A.erase v) P &&
        checked H code fuel (pc + (w >>> 7)) A (insert v P)
    else
      decide (badWord H w ∧ (block H w).erase v ⊆ P) &&
        (decide (v ∈ P) || checked H code fuel (pc+1) (A.erase v) P)

theorem checked_sound (H code : Array Nat) (fuel pc : Nat) (A P X : Finset Nat)
    (good : admissible X) (low : P ⊆ X) (high : X ⊆ A)
    (ok : checked H code fuel pc A P = true) : ∃ T : Finset Nat, T.card ≤ 3 ∧ maskCover X T := by
  induction fuel generalizing pc A P with
  | zero => simp [checked] at ok
  | succ fuel ih =>
    let w := wordAt code pc
    let v := arg H w 0
    by_cases leaf : w % 4 = 0
    · unfold w at leaf
      have test : maskCover A (leafSet H w) := by
        simpa only [checked, ite_eq_left leaf,
          decide_eq_true_eq] using ok
      refine ⟨leafSet H w, ?_, fun a ha b hb he => test a (high ha) b (high hb) he⟩
      unfold leafSet
      exact (Finset.card_insert_le _ _).trans (by
        have := Finset.card_insert_le (arg H w 1) ({arg H w 2} : Finset Nat)
        simp only [Finset.card_singleton] at this
        omega)
    · by_cases branch : w % 4 = 1
      · unfold w at leaf branch
        have both : checked H code fuel (pc+1) (A.erase v) P = true ∧
            checked H code fuel (pc + (w >>> 7)) A (insert v P) = true := by
          simpa only [checked, ite_eq_right leaf, ite_eq_left branch, Bool.and_eq_true] using ok
        by_cases hx : v ∈ X
        · exact ih _ _ _ (Finset.insert_subset hx low) high both.2
        · have hi : X ⊆ A.erase v := by
            intro x h
            exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hx h, high h⟩
          exact ih _ _ _ low hi both.1
      · unfold w at leaf branch
        have step : (badWord H w ∧ (block H w).erase v ⊆ P) ∧
            (v ∈ P ∨ checked H code fuel (pc+1) (A.erase v) P = true) := by
          simpa only [checked, ite_eq_right leaf, ite_eq_right branch, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq] using ok
        have absent : v ∉ X := by
          intro hv
          apply good _ _ _ _ _ step.1.1
          intro x hx
          by_cases eq : x = v
          · exact eq ▸ hv
          · exact low (step.1.2 (Finset.mem_erase.mpr ⟨eq, hx⟩))
        rcases step.2 with mem | nextStep
        · exact False.elim (absent (low mem))
        · have hi : X ⊆ A.erase v := by
            intro x h
            exact Finset.mem_erase.mpr ⟨by rintro rfl; exact absent h, high h⟩
          exact ih _ _ _ low hi nextStep

def packBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k+1, f => Nat.bit (f 0) (packBits k (fun j => f (j+1)))

theorem pack_test (k j : Nat) (f : Nat → Bool) :
    (packBits k f).testBit j = (decide (j < k) && f j) := by
  induction k generalizing j f with
  | zero => simp [packBits]
  | succ k ih =>
    cases j with
    | zero => simp [packBits]
    | succ j => simp [packBits, Nat.testBit_bit_succ, ih]

theorem pack_lt (k : Nat) (f : Nat → Bool) : packBits k f < 2^k := by
  induction k generalizing f with
  | zero => simp [packBits]
  | succ k ih =>
    have h := ih (fun j => f (j+1))
    cases hb : f 0 <;> simp [packBits, hb, Nat.bit, pow_succ] <;> omega

def maskOf (S : Finset (Fin 8)) :=
  packBits 8 fun j => if h : j < 8 then decide ((⟨j,h⟩ : Fin 8) ∈ S) else false

theorem mask_bit (S : Finset (Fin 8)) (i : Fin 8) :
    (maskOf S).testBit i.val = decide (i ∈ S) := by simp [maskOf, pack_test, i.isLt]

theorem mask_inter (S T : Finset (Fin 8)) :
    maskOf (S ∩ T) = maskOf S &&& maskOf T := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8 <;> simp [maskOf, pack_test, Nat.testBit_and, hi]

theorem mask_zero (S : Finset (Fin 8)) : maskOf S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have e := mask_bit S v
    simp [h, hv] at e
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8 <;> simp [maskOf, pack_test, hi]

def sideChoice (C : AndCountCircuit n) (c : Fin 8) (i : Fin C.size) := c.val.testBit i.val

theorem all_choices (C : AndCountCircuit n) (bound : C.size ≤ 3) :
    Function.Surjective (sideChoice C) := by
  intro q
  let f (i : Nat) := if h : i < C.size then q ⟨i,h⟩ else false
  refine ⟨⟨packBits 3 f, pack_lt 3 f⟩, ?_⟩
  funext i
  have hi : i.val < 3 := lt_of_lt_of_le i.isLt bound
  simp [sideChoice, pack_test, hi, f, i.isLt]

noncomputable def maskSites (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) : Finset (Fin 8) := by
  classical
  exact Finset.univ.filter fun c => sideChoice C c ∈ corners C G

noncomputable def maskProfile (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (v : Fin n) :=
  (maskSites C G).filter fun c => v ∉ clause C (sideChoice C c)

theorem mask_enclosed (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (bound : C.size ≤ 3) (U : Finset (Fin n)) :
    indep G U ↔ ∃ c : Fin 8, c ∈ maskSites C G ∧ ∀ v ∈ U, c ∈ maskProfile C G v := by
  classical
  rw [enclosed_iff C G h U]
  constructor
  · rintro ⟨q, hq, all⟩
    obtain ⟨c, rfl⟩ := all_choices C bound q
    have hc : c ∈ maskSites C G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    exact ⟨c, hc, fun v hv => Finset.mem_filter.mpr ⟨hc, (Finset.mem_filter.mp (all v hv)).2⟩⟩
  · rintro ⟨c, hc, all⟩
    have hq : sideChoice C c ∈ corners C G := (Finset.mem_filter.mp hc).2
    exact ⟨_, hq, fun v hv => Finset.mem_filter.mpr ⟨hq, (Finset.mem_filter.mp (all v hv)).2⟩⟩

theorem mask_adj (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (bound : C.size ≤ 3) (u v : Fin n) :
    G.Adj u v ↔ maskOf (maskProfile C G u) &&& maskOf (maskProfile C G v) = 0 := by
  classical
  rw [← mask_inter, mask_zero, ← Finset.disjoint_iff_inter_eq_empty, profile_adj C G h]
  rw [Finset.disjoint_left, Finset.disjoint_left]
  constructor
  · intro no c hu hv
    have corner : sideChoice C c ∈ corners C G := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    exact no (Finset.mem_filter.mpr ⟨corner, (Finset.mem_filter.mp hu).2⟩)
      (Finset.mem_filter.mpr ⟨corner, (Finset.mem_filter.mp hv).2⟩)
  · intro no q hu hv
    obtain ⟨c, rfl⟩ := all_choices C bound q
    have corner : c ∈ maskSites C G :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).1⟩
    exact no (Finset.mem_filter.mpr ⟨corner, (Finset.mem_filter.mp hu).2⟩)
      (Finset.mem_filter.mpr ⟨corner, (Finset.mem_filter.mp hv).2⟩)

theorem mask_triple (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (h : correctOn C G) (bound : C.size ≤ 3) (a b c : Fin n)
    (hab : ¬ G.Adj a b) (hbc : ¬ G.Adj b c) (hca : ¬ G.Adj c a) :
    maskOf (maskProfile C G a) &&& maskOf (maskProfile C G b) &&&
      maskOf (maskProfile C G c) ≠ 0 := by
  classical
  have independent : indep G {a,b,c} := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first | exact G.loopless.irrefl _ | assumption |
      exact fun e => hab e.symm | exact fun e => hbc e.symm | exact fun e => hca e.symm
  obtain ⟨q, _, all⟩ := (mask_enclosed C G h bound _).mp independent
  rw [← mask_inter, ← mask_inter, ne_eq, mask_zero]
  exact Finset.Nonempty.ne_empty ⟨q, Finset.mem_inter.mpr
    ⟨Finset.mem_inter.mpr ⟨all a (by simp), all b (by simp)⟩, all c (by simp)⟩⟩

theorem image_admissible (G : SimpleGraph (Fin n)) (f : Fin n → Nat)
    (pair : ∀ u v, G.Adj u v ↔ f u &&& f v = 0)
    (triple : ∀ a b c, ¬ G.Adj a b → ¬ G.Adj b c → ¬ G.Adj c a →
      f a &&& f b &&& f c ≠ 0)
    (square : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) :
    admissible (Finset.univ.image f) := by
  classical
  intro four a b c d bad sub
  have pre (x) (hx : x ∈ blockSet four a b c d) : ∃ i, f i = x := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (sub hx)
    exact ⟨i, hi⟩
  obtain ⟨u, rfl⟩ := pre a (by cases four <;> simp [blockSet])
  obtain ⟨v, rfl⟩ := pre b (by cases four <;> simp [blockSet])
  obtain ⟨w, rfl⟩ := pre c (by cases four <;> simp [blockSet])
  cases four with
  | false =>
    obtain ⟨ab, bc, ca, abc⟩ := bad
    exact triple u v w (fun e => ab ((pair _ _).mp e))
      (fun e => bc ((pair _ _).mp e)) (fun e => ca ((pair _ _).mp e)) abc
  | true =>
    obtain ⟨z, rfl⟩ := pre d (by simp [blockSet])
    obtain ⟨ac, bd, ab, bc, cd, da⟩ := bad
    exact square u v w z (fun e => ac (congrArg f e)) (fun e => bd (congrArg f e))
      ((pair _ _).mpr ab) ((pair _ _).mpr bc) ((pair _ _).mpr cd) ((pair _ _).mpr da)

theorem transfer_host [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) (f : Fin n → Nat)
    (pair : ∀ u v, G.Adj u v ↔ f u &&& f v = 0)
    (triple : ∀ a b c, ¬ G.Adj a b → ¬ G.Adj b c → ¬ G.Adj c a →
      f a &&& f b &&& f c ≠ 0)
    (square : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (T : Finset Nat) (host : ∀ X ⊆ T, admissible X → ∃ Q : Finset Nat, Q.card ≤ 3 ∧ maskCover X Q)
    (contained : ∀ v, f v ∈ T) :
    ∃ Q : Finset (Fin n), Q.card ≤ 3 ∧ ∀ a b, G.Adj a b → a ∈ Q ∨ b ∈ Q := by
  classical
  have sub : Finset.univ.image f ⊆ T := by
    rintro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact contained v
  obtain ⟨Q, card, cover⟩ := host _ sub (image_admissible G f pair triple square)
  have star := class_star f G (fun a b v e => by rw [pair, pair, e]) square
  obtain ⟨V, bound, full⟩ := lift_cover f G star Q (fun a b edge =>
    cover _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
      _ (Finset.mem_image_of_mem _ (Finset.mem_univ b)) ((pair a b).mp edge))
  exact ⟨V, bound.trans card, full⟩

def wiring (C : AndCountCircuit n) (i : Nat) (b : Bool) (j : Nat) : Bool :=
  if hi : i < C.size then
    if hj : j < C.size then decide ((⟨j,hj⟩ : Fin C.size) ∈
      if b then C.rightGates ⟨i,hi⟩ else C.leftGates ⟨i,hi⟩) else false
  else false

def outputFlag (C : AndCountCircuit n) (i : Nat) : Bool :=
  if h : i < C.size then decide ((⟨i,h⟩ : Fin C.size) ∈ C.outGates) else false

def topology (C : AndCountCircuit n) := packBits 9 fun k => match k with
  | 0 => wiring C 1 false 0
  | 1 => wiring C 1 true 0
  | 2 => wiring C 2 false 0
  | 3 => wiring C 2 false 1
  | 4 => wiring C 2 true 0
  | 5 => wiring C 2 true 1
  | k+6 => outputFlag C k

def wireSlot (i : Nat) (b : Bool) (j : Nat) :=
  if i = 1 then b.toNat else 2 + 2*b.toNat + j

theorem topology_wire (C : AndCountCircuit n) (i j : Nat) (b : Bool)
    (hi : i < 3) (hj : j < i) :
    (topology C).testBit (wireSlot i b j) = wiring C i b j := by
  unfold topology
  rw [pack_test]
  interval_cases i <;> interval_cases j <;> cases b <;> rfl

theorem topology_out (C : AndCountCircuit n) (i : Nat) (hi : i < 3) :
    (topology C).testBit (6+i) = outputFlag C i := by
  unfold topology
  rw [pack_test]
  interval_cases i <;> rfl

def rawFlag (C : AndCountCircuit n) (v : Fin n) (i : Nat) (b : Bool) : Bool :=
  if hi : i < C.size then
    decide (v ∈ if b then C.rightVars ⟨i,hi⟩ else C.leftVars ⟨i,hi⟩)
  else false

def patternOf (C : AndCountCircuit n) (v : Fin n) := packBits 6 fun k =>
  rawFlag C v (k/2) (k.testBit 0)

theorem pattern_raw (C : AndCountCircuit n) (v : Fin n) (i : Nat) (b : Bool) (hi : i < 3) :
    (patternOf C v).testBit (2*i + b.toNat) = rawFlag C v i b := by
  unfold patternOf
  rw [pack_test]
  interval_cases i <;> cases b <;> rfl

def numGate (t p c : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | d+1, i =>
    let b := c.testBit i
    p.testBit (2*i + b.toNat) || (List.range i).any fun j =>
      t.testBit (wireSlot i b j) && numGate t p c d j

theorem num_support (C : AndCountCircuit n) (bound : C.size ≤ 3) (v : Fin n) (c : Fin 8)
    (d : Nat) (i : Fin C.size) :
    numGate (topology C) (patternOf C v) c.val d i.val = true ↔
      v ∈ support C (sideChoice C c) d i := by
  induction d generalizing i with
  | zero => simp [numGate, support]
  | succ d ih =>
    have h3 := lt_of_lt_of_le i.isLt bound
    simp only [numGate, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      support, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, pattern_raw C v _ _ h3]
    apply or_congr
    · cases e : c.val.testBit i.val <;> simp [rawFlag, vars, sideChoice, i.isLt, e]
    · constructor
      · rintro ⟨j, lt, wire, pass⟩
        let k : Fin C.size := ⟨j, lt_trans lt i.isLt⟩
        rw [topology_wire _ _ _ _ h3 lt] at wire
        have mem : k ∈ parents C (sideChoice C c) i := by
          cases e : c.val.testBit i.val <;> simpa [wiring, parents, sideChoice, i.isLt, k, lt_trans lt i.isLt, e] using wire
        exact ⟨k, ⟨mem, lt⟩, (ih k).mp pass⟩
      · rintro ⟨k, ⟨mem, lt⟩, pass⟩
        refine ⟨k.val, lt, ?_, (ih k).mpr pass⟩
        rw [topology_wire _ _ _ _ h3 lt]
        cases e : c.val.testBit i.val <;> simpa [wiring, parents, sideChoice, i.isLt, k.isLt, e] using mem

theorem support_stable (C : AndCountCircuit n) (q : Fin C.size → Bool)
    (a : Nat) (i : Fin C.size) (ha : i.val < a) (b : Nat) (hb : i.val < b) :
    support C q a i = support C q b i := by
  induction a generalizing i b with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [support]
      congr 1
      apply Finset.biUnion_congr rfl
      intro j hj
      have lt : j.val < i.val := (Finset.mem_filter.mp hj).2
      exact ih j (by omega) b (by omega)

theorem no_outVar (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (v : Fin n) : v ∉ C.outVars := by
  have single : indep G {v} := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b; exact G.loopless.irrefl _
  obtain ⟨I, sub, maximal⟩ := extend_indep G {v} single
  intro member
  exact avoids C I (h I maximal).1 ⟨v, Finset.mem_union_left _ member, sub (by simp)⟩

def numOut (t p c : Nat) :=
  (List.range 3).any fun i => t.testBit (6+i) && numGate t p c 3 i

theorem num_clause (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (bound : C.size ≤ 3) (v : Fin n) (c : Fin 8) :
    numOut (topology C) (patternOf C v) c.val = true ↔ v ∈ clause C (sideChoice C c) := by
  simp only [numOut, List.any_eq_true, List.mem_range, Bool.and_eq_true, clause, Finset.mem_union,
    no_outVar C G h v, false_or, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, flag, ok⟩
    rw [topology_out C i hi] at flag
    by_cases inside : i < C.size
    · let j : Fin C.size := ⟨i, inside⟩
      refine ⟨j, by simpa [outputFlag, inside, j] using flag, ?_⟩
      rw [support_stable C _ C.size j j.isLt 3 hi]
      exact (num_support C bound v c 3 j).mp ok
    · simp [outputFlag, inside] at flag
  · rintro ⟨j, hout, hv⟩
    have hi := lt_of_lt_of_le j.isLt bound
    refine ⟨j.val, hi, ?_, (num_support C bound v c 3 j).mpr ?_⟩
    · simpa [topology_out C _ hi, outputFlag, j.isLt] using hout
    · rwa [support_stable C _ 3 j hi C.size j.isLt]

def wholeProfile (t p : Nat) := packBits 8 fun c => !numOut t p c

theorem numeric_profile (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (bound : C.size ≤ 3) (v : Fin n) :
    maskOf (maskProfile C G v) =
      maskOf (maskSites C G) &&& wholeProfile (topology C) (patternOf C v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 8
  · let c : Fin 8 := ⟨i,hi⟩
    rw [show i = c.val from rfl, mask_bit, mask_bit]
    have eq := num_clause C G h bound v c
    have small : c.val < 8 := c.isLt
    cases val : numOut (topology C) (patternOf C v) c.val <;>
      simp_all [maskProfile, wholeProfile, pack_test]
  · simp [maskOf, wholeProfile, pack_test, hi]

def oldIndex (perm j : Nat) := (perm >>> (3*j)) % 8
def relabel (perm a : Nat) := packBits 8 fun j => a.testBit (oldIndex perm j)
def permOK (perm : Nat) := ∀ i : Fin 8, ∃ j : Fin 8, oldIndex perm j.val = i.val
instance (perm : Nat) : Decidable (permOK perm) := inferInstanceAs
  (Decidable (∀ i : Fin 8, ∃ j : Fin 8, oldIndex perm j.val = i.val))

theorem relabel_inter (p a b : Nat) : relabel p (a &&& b) = relabel p a &&& relabel p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8 <;> simp [relabel, pack_test, Nat.testBit_and, hi]

theorem relabel_zero (p a : Nat) (hp : permOK p) (ha : a < 256) :
    relabel p a = 0 ↔ a = 0 := by
  constructor
  · intro eq
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · obtain ⟨j,hj⟩ := hp ⟨i,hi⟩
      have bit := congrArg (fun x : Nat => x.testBit j.val) eq
      simpa [relabel, pack_test, j.isLt, hj] using bit
    · have large : 2^8 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha large)
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    simp [relabel, pack_test]

theorem relabeled_pair (perm : Nat) (ok : permOK perm) (a b : Nat) (ha : a < 256) :
    relabel perm a &&& relabel perm b = 0 ↔ a &&& b = 0 := by
  rw [← relabel_inter]
  exact relabel_zero _ _ ok (lt_of_le_of_lt Nat.and_le_left ha)

theorem relabeled_triple (perm : Nat) (ok : permOK perm) (a b c : Nat) (ha : a < 256) :
    relabel perm a &&& relabel perm b &&& relabel perm c = 0 ↔ a &&& b &&& c = 0 := by
  rw [← relabel_inter, ← relabel_inter]
  exact relabel_zero _ _ ok (lt_of_le_of_lt (Nat.and_le_left.trans Nat.and_le_left) ha)


#print axioms numeric_profile
#print axioms transfer_host
#print axioms relabeled_triple
end PEqualNP.Outside.L_meta_958_aux
