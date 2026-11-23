import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_908_aux

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


def bare (C : AndCountCircuit n) (side : Fin C.size × Bool) :=
  if side.2 then C.rightVars side.1 else C.leftVars side.1

def liveSides (C : AndCountCircuit n) (q : Fin C.size → Bool) :
    Nat → Fin C.size → Finset (Fin C.size × Bool)
  | 0, _ => ∅
  | d+1, i => insert (i,q i) (((parents C q i).filter (· < i)).biUnion (liveSides C q d))

theorem support_sides (C : AndCountCircuit n) (q : Fin C.size → Bool)
    (d : Nat) (i : Fin C.size) (v : Fin n) :
    v ∈ support C q d i ↔ ∃ side ∈ liveSides C q d i, v ∈ bare C side := by
  induction d generalizing i with
  | zero => simp [support, liveSides]
  | succ d ih =>
    simp only [support, liveSides, Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert]
    constructor
    · rintro (here | ⟨j,hj,previous⟩)
      · exact ⟨(i,q i), Or.inl rfl, here⟩
      · obtain ⟨s,hs,hv⟩ := (ih j).mp previous
        exact ⟨s, Or.inr ⟨j,hj,hs⟩, hv⟩
    · rintro ⟨s,hs,hv⟩
      rcases hs with rfl | ⟨j,hj,prev⟩
      · exact Or.inl hv
      · exact Or.inr ⟨j,hj,(ih j).mpr ⟨s,prev,hv⟩⟩

def reached (C : AndCountCircuit n) (q : Fin C.size → Bool) :=
  C.outGates.biUnion (liveSides C q C.size)

theorem clause_sides (C : AndCountCircuit n) (q : Fin C.size → Bool) (v : Fin n) :
    v ∈ clause C q ↔ v ∈ C.outVars ∨ ∃ s ∈ reached C q, v ∈ bare C s := by
  simp only [clause, reached, Finset.mem_union, Finset.mem_biUnion, support_sides]
  grind

def choice (C : AndCountCircuit n) (c : Fin 32) (i : Fin C.size) := c.val.testBit i.val

theorem choices_surject (C : AndCountCircuit n) (bound : C.size ≤ 5) :
    Function.Surjective (choice C) := by
  intro q
  let bits (i : Nat) := if h : i < C.size then q ⟨i,h⟩ else false
  refine ⟨⟨packBits 5 bits, pack_lt 5 bits⟩, ?_⟩
  funext i
  have hi := lt_of_lt_of_le i.isLt bound
  simp [choice, pack_test, hi, bits, i.isLt]

def encSide (s : Fin k × Bool) : Nat := 2*s.1.val + s.2.toNat

theorem side_lt (bound : k ≤ 5) (s : Fin k × Bool) : encSide s < 10 := by
  obtain ⟨i,b⟩ := s
  have hi := i.isLt
  cases b <;> simp [encSide] <;> omega

theorem side_injective : Function.Injective (@encSide k) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ eq
  cases a <;> cases b <;> simp [encSide] at eq ⊢ <;> first | exact Fin.ext (by omega) | omega

def sideMask (S : Finset (Fin k × Bool)) := packBits 10 fun j => decide (j ∈ S.image encSide)

theorem side_bit (S : Finset (Fin k × Bool)) (s : Fin k × Bool) (bound : k ≤ 5) :
    (sideMask S).testBit (encSide s) = decide (s ∈ S) := by
  have eq : encSide s ∈ S.image encSide ↔ s ∈ S := by
    constructor
    · intro h
      obtain ⟨t,ht,he⟩ := Finset.mem_image.mp h
      exact side_injective he ▸ ht
    · exact Finset.mem_image_of_mem _
  simp only [sideMask, pack_test, decide_eq_true (side_lt bound s), Bool.true_and, eq]

theorem sideMask_disjoint (S T : Finset (Fin k × Bool)) (bound : k ≤ 5) :
    sideMask S &&& sideMask T = 0 ↔ ∀ s ∈ S, s ∉ T := by
  constructor
  · intro eq s hs ht
    have bit := congrArg (fun x : Nat => x.testBit (encSide s)) eq
    simp [Nat.testBit_and, side_bit _ _ bound, hs, ht] at bit
  · intro disjoint
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases pos : j ∈ S.image encSide
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp pos
      simp [Nat.testBit_and, side_bit _ _ bound, disjoint s hs]
    · have absent : (sideMask S).testBit j = false := by
        simp only [sideMask, pack_test, decide_eq_false pos, Bool.and_false]
      simp [Nat.testBit_and, absent]

def variableSides (C : AndCountCircuit n) (v : Fin n) :=
  Finset.univ.filter fun s : Fin C.size × Bool => v ∈ bare C s

theorem corner_witness (C : AndCountCircuit n) (bound : C.size ≤ 5) (I : Finset (Fin n))
    (noRaw : C.outVars = ∅) (neg : C.eval I = false)
    (positive : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∃ c : Fin 32, ∀ v, v ∈ I ↔
      sideMask (reached C (choice C c)) &&& sideMask (variableSides C v) = 0 := by
  obtain ⟨c,hc⟩ := choices_surject C bound (left C I)
  refine ⟨c, fun v => ?_⟩
  rw [hc, complement_clause C I neg positive v, clause_sides, noRaw, sideMask_disjoint _ _ bound]
  simp [variableSides]

def edgeList : List (Nat × Nat) :=
  [(0,1), (0,2), (1,3), (1,4), (2,5), (2,6), (3,5),
   (3,7), (4,6), (4,8), (5,7), (6,8), (7,8)]

abbrev graph := SimpleGraph.fromRel (fun a b : Fin 9 => (a.val,b.val) ∈ edgeList)
def negatives : List Nat := [25,28,49,73,97,98,134,145,148,193,194,262,265,268,289,290]
def rowSet (m : Nat) : Finset (Fin 9) := Finset.univ.filter fun i => m.testBit i.val

abbrev independent (I : Finset (Fin 9)) := ∀ v ∈ I, ∀ w ∈ I, ¬ graph.Adj v w
abbrev maximal (I : Finset (Fin 9)) := ∀ w : Fin 9, w ∉ I → ∃ a ∈ I, graph.Adj a w
abbrev correct (C : AndCountCircuit 9) := ∀ I, independent I → maximal I →
  C.eval I = false ∧ ∀ w, w ∉ I → C.eval (insert w I) = true

def rowCheck (I : Finset (Fin 9)) := decide (independent I) && decide (maximal I)

theorem rowCheck_spec (I : Finset (Fin 9)) : rowCheck I = true ↔ independent I ∧ maximal I := by
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq]

theorem negative_rows : ∀ m ∈ negatives, independent (rowSet m) ∧ maximal (rowSet m) := by
  have checked : negatives.all (fun m => rowCheck (rowSet m)) = true := by
    decide +kernel
  intro m hm
  exact (rowCheck_spec _).mp (List.all_eq_true.mp checked m hm)

theorem all_vertices : ∀ v : Fin 9, ∃ m ∈ negatives, v ∈ rowSet m := by decide +kernel

theorem empty_outVars (C : AndCountCircuit 9) (ok : correct C) : C.outVars = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨m,hm,member⟩ := all_vertices v
  obtain ⟨ind,maxI⟩ := negative_rows m hm
  exact avoids C _ (ok _ ind maxI).1 ⟨v, Finset.mem_union_left _ hv, member⟩

theorem required_rows (C : AndCountCircuit 9) (bound : C.size ≤ 5) (ok : correct C) :
    ∀ m ∈ negatives, ∃ c : Fin 32, ∀ v : Fin 9, m.testBit v.val = true ↔
      sideMask (reached C (choice C c)) &&& sideMask (variableSides C v) = 0 := by
  intro m hm
  obtain ⟨ind, maxI⟩ := negative_rows m hm
  obtain ⟨neg, pos⟩ := ok _ ind maxI
  obtain ⟨c,hc⟩ := corner_witness C bound _ (empty_outVars C ok) neg pos
  exact ⟨c, fun v => by simpa [rowSet] using hc v⟩

theorem live_stable (C : AndCountCircuit n) (q : Fin C.size → Bool) (a b : Nat)
    (i : Fin C.size) (ha : i.val < a) (hb : i.val < b) :
    liveSides C q a i = liveSides C q b i := by
  induction a generalizing b i with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [liveSides]
      congr 1
      apply Finset.biUnion_congr rfl
      intro j hj
      have hji : j.val < i.val := (Finset.mem_filter.mp hj).2
      exact ih b j (by omega) (by omega)

theorem live_root (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (j : Fin C.size) (hj : j.val < d) : (j,q j) ∈ liveSides C q d j := by
  cases d with
  | zero => omega
  | succ d => exact Finset.mem_insert_self _ _

theorem live_subtree (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i j : Fin C.size) (depth : i.val < d) (found : (j,q j) ∈ liveSides C q d i) :
    liveSides C q C.size j ⊆ liveSides C q d i := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    rw [liveSides, Finset.mem_insert] at found
    rcases found with eq | child
    · have same : j = i := congrArg Prod.fst eq
      subst j
      exact (live_stable C q C.size (d+1) i i.isLt depth).subset
    · obtain ⟨k,hk,prev⟩ := Finset.mem_biUnion.mp child
      have lt : k.val < i.val := (Finset.mem_filter.mp hk).2
      intro s hs
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨k,hk,ih k (by omega) prev hs⟩)

theorem live_predecessor (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i j : Fin C.size) (found : (j,q j) ∈ liveSides C q d i) :
    j = i ∨ ∃ k : Fin C.size, (k,q k) ∈ liveSides C q d i ∧
      j < k ∧ j ∈ parents C q k := by
  induction d generalizing i with
  | zero => simp [liveSides] at found
  | succ d ih =>
    rw [liveSides, Finset.mem_insert] at found
    rcases found with eq | child
    · exact Or.inl (congrArg Prod.fst eq)
    · obtain ⟨v,hv,prev⟩ := Finset.mem_biUnion.mp child
      rcases ih v prev with rfl | ⟨k,hk,lt,parent⟩
      · obtain ⟨parent,lt⟩ := Finset.mem_filter.mp hv
        exact Or.inr ⟨i, Finset.mem_insert_self _ _, lt, parent⟩
      · exact Or.inr ⟨k,Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨v,hv,hk⟩),lt,parent⟩

theorem reached_rule (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :
    (i,q i) ∈ reached C q ↔ i ∈ C.outGates ∨ ∃ j : Fin C.size,
      (j,q j) ∈ reached C q ∧ i < j ∧ i ∈ parents C q j := by
  constructor
  · intro hit
    obtain ⟨root,hr,mem⟩ := Finset.mem_biUnion.mp hit
    rcases live_predecessor C q C.size root i mem with rfl | ⟨j,hj,lt,parent⟩
    · exact Or.inl hr
    · exact Or.inr ⟨j,Finset.mem_biUnion.mpr ⟨root,hr,hj⟩,lt,parent⟩
  · rintro (out | ⟨j,seen,lt,parent⟩)
    · exact Finset.mem_biUnion.mpr ⟨i,out,live_root C q C.size i i.isLt⟩
    · obtain ⟨root,hr,mem⟩ := Finset.mem_biUnion.mp seen
      apply Finset.mem_biUnion.mpr
      refine ⟨root,hr,live_subtree C q C.size root j root.isLt mem ?_⟩
      rw [live_stable C q C.size (C.size+1) j j.isLt (by omega)]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_filter.mpr ⟨parent,lt⟩,live_root C q C.size i i.isLt⟩)

theorem reached_choice (C : AndCountCircuit n) (q : Fin C.size → Bool) (s : Fin C.size × Bool)
    (hs : s ∈ reached C q) : s.2 = q s.1 := by
  have step (d : Nat) (i : Fin C.size) (mem : s ∈ liveSides C q d i) : s.2 = q s.1 := by
    induction d generalizing i with
    | zero => simp [liveSides] at mem
    | succ d ih =>
      rcases Finset.mem_insert.mp mem with eq | child
      · rw [eq]
      · obtain ⟨k,_,found⟩ := Finset.mem_biUnion.mp child
        exact ih k found
  obtain ⟨i,_,hit⟩ := Finset.mem_biUnion.mp hs
  exact step C.size i hit

def suffix (C : AndCountCircuit n) (q : Fin C.size → Bool) (k : Nat) :=
  (reached C q).filter fun s => k ≤ s.1.val

def incoming (C : AndCountCircuit n) (i : Fin C.size) :=
  Finset.univ.filter fun s : Fin C.size × Bool =>
    i < s.1 ∧ i ∈ if s.2 then C.rightGates s.1 else C.leftGates s.1

theorem active_iff (C : AndCountCircuit n) (bound : C.size ≤ 5)
    (q : Fin C.size → Bool) (i : Fin C.size) :
    (i,q i) ∈ reached C q ↔ i ∈ C.outGates ∨
      sideMask (suffix C q (i.val+1)) &&& sideMask (incoming C i) ≠ 0 := by
  rw [reached_rule]
  apply or_congr Iff.rfl
  rw [ne_eq, sideMask_disjoint _ _ bound]
  constructor
  · rintro ⟨j,hj,lt,parent⟩ disjoint
    have hs : (j,q j) ∈ suffix C q (i.val+1) :=
      Finset.mem_filter.mpr ⟨hj, show i.val < j.val from lt⟩
    exact disjoint _ hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt,parent⟩)
  · intro h
    push Not at h
    obtain ⟨⟨j,b⟩,hs,hi⟩ := h
    have seen := (Finset.mem_filter.mp hs).1
    have eq : b = q j := reached_choice C q (j,b) seen
    subst b
    obtain ⟨lt,parent⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨j,seen,lt,parent⟩

theorem suffix_step (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :
    suffix C q i.val = if (i,q i) ∈ reached C q then insert (i,q i) (suffix C q (i.val+1))
      else suffix C q (i.val+1) := by
  ext s
  have atGate (h : s ∈ reached C q) (eq : s.1.val = i.val) : s = (i,q i) :=
    Prod.ext (Fin.ext eq) (by rw [reached_choice C q s h, Fin.ext eq])
  by_cases hit : (i,q i) ∈ reached C q
  · simp only [hit, ite_true, Finset.mem_insert, suffix, Finset.mem_filter]
    constructor
    · rintro ⟨h,le⟩
      by_cases eq : s.1.val = i.val
      · exact Or.inl (atGate h eq)
      · exact Or.inr ⟨h, by omega⟩
    · rintro (rfl | ⟨h,le⟩)
      · exact ⟨hit,le_rfl⟩
      · exact ⟨h,by omega⟩
  · simp only [hit, ite_false, suffix, Finset.mem_filter]
    constructor
    · rintro ⟨h,le⟩
      have ne : s.1.val ≠ i.val := fun eq => hit (atGate h eq ▸ h)
      exact ⟨h,by omega⟩
    · rintro ⟨h,le⟩; exact ⟨h,by omega⟩

theorem mask_empty : sideMask (∅ : Finset (Fin k × Bool)) = 0 := by
  apply Nat.eq_of_testBit_eq
  simp [sideMask, pack_test]

theorem mask_insert (S : Finset (Fin k × Bool)) (s : Fin k × Bool) (bound : k ≤ 5) :
    sideMask (insert s S) = sideMask S ||| 2^(encSide s) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases eq : j = encSide s
  · subst j
    simp [Nat.testBit_or, side_bit _ _ bound]
  · have same : j ∈ (insert s S).image encSide ↔ j ∈ S.image encSide := by
      rw [Finset.image_insert, Finset.mem_insert]
      simp [eq]
    simp only [Nat.testBit_or, Nat.testBit_two_pow, decide_eq_false (Ne.symm eq),
      Bool.or_false, sideMask, pack_test, same]

def expand (F : Finset Nat) (k control : Nat) (output : Bool) : Finset Nat :=
  F.biUnion fun r =>
    if output || decide (r &&& control ≠ 0) then {r ||| 2^(2*k), r ||| 2^(2*k+1)} else {r}

def fitsRows (F : Finset Nat) := ∃ f : Fin 9 → Nat, (∀ v, f v < 1024) ∧
  ∀ m ∈ negatives, ∃ r ∈ F, ∀ v : Fin 9, m.testBit v.val = true ↔ r &&& f v = 0

def realizable : Nat → Finset Nat → Prop
  | 0, F => fitsRows F
  | k+1, F => ∃ w < 1024, ∃ output : Bool, realizable k (expand F k w output)

theorem circuit_realizable (C : AndCountCircuit 9) (bound : C.size ≤ 5) (ok : correct C) :
    realizable 5 {0} := by
  have build (k : Nat) (F : Finset Nat)
      (includes : ∀ c : Fin 32, sideMask (suffix C (choice C c) k) ∈ F) : realizable k F := by
    induction k generalizing F with
    | zero =>
      refine ⟨fun v => sideMask (variableSides C v), fun _ => pack_lt 10 _, ?_⟩
      intro m hm
      obtain ⟨c,eq⟩ := required_rows C bound ok m hm
      refine ⟨_,?_,eq⟩
      simpa [suffix] using includes c
    | succ k ih =>
      by_cases existsGate : k < C.size
      · let i : Fin C.size := ⟨k,existsGate⟩
        let w := sideMask (incoming C i)
        let out := decide (i ∈ C.outGates)
        refine ⟨w,pack_lt 10 _,out,ih _ ?_⟩
        intro c
        let q := choice C c
        let old := sideMask (suffix C q (k+1))
        apply Finset.mem_biUnion.mpr
        refine ⟨old,includes c,?_⟩
        have step := suffix_step C q i
        change suffix C q k = _ at step
        have cond := active_iff C bound q i
        change (i,q i) ∈ reached C q ↔ i ∈ C.outGates ∨ old &&& w ≠ 0 at cond
        change sideMask (suffix C q k) ∈
          (if out || decide (old &&& w ≠ 0) then {old ||| 2^(2*k),old ||| 2^(2*k+1)} else {old})
        rw [step]
        by_cases active : (i,q i) ∈ reached C q
        · have test : (out || decide (old &&& w ≠ 0)) = true := by
            simpa [out, Bool.or_eq_true] using cond.mp active
          rw [ite_eq_left active, test, ite_eq_left rfl, mask_insert _ _ bound]
          cases q i <;> simp [encSide, i, old]
        · have test : (out || decide (old &&& w ≠ 0)) = false := by
            have neg := mt cond.mpr active
            simp_all [out]
          rw [ite_eq_right active, test, ite_eq_right (by decide : ¬ false = true)]
          exact Finset.mem_singleton_self _
      · refine ⟨0,by decide,false,ih _ ?_⟩
        intro c
        have empty (j : Nat) (hj : k ≤ j) : suffix C (choice C c) j = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro s hs
          have := (Finset.mem_filter.mp hs).2
          have := s.1.isLt
          omega
        have zero := includes c
        rw [empty (k+1) (by omega), mask_empty] at zero
        rw [empty k le_rfl, mask_empty]
        exact Finset.mem_biUnion.mpr ⟨0,zero,by simp⟩
  apply build
  intro c
  have empty : suffix C (choice C c) 5 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have five := (Finset.mem_filter.mp hs).2
    have small := s.1.isLt
    omega
  simp [empty, mask_empty]

end PEqualNP.Outside.L_meta_908_aux
