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

theorem circuit_realizable_at (C : AndCountCircuit 9) (bound : C.size ≤ 5) (ok : correct C)
    (count : Nat) (above : C.size ≤ count) : realizable count {0} := by
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
  have empty : suffix C (choice C c) count = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have five := (Finset.mem_filter.mp hs).2
    have small := s.1.isLt
    omega
  simp [empty, mask_empty]

theorem circuit_realizable (C : AndCountCircuit 9) (bound : C.size ≤ 5) (ok : correct C) :
    realizable 5 {0} := circuit_realizable_at C bound ok 5 bound

def rowValue (f : Fin 9 → Nat) (r : Nat) := packBits 9 fun i =>
  if hi : i < 9 then decide (r &&& f ⟨i,hi⟩ = 0) else false

theorem negative_bound : ∀ m ∈ negatives, m < 512 := by
  have all : negatives.all (fun m => decide (m < 512)) = true := by decide +kernel
  intro m hm; exact of_decide_eq_true (List.all_eq_true.mp all _ hm)

theorem rowValue_eq (f : Fin 9 → Nat) (m r : Nat) (bound : m < 512)
    (e : ∀ v : Fin 9, m.testBit v.val = true ↔ r &&& f v = 0) : rowValue f r = m := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j < 9
  · have eq := e ⟨j,h⟩
    cases b : m.testBit j <;> simp_all [rowValue, pack_test]
  · have large : 2^9 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    simp [rowValue, pack_test, h, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le bound large)]

theorem required_card (F : Finset Nat) (ok : fitsRows F) : 16 ≤ F.card := by
  obtain ⟨f,_,all⟩ := ok
  have sub : negatives.toFinset ⊆ F.image (rowValue f) := by
    intro m hm
    have mem := List.mem_toFinset.mp hm
    obtain ⟨r,hr,e⟩ := all m mem
    exact Finset.mem_image.mpr ⟨r,hr,rowValue_eq f m r (negative_bound m mem) e⟩
  have sz : negatives.toFinset.card = 16 := by decide +kernel
  exact sz ▸ (Finset.card_le_card sub).trans Finset.card_image_le

theorem expand_card (F : Finset Nat) (k w : Nat) (out : Bool) :
    (expand F k w out).card ≤ 2 * F.card := by
  unfold expand
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _r ∈ F, 2 := by
      apply Finset.sum_le_sum
      intro r hr
      split
      · exact (Finset.card_insert_le _ _).trans (by simp)
      · simp
    _ = _ := by simp [Nat.mul_comm]

theorem capacity (k : Nat) (F : Finset Nat) (ok : realizable k F) : 16 ≤ 2^k * F.card := by
  induction k generalizing F with
  | zero => simpa using required_card F ok
  | succ k ih =>
    obtain ⟨w,_,out,next⟩ := ok
    calc
      16 ≤ 2^k * (expand F k w out).card := ih _ next
      _ ≤ 2^k * (2 * F.card) := Nat.mul_le_mul_left _ (expand_card F k w out)
      _ = _ := by rw [pow_succ, Nat.mul_assoc]

theorem forced_expansion (k : Nat) (F : Finset Nat) (full : 2^(k+1) * F.card = 16)
    (ok : realizable (k+1) F) : realizable k (expand F k 0 true) := by
  obtain ⟨w,_,out,next⟩ := ok
  have cap := capacity k _ next
  have maxed : 2 * F.card ≤ (expand F k w out).card := by
    rw [← full, pow_succ, Nat.mul_assoc] at cap
    exact Nat.le_of_mul_le_mul_left cap (by positivity)
  have every (r : Nat) (hr : r ∈ F) : (out || decide (r &&& w ≠ 0)) = true := by
    by_contra miss
    have bounds : expand F k w out ⊆ insert r (expand (F.erase r) k w out) := by
      intro x hx
      obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
      by_cases eq : s = r
      · subst s
        have same : x = r := by simpa only [ite_eq_right miss, Finset.mem_singleton] using hx
        exact Finset.mem_insert.mpr (Or.inl same)
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨s,Finset.mem_erase.mpr ⟨eq,hs⟩,hx⟩)
    have one := (Finset.card_le_card bounds).trans (Finset.card_insert_le _ _)
    have two := expand_card (F.erase r) k w out
    have rm := Finset.card_erase_add_one hr
    omega
  have same : expand F k 0 true = expand F k w out := by
    unfold expand
    apply Finset.biUnion_congr rfl
    intro r hr
    simp only [every r hr, Bool.true_or]
  rwa [same]

def targetGroup (v : Fin 9) (b : Bool) := negatives.toFinset.filter fun m => m.testBit v.val = b

def cornerGroup (F : Finset Nat) (w : Nat) (b : Bool) := F.filter fun r => decide (r &&& w = 0) = b

theorem group_bound (F : Finset Nat) (f : Fin 9 → Nat)
    (all : ∀ m ∈ negatives, ∃ r ∈ F, ∀ v : Fin 9, m.testBit v.val = true ↔ r &&& f v = 0)
    (v : Fin 9) (b : Bool) : (targetGroup v b).card ≤ (cornerGroup F (f v) b).card := by
  have sub : targetGroup v b ⊆ (cornerGroup F (f v) b).image (rowValue f) := by
    intro m hm
    obtain ⟨inList,bit⟩ := Finset.mem_filter.mp hm
    have mem := List.mem_toFinset.mp inList
    obtain ⟨r,hr,e⟩ := all m mem
    refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr,?_⟩, rowValue_eq f m r (negative_bound m mem) e⟩
    have atV := e v
    cases b <;> simp_all
  exact (Finset.card_le_card sub).trans Finset.card_image_le

def first : Finset Nat := expand {0} 3 0 true
def second := expand first 2 0 true
def third := expand second 1 0 true
def fourth := expand third 0 0 true

theorem four_impossible : ¬ realizable 4 {0} := by
  intro ok
  have a : realizable 3 first := forced_expansion 3 {0} (by decide +kernel) ok
  have b : realizable 2 second := forced_expansion 2 first (by decide +kernel) a
  have c : realizable 1 third := forced_expansion 1 second (by decide +kernel) b
  have d : fitsRows fourth := forced_expansion 0 third (by decide +kernel) c
  obtain ⟨f,bounded,all⟩ := d
  have need := group_bound fourth f all 1 true
  have other := group_bound fourth f all 1 false
  have yesCount : (targetGroup 1 true).card = 5 := by decide +kernel
  have noCount : (targetGroup 1 false).card = 11 := by decide +kernel
  rw [yesCount] at need
  rw [noCount] at other
  have test : (List.range 1024).all (fun w =>
      decide (¬ (5 ≤ (cornerGroup fourth w true).card ∧ 11 ≤ (cornerGroup fourth w false).card))) = true := by
    decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp test (f 1) (List.mem_range.mpr (bounded 1)))) ⟨need,other⟩

theorem five_necessary (C : AndCountCircuit 9) (ok : correct C) : 5 ≤ C.size := by
  by_contra low
  exact four_impossible (circuit_realizable_at C (by omega) ok 4 (by omega))

def oldIndex (perm j : Nat) := (perm >>> (4*j)) % 16
def relabel (perm a : Nat) := packBits 10 fun j => a.testBit (oldIndex perm j)
abbrev permOK (perm : Nat) := ∀ i : Fin 10, ∃ j : Fin 10, oldIndex perm j.val = i.val
theorem relabel_inter (p a b : Nat) : relabel p (a &&& b) = relabel p a &&& relabel p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10 <;> simp [relabel, pack_test, Nat.testBit_and, hi]

theorem relabel_zero (p a : Nat) (hp : permOK p) (ha : a < 1024) :
    relabel p a = 0 ↔ a = 0 := by
  constructor
  · intro eq
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 10
    · obtain ⟨j,hj⟩ := hp ⟨i,hi⟩
      have bit := congrArg (fun x : Nat => x.testBit j.val) eq
      simpa [relabel, pack_test, j.isLt, hj] using bit
    · have large : 2^10 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha large)
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    simp [relabel, pack_test]

theorem relabeled_pair (perm : Nat) (ok : permOK perm) (a b : Nat) (hb : b < 1024) :
    relabel perm a &&& relabel perm b = 0 ↔ a &&& b = 0 := by
  rw [← relabel_inter]
  exact relabel_zero _ _ ok (lt_of_le_of_lt Nat.and_le_right hb)


theorem relabel_or (p a b : Nat) : relabel p (a ||| b) = relabel p a ||| relabel p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10 <;> simp [relabel, pack_test, Nat.testBit_or, hi]

abbrev fixesLow (p k : Nat) := ∀ i : Fin (2*k), relabel p (2^i.val) = 2^i.val

theorem realizable_transfer (k : Nat) (F H : Finset Nat) (p : Nat) (hp : permOK p)
    (fixes : fixesLow p k) (sub : ∀ r ∈ F, relabel p r ∈ H)
    (ok : realizable k F) : realizable k H := by
  induction k generalizing F H with
  | zero =>
    obtain ⟨f,bound,all⟩ := ok
    refine ⟨fun v => relabel p (f v),fun _ => pack_lt 10 _,?_⟩
    intro m hm
    obtain ⟨r,hr,eq⟩ := all m hm
    exact ⟨_,sub r hr,fun v => (eq v).trans (relabeled_pair p hp r (f v) (bound v)).symm⟩
  | succ k ih =>
    obtain ⟨w,hw,out,next⟩ := ok
    refine ⟨relabel p w,pack_lt 10 _,out,ih _ _ (fun i => fixes ⟨i.val,by have := i.isLt; omega⟩) ?_ next⟩
    intro x hx
    obtain ⟨r,hr,hx⟩ := Finset.mem_biUnion.mp hx
    refine Finset.mem_biUnion.mpr ⟨relabel p r,sub r hr,?_⟩
    have hit := relabeled_pair p hp r w hw
    by_cases h : (out || decide (r &&& w ≠ 0)) = true
    · have h' : (out || decide (relabel p r &&& relabel p w ≠ 0)) = true := by simpa only [ne_eq, hit] using h
      simp only [h, ite_true, Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [h', ite_true, Finset.mem_insert, Finset.mem_singleton]
      rcases hx with rfl | rfl
      · exact Or.inl ((relabel_or _ _ _).trans (congrArg _ (fixes ⟨2*k,by omega⟩)))
      · exact Or.inr ((relabel_or _ _ _).trans (congrArg _ (fixes ⟨2*k+1,by omega⟩)))
    · have h' : ¬ (out || decide (relabel p r &&& relabel p w ≠ 0)) = true := by simpa only [ne_eq, hit] using h
      rw [ite_eq_right h] at hx
      have eq := Finset.mem_singleton.mp hx
      rw [ite_eq_right h', Finset.mem_singleton, eq]


def freeBits (k : Nat) := 2*(k+1)

def domain (k : Nat) := (1023 >>> freeBits k) <<< freeBits k

theorem controls_recovered (k : Fin 5) (w : Fin 1024) :
    ((w.val >>> freeBits k.val) <<< freeBits k.val) = (w.val &&& domain k.val) ∧
    w.val >>> freeBits k.val < 2^(8-2*k.val) := by
  have yes : ∀ i : Fin 5, ∀ u : Fin 1024,
      ((u.val >>> freeBits i.val) <<< freeBits i.val) = (u.val &&& domain i.val) ∧
      u.val >>> freeBits i.val < 2^(8-2*i.val) := by decide +kernel
  exact yes k w

theorem expand_collapses (F : Finset Nat) (k w : Nat) (out : Bool)
    (stored : ∀ r ∈ F, r &&& domain k = r) :
    expand F k w out = expand F k (w &&& domain k) out := by
  apply Finset.biUnion_congr rfl
  intro r hr
  have eq : r &&& (w &&& domain k) = r &&& w := by
    rw [Nat.and_comm w, ← Nat.and_assoc, stored r hr]
  rw [eq]

def nextRows (rows : List Nat) (k j : Nat) : List Nat :=
  rows.flatMap fun r =>
    if j = 2^(8-2*k) ∨ r &&& (j <<< freeBits k) ≠ 0 then
      [r ||| 2^(2*k), r ||| 2^(2*k+1)] else [r]

theorem children_rows (rows : List Nat) (k j : Nat) (_le : j ≤ 2^(8-2*k)) :
    (nextRows rows k j).toFinset =
      expand rows.toFinset k (j <<< freeBits k) (decide (j = 2^(8-2*k))) := by
  ext x
  simp only [nextRows, List.mem_toFinset, List.mem_flatMap, expand, Finset.mem_biUnion]
  apply exists_congr
  intro r
  by_cases h : j = 2^(8-2*k) ∨ r &&& (j <<< freeBits k) ≠ 0
  · simp [h, Bool.or_eq_true, List.mem_cons, Finset.mem_insert]
  · simp [h, Bool.or_eq_true]

theorem choose_child (rows : List Nat) (k : Fin 5)
    (stored : ∀ r ∈ rows, r &&& domain k.val = r) (ok : realizable (k.val+1) rows.toFinset) :
    ∃ j ≤ 2^(8-2*k.val), realizable k.val (nextRows rows k.val j).toFinset := by
  obtain ⟨w,hw,out,good⟩ := ok
  have norm := controls_recovered k ⟨w,hw⟩
  cases out with
  | false =>
    refine ⟨_,norm.2.le,?_⟩
    rw [children_rows _ _ _ norm.2.le, norm.1]
    simpa only [decide_eq_false (Nat.ne_of_lt norm.2)] using
      expand_collapses rows.toFinset k.val w false (by simpa using stored) ▸ good
  | true =>
    refine ⟨_,Nat.le_refl _,?_⟩
    rw [children_rows _ _ _ le_rfl]
    simpa [expand] using good


def hostAt (hosts : Array (List Nat)) (j : Nat) := hosts[j]?.getD []

def entryAt (width bits : Nat) (tags : Array Nat) (j : Nat) :=
  tags[((bits >>> (width*j)) % (2^width))]?.getD 0

def transitionOK (hosts : Array (List Nat)) (rows : List Nat) (k j tag : Nat) : Bool :=
  let child := nextRows rows k j
  if tag = 0 then decide (2^k * child.length < 16) else
    let idx := tag % 512
    let p := tag >>> 9
    decide (idx < hosts.size) && decide (permOK p) && decide (fixesLow p k) &&
      child.all fun r => (hostAt hosts idx).contains (relabel p r)

theorem transition_sound (hosts : Array (List Nat)) (rows : List Nat) (k j tag : Nat)
    (checked : transitionOK hosts rows k j tag = true)
    (possible : realizable k (nextRows rows k j).toFinset) :
    ∃ i < hosts.size, realizable k (hostAt hosts i).toFinset := by
  unfold transitionOK at checked
  dsimp only at checked
  split at checked
  · have cap := capacity k _ possible
    have large := cap.trans (Nat.mul_le_mul_left (2^k) (List.toFinset_card_le (l := nextRows rows k j)))
    exact False.elim ((Nat.not_lt_of_le large) (of_decide_eq_true checked))
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
    refine ⟨_,checked.1.1.1,realizable_transfer k _ _ _ checked.1.1.2 checked.1.2 ?_ possible⟩
    intro r hr
    simpa using checked.2 r (List.mem_toFinset.mp hr)

def checkParent (hosts : Array (List Nat)) (rows : List Nat) (k width bits : Nat) (tags : Array Nat) :=
  rows.all (fun r => r &&& domain k == r) &&
    (List.range (2^(8-2*k)+1)).all (fun j => transitionOK hosts rows k j (entryAt width bits tags j))

theorem descend (hosts : Array (List Nat)) (rows : List Nat) (k : Fin 5) (width bits : Nat) (tags : Array Nat)
    (checked : checkParent hosts rows k.val width bits tags = true)
    (possible : realizable (k.val+1) rows.toFinset) : ∃ i < hosts.size, realizable k.val (hostAt hosts i).toFinset := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
  obtain ⟨j,le,good⟩ := choose_child rows k checked.1 possible
  exact transition_sound hosts rows k.val j _ (checked.2 j (List.mem_range.mpr (by omega))) good

def hosts0 : Array (List Nat) := #[[0]]

def hosts1 : Array (List Nat) := #[[0],[256,512]]

def hosts2 : Array (List Nat) := #[[256,512],[320,384,512],[320,384,576,640]]

def hosts3 : Array (List Nat) := #[[272,288,576,640],[288,336,400,576,640],[320,384,576,640],[336,352,384,512],[336,352,384,592,608,640],[336,352,400,416,512],[336,352,400,416,592,608,640],[336,352,400,416,592,608,656,672]]

def hosts4 : Array (List Nat) := #[[88,104,340,356,384,596,612,640],[104,340,344,356,384,596,600,612,640],[264,340,356,404,420,592,608,640],[276,292,328,392,592,608,656,672],[280,296,340,356,388,592,608,640],[280,296,340,356,404,420,584,596,612,648,660,676],[280,296,340,356,404,420,592,608,640],[292,328,340,392,404,592,608,656,672],[296,340,344,356,404,408,420,596,600,608,660,664,672],[324,328,388,392,592,608,656,672],[324,328,404,408,420,424,596,600,612,616,656,672],[328,340,356,392,404,420,596,600,612,616,656,672],[328,340,356,400,416,584,596,612,656,672],[328,340,356,404,408,420,424,596,600,612,616,656,672],[336,352,400,416,520,596,612,644],[336,352,400,416,520,596,612,660,676],[336,352,400,416,592,608,656,672],[340,344,352,384,596,600,608,640],[340,344,352,404,408,416,536,596,608,660,672],[340,344,352,404,408,416,544,596,600,660,664],[340,344,352,404,408,416,596,600,608,640],[340,344,352,404,408,416,596,600,608,660,664,672],[340,344,356,360,384,596,600,612,616,640],[340,344,356,360,388,392,592,608,640],[340,344,356,360,388,392,592,608,656,672],[340,344,356,360,400,416,584,596,612,640],[340,344,356,360,404,408,416,512],[340,344,356,360,404,408,416,596,600,612,616,640],[340,344,356,360,404,408,416,596,600,612,616,660,664,672],[340,344,356,360,404,408,420,424,512],[340,344,356,360,404,408,420,424,596,600,612,616,640],[340,344,356,360,404,408,420,424,596,600,612,616,660,664,672],[340,344,356,360,404,408,420,424,596,600,612,616,660,664,676,680]]

def hosts5 : Array (List Nat) := #[[26,341,342,345,352,405,406,409,416,534,597,601,608,661,665,672],[26,341,342,345,352,405,406,409,416,597,598,601,608,661,662,665,672],[74,326,341,345,357,361,404,408,416,582,597,601,613,617,660,664,672],[74,341,342,345,357,358,361,400,416,597,598,601,613,614,617,640],[85,86,89,90,101,102,105,106,386,405,409,421,425,660,664,672],[85,86,89,90,101,102,105,106,405,406,408,416,661,662,664,672],[85,86,89,90,101,102,105,106,405,406,409,410,416,661,662,665,666,672],[85,86,89,90,356,360,402,405,409,416,612,616,658,661,665,672],[85,86,89,90,356,360,405,406,409,410,416,612,616,661,662,665,666,672],[85,86,89,90,357,358,360,405,406,409,410,416,613,614,616,661,662,665,666,672],[85,86,89,90,357,358,361,362,405,406,409,410,416,613,614,617,618,661,662,665,666,672],[85,86,101,102,344,360,405,406,408,416,600,616,661,662,664,672],[85,86,344,357,358,360,405,406,408,416,600,613,614,616,661,662,664,672],[85,86,345,346,357,358,360,405,406,409,410,416,601,602,613,614,616,661,662,665,666,672],[85,89,326,330,357,361,404,408,416,582,586,613,617,660,664,672],[85,89,342,346,356,360,402,405,409,416,598,602,612,616,658,661,665,672],[85,149,282,342,345,352,406,409,416,538,598,601,608,662,665,672],[86,90,102,106,341,345,353,404,408,416,597,601,609,660,664,672],[86,90,102,106,341,345,357,361,386,405,409,421,425,597,601,613,617,642,661,665,677,681],[86,90,102,106,341,345,357,361,402,405,409,416,597,601,613,617,658,661,665,672],[86,90,102,106,341,345,357,361,404,408,416,581,585,660,664,672],[86,90,102,106,341,345,357,361,404,408,416,597,601,613,617,640],[86,90,102,106,341,345,357,361,405,406,408,416,597,601,613,617,661,662,664,672],[86,90,102,106,341,345,357,361,405,406,409,410,416,597,601,613,617,661,662,665,666,672],[86,90,150,154,341,345,356,360,405,409,416,597,601,612,616,661,665,672],[86,90,341,345,353,354,404,408,416,597,601,609,610,660,664,672],[86,90,341,345,354,357,361,386,405,409,421,425,597,601,610,613,617,642,661,665,677,681],[86,90,341,345,354,357,361,405,406,409,410,416,597,601,610,613,617,661,662,665,666,672],[86,90,341,345,356,360,402,405,409,416,597,601,612,616,658,661,665,672],[86,90,341,345,357,358,360,392,405,406,421,422,597,601,613,614,616,648,661,662,677,678],[86,90,341,345,357,358,360,405,406,409,410,416,597,601,613,614,616,661,662,665,666,672],[86,90,341,345,357,358,361,362,405,406,409,410,416,597,601,613,614,617,618,661,662,665,666,672],[86,102,150,166,280,296,341,357,405,421,584,597,613,648,661,677],[86,102,341,344,357,360,392,405,406,421,422,597,600,613,616,648,661,662,677,678],[86,102,341,344,357,360,405,406,408,416,597,600,613,616,661,662,664,672],[86,150,282,341,345,352,405,409,416,538,597,601,608,661,665,672],[86,150,341,345,346,357,358,360,405,409,410,416,597,601,602,613,614,616,661,665,666,672],[86,341,344,357,358,360,405,406,408,416,597,600,613,614,616,661,662,664,672],[86,341,345,346,357,358,360,405,406,409,410,416,597,601,602,613,614,616,661,662,665,666,672],[89,90,105,106,341,342,356,405,406,409,410,416,597,598,612,661,662,665,666,672],[89,90,105,106,341,342,357,358,404,409,410,416,597,598,613,614,660,665,666,672],[89,90,153,154,341,342,356,360,405,406,416,597,598,612,616,661,662,672],[89,90,341,342,356,360,402,405,409,416,597,598,612,616,658,661,665,672],[89,90,341,342,356,360,405,406,409,410,416,597,598,612,616,661,662,665,666,672],[89,104,278,282,341,356,405,409,416,534,538,597,612,661,665,672],[89,105,326,330,341,357,404,408,416,582,586,597,613,660,664,672],[89,105,338,341,354,357,392,404,420,594,597,610,613,648,660,676],[89,153,282,341,342,356,360,405,406,420,424,538,597,598,612,616,661,662,676,680],[89,153,294,341,342,346,357,360,405,406,410,421,424,550,597,598,602,613,616,661,662,666,677,680],[89,153,341,342,346,356,360,402,405,416,597,598,602,612,616,658,661,672],[89,326,330,341,357,361,404,408,416,582,586,597,613,617,660,664,672],[89,341,342,346,356,360,402,405,409,416,597,598,602,612,616,658,661,665,672],[90,98,341,342,345,357,361,404,408,416,597,598,601,613,617,660,664,672],[90,106,341,342,345,357,358,361,384,597,598,601,613,614,617,640],[90,106,341,342,345,357,358,361,392,405,406,421,422,597,598,601,613,614,617,648,661,662,677,678],[90,106,341,342,345,357,358,361,405,406,409,410,416,597,598,601,613,614,617,661,662,665,666,672],[90,154,294,341,342,345,357,360,405,406,409,421,424,550,597,598,601,613,616,661,662,665,677,680],[90,154,341,342,345,352,405,406,409,416,533,544,598,601,662,665],[90,154,341,342,345,352,405,406,409,416,534,544,597,601,661,665],[90,154,341,342,345,352,405,406,409,416,544,597,598,601,661,662,665],[90,154,341,342,345,356,360,405,406,409,416,597,598,601,612,616,661,662,665,672],[90,154,341,342,345,357,358,360,405,406,409,416,597,598,601,613,614,616,661,662,665,672],[90,341,342,345,353,354,404,408,416,597,598,601,609,610,660,664,672],[90,341,342,345,353,354,404,408,420,424,597,598,601,609,610,660,664,676,680],[90,341,342,345,356,360,402,405,409,416,597,598,601,612,616,658,661,665,672],[90,341,342,345,357,358,360,392,405,406,421,422,597,598,601,613,614,616,648,661,662,677,678],[90,341,342,345,357,358,360,405,406,409,410,416,597,598,601,613,614,616,661,662,665,666,672],[90,341,342,345,357,358,361,362,405,406,409,410,416,597,598,601,613,614,617,618,661,662,665,666,672],[98,105,341,342,345,346,357,404,408,416,597,598,601,602,613,660,664,672],[98,341,342,345,346,357,361,404,408,416,597,598,601,602,613,617,660,664,672],[101,102,105,106,341,342,345,346,404,408,416,597,598,601,602,660,664,672],[101,102,105,106,341,342,345,346,405,406,408,416,597,598,601,602,661,662,664,672],[101,102,341,342,344,360,405,406,408,416,597,598,600,616,661,662,664,672],[101,102,341,342,345,346,361,362,405,406,408,416,597,598,601,602,617,618,661,662,664,672],[101,105,341,342,345,346,354,404,408,416,597,598,601,602,610,660,664,672],[102,106,341,342,345,346,357,361,402,405,409,416,597,598,601,602,613,617,658,661,665,672],[102,106,341,342,345,346,357,361,405,406,408,416,597,598,601,602,613,617,661,662,664,672],[102,341,342,344,357,360,392,405,406,421,422,597,598,600,613,616,648,661,662,677,678],[102,341,342,344,357,360,405,406,408,416,597,598,600,613,616,661,662,664,672],[104,278,282,341,345,356,405,409,416,534,538,597,601,612,661,665,672],[104,341,342,345,346,356,401,402,416,597,598,601,602,612,657,658,672],[105,106,341,342,345,346,357,358,402,405,409,420,424,597,598,601,602,613,614,658,661,665,676,680],[105,326,330,341,345,357,404,408,416,582,586,597,601,613,660,664,672],[106,341,342,345,346,357,358,361,384,597,598,601,602,613,614,617,640],[106,341,342,345,346,357,358,361,405,406,409,410,416,597,598,601,602,613,614,617,661,662,665,666,672],[149,150,282,341,342,345,352,409,416,538,597,598,601,608,665,672],[149,282,341,342,345,352,406,409,416,538,597,598,601,608,662,665,672],[150,166,341,342,344,357,358,360,392,405,421,597,598,600,613,614,616,648,661,677],[150,282,341,342,345,352,405,409,416,538,597,598,601,608,661,665,672],[150,341,342,345,346,357,358,360,405,409,410,416,597,598,601,602,613,614,616,661,665,666,672],[153,154,341,342,345,346,356,360,405,406,416,597,598,601,602,612,616,661,662,672],[153,169,340,344,356,360,386,405,421,596,600,612,616,642,661,677],[153,341,342,345,346,356,360,402,405,416,597,598,601,602,612,616,658,661,672],[154,341,342,345,346,357,358,360,405,406,409,416,597,598,601,602,613,614,616,661,662,665,672],[165,330,341,342,345,357,358,361,405,406,408,422,424,586,597,598,601,613,614,617,661,662,664,678,680],[165,341,342,344,357,358,360,390,405,408,424,597,598,600,613,614,616,646,661,664,680],[166,330,341,342,345,357,358,361,405,406,408,421,424,586,597,598,601,613,614,617,661,662,664,677,680],[166,341,342,344,357,358,360,392,405,406,421,597,598,600,613,614,616,648,661,662,677],[168,341,342,345,346,353,354,404,408,420,597,598,601,602,609,610,660,664,676],[169,340,344,356,360,386,405,409,421,596,600,612,616,642,661,665,677],[266,278,294,341,345,357,361,405,409,421,425,584,596,612,656,672],[266,281,326,341,357,361,390,405,421,425,596,600,608,660,664,672],[266,297,326,341,345,357,390,405,409,421,596,600,608,660,664,672],[266,337,342,353,358,401,406,417,422,596,600,612,616,648,660,676],[266,341,342,345,357,358,361,405,406,409,421,422,425,597,598,600,613,614,616,648,661,662,677,678],[274,290,341,345,357,361,405,409,421,425,584,596,612,648,660,676],[277,278,281,282,293,294,296,597,598,601,602,608,661,662,665,666,672],[277,280,293,296,342,358,406,422,582,584,597,613,646,648,661,677],[277,281,326,330,357,361,386,421,425,596,600,612,616,660,664,672],[277,293,329,338,354,393,402,418,596,600,612,616,660,664,676,680],[277,293,330,342,345,358,361,394,406,409,422,425,597,598,600,613,614,616,661,662,664,677,678,680],[277,293,338,345,354,361,393,402,418,596,600,612,616,648,660,676],[277,293,338,345,354,361,402,409,418,425,596,600,612,616,648,660,676],[277,293,342,344,358,360,406,408,422,424,582,597,600,613,616,646,661,664,677,680],[278,280,294,296,341,357,405,421,582,584,597,613,646,648,661,677],[278,282,290,341,345,357,361,405,409,421,425,578,597,601,613,617,642,661,665,677,681],[278,282,290,341,345,357,361,405,409,421,425,582,586,597,601,613,617,642,661,665,677,681],[278,282,290,341,345,357,361,405,409,421,425,596,600,608,660,664,672],[278,282,290,341,345,357,361,405,409,421,425,596,600,612,616,640],[278,282,290,341,345,357,361,405,409,421,425,597,598,601,602,608,661,662,665,666,672],[278,282,294,296,341,345,357,405,409,421,597,598,601,602,608,661,662,665,666,672],[278,282,294,298,341,345,357,361,405,409,417,596,600,612,616,640],[278,282,294,298,341,345,357,361,405,409,421,425,596,600,612,616,640],[278,282,341,345,352,405,409,416,534,538,597,601,608,661,665,672],[278,294,330,341,345,357,361,394,405,409,421,425,594,597,601,610,613,617,658,661,665,674,677,681],[278,294,330,341,345,357,361,394,405,409,421,425,597,598,600,613,614,616,661,662,664,677,678,680],[278,294,341,344,357,360,405,408,421,424,582,597,600,613,616,646,661,664,677,680],[278,294,341,344,357,360,405,408,421,424,597,598,600,613,614,616,645,648,662,678],[278,294,341,344,357,360,405,408,421,424,597,598,600,613,614,616,646,648,661,677],[278,294,341,344,357,360,405,408,421,424,597,598,600,613,614,616,648,661,662,677,678],[280,296,341,342,357,358,405,406,421,422,581,582,584,645,646,648],[280,296,341,342,357,358,405,406,421,422,582,584,597,613,646,648,661,677],[280,296,341,342,357,358,405,406,421,422,584,597,598,613,614,648,661,662,677,678],[281,282,290,297,341,342,357,405,406,421,596,600,608,660,664,672],[281,282,296,341,342,356,405,406,420,594,597,601,608,658,661,665,672],[281,282,296,341,342,356,405,406,420,597,598,601,602,608,661,662,665,666,672],[281,282,341,342,354,357,361,405,406,418,421,425,597,598,601,602,612,616,661,662,665,666,676,680],[281,282,341,342,356,360,405,406,420,424,594,597,601,612,616,658,661,665,676,680],[281,296,341,342,346,356,405,406,410,420,594,597,601,608,658,661,665,672],[281,297,338,341,354,357,386,405,421,596,600,612,616,648,660,676],[281,297,338,341,354,357,402,405,418,421,596,600,612,616,648,660,676],[281,341,342,346,354,357,361,405,406,410,418,421,425,537,597,598,602,612,616,661,662,666,676,680],[281,341,342,346,356,360,405,406,410,420,424,537,594,597,612,616,658,661,676,680],[282,296,341,342,345,356,405,406,409,420,593,594,608,657,658,672],[282,296,341,342,345,356,405,406,409,420,594,597,601,608,658,661,665,672],[282,296,341,342,345,357,358,405,406,409,421,422,584,597,598,613,614,648,661,662,677,678],[282,296,341,342,345,357,358,405,406,409,421,422,597,598,601,602,608,661,662,665,666,672],[282,298,341,342,345,357,358,361,390,405,409,421,425,594,597,601,610,613,617,642,661,665,677,681],[282,298,341,342,345,357,358,361,405,406,409,421,422,425,586,597,598,601,613,614,617,650,661,662,665,677,678,681],[282,298,341,342,345,357,358,361,405,406,409,421,422,425,597,598,600,613,614,616,645,648,662,678],[282,298,341,342,345,357,358,361,405,406,409,421,422,425,597,598,600,613,614,616,646,648,661,677],[282,298,341,342,345,357,358,361,405,406,409,421,422,425,597,598,600,613,614,616,648,661,662,677,678],[282,341,342,345,352,405,406,409,416,538,597,598,601,608,661,662,665,672],[282,341,342,345,353,354,405,406,409,417,418,538,597,598,601,612,616,661,662,665,676,680],[282,341,342,345,354,357,361,405,406,409,418,421,425,538,597,598,601,612,616,661,662,665,676,680],[290,293,297,341,342,345,346,405,406,409,410,596,600,608,660,664,672],[290,341,342,345,346,357,361,402,405,409,421,425,582,586,597,601,613,617,642,661,665,677,681],[293,294,296,341,342,344,405,406,408,597,598,600,608,661,662,664,672],[293,294,330,341,342,345,361,394,405,406,409,425,594,597,601,610,613,617,658,661,665,674,677,681],[293,329,338,341,354,393,402,405,418,596,600,612,616,660,664,676,680],[293,330,341,342,345,358,361,394,405,406,409,422,425,597,598,600,613,614,616,661,662,664,677,678,680],[293,341,342,344,358,360,405,406,408,422,424,582,597,600,613,616,646,661,664,677,680],[294,296,341,342,344,357,405,406,408,421,584,597,598,613,614,648,661,662,677,678],[294,296,341,342,344,357,405,406,408,421,597,598,600,608,661,662,664,672],[294,330,341,342,345,357,361,394,405,406,409,421,425,594,597,601,610,613,617,658,661,665,674,677,681],[294,330,341,342,345,357,361,394,405,406,409,421,425,597,598,600,613,614,616,661,662,664,677,678,680],[294,341,342,344,357,360,405,406,408,421,424,582,597,600,613,616,646,661,664,677,680],[296,340,344,356,404,408,420,553,578,597,601,613,642,661,665,677],[296,340,344,356,404,408,420,578,597,601,613,617,642,661,665,677,681],[296,341,342,344,357,358,405,406,408,421,422,584,597,598,613,614,648,661,662,677,678],[296,341,342,344,357,358,405,406,408,421,422,597,598,600,608,661,662,664,672],[296,341,342,345,346,356,405,406,409,410,420,594,597,601,608,658,661,665,672],[296,341,342,345,346,357,358,405,406,409,410,421,422,597,598,601,602,608,661,662,665,666,672],[297,298,338,341,345,357,358,402,405,409,421,422,597,598,601,602,612,616,661,662,665,666,676,680],[297,338,341,345,354,357,402,405,409,418,421,552,597,598,601,602,612,661,662,665,666,676],[297,338,341,345,357,358,362,402,405,409,421,422,426,597,598,601,602,612,616,661,662,665,666,676,680],[298,338,341,345,357,358,361,402,405,409,421,422,425,597,598,601,602,612,616,661,662,665,666,676,680],[298,341,342,345,346,357,358,361,405,406,409,410,421,422,425,597,598,601,602,613,614,616,661,662,665,666,677,678,680],[322,341,345,357,361,404,408,416,578,597,601,613,617,660,664,672],[322,341,345,357,361,405,406,409,410,418,421,425,597,598,601,602,610,613,617,660,664,672],[325,326,328,405,406,408,421,422,424,597,598,600,613,614,616,656,672],[325,326,328,405,406,409,410,421,422,424,597,598,601,602,613,614,616,657,658,672],[325,326,329,330,401,402,417,418,596,600,612,616,660,664,676,680],[325,326,329,330,401,402,421,422,425,426,597,598,601,602,612,616,657,658,676,680],[325,326,345,346,360,405,406,409,410,421,422,424,597,598,601,602,613,614,616,657,658,672],[325,329,338,354,389,393,402,418,596,600,612,616,660,664,676,680],[325,329,338,354,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,676,680],[326,328,341,357,390,392,405,421,597,598,600,613,614,616,656,672],[326,328,341,357,405,406,408,421,422,424,597,598,600,613,614,616,656,672],[326,330,341,345,353,404,408,416,582,586,597,601,609,660,664,672],[326,330,341,345,357,361,386,405,409,417,596,600,612,616,660,664,672],[326,330,341,345,357,361,386,405,409,421,425,596,600,612,616,660,664,672],[326,330,341,345,357,361,386,405,409,421,425,597,598,601,602,613,614,617,618,660,664,672],[326,330,341,345,357,361,390,394,405,409,421,425,546,553,594,597,601,613,658,661,665,677],[326,330,341,345,357,361,390,394,405,409,421,425,546,594,597,601,613,617,658,661,665,677,681],[326,330,341,345,357,361,390,394,405,409,421,425,553,594,597,601,610,613,658,661,665,674,677],[326,330,341,345,357,361,390,394,405,409,421,425,594,597,601,610,613,617,658,661,665,674,677,681],[326,330,341,345,357,361,401,402,417,418,582,586,597,601,613,617,660,664,676,680],[326,330,341,345,357,361,401,402,417,418,596,600,612,616,660,664,676,680],[326,330,341,345,357,361,402,405,409,418,421,425,514,597,601,613,617,661,665,677,681],[326,330,341,345,357,361,404,408,416,582,586,597,601,613,617,660,664,672],[326,330,341,345,357,361,404,408,420,424,597,598,601,602,609,610,660,664,672],[326,330,341,345,357,361,405,406,409,410,417,418,597,598,601,602,613,614,617,618,660,664,672],[326,330,341,345,357,361,405,406,409,410,417,422,426,597,598,601,602,613,614,617,618,660,664,672],[326,330,341,345,357,361,405,406,409,410,418,421,425,597,598,601,602,613,614,617,618,660,664,672],[326,330,341,345,357,361,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,658,661,665,674,677,681],[326,330,341,345,357,361,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,672],[326,341,344,357,360,405,406,408,421,422,424,582,597,601,602,613,617,618,657,658,673,674],[328,341,342,357,358,392,405,406,421,422,597,598,600,613,614,616,656,672],[328,341,342,357,358,405,406,408,421,422,424,597,598,600,613,614,616,656,672],[329,330,341,342,357,358,393,394,405,406,421,422,534,550,597,600,613,616,661,664,677,680],[329,330,341,342,357,358,393,394,405,406,421,422,594,597,601,610,613,617,660,664,676,680],[329,330,341,342,357,358,401,402,417,418,596,600,612,616,660,664,676,680],[329,338,341,354,357,393,405,406,410,421,422,426,597,598,601,602,613,614,617,618,660,664,676,680],[329,338,341,354,357,404,408,420,424,585,594,597,610,613,660,664,676,680],[329,338,341,354,357,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,676,680],[330,341,342,345,357,358,361,394,405,406,409,421,422,425,597,598,601,602,613,614,617,618,661,662,664,677,678,680],[330,341,342,345,357,358,361,405,406,408,421,422,424,520,597,598,613,614,661,662,677,678],[330,341,342,345,357,358,361,405,406,408,421,422,424,586,597,598,601,613,614,617,661,662,664,677,678,680],[330,341,342,345,357,358,361,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,664,677,678,680],[337,338,353,354,390,394,405,409,421,425,597,598,600,613,614,616,646,648,661,677],[337,338,353,354,394,405,406,409,421,422,425,597,598,601,602,613,614,617,618,648,660,676],[337,338,353,354,401,402,417,418,596,600,612,616,660,664,676,680],[337,338,353,354,404,408,420,424,585,586,597,598,613,614,648,660,676],[337,338,353,354,404,408,420,424,586,597,598,601,613,614,617,648,660,676],[337,338,353,354,405,406,409,410,420,424,597,598,601,602,613,614,617,618,648,661,662,676],[337,338,353,354,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,648,660,676],[337,338,353,354,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,676,680],[337,338,356,360,401,402,420,424,552,597,598,601,602,612,661,662,665,666,676],[337,338,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,676,680],[338,341,345,354,357,361,389,393,402,418,596,600,612,616,660,664,676,680],[338,341,345,354,357,361,389,393,406,410,422,426,594,597,601,610,613,617,660,664,676,680],[338,341,345,354,357,361,390,394,405,409,421,425,594,597,601,610,613,617,660,664,676,680],[338,341,345,354,357,361,393,394,405,406,421,422,594,597,601,610,613,617,648,660,676],[338,341,345,354,357,361,393,394,405,406,421,422,594,597,601,610,613,617,660,664,676,680],[338,341,345,354,357,361,402,405,409,418,421,425,522,597,598,601,613,614,617,646,661,665,677,681],[338,341,345,354,357,361,402,405,409,418,421,425,537,597,598,602,612,616,661,662,666,676,680],[338,341,345,354,357,361,402,405,409,418,421,425,538,597,598,601,612,616,661,662,665,676,680],[338,341,345,354,357,361,402,405,409,418,421,425,552,597,598,601,602,612,661,662,665,666,676],[338,341,345,354,357,361,402,405,409,418,421,425,585,597,598,602,613,614,618,648,660,676],[338,341,345,354,357,361,402,405,409,418,421,425,586,597,598,601,613,614,617,648,660,676],[338,341,345,354,357,361,402,405,409,418,421,425,597,598,601,602,612,616,661,662,665,666,676,680],[338,341,345,354,357,361,404,408,420,424,585,594,597,610,613,648,660,676],[338,341,345,354,357,361,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,676,680],[338,341,345,356,360,402,405,409,420,424,537,594,597,612,616,658,661,676,680],[338,341,345,356,360,402,405,409,420,424,552,594,597,601,612,658,661,665,676],[338,341,345,356,360,402,405,409,420,424,594,597,601,612,616,640],[338,341,345,356,360,402,405,409,420,424,594,597,601,612,616,658,661,665,676,680],[338,341,345,356,360,402,405,409,420,424,594,597,601,613,614,617,618,642,645,649],[338,341,345,357,358,361,362,405,406,409,410,420,424,594,597,601,613,614,617,618,661,662,665,666,676,680],[338,341,345,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,676,680],[340,344,356,360,386,405,409,417,596,600,612,616,642,661,665,673],[340,344,356,360,386,405,409,421,425,596,600,612,616,642,661,665,677,681],[340,344,356,360,390,394,405,409,421,425,594,597,601,610,613,617,642,661,665,677,681],[340,344,356,360,390,394,405,409,421,425,597,598,601,602,613,614,617,618,642,657,673],[340,344,356,360,402,405,409,418,421,425,586,597,598,601,613,614,617,642,661,665,677,681],[340,344,356,360,402,405,409,418,421,425,597,598,601,602,613,614,617,618,642,649,661,677],[340,344,356,360,402,405,409,418,421,425,597,598,601,602,613,614,617,618,642,661,665,677,681],[340,344,356,360,404,408,416,514,597,601,613,617,661,665,677,681],[340,344,356,360,404,408,420,424,514,597,601,613,617,661,665,673],[340,344,356,360,404,408,420,424,514,597,601,613,617,661,665,677,681],[340,344,356,360,404,408,420,424,522,593,598,609,614,646,657,673],[340,344,356,360,404,408,420,424,522,593,598,609,614,657,662,673,678],[340,344,356,360,404,408,420,424,537,553,594,597,610,613,642,645],[340,344,356,360,404,408,420,424,537,553,594,597,610,613,642,661,677],[340,344,356,360,404,408,420,424,546,597,598,601,602,609,661,662,665,666,673],[340,344,356,360,404,408,420,424,582,586,597,601,613,617,642,657,673],[340,344,356,360,404,408,420,424,586,597,598,601,613,614,617,642,657,673],[340,344,356,360,404,408,420,424,594,597,601,610,613,617,642,649,661,677],[340,344,356,360,404,408,420,424,594,597,601,610,613,617,642,661,665,677,681],[340,344,356,360,404,408,420,424,596,600,612,616,660,664,676,680],[340,344,356,360,404,408,420,424,597,598,601,602,609,610,642,661,665,673],[340,344,356,360,404,408,420,424,597,598,601,602,610,613,617,642,661,665,677,681],[340,344,356,360,404,408,420,424,597,598,601,602,613,614,617,618,642,661,665,673],[340,344,356,360,404,408,420,424,597,598,601,602,613,614,617,618,642,661,665,677,681],[340,344,356,360,405,406,409,410,418,421,425,597,598,601,602,613,614,617,618,642,661,665,677,681],[340,344,356,360,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,642,661,665,673],[340,344,356,360,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,642,661,665,677,681],[341,342,344,352,405,406,408,416,597,598,600,608,661,662,664,672],[341,342,344,352,405,406,408,421,422,424,597,598,600,613,614,616,645,646,648],[341,342,344,357,358,360,389,390,392,597,598,600,608,661,662,664,672],[341,342,344,357,358,360,389,390,408,424,597,598,600,613,614,616,640],[341,342,344,357,358,360,390,392,405,421,597,598,600,613,614,616,640],[341,342,344,357,358,360,390,405,408,421,424,597,598,600,613,614,616,640],[341,342,344,357,358,360,390,405,408,421,424,597,598,600,613,614,616,646,661,664,677,680],[341,342,344,357,358,360,392,405,406,421,422,520,597,598,613,614,661,662,677,678],[341,342,344,357,358,360,392,405,406,421,422,534,550,597,600,613,616,648,661,677],[341,342,344,357,358,360,392,405,406,421,422,597,598,600,613,614,616,640],[341,342,344,357,358,360,392,405,406,421,422,597,598,600,613,614,616,648,661,662,677,678],[341,342,344,357,358,360,405,406,408,416,597,598,600,613,614,616,640],[341,342,344,357,358,360,405,406,408,416,597,598,600,613,614,616,645,646,648],[341,342,344,357,358,360,405,406,408,416,597,598,600,613,614,616,661,662,664,672],[341,342,344,357,358,360,405,406,408,421,422,424,520,597,598,613,614,646,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,520,597,598,613,614,661,662,677,678],[341,342,344,357,358,360,405,406,408,421,422,424,522,534,550,585,597,613,649,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,522,597,598,601,613,614,617,646,661,665,677,681],[341,342,344,357,358,360,405,406,408,421,422,424,522,597,598,601,613,614,617,661,662,665,677,678,681],[341,342,344,357,358,360,405,406,408,421,422,424,534,550,585,586,597,613,649,650,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,534,550,597,600,613,616,645,648],[341,342,344,357,358,360,405,406,408,421,422,424,534,550,597,600,613,616,648,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,537,553,582,586,597,613,646,650,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,640],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,645,646,648],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,645,646,664,680],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,646,648,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,646,661,664,677,680],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,648,661,662,677,678],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,661,662,664,672],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,661,662,664,677,678,680],[341,342,345,346,352,405,406,409,410,416,533,534,537,538,608,672],[341,342,345,346,352,405,406,409,410,416,534,538,544,597,601,661,665],[341,342,345,346,352,405,406,409,410,416,534,538,597,601,608,661,665,672],[341,342,345,346,352,405,406,409,410,416,538,544,597,598,601,661,662,665],[341,342,345,346,352,405,406,409,410,416,538,597,598,601,608,661,662,665,672],[341,342,345,346,352,405,406,409,410,416,544,597,598,601,602,661,662,665,666],[341,342,345,346,352,405,406,409,410,416,597,598,601,602,608,640],[341,342,345,346,352,405,406,409,410,416,597,598,601,602,608,661,662,665,666,672],[341,342,345,346,353,354,404,408,416,597,598,601,602,609,610,660,664,672],[341,342,345,346,353,354,404,408,420,424,597,598,601,602,609,610,660,664,676,680],[341,342,345,346,353,354,405,406,409,410,417,418,534,550,597,600,613,616,661,664,677,680],[341,342,345,346,353,354,405,406,409,410,417,418,597,598,601,602,613,614,617,618,660,664,676,680],[341,342,345,346,353,354,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,676,680],[341,342,345,346,353,358,362,404,408,416,582,586,597,601,609,640],[341,342,345,346,353,358,362,404,408,416,582,586,597,601,609,660,664,672],[341,342,345,346,354,357,361,386,389,393,596,600,608,660,664,672],[341,342,345,346,354,357,361,386,405,409,421,425,597,598,601,602,610,613,617,660,664,672],[341,342,345,346,354,357,361,404,408,416,578,597,601,613,617,640],[341,342,345,346,354,357,361,404,408,416,578,597,601,613,617,642,661,665,677,681],[341,342,345,346,354,357,361,404,408,416,578,597,601,613,617,660,664,672],[341,342,345,346,354,357,361,404,408,416,597,598,601,602,610,613,617,640],[341,342,345,346,354,357,361,404,408,418,421,425,597,598,601,602,610,613,617,640],[341,342,345,346,354,357,361,405,406,409,410,418,421,425,597,598,601,602,610,613,617,660,664,672],[341,342,345,346,354,357,361,405,406,409,410,418,421,425,597,598,601,602,610,613,617,660,664,674,677,681],[341,342,345,346,356,360,401,402,416,584,597,598,612,657,658,672],[341,342,345,346,356,360,401,402,416,597,598,601,602,612,616,640],[341,342,345,346,356,360,402,405,409,416,597,598,601,602,612,616,658,661,665,672],[341,342,345,346,356,360,405,406,409,410,420,424,537,594,597,610,613,617,658,661,674,677,681],[341,342,345,346,356,360,405,406,409,410,420,424,544,594,597,601,658,661,665],[341,342,345,346,356,360,405,406,409,410,420,424,546,553,594,597,601,613,658,661,665,677],[341,342,345,346,356,360,405,406,409,410,420,424,546,594,597,601,613,617,658,661,665,677,681],[341,342,345,346,356,360,405,406,409,410,420,424,553,594,597,601,610,613,658,661,665,674,677],[341,342,345,346,357,358,360,384,597,598,601,602,613,614,616,640],[341,342,345,346,357,358,360,389,390,392,597,598,601,602,613,614,616,657,658,672],[341,342,345,346,357,358,360,389,390,409,410,424,597,598,601,602,613,614,616,657,658,672],[341,342,345,346,357,358,360,405,406,409,410,416,544,597,598,601,602,661,662,665,666],[341,342,345,346,357,358,360,405,406,409,410,416,597,598,601,602,613,614,616,640],[341,342,345,346,357,358,360,405,406,409,410,416,597,598,601,602,613,614,616,661,662,665,666,672],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,534,597,601,602,613,614,616,661,665,666,677,678,680],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,538,597,598,601,613,614,616,661,662,665,677,678,680],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,544,597,598,601,602,661,662,665,666],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,552,597,598,601,602,613,614,661,662,665,666,677,678],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,597,598,601,602,613,614,616,640],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,597,598,601,602,613,614,616,661,662,665,666,672],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,597,598,601,602,613,614,616,661,662,665,666,677,678,680],[341,342,345,346,357,358,361,362,384,597,598,601,602,613,614,617,618,640],[341,342,345,346,357,358,361,362,386,389,393,596,600,612,616,660,664,672],[341,342,345,346,357,358,361,362,386,405,409,417,596,600,612,616,640],[341,342,345,346,357,358,361,362,386,405,409,417,596,600,612,616,660,664,672],[341,342,345,346,357,358,361,362,386,405,409,421,425,596,600,612,616,640],[341,342,345,346,357,358,361,362,386,405,409,421,425,596,600,612,616,642,661,665,677,681],[341,342,345,346,357,358,361,362,386,405,409,421,425,596,600,612,616,660,664,672],[341,342,345,346,357,358,361,362,389,390,393,394,593,594,609,610,660,664,676,680],[341,342,345,346,357,358,361,362,389,390,393,394,593,594,612,616,657,658,676,680],[341,342,345,346,357,358,361,362,389,393,402,418,596,600,612,616,640],[341,342,345,346,357,358,361,362,389,393,402,418,596,600,612,616,658,661,665,674,677,681],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,594,597,601,610,613,617,640],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,594,597,601,610,613,617,642,661,665,677,681],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,594,597,601,610,613,617,658,661,665,674,677,681],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,597,598,600,613,614,616,661,662,664,677,678,680],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,597,598,601,602,609,610,660,664,672],[341,342,345,346,357,358,361,362,392,404,420,593,594,609,610,640],[341,342,345,346,357,358,361,362,401,402,417,418,596,600,612,616,640],[341,342,345,346,357,358,361,362,401,402,417,418,596,600,612,616,646,650,661,665,677,681],[341,342,345,346,357,358,361,362,401,402,417,418,596,600,612,616,650,661,662,665,677,678,681],[341,342,345,346,357,358,361,362,401,402,417,418,597,598,601,602,612,616,648,661,662,676],[341,342,345,346,357,358,361,362,401,402,421,422,425,426,597,598,601,602,612,616,640],[341,342,345,346,357,358,361,362,402,405,409,418,421,425,597,598,601,602,612,616,640],[341,342,345,346,357,358,361,362,404,408,416,581,582,585,586,660,664,672],[341,342,345,346,357,358,361,362,404,408,416,582,586,597,601,613,617,640],[341,342,345,346,357,358,361,362,404,408,416,582,586,597,601,613,617,642,661,665,673],[341,342,345,346,357,358,361,362,404,408,420,424,585,594,597,610,613,640],[341,342,345,346,357,358,361,362,404,408,420,424,597,598,601,602,609,610,640],[341,342,345,346,357,358,361,362,405,406,408,416,581,582,585,586,661,662,664,672],[341,342,345,346,357,358,361,362,405,406,408,421,422,424,586,597,598,601,613,614,617,640],[341,342,345,346,357,358,361,362,405,406,408,421,422,424,586,597,598,601,613,614,617,648,661,662,677,678],[341,342,345,346,357,358,361,362,405,406,409,410,416,597,598,601,602,613,614,617,618,640],[341,342,345,346,357,358,361,362,405,406,409,410,416,597,598,601,602,613,614,617,618,661,662,665,666,672],[341,342,345,346,357,358,361,362,405,406,409,410,420,424,594,597,601,613,614,617,618,640],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,424,512],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,424,597,598,601,602,613,614,617,618,640],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,424,597,598,601,602,613,614,617,618,661,662,665,666,672],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,424,597,598,601,602,613,614,617,618,661,662,665,666,677,678,680],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,512],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,640],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,672],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,677,678,680],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,677,678,681,682]]

def tags0_0 : Array Nat := #[0x130eca8642000,0x130eca8642001]

theorem move0_0 (h : realizable 5 (hostAt hosts0 0).toFinset) :
    ∃ i < hosts1.size, realizable 4 (hostAt hosts1 i).toFinset :=
  descend hosts1 (hostAt hosts0 0) ⟨4,by decide⟩ 1 0x2 tags0_0 (by decide +kernel) h

theorem layer0 (h : ∃ i < hosts0.size, realizable 5 (hostAt hosts0 i).toFinset) :
    ∃ i < hosts1.size, realizable 4 (hostAt hosts1 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 1 at hi
  interval_cases i

  · exact move0_0 h

def tags1_0 : Array Nat := #[0x0,0xed30a8642000]

theorem move1_0 (h : realizable 4 (hostAt hosts1 0).toFinset) :
    ∃ i < hosts2.size, realizable 3 (hostAt hosts2 i).toFinset :=
  descend hosts2 (hostAt hosts1 0) ⟨3,by decide⟩ 1 0x10 tags1_0 (by decide +kernel) h

def tags1_1 : Array Nat := #[0x130eca8642000,0x130eca8642001,0x112eca8642001,0x130eca8642002]

theorem move1_1 (h : realizable 4 (hostAt hosts1 1).toFinset) :
    ∃ i < hosts2.size, realizable 3 (hostAt hosts2 i).toFinset :=
  descend hosts2 (hostAt hosts1 1) ⟨3,by decide⟩ 2 0x3e4 tags1_1 (by decide +kernel) h

theorem layer1 (h : ∃ i < hosts1.size, realizable 4 (hostAt hosts1 i).toFinset) :
    ∃ i < hosts2.size, realizable 3 (hostAt hosts2 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 2 at hi
  interval_cases i

  · exact move1_0 h

  · exact move1_1 h

def tags2_0 : Array Nat := #[0x0,0x130a8ec642002]

theorem move2_0 (h : realizable 3 (hostAt hosts2 0).toFinset) :
    ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset :=
  descend hosts3 (hostAt hosts2 0) ⟨2,by decide⟩ 1 0x1f000 tags2_0 (by decide +kernel) h

def tags2_1 : Array Nat := #[0x0,0x130eca8642003,0x130cea8642003,0x130eca8642005,0x112eca8642000,0x130a8ec642001,0x130a8ce642001,0xa930ec642004]

theorem move2_1 (h : realizable 3 (hostAt hosts2 1).toFinset) :
    ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset :=
  descend hosts3 (hostAt hosts2 1) ⟨2,by decide⟩ 3 0x7ffffac6db688 tags2_1 (by decide +kernel) h

def tags2_2 : Array Nat := #[0x130eca8642002,0x130eca8642004,0x130cea8642004,0x130eca8642007,0xed30a8642004,0x130eca8642006,0x130cea8642006,0xed12a8642004,0x112eca8642006,0x112cea8642006]

theorem move2_2 (h : realizable 3 (hostAt hosts2 2).toFinset) :
    ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset :=
  descend hosts3 (hostAt hosts2 2) ⟨2,by decide⟩ 4 0x33333398736543210 tags2_2 (by decide +kernel) h

theorem layer2 (h : ∃ i < hosts2.size, realizable 3 (hostAt hosts2 i).toFinset) :
    ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 3 at hi
  interval_cases i

  · exact move2_0 h

  · exact move2_1 h

  · exact move2_2 h

def tags3_0 : Array Nat := #[0x0,0x13064eca82009]

theorem move3_0 (h : realizable 2 (hostAt hosts3 0).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 0) ⟨1,by decide⟩ 1 0x1ffff8888f0008000 tags3_0 (by decide +kernel) h

def tags3_1 : Array Nat := #[0x0,0xed3064a82000,0x130ec64a82002,0x130ec64a82004,0x130ec64a82006,0x130ce64a82002,0x130ce64a82004,0x130ce64a82006,0x112ec64a8200f,0x6530eca8200c,0x130ec648a2003,0x112ec64a8200e,0x13064eca82007,0x112ce64a8200e,0x13064cea82007]

theorem move3_1 (h : realizable 2 (hostAt hosts3 1).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 1) ⟨1,by decide⟩ 4 0x9999999999999999999889e8d9c8b9a8099997777444411119988765043201000 tags3_1 (by decide +kernel) h

def tags3_2 : Array Nat := #[0x0,0x130ec64a82010]

theorem move3_2 (h : realizable 2 (hostAt hosts3 2).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 2) ⟨1,by decide⟩ 1 0x1fffff000f000f000 tags3_2 (by decide +kernel) h

def tags3_3 : Array Nat := #[0x0,0x6530eca82011]

theorem move3_3 (h : realizable 2 (hostAt hosts3 3).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 3) ⟨1,by decide⟩ 1 0x1fffff80000000000 tags3_3 (by decide +kernel) h

def tags3_4 : Array Nat := #[0x0,0x130eca8642011,0x130ec8a642011,0x130eca8642016,0xcf30a8642009,0x130ec64a8200c,0x130ec648a200c,0x13064eca82015,0x130eca8642017,0x130ec64a82019,0x130ec648a2019,0x13064eca82013,0xed3064a82018,0x13064eca82012,0x13064ec8a2012,0x112eca8642017,0x112ec64a82019,0x112ec648a2019,0x11264eca82013,0xed1264a82018,0x11264eca82012,0x11264ec8a2012]

theorem move3_4 (h : realizable 2 (hostAt hosts3 4).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 4) ⟨1,by decide⟩ 5 0x739ce739ce739ce739ce739ce73d69394a529460f39ce73b9ac5ad6b5a92839ce7398a418c6318820 tags3_4 (by decide +kernel) h

def tags3_5 : Array Nat := #[0x0,0x130eca864201d,0x130eca864201a,0x130ec8a64201a,0x130cea864201a,0x130ce8a64201a,0x6530eca82000,0x6530ec8a2000,0x6530eca82016,0x6530a8ec2000,0x6530eca82001,0x6530ec8a2001,0x6530a8ce2000,0x6530cea82001,0x6530ce8a2001]

theorem move3_5 (h : realizable 2 (hostAt hosts3 5).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 5) ⟨1,by decide⟩ 4 0x8888888888888888888888edc8ba9876011111111111111111111154013201000 tags3_5 (by decide +kernel) h

def tags3_6 : Array Nat := #[0x0,0x130eca8642014,0x130ec8a642014,0x130eca864201e,0x130a8ec642013,0x130eca864201b,0x130ec8a64201b,0xcf30a8642018,0xed3064a8200b,0xed30648a200b,0x6530eca8201c,0xeca930642013,0xed30a864201b,0xed308a64201b,0xcea865302005,0xec6530a82008,0xec65308a2008,0x112eca8642018,0x130ec64a8200b,0x130ec648a200b,0x112a864ec2005,0x13064eca82008,0x13064ec8a2008,0x112cea864200a,0x130ec64a8200d,0x130ec648a200d]

theorem move3_6 (h : realizable 2 (hostAt hosts3 6).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 6) ⟨1,by decide⟩ 5 0xa5294a5294a5294a5294a5294a5671755ab454e515294a541ee18c631b58b5294a52507198a418820 tags3_6 (by decide +kernel) h

def tags3_7 : Array Nat := #[0x130eca8642010,0x130eca8642015,0x130ec8a642015,0x130eca8642020,0x130a8ec642015,0x130eca864201c,0x130ec8a64201c,0x130a8ce642015,0x130cea864201c,0x130ce8a64201c,0xeca930642015,0xed30a864201c,0xed308a64201c,0xa930ec64201c,0x130eca864201f,0x130ec8a64201f,0xa930ce64201c,0x130cea864201f,0x130ce8a64201f,0xeca912642015,0xed12a864201c,0xed128a64201c,0xa912ec64201c,0x112eca864201f,0x112ec8a64201f,0xa912ce64201c,0x112cea864201f,0x112ce8a64201f]

theorem move3_7 (h : realizable 2 (hostAt hosts3 7).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 7) ⟨1,by decide⟩ 5 0x318c6318c6318c6318c6318c631ef591e2f61d69318c631ca301bdcd1b16a18c631a507198a418820 tags3_7 (by decide +kernel) h

theorem layer3 (h : ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 8 at hi
  interval_cases i

  · exact move3_0 h

  · exact move3_1 h

  · exact move3_2 h

  · exact move3_3 h

  · exact move3_4 h

  · exact move3_5 h

  · exact move3_6 h

  · exact move3_7 h

def tags4_0 : Array Nat := #[0x0,0x2130eca8647b]

theorem move4_0 (h : realizable 1 (hostAt hosts4 0).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 0) ⟨0,by decide⟩ 1 0x1fffffcccfffffcccfffff88800000000fffff88800000000fffff88800000000 tags4_0 (by decide +kernel) h

def tags4_1 : Array Nat := #[0x0,0x130ec20a86435,0x2130eca86498,0x13020eca86401,0x13020ec46a823,0x13020ec8a6423,0x13020ec8a4610,0x13020eca8643b,0x130ec20a86403,0x13020ec64a83a,0x13020eca8643a,0x13020eca86439,0x13020eca86400,0x2130ec64a855,0x13020ec64a800,0x2130ec64a858,0x2130eca86455,0x2130eca86458,0x2130eca86456,0x11220eca8643b,0x112ec20a86403,0x11220ec64a83a,0x11220eca8643a,0x11220eca86439,0x11220eca86400,0x2112ec64a855,0x11220ec64a800,0x2112ec64a858,0x2112eca86455,0x2112eca86458,0x2112eca86456]

theorem move4_1 (h : realizable 1 (hostAt hosts4 1).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 1) ⟨0,by decide⟩ 5 0x210842108421084210842108421084210863108631084210842108421084210842108421086310863108421084210842108421084217bbc16c7a167009ce739ce739ce739ce739ce739dec09d68098000108421084210842108421084214a3013c6e1358039ce739ce739ce739ce739ce73ad403a500380001084210842108421084210842118a011060100000842108421084210842108421080000800008000 tags4_1 (by decide +kernel) h

def tags4_2 : Array Nat := #[0x0,0x2130eca864b2]

theorem move4_2 (h : realizable 1 (hostAt hosts4 2).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 2) ⟨0,by decide⟩ 1 0x1ffffffffffffffffccccc888c888c888fffff00000000000ccccc00000000000 tags4_2 (by decide +kernel) h

def tags4_3 : Array Nat := #[0x0,0x13020eca864b9]

theorem move4_3 (h : realizable 1 (hostAt hosts4 3).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 3) ⟨0,by decide⟩ 1 0x1fffffffffffffffffaaac888c888c888fffff000f000f000faaac000c000c000 tags4_3 (by decide +kernel) h

def tags4_4 : Array Nat := #[0x0,0x2130eca864bd]

theorem move4_4 (h : realizable 1 (hostAt hosts4 4).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 4) ⟨0,by decide⟩ 1 0x1fffffffffffffffffcccf888a888a888fffff00000000000fcccf00000000000 tags4_4 (by decide +kernel) h

def tags4_5 : Array Nat := #[0x0,0x130eca8642084,0x4730eca820b6,0x13020eca864c4,0x130ec64a8209d,0x130eca8206473,0x1306420eca8c5,0x130ec648a209d,0x130ec8a206473,0x1306420ec8ac5,0xed30a8206412,0x112a864ec209d,0x112a8ec206473,0x1126420a8ecc5,0x13064eca82156,0x130eca8206474,0x1302064eca899,0x13064ec8a2156,0x130ec8a206474,0x1302064ec8a99,0x13020eca864c2,0x112a864ce209d,0x112a8ce206473,0x1126420a8cec5,0x13064cea82156,0x130cea8206474,0x1302064cea899,0x13064ce8a2156,0x130ce8a206474,0x1302064ce8a99,0x13020cea864c2,0xa912ec206412,0x11220a8ec64c2,0x112208aec64c2,0xed3064a82046,0x13064ec20a969,0xed3064a82047,0x13020ec64a8d2,0xed30648a2047,0x13020ec648ad2,0x13020a864ed26,0x13020a864ed29,0x13020eca864c1,0x13020eca864c3,0x13020ec8a64c1,0x13020ec8a64c3,0x13020a864cf26,0x13020a864cf29,0x13020cea864c1,0x13020cea864c3,0x13020ce8a64c1,0x13020ce8a64c3,0xa91264ec2046,0x11264a820ed69,0x11220ec64a926,0x11220ec64a929,0x11220ec648b26,0x11220ec648b29,0xa91264ec2047,0x11220a864ecd2,0x11220a8ec64c1,0x11220a8ec64c3,0x112208aec64c1,0x112208aec64c3,0xa91264ce2047,0x11220a864ced2,0x11220a8ce64c1,0x11220a8ce64c3,0x112208ace64c1,0x112208ace64c3]

theorem move4_5 (h : realizable 1 (hostAt hosts4 5).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 5) ⟨0,by decide⟩ 7 0x3060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060d0a1060d020060cf9f060c18307150c4070d0420704fc0060c18306fd0be06f503c06ecfba060c18306e50b806dd03606d4fb4060c183060c183060c183060c183060cf1e06ccf3206c4f3006bcf2e060ca1406b4a2c06aca2a06a4a28060c50a069c5260694524068c522060c183060d0a1060d020060cf9f060cf1e0674e1b0668c98065cb15060ca14064c911064078e063460b060c50a062440706182840608080 tags4_5 (by decide +kernel) h

def tags4_6 : Array Nat := #[0x0,0xed30a8206415,0xed308a206415,0x130eca820647a,0x130eca8206476,0x130eca8206479,0x130ec8a206476,0x130ec8a206479,0xcea821306420,0x130ec20a86464,0x20ed30a8642c,0x20ed30a8644f,0x130ec208a6464,0x20ed308a642c,0x20ed308a644f,0x2130eca864c8,0x13020a8ec6469,0x2130eca86402,0x2130ec8a6402,0x2130eca8642d,0x2130ec8a642d,0x2130a8ec642e,0x13020eca86466,0x2130eca86452,0x13020ec8a6466,0x2130ec8a6452,0x2130eca8640e,0x13020eca86465,0x2130eca86432,0x13020ec8a6465,0x2130ec8a6432]

theorem move4_6 (h : realizable 1 (hostAt hosts4 6).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 6) ⟨0,by decide⟩ 5 0xf7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7be527be317be107bdef7fa5d7f23b7ea007bdef7e6587de367d6007bdef7d2407ce20782007bdef7bdef7bdef7bdef7bdef739ce5ad6b4210818c6318c6318c6318c6318c631084208421000007bdef7be527be317be107bdef735805a9204000018c6319cc0194801800018c63100000800000000 tags4_6 (by decide +kernel) h

def tags4_7 : Array Nat := #[0x0,0xed3020a8642e,0xed308a20640e,0xed1220a8645b,0x2130eca864d6,0xa930ec206414,0x130ec20a8648b,0x130ec20a84667,0x130ec20a8648c,0x130ec8a20646c,0x130ec208a646f,0x130ec208a6470,0x112ec20a86508,0xa930ce206414,0x130ce20a8648b,0x130ce20a84667,0x130ce20a8648c,0x130ce8a20646c,0x130ce208a646f,0x130ce208a6470,0x112ce20a86508,0x112ec20a84706,0x130ec208a646d,0x112ec20a84705,0x6512ec20a804,0x112ec20a86507,0x13020eca8649f,0x112ce20a84705,0x6512ce20a804,0x112ce20a86507,0x13020cea8649f]

theorem move4_7 (h : realizable 1 (hostAt hosts4 7).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 7) ⟨0,by decide⟩ 5 0x421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108425495254952129427a9d2569c26e802118c269992559825d802106325860254602006021084210842108421084210849ce73842106b5ad210845ad6b42108294a52108410842084210000021084210842549525495212949ca2083dc0680002118c5a92041cc02800021063100000800000000 tags4_7 (by decide +kernel) h

def tags4_8 : Array Nat := #[0x0,0x130eca86420aa,0xed30a8462048,0xed3020a86436,0x130ec64a820a9,0x130eca86420ac,0xed304620a81a,0x8b30ec6420d4,0x130a8ec2064e8,0x130a8ec2046e7,0x2130eca864da,0x130a864ec2122,0x130a8ec206545,0x130a8ec462157,0x130ec20a86497,0x130ec6420a89c,0x130ec20a86468,0x130ec2064a893,0xa93020ec64d3,0x13020a8ec649a,0x13020a8ec648d,0x130a864ce2122,0x130a8ce206545,0x130a8ce462157,0x130ce20a86497,0x130ce6420a89c,0x130ce20a86468,0x130ce2064a893,0xa93020ce64d3,0x13020a8ce649a,0x13020a8ce648d,0x112ec20a86528,0xeca93064205a,0xed30a820644b,0xed30a8462049,0xa8ec213064d2,0xec2130a86438,0xec2130a84630,0x130a8ec206571,0x130ec20a86496,0x130ec20a86495,0x20a930ec6451,0x2130eca86460,0x2130eca8645e,0x130a8ce206571,0x130ce20a86496,0x130ce20a86495,0x20a930ce6451,0x2130cea86460,0x2130cea8645e,0xed12a8642062,0x112eca8206553,0x112ec20a8472c,0x112ec6420a8c2,0x130ec2046a87c,0xa912ec206574,0x13020eca8647d,0x13020eca8646e,0x112a8ec642176,0x112ec20a86527,0x13020ec64a89e,0x112ec2064a8eb,0x13020ec64a8a4,0x13020a8ec6488,0x13020eca864a5,0x13020eca864a0,0x112a8ce642176,0x112ce20a86527,0x13020ce64a89e,0x112ce2064a8eb,0x13020ce64a8a4,0x13020a8ce6488,0x13020cea864a5,0x13020cea864a0]

theorem move4_8 (h : realizable 1 (hostAt hosts4 8).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 8) ⟨0,by decide⟩ 7 0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a1428f9f1428f9f142850a15264471518fc515121c2142850a150603f14f8fbd14f1dba142850a14e5c3714d8fb514d19b2142850a142850a142850a142850a142850a14c582f3060c1830b96ac142850a14ad5291c3870e1ca13a6142850a1495223060c18306890a0142850a142850a1428f9f1428f9f142850a1478e9c306cd19305cb15142850a14509921c4480f1c3460b142850a142440706182840608080 tags4_8 (by decide +kernel) h

def tags4_9 : Array Nat := #[0x0,0x130ec20a864de]

theorem move4_9 (h : realizable 1 (hostAt hosts4 9).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 9) ⟨0,by decide⟩ 1 0x1ffffffffffffffffffff888888888888fffff000f000f000ffff800080008000 tags4_9 (by decide +kernel) h

def tags4_10 : Array Nat := #[0x0,0x130eca86420b4,0x130eca84620b4,0xa930ec64200a,0x112ce64a820b4,0x130eca86420b5,0x130eca84620b5,0x130ec20a864e2,0x112ce648a20b4,0x130ec8a6420b5,0x130ec8a4620b5,0x130ec208a64e2,0x6512cea8200a,0x112ce2064a8e2,0x112ce2046a8e2,0x130ec20a864e3,0xa930ec642008,0xa930ec642009,0xa930ec462009,0x130ec2064a8fe,0x130ec20a864dd,0x130ec20a846dd,0x130ec20648afe,0x130ec208a64dd,0x130ec208a46dd,0x6512cea82008,0x112ce20a864fe,0x112ce20a846fe,0x6512cea82009,0x112ce2064a8dd,0x112ce2046a8dd,0x6512ce8a2009,0x112ce20648add,0x112ce20468add,0xa8ed30642008,0xa8ed30642009,0xa8ed30462009,0xed302064a8fe,0xed3020a864dd,0xed3020a846dd,0xed3020648afe,0xed30208a64dd,0xed30208a46dd,0x130cea8642169,0x130ce20a86574,0x130ce20a84774,0xcf302064a974,0x130ce20a86575,0x130ce20a84775,0xcf3020648b74,0x130ce208a6575,0x130ce208a4775,0x64cf12a82008,0xcf1220a864fe,0xcf1220a846fe,0x64cf12a82009,0xcf122064a8dd,0xcf122046a8dd,0x64cf128a2009,0xcf1220648add,0xcf1220468add,0xed12a8642169,0xed1220a86574,0xed1220a84774,0x112ec2064a974,0xed1220a86575,0xed1220a84775,0x112ec20648b74,0xed12208a6575,0xed12208a4775]

theorem move4_10 (h : realizable 1 (hostAt hosts4 10).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 10) ⟨0,by decide⟩ 7 0xf1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3868c1e3868c1e3868c1e3868c1e3c78f1f162431f0a0c01efdf3d1e3868c1ef1dba1ee5c371ed9ab41e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1ecd9311ec17ae1eb562b1e3c78f162c58b0e1c387060c1831e3c78f16a94a80e9d32506911a21e3c78f1e3c78f1e3c78f1e3c78f1e3868c1e8501f1e78e9c1e6cd191e3c78f1660b960e54a1306488901e3868c16284880e182840608080 tags4_10 (by decide +kernel) h

def tags4_11 : Array Nat := #[0x0,0x130eca86420d0,0xa930ec46200b,0xa930ec206417,0x112ec64a82118,0x112eca8206547,0x130ec6420a8f8,0x13020eca864ee,0x112ec648a2118,0x112ec8a206547,0x130ec64208af8,0x13020ec8a64ee,0xed12a8206567,0x13020eca864f1,0x130a8ec642087,0x130a8ec206477,0xa930ec642027,0x112eca820657b,0x130eca82064c0,0x13020eca864ae,0x112ec8a20657b,0x130ec8a2064c0,0x13020ec8a64ae,0x11220eca86553,0x112cea86420df,0xcf12a82064fd,0xcf1246a820b7,0x112ce2064a8dc,0xcf1220a864ff,0x130ec2064a8cf,0x112ce20648adc,0xcf12208a64ff,0x130ec20648acf,0xcf1220a86501,0xa8ed30642029,0xa930ec206413,0xa930ec642028,0xed3020a864e9,0x130ec20a864f0,0x130ec20a864ef,0xed30208a64e9,0x130ec208a64f0,0x130ec208a64ef,0xed30a82064c5,0xed3020a864e8,0xed3020a864e7,0xed3020a864ea,0x13020eca864ed,0x13020eca864ec,0xed30208a64ea,0x13020ec8a64ed,0x13020ec8a64ec,0xed1264a82179,0x112ec46a8216a,0xed1264a8217e,0x11220ec64a93f,0xed12648a217e,0x11220ec648b3f,0x112a820ec6526,0x11220a8ec652c,0x11220eca86552,0x11220eca86554,0x11220ec8a6552,0x11220ec8a6554,0xcf12a82064fe,0xed1220a8656c,0xcf1220a86500,0x11220eca86550,0xcf12208a6500,0x11220ec8a6550]

theorem move4_11 (h : realizable 1 (hostAt hosts4 11).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 11) ⟨0,by decide⟩ 7 0xd1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a350a11b150c41b0d0c21b050c01a34b971afcbbe1af4bbc1aecbba1a3460c1ae46381adc6361ad46341a3468d1a3468d1a3468d1a3468d1a3468d1acd9311ac17ae1ab562b1a3468d162c58b0e1c387060c1831a3468d16a94a80e9d32506911a21a3468d1a3468d1a3468d1a3468d1a350a11a80f9e1a74e1b1a68c981a34b971658a940e4c911064078e1a3460c16284880e182840608080 tags4_11 (by decide +kernel) h

def tags4_12 : Array Nat := #[0x0,0x130a8ec20647b,0x130eca82064b2,0x130eca82064bd,0x130eca82064c8,0x130ec8a2064b2,0x130ec8a2064bd,0x130ec8a2064c8,0x130cea82064fc,0x13020eca864f7,0xed30a82046b9,0x130cea82064fb,0x130ec20a864d6,0x130ce8a2064fb,0x130ec208a64d6,0xeca930206475,0xa8ed30206411,0xa930ec206418,0xed30a82064be,0xed30a82064bf,0x130ec20a864f2,0x13020eca864f5,0xed308a2064be,0xed308a2064bf,0x130ec208a64f2,0x13020ec8a64f5,0xcf3020a8650d,0xcf30a820650a,0xed3020a864e6,0xcf3020a8650c,0x13020eca864f4,0xcf30208a650c,0x13020ec8a64f4,0xeca912206475,0xa8ed12206411,0xa912ec206418,0xed12a82064be,0xed12a82064bf,0x112ec20a864f2,0x11220eca864f5,0xed128a2064be,0xed128a2064bf,0x112ec208a64f2,0x11220ec8a64f5,0xcf1220a8650d,0xcf12a820650a,0xed1220a864e6,0xcf1220a8650c,0x11220eca864f4,0xcf12208a650c,0x11220ec8a64f4]

theorem move4_12 (h : realizable 1 (hostAt hosts4 12).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 12) ⟨0,by decide⟩ 6 0x9249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249b2c272b31270b2f26eb2d249249aebaeb9e79e78e38e3249b2caeaa689e69648e284024924924924924924924924924969a26069f25e69d25c69b24924965965955555545145124969a6585d65544d24503c024924924924924924924924924920824e20d24c20b24a2002492491c71c71041040410412492081c6140103080040000 tags4_12 (by decide +kernel) h

def tags4_13 : Array Nat := #[0x0,0x130eca86420d1,0xa930ec46200c,0xa930ec20641f,0x130ec64a82117,0x130eca82064b3,0x130eca84620b8,0x130eca82064ce,0x130ec648a2117,0x130ec8a2064b3,0x130ec8a4620b8,0x130ec8a2064ce,0x112cea8206515,0x2130eca864f9,0xa930ec64202b,0xa930ec20641b,0xa930ec46200d,0x130eca82064ca,0x130eca82064cc,0x130eca82064cb,0x130ec8a2064ca,0x130ec8a2064cc,0x130ec8a2064cb,0x112a8ce6420e4,0x112cea8206501,0x130cea820476c,0x112cea86420e1,0x112cea8206513,0xed3020a864d5,0x112ce8a6420e1,0x112ce8a206513,0xed30208a64d5,0xa8ed3064202b,0xa8ed3020641b,0xa8ed3046200d,0xed30a82064ca,0xed30a82064cc,0xed30a82064cb,0xed308a2064ca,0xed308a2064cc,0xed308a2064cb,0xcea821306529,0xeca82130647d,0xeca82130466e,0xec2130a864ad,0xec2130a864b0,0xec2130a864af,0xec21308a64ad,0xec21308a64b0,0xec21308a64af,0xcea9126420e4,0xcf12a8206501,0xed12a820476c,0xcf12a86420e1,0xcf12a8206513,0x130ec20a864d5,0xcf128a6420e1,0xcf128a206513,0x130ec208a64d5,0x112a820ec6529,0x130a820ec647d,0x130a820ec466e,0x13020eca864ad,0x13020eca864b0,0x13020eca864af,0x13020ec8a64ad,0x13020ec8a64b0,0x13020ec8a64af,0x112cea86420e2,0x130eca82046ba,0x112cea8206514,0x130ec20a864d7,0x112ce8a206514,0x130ec208a64d7]

theorem move4_13 (h : realizable 1 (hostAt hosts4 13).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 13) ⟨0,by decide⟩ 7 0xd1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3460c1b246481b1c6461b146441a3468d1b0e1411b01fbe1af5e3b1a3460c1ae9cb81addb351ad19b21a3468d1a3468d1a3468d1a3468d1a3468d1ac582f1ab96ac1aad5291a3468d162c58b0e1c387060c1831a3468d16a13a60e9522306890a01a3468d1a3468d1a3468d1a3468d1a3460c1a7cf1d1a70d9a1a64c171a3468d1658a940e4c911064078e1a3460c16284880e182840608080 tags4_13 (by decide +kernel) h

def tags4_14 : Array Nat := #[0x0,0x2130eca864fb]

theorem move4_14 (h : realizable 1 (hostAt hosts4 14).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 14) ⟨0,by decide⟩ 1 0x1fffffffffffffffffffff000f000f000ccccc88888888888ccccc00080008000 tags4_14 (by decide +kernel) h

def tags4_15 : Array Nat := #[0x0,0x112ec20a86469,0x112ec208a6469,0x130eca8206504,0x2130eca864fc,0x112a820ec6469,0x130eca8206502,0x13020eca864a7,0x13020eca864a8,0x130ec8a206502,0x13020ec8a64a7,0x13020ec8a64a8,0x112a820ce6469,0x130cea8206502,0x13020cea864a7,0x13020cea864a8,0x130ce8a206502,0x13020ce8a64a7,0x13020ce8a64a8,0x2130eca8645b,0x2130ec8a645b,0x2130a8ec645b,0x130eca8206503,0x2130eca86463,0x130ec8a206503,0x2130ec8a6463,0x2130a8ce645b,0x130cea8206503,0x2130cea86463,0x130ce8a206503,0x2130ce8a6463]

theorem move4_15 (h : realizable 1 (hostAt hosts4 15).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 15) ⟨0,by decide⟩ 5 0x421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108494a527bdef6318c210845ad6b42108294a52108410842084210000021063210632106321063210632787d2707b26860210632647825c7625460210632506024c60200602106321063210632106321063946007b9a060000210635a92041cc02800021063100000800000000 tags4_15 (by decide +kernel) h

def tags4_16 : Array Nat := #[0x0,0x130eca820650e]

theorem move4_16 (h : realizable 1 (hostAt hosts4 16).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 16) ⟨0,by decide⟩ 1 0x1fffffffffffffffffffff000f000f000fffff000f000f000fffff000f000f000 tags4_16 (by decide +kernel) h

def tags4_17 : Array Nat := #[0x0,0x13020eca86516]

theorem move4_17 (h : realizable 1 (hostAt hosts4 17).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 17) ⟨0,by decide⟩ 1 0x1fffffffffffffffffffff80000000000fffff80000000000fffff80000000000 tags4_17 (by decide +kernel) h

def tags4_18 : Array Nat := #[0x0,0x130eca8206537,0x8b30ec20650d,0xa930ec2046e6,0x2130eca8651c,0x130a8ec64214d,0x130a8ec206548,0x130a8ec206543,0x130ec20a8651e,0x8b30ec20650f,0x8b30ec206510,0x13020a8ec648e,0x130a8ce64214d,0x130a8ce206548,0x130a8ce206543,0x130ce20a8651e,0x8b30ce20650f,0x8b30ce206510,0x13020a8ce648e,0x8b30ec206512,0xeca930642050,0xeca930206445,0xeca93020464a,0xed3020a86457,0x8aed30206509,0xec20a930462f,0xa930ec206565,0xa930ec206568,0x130ec20a8652a,0x130ec20a8652b,0x8b30ec206511,0x2130eca8645f,0xa930ce206565,0xa930ce206568,0x130ce20a8652a,0x130ce20a8652b,0x8b30ce206511,0x2130cea8645f,0xeca912206419,0xed12a820641c,0xed12a820460f,0xed1220a86421,0xa912ec2064c6,0x112ec20a8647e,0x112ec20a84671,0x112a8ec2064c9,0x112ec20a86480,0x112ec20a8647f,0x112ec20a86481,0x13020a8ec6489,0x13020eca864a6,0x13020eca864a1,0x112a8ce2064c9,0x112ce20a86480,0x112ce20a8647f,0x112ce20a86481,0x13020a8ce6489,0x13020cea864a6,0x13020cea864a1]

theorem move4_18 (h : realizable 1 (hostAt hosts4 18).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 18) ⟨0,by decide⟩ 6 0x410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410413ae78df7df7df6d74104104133cb1c30c30c2fbad10410412caeaa69a69a689e61041041044d31041041044d31041041254e48e38e38e286010410411f4de75d75d75c6da1041041194d85d75d75d65541041041044d31041041044d31041041124503cf3cf3ce34c10410410b289208208207185104104103080041041040000 tags4_18 (by decide +kernel) h

def tags4_19 : Array Nat := #[0x0,0x130eca864213a,0x2130a8ec6418,0x2130a8ec4618,0x2130eca86520,0x130a8ec64214e,0x130a8ec206549,0x130a8ec204749,0x130ec20a8651d,0x2130a8ec6429,0x2130a8ec643c,0x2130a8ec463c,0x130a8ce64214e,0x130a8ce206549,0x130a8ce204749,0x130ce20a8651d,0x2130a8ce6429,0x2130a8ce643c,0x2130a8ce463c,0x130ec20a86525,0x130a8ec642173,0x130eca8206551,0x130eca8204751,0x20a930ec6446,0x2130eca86457,0x2130eca84657,0x130a8ec20657d,0x130ec20a86524,0x130ec20a84724,0x2130a8ec645a,0x2130eca86461,0x2130eca84661,0x130a8ce20657d,0x130ce20a86524,0x130ce20a84724,0x2130a8ce645a,0x2130cea86461,0x2130cea84661,0x112ec20a86482,0x112ec20a86483,0x112ec20a84683,0x112ec20a86484,0x2130a8ec6408,0x2130eca86421,0x2130eca84621,0x13020a8ec6487,0x13020eca864a2,0x13020eca846a2,0x13020eca864a9,0x2130a8ec642b,0x2130eca8644d,0x2130eca8464d,0x13020a8ce6487,0x13020cea864a2,0x13020cea846a2,0x13020cea864a9,0x2130a8ce642b,0x2130cea8644d,0x2130cea8464d]

theorem move4_19 (h : realizable 1 (hostAt hosts4 19).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 19) ⟨0,by decide⟩ 6 0x410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410413ae78df7df7df6d74104104133cb1c30c30c2fbad10410412caeaa69a69a689e61041041041044d34d34d34d31041041259234d34d34e286010410411f79d4d34d34dc6da1041041196174d34d34d65541041041041044d34d34d34d31041041124503cf3cf3ce34c10410410b289208208207185104104103080041041040000 tags4_19 (by decide +kernel) h

def tags4_20 : Array Nat := #[0x0,0x130eca864213b,0x130eca82064f6,0x130eca82046f6,0x130ec20a8652d,0x130eca820654e,0x130ec20a8651a,0x130ec20a8471a,0x130ec20a8651f,0x130ec20a86519,0x130ec20a8651b,0x130ec20a8471b,0xed3020a864bb,0xed3020a846bb,0xed3020a864d0,0x20ed30a8640b,0x20ed30a86422,0x20ed30a84622,0x2130eca86523,0xed30a820654e,0xed3020a8651a,0xed3020a8471a,0xed3020a8651f,0xed3020a86519,0xed3020a8651b,0xed3020a8471b,0xec2130a8649d,0xec2130a864a3,0xec2130a846a3,0xec2130a864aa,0x20ed30a86448,0x20ed30a8644e,0x20ed30a8464e,0x130ec20a864bb,0x130ec20a846bb,0x130ec20a864d0,0x2130eca8640b,0x2130eca86422,0x2130eca84622,0x13020eca8649d,0x13020eca864a3,0x13020eca846a3,0x13020eca864aa,0x2130eca86448,0x2130eca8644e,0x2130eca8464e,0x130ec20a864b4,0x130ec20a864bc,0x130ec20a846bc,0x130ec20a864d1,0x2130eca8640c,0x2130eca86425,0x2130eca84625]

theorem move4_20 (h : realizable 1 (hostAt hosts4 20).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 20) ⟨0,by decide⟩ 6 0x124924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924b4cf2c71c71c70bee4924924adb2baaaaaaaa9a274924924a69648e38e38e28404924924924924924924924924924924a07de75d75d75c6da10410410410410410410410410410411961759659659551349249249249249249249249249249249140f38e38e38d30010410410b289208208207185104104103080041041040000 tags4_20 (by decide +kernel) h

def tags4_21 : Array Nat := #[0x0,0x130eca8642116,0x130eca8462116,0x130eca864213c,0x8b30ec6420de,0x130eca82064f7,0x130eca82046f7,0x130ec20a86534,0x130eca864213d,0x130eca820654f,0x130eca820474f,0x130ec20a86520,0x130a8ec20653e,0x130ec20a8651c,0x130ec20a8471c,0x130cea864213d,0x130cea820654f,0x130cea820474f,0x130ce20a86520,0x130a8ce20653e,0x130ce20a8651c,0x130ce20a8471c,0xed30a864213d,0xed30a820654f,0xed30a820474f,0xed3020a86520,0xeca93020653e,0xed3020a8651c,0xed3020a8471c,0x130ec20a8652e,0x130ec20a86530,0x130ec20a84730,0x130ec20a86532,0x130ec20a8652f,0x130ec20a86531,0x130ec20a84731,0x130ce20a8652e,0x130ce20a86530,0x130ce20a84730,0x130ce20a86532,0x130ce20a8652f,0x130ce20a86531,0x130ce20a84731,0xed12a864213d,0xed12a820654f,0xed12a820474f,0xed1220a86520,0xeca91220653e,0xed1220a8651c,0xed1220a8471c,0x112ec20a8652e,0x112ec20a86530,0x112ec20a84730,0x112ec20a86532,0x112ec20a8652f,0x112ec20a86531,0x112ec20a84731,0x112ce20a8652e,0x112ce20a86530,0x112ce20a84730,0x112ce20a86532,0x112ce20a8652f,0x112ce20a86531,0x112ce20a84731]

theorem move4_21 (h : realizable 1 (hostAt hosts4 21).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 21) ⟨0,by decide⟩ 6 0x71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71fffbdf3cf3cf3beb91c71c71f8df6d75d75d74cf21c71c71f1c2fbaebaebadb2b1c71c71c71c71c71c71c71c71c71c71eaa689e79e79e69641c71c71e38a182082081f79d1c71c71dc6da6596596585d61c71c71c71c71c71c71c71c71c71c71d551349249249140f1c71c71ce34c2cb2cb2ca2481c71c71c61440c30c30c2040 tags4_21 (by decide +kernel) h

def tags4_22 : Array Nat := #[0x0,0x130eca8642162,0x130eca8642155,0x130eca8462155,0x130ec8a642155,0x130ec8a462155,0x13020eca8647b,0x13020eca8467b,0x13020eca8653c,0x13020ec64a87b,0x13020eca86498,0x13020eca84698,0x13020ec648a7b,0x13020ec8a6498,0x13020ec8a4698,0x13020eca86536,0x13020eca84736,0x13020eca8653a,0x13020ec64a936,0x13020eca86538,0x13020eca84738,0x13020ec648b36,0x13020ec8a6538,0x13020ec8a4738,0x13020eca86535,0x13020eca86537,0x13020eca84737,0x13020ec64a937,0x13020eca86539,0x13020eca84739,0x13020ec648b37,0x13020ec8a6539,0x13020ec8a4739,0x11220eca86536,0x11220eca84736,0x11220eca8653a,0x11220ec64a936,0x11220eca86538,0x11220eca84738,0x11220ec648b36,0x11220ec8a6538,0x11220ec8a4738,0x11220eca86535,0x11220eca86537,0x11220eca84737,0x11220ec64a937,0x11220eca86539,0x11220eca84739,0x11220ec648b37,0x11220ec8a6539,0x11220ec8a4739]

theorem move4_22 (h : realizable 1 (hostAt hosts4 22).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 22) ⟨0,by decide⟩ 6 0x8208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208232c7022fbad22caea8e38e38e38e38e38e38e38e38e38e38e9a278e69648e28402082082082082082082082082082082207de21d71b21a6584514514514514514514514514514514575954544d24503c020820820820820820820820820820820e34c20b289207180041041041041041041041041041041045100043080040000 tags4_22 (by decide +kernel) h

def tags4_23 : Array Nat := #[0x0,0xed3020a86572,0xed30208a6572,0x130ec2064a972,0x130ec2046a972,0x130ec20a86573,0xec20a9306482,0xec2130a8648f,0xec2130a8468f,0x20ed30a86450,0xec21308a648f,0xec21308a468f,0x20ed308a6450,0x2130eca8653d,0x13020ec64a88f,0x13020ec46a88f,0x13020ec648a8f,0x13020ec468a8f,0x1302064eca882,0x2130ec64a850,0x2130ec46a850,0x2130eca86419,0x2130eca84619,0x20ed3064a819,0x2130eca8643e,0x2130eca8463e,0x20ed30648a19,0x2130ec8a643e,0x2130ec8a463e]

theorem move4_23 (h : realizable 1 (hostAt hosts4 23).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 23) ⟨0,by decide⟩ 5 0xd6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6f37a6e7176daa06d2726d2726d2726d2726d2726c6006bdc0680006b5ad6b5ad6b5ad6b5ad6b5ad6318c4a529318c6294a5294a5294a5294a5294a51084208421000006b5ad6b5ad6b5ad6b5ad6b5ad62d404a0e0300002906029060290602906029060100000800000000 tags4_23 (by decide +kernel) h

def tags4_24 : Array Nat := #[0x0,0xeca930642135,0x130eca8206544,0x130eca8204744,0xed30a8206579,0x130ec8a206544,0x130ec8a204744,0xed308a206579,0x6512eca82006,0x11220eca86509,0x11220eca84709,0x2130eca8653e,0x130a864ec2082,0x130a8ec20649b,0x130a8ec20469b,0xa930ec206446,0x11264eca8206a,0x130eca8206563,0x130eca8204763,0x2130eca86462,0x11264ec8a206a,0x130ec8a206563,0x130ec8a204763,0x2130ec8a6462,0xa8cf30206407,0xa8cf30204607,0xa8cf30206408,0xcf3020a864df,0xcf3020a864e0,0xcf3020a846e0,0xce2130a864e4,0xcf30208a64df,0xcf30208a64e0,0xcf30208a46e0,0xce21308a64e4,0x112ec20a8650a,0x112ec20a8470a,0x6512eca82005,0x112ec20a8650b,0x112ec20a8470b,0x6512ec8a2005,0x112ec208a650b,0x112ec208a470b,0x130cea82064b6,0x130ec20a864c6,0x130ec20a846c6,0x130ec20a864d4,0x2130eca8643f,0x2130eca8463f,0x130ec208a64d4,0x2130ec8a643f,0x2130ec8a463f]

theorem move4_24 (h : realizable 1 (hostAt hosts4 24).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 24) ⟨0,by decide⟩ 6 0xb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2f3cb12f0bee2edb2b2ca2482ca2482ca2482ca2482ca2482eaa682e79a52e48c02cb2cb2cb2cb2cb2cb2cb2cb2cb2cb8a28a279e79e69a69a2cb2cb5d75d74d34d33cf3cf2cb2cb1c71c71041040410412cb2cb2cb2cb2cb2cb2cb2cb2cb2cb8a181f79d71b6996002ca2485d65544d24503ce34c2ca2481c6140103080040000 tags4_24 (by decide +kernel) h

def tags4_25 : Array Nat := #[0x0,0x130a8ec206536,0x130eca8206546,0x130eca8206542,0x130eca820657a,0x130ec8a206546,0x130ec8a206542,0x130ec8a20657a,0xed30a8206566,0x13020eca86551,0xec2130a86475,0x20ed30a84611,0x2130eca8654f,0xec2130a86485,0x20ed30a86434,0x2130eca86431,0xec21308a6485,0x20ed308a6434,0x2130ec8a6431,0x20ed30a86445,0xed30a8642172,0xed30a820476b,0xed30a8206564,0x130ec20a8657c,0xed308a206564,0x130ec208a657c,0xec2130a8649b,0x20ed30a8644a,0x20ed30a86444,0x2130eca8645c,0x20ed308a6444,0x2130ec8a645c,0x112a820ec6472,0x112a820ec466b,0x13020a8ec6483,0x13020eca86486,0x13020eca86490,0x13020eca8648a,0x13020eca864ab,0x13020ec8a6486,0x13020ec8a6490,0x13020ec8a648a,0x13020ec8a64ab,0x2130eca86407,0x2130eca8641c,0x2130eca8640f,0x2130eca8642a,0x2130eca86440,0x2130eca86433,0x2130ec8a642a,0x2130ec8a6440,0x2130ec8a6433]

theorem move4_25 (h : realizable 1 (hostAt hosts4 25).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 25) ⟨0,by decide⟩ 6 0xc30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c333cb1330bee32db2b30c30caaaaaa9a69a68a28a230c30caa9a279a59238a180030c30c30c30c30c30c30c30c30c4d331f4de31d4dc31b4da24924924924924924924924924920825921825721625521430c30c30c30c30c30c30c30c30c4d331245030f38d30b2802492491c71c71041040410412492081c6140103080040000 tags4_25 (by decide +kernel) h

def tags4_26 : Array Nat := #[0x0,0x2130eca86555]

theorem move4_26 (h : realizable 1 (hostAt hosts4 26).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 26) ⟨0,by decide⟩ 1 0x1fffffffffffffffffffff888f800f80000000000000000000000000000000000 tags4_26 (by decide +kernel) h

def tags4_27 : Array Nat := #[0x0,0x130eca8642121,0x130eca8462121,0x130eca8642181,0x130ec64a8211f,0x130eca8642159,0x130eca8462159,0x130ec648a2119,0x130ec8a20654a,0x130ec8a20474a,0x13020eca8655d,0x130a864ec211d,0x130a8ec642158,0x130a8ec462158,0x1308a6420ecc7,0x130a820ec64d9,0x130a820ec46d9,0x20ed30a86405,0x20ed30a86416,0x20ed30a84616,0x2130eca8655a,0x20ed3064a813,0x2130eca8643d,0x2130eca8463d,0x20ed308a6428,0x2130eca86424,0x2130eca84624,0xed30a864217d,0xed30a8206578,0xed30a8204778,0x130ec6420a96d,0x130ec20a8657f,0x130ec20a8477f,0x130ec8a642177,0x130eca8206583,0x130eca8204783,0x20ed30a86447,0x20ed30a8644c,0x20ed30a8464c,0x20ed3064a84b,0x2130eca8645d,0x2130eca8465d,0x20ed30a86449,0x2130eca86459,0x2130eca84659,0x13020eca8646a,0x13020eca86478,0x13020eca84678,0x13020eca864ac,0x13020ec64a877,0x13020eca86492,0x13020eca84692,0x2130ec8a6427,0x2130a8ec641d,0x2130a8ec461d,0x13020a864ec73,0x13020a8ec6491,0x13020a8ec4691,0x2130a864ec1a,0x2130a8ec6441,0x2130a8ec4641,0x2130eca86409,0x2130eca8641e,0x2130eca8461e,0x2130ec64a81b,0x2130eca86442,0x2130eca84642,0x2130eca8640d,0x2130eca86426,0x2130eca84626]

theorem move4_27 (h : realizable 1 (hostAt hosts4 27).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 27) ⟨0,by decide⟩ 7 0x142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142916243290a0c028fdf3d2850a1428f1dba60c183060e5c372850a1428d9ab460cd93160bd72d2850a142850a142850a142850a142850a1428b15aa28a542728992a4142850a142850a142850a142850a142850a148d1211480f9e1474e1b2850a142850a142850a142850a142850a142868c98285cb15284c911142850a144078e060c183063460b142850a142440706182840608080 tags4_27 (by decide +kernel) h

def tags4_28 : Array Nat := #[0x0,0x130eca8642123,0x130eca8462123,0x130eca8642182,0x130ec64a82120,0x130eca864215a,0x130eca846215a,0x1308aec64213e,0xa930ec2064f1,0xa930ec2046f1,0x13020eca86561,0x130a864ec2120,0x130a8ec64215a,0x130a8ec46215a,0x8b306420ecc4,0x130a820ec64da,0x130a820ec46da,0x130cea864213e,0xed30a82064f1,0xed30a82046f1,0xcf306420a8c4,0x130ec20a864da,0x130ec20a846da,0xce8b306420e3,0x130eca82064f9,0x130eca82046f9,0xeca86530212e,0xeca93020654b,0xeca93020474b,0x13020eca8655e,0x130ec6420a96e,0x130ec20a86580,0x130ec20a84780,0x8b30ec642140,0xa93020ec6570,0xa93020ec4770,0x130a86420ed6e,0x130a820ec6580,0x130a820ec4780,0xa9302064ed6f,0x13020a8ec655c,0x13020a8ec475c,0xcf30a8642140,0xed3020a86570,0xed3020a84770,0xed302064a96f,0x13020eca8655c,0x13020eca8475c,0xeca930206541,0x13020eca8655b,0x13020eca8475b,0xeca86512212e,0xeca91220654b,0xeca91220474b,0x11220eca8655e,0x112ec6420a96e,0x112ec20a86580,0x112ec20a84780,0x8b12ec642140,0xa91220ec6570,0xa91220ec4770,0x112a86420ed6e,0x112a820ec6580,0x112a820ec4780,0xa9122064ed6f,0x11220a8ec655c,0x11220a8ec475c,0xcf12a8642140,0xed1220a86570,0xed1220a84770,0xed122064a96f,0x11220eca8655c,0x11220eca8475c,0xeca912206541,0x11220eca8655b,0x11220eca8475b]

theorem move4_28 (h : realizable 1 (hostAt hosts4 28).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 28) ⟨0,by decide⟩ 7 0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a152e54915223c61516243142850a150a0c06cd9b366cfdf3d142850a14f1dba6ce5c376cd5a33142850a142850a142850a142850a142850a14c98b014bd72d14b15aa142850a14a54273a74e9d3a992a4142850a148d1213a80f9e3a70d9a142850a142850a142850a142850a142850a1464c171458a94144c911142850a144078e060c183063460b142850a142440706182840608080 tags4_28 (by decide +kernel) h

def tags4_29 : Array Nat := #[0x0,0x130eca8642188,0x130eca8642184,0x130eca8462184,0x130ec8a642184,0x130ec8a462184,0x130cea8642184,0x130cea8462184,0x130ce8a642184,0x130ce8a462184,0x2130eca86562,0x2130eca86435,0x2130eca84635,0x2130ec8a6435,0x2130ec8a4635,0x2130a8ec6435,0x2130a8ec4635,0x213064eca835,0x2130eca86453,0x2130eca84653,0x213064ec8a35,0x2130ec8a6453,0x2130ec8a4653,0x2130a8ce6435,0x2130a8ce4635,0x213064cea835,0x2130cea86453,0x2130cea84653,0x213064ce8a35,0x2130ce8a6453,0x2130ce8a4653]

theorem move4_29 (h : realizable 1 (hostAt hosts4 29).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 29) ⟨0,by decide⟩ 5 0xa5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a57bbc56f59562e05294a55ab454e51541e05294a539a053160500000842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210a50009cc008000084210948008c400800008421080000800008000 tags4_29 (by decide +kernel) h

def tags4_30 : Array Nat := #[0x0,0x130eca864212d,0x130eca846212d,0x130eca8642189,0x130ec64a8212d,0x130eca864215f,0x130eca846215f,0x130ec648a212d,0x130ec8a64215f,0x130ec8a46215f,0x130a864ec2125,0x130a8ec64215d,0x130a8ec46215d,0x13064eca8215d,0x130eca8642185,0x130eca8462185,0x13064ec8a215d,0x130ec8a642185,0x130ec8a462185,0x20ed30a86406,0x20ed30a86417,0x20ed30a84617,0x2130eca86582,0x20ed3064a817,0x20ed30a86437,0x20ed30a84637,0x20ed30648a17,0x20ed308a6437,0x20ed308a4637,0xeca865302125,0xeca93064215d,0xeca93046215d,0xec6530a8215d,0xed30a8642185,0xed30a8462185,0xec65308a215d,0xed308a642185,0xed308a462185,0x20eca8653012,0x20eca9306436,0x20eca9304636,0x20ec6530a836,0x20ed30a86454,0x20ed30a84654,0x20ec65308a36,0x20ed308a6454,0x20ed308a4654,0x2130eca86406,0x2130eca86417,0x2130eca84617,0x2130ec64a817,0x2130eca86437,0x2130eca84637,0x2130ec648a17,0x2130ec8a6437,0x2130ec8a4637,0x2130a864ec12,0x2130a8ec6436,0x2130a8ec4636,0x213064eca836,0x2130eca86454,0x2130eca84654,0x213064ec8a36,0x2130ec8a6454,0x2130ec8a4654,0x2130eca8640a,0x2130eca8641f,0x2130eca8461f,0x2130ec64a81f,0x2130eca86443,0x2130eca84643,0x2130ec648a1f,0x2130ec8a6443,0x2130ec8a4643]

theorem move4_30 (h : realizable 1 (hostAt hosts4 30).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 30) ⟨0,by decide⟩ 7 0x162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162d264472d1a2c42d0e1412c58b162d01fbe2cf5e3b2ce9cb82c58b162cddb352cd19b22cc582f2c58b162c58b162c58b162c58b162c58b162cb96ac2cad5292ca13a6060c183060c183060c183060c183060c183069522306890a0067cf1d2c58b162c58b162c58b162c58b162c58b162c70d9a2c64c172c54a13060c1830648890063c70d063058a060c183062440706182840608080 tags4_30 (by decide +kernel) h

def tags4_31 : Array Nat := #[0x0,0x130eca8642133,0x130eca8462133,0x130eca864218a,0x130ec64a82132,0x130eca8642160,0x130eca8462160,0x130ec648a212f,0x130ec8a20654c,0x130ec8a20474c,0x2130eca86587,0x130a864ec2132,0x130a8ec642160,0x130a8ec462160,0x13064eca8215e,0x130eca8642186,0x130eca8462186,0x8b306420ed6f,0xa93020ec64d8,0xa93020ec46d8,0x130a864ce212f,0x130a8ce20654c,0x130a8ce20474c,0xcf306420a96f,0xed3020a864d8,0xed3020a846d8,0xce8b30642141,0xeca9302064f3,0xeca9302046f3,0xeca865302132,0xeca930642160,0xeca930462160,0xec6530a8215e,0xed30a8642186,0xed30a8462186,0x8aec6421316f,0xa8ec213064d8,0xa8ec213046d8,0xa86530ec215e,0xa930ec642186,0xa930ec462186,0x8a642130ec94,0xa82130ec64b1,0xa82130ec46b1,0xcea86421316f,0xeca8213064d8,0xeca8213046d8,0xce642130a894,0xec2130a864b1,0xec2130a846b1,0xce8a642130cd,0xeca8213064db,0xeca8213046db,0xeca86512212f,0xeca91220654c,0xeca91220474c,0x112ec6420a96f,0x130ec20a864d8,0x130ec20a846d8,0x1128aec642141,0x130a8ec2064f3,0x130a8ec2046f3,0x112a86420ed6f,0x130a820ec64d8,0x130a820ec46d8,0x1126420eca894,0x13020eca864b1,0x13020eca846b1,0x1128a6420eccd,0x130a820ec64db,0x130a820ec46db,0x112cea8642141,0x130eca82064f3,0x130eca82046f3,0x112ce6420a8cd,0x130ec20a864db,0x130ec20a846db,0x112ce8a6420e5,0x130eca82064fa,0x130eca82046fa]

theorem move4_31 (h : realizable 1 (hostAt hosts4 31).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 31) ⟨0,by decide⟩ 7 0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a153e74d15325ca1526447142850a151a2c4150e1411501fbe142850a14f5e3b14e9cb814ddb35142850a142850a142850a142850a142850a14d19b214c582f14b96ac142850a14ad529060c18306a13a6142850a149522306890a0067cf1d142850a142850a142850a142850a142850a1470d9a1464c171458a94142850a144c911064078e063460b142850a142440706182840608080 tags4_31 (by decide +kernel) h

def tags4_32 : Array Nat := #[0x130eca864210e,0x130eca8642134,0x130eca8462134,0x130eca864218c,0x130ec64a82134,0x130eca8642161,0x130eca8462161,0x130ec648a2134,0x130ec8a642161,0x130ec8a462161,0x130a864ec2134,0x130a8ec642161,0x130a8ec462161,0x13064eca82161,0x130eca8642187,0x130eca8462187,0x13064ec8a2161,0x130ec8a642187,0x130ec8a462187,0x130a864ce2134,0x130a8ce642161,0x130a8ce462161,0x13064cea82161,0x130cea8642187,0x130cea8462187,0x13064ce8a2161,0x130ce8a642187,0x130ce8a462187,0xeca865302134,0xeca930642161,0xeca930462161,0xec6530a82161,0xed30a8642187,0xed30a8462187,0xec65308a2161,0xed308a642187,0xed308a462187,0xa86530ec2161,0xa930ec642187,0xa930ec462187,0x6530eca82187,0x130eca864218b,0x130eca846218b,0x6530ec8a2187,0x130ec8a64218b,0x130ec8a46218b,0xa86530ce2161,0xa930ce642187,0xa930ce462187,0x6530cea82187,0x130cea864218b,0x130cea846218b,0x6530ce8a2187,0x130ce8a64218b,0x130ce8a46218b,0xeca865122134,0xeca912642161,0xeca912462161,0xec6512a82161,0xed12a8642187,0xed12a8462187,0xec65128a2161,0xed128a642187,0xed128a462187,0xa86512ec2161,0xa912ec642187,0xa912ec462187,0x6512eca82187,0x112eca864218b,0x112eca846218b,0x6512ec8a2187,0x112ec8a64218b,0x112ec8a46218b,0xa86512ce2161,0xa912ce642187,0xa912ce462187,0x6512cea82187,0x112cea864218b,0x112cea846218b,0x6512ce8a2187,0x112ce8a64218b,0x112ce8a46218b]

theorem move4_32 (h : realizable 1 (hostAt hosts4 32).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 32) ⟨0,by decide⟩ 7 0x3060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183074684f073a6cc072e549060c18307223c60716243070a0c0060c18306fdf3d06f1dba06e5c37060c183060c183060c183060c183060c18306d9ab406cd93106c17ae060c18306b562b06a94a8069d325060c18306911a2068501f0678e9c060c183060c183060c183060c183060c183066cd190660b960654a13060c1830648890063c70d063058a060c183062440706182840608080 tags4_32 (by decide +kernel) h

theorem layer4 (h : ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 33 at hi
  interval_cases i

  · exact move4_0 h

  · exact move4_1 h

  · exact move4_2 h

  · exact move4_3 h

  · exact move4_4 h

  · exact move4_5 h

  · exact move4_6 h

  · exact move4_7 h

  · exact move4_8 h

  · exact move4_9 h

  · exact move4_10 h

  · exact move4_11 h

  · exact move4_12 h

  · exact move4_13 h

  · exact move4_14 h

  · exact move4_15 h

  · exact move4_16 h

  · exact move4_17 h

  · exact move4_18 h

  · exact move4_19 h

  · exact move4_20 h

  · exact move4_21 h

  · exact move4_22 h

  · exact move4_23 h

  · exact move4_24 h

  · exact move4_25 h

  · exact move4_26 h

  · exact move4_27 h

  · exact move4_28 h

  · exact move4_29 h

  · exact move4_30 h

  · exact move4_31 h

  · exact move4_32 h

theorem classified5 (possible : realizable 5 {0}) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset := by
  have initial : ∃ i < hosts0.size, realizable 5 (hostAt hosts0 i).toFinset := ⟨0,by decide,by simpa [hosts0, hostAt] using possible⟩
  exact layer4 (layer3 (layer2 (layer1 (layer0 (initial)))))

end PEqualNP.Outside.L_meta_908_aux
