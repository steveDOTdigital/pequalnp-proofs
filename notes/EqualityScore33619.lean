import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

open scoped BigOperators
open Finset

namespace EqualityScore33619

variable {Edge Row : Type} [DecidableEq Edge]

def allMass (weight : Row → ℤ) (hit : Row → Edge → Prop) [∀ r e, Decidable (hit r e)]
    (rows : Finset Row) (edges : Finset Edge) : ℤ :=
  ∑ r ∈ rows, if ∀ e ∈ edges, hit r e then weight r else 0

def anyMass (weight : Row → ℤ) (hit : Row → Edge → Prop) [∀ r e, Decidable (hit r e)]
    (rows : Finset Row) (edges : Finset Edge) : ℤ :=
  ∑ r ∈ rows, if ∃ e ∈ edges, hit r e then weight r else 0

theorem filteredMass (weight : Row → ℤ) (hit : Row → Edge → Prop) [∀ r e, Decidable (hit r e)]
    (rows : Finset Row) (edges : Finset Edge) (a : Edge) :
    allMass weight hit (rows.filter fun r => hit r a) edges =
      allMass weight hit rows (insert a edges) := by
  unfold allMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : hit r a <;> simp [h]

theorem anyInsert (weight : Row → ℤ) (hit : Row → Edge → Prop) [∀ r e, Decidable (hit r e)]
    (rows : Finset Row) (edges : Finset Edge) (a : Edge) :
    anyMass weight hit rows (insert a edges) =
      anyMass weight hit rows edges + allMass weight hit rows {a}
        - anyMass weight hit (rows.filter fun r => hit r a) edges := by
  unfold anyMass allMass
  rw [Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : hit r a <;> by_cases e : ∃ x ∈ edges, hit r x <;>
    simp [h, e]

theorem massIsLinear (weight : Row → ℤ) (hit : Row → Edge → Prop) [∀ r e, Decidable (hit r e)]
    (edges : Finset Edge) (rows : Finset Row)
    (balance : ∀ part ⊆ edges, 2 ≤ part.card → allMass weight hit rows part = 0) :
    anyMass weight hit rows edges = ∑ a ∈ edges, allMass weight hit rows {a} := by
  induction edges using Finset.induction_on generalizing rows with
  | empty => simp [anyMass]
  | @insert a edges absent ih =>
    have smaller : ∀ part ⊆ edges, 2 ≤ part.card → allMass weight hit rows part = 0 :=
      fun part partSub size => balance part (partSub.trans (Finset.subset_insert _ _)) size
    have filtered (part : Finset Edge) (inc : part ⊆ edges) (size : 1 ≤ part.card) :
        allMass weight hit (rows.filter fun r => hit r a) part = 0 := by
      rw [filteredMass]
      have aNotMem : a ∉ part := fun found => absent (inc found)
      have inserted : insert a part ⊆ insert a edges := by
        intro x hx
        simp only [Finset.mem_insert] at hx ⊢
        exact hx.imp_right (fun member => inc member)
      apply balance _ inserted
      rw [Finset.card_insert_of_notMem aNotMem]
      omega
    have intersection : anyMass weight hit (rows.filter fun r => hit r a) edges = 0 := by
      rw [ih _ (fun part inc size => filtered part inc (by omega))]
      apply Finset.sum_eq_zero
      intro e he
      exact filtered {e} (Finset.singleton_subset_iff.mpr he) (by simp)
    rw [anyInsert, ih rows smaller, intersection, sub_zero, Finset.sum_insert absent, add_comm]

#print axioms massIsLinear


def scoreWeight (base label : Row → Bool) (r : Row) : ℤ :=
  if base r then 0 else if label r then 1 else -1

def correct (rows : Finset Row) (label out : Row → Bool) : ℤ :=
  ∑ r ∈ rows, if out r = label r then 1 else 0

def predicted (base : Row → Bool) (hit : Row → Edge → Prop)
    [∀ r e, Decidable (hit r e)] (edges : Finset Edge) (r : Row) : Bool :=
  base r || decide (∃ e ∈ edges, hit r e)

omit [DecidableEq Edge] in
theorem scoreChange (base label : Row → Bool) (hit : Row → Edge → Prop)
    [∀ r e, Decidable (hit r e)] (edges : Finset Edge) (rows : Finset Row) :
    correct rows label (predicted base hit edges) - correct rows label base =
      anyMass (scoreWeight base label) hit rows edges := by
  unfold correct anyMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  cases hb : base r <;> cases hl : label r <;>
    by_cases saw : ∃ e ∈ edges, hit r e <;> simp [predicted,scoreWeight,hb,hl,saw]

omit [DecidableEq Edge] in
theorem massByCard (base label : Row → Bool) (hit : Row → Edge → Prop)
    [∀ r e, Decidable (hit r e)] (rows : Finset Row) (edges : Finset Edge) :
    allMass (scoreWeight base label) hit rows edges =
      ((rows.filter fun r => base r = false ∧ label r = true ∧ ∀ e ∈ edges, hit r e).card : ℤ) -
      ((rows.filter fun r => base r = false ∧ label r = false ∧ ∀ e ∈ edges, hit r e).card : ℤ) := by
  have count (p : Row → Prop) [DecidablePred p] :
      (∑ r ∈ rows, if p r then (1 : ℤ) else 0) = ((rows.filter p).card : ℤ) := by
    rw [← Finset.sum_filter]
    simp
  rw [← count, ← count, ← Finset.sum_sub_distrib]
  unfold allMass
  apply Finset.sum_congr rfl
  intro r _
  cases hb : base r <;> cases hl : label r <;> by_cases all : ∀ e ∈ edges, hit r e <;>
    simp [scoreWeight, hb, hl, all]
  split <;> simp_all

theorem scoreWithBalance (base label : Row → Bool) (hit : Row → Edge → Prop)
    [∀ r e, Decidable (hit r e)] (edges : Finset Edge) (rows : Finset Row)
    (balance : ∀ part ⊆ edges, 2 ≤ part.card →
      (rows.filter fun r => base r = false ∧ label r = true ∧ ∀ e ∈ part, hit r e).card =
      (rows.filter fun r => base r = false ∧ label r = false ∧ ∀ e ∈ part, hit r e).card) :
    correct rows label (predicted base hit edges) =
      correct rows label base + ∑ e ∈ edges, allMass (scoreWeight base label) hit rows {e} := by
  have linear := massIsLinear (scoreWeight base label) hit edges rows (by
    intro part sub big
    rw [massByCard, balance part sub big, sub_self])
  have total := scoreChange base label hit edges rows
  rw [linear] at total
  omega

#print axioms scoreWithBalance

end EqualityScore33619


open scoped BigOperators
open Finset

namespace EqualityScore33619

variable {Edge Row : Type} [DecidableEq Edge]

def countWhere (xs : List Row) (condition : Row → Prop) [DecidablePred condition] : ℕ :=
  (xs.filter fun r => decide (condition r)).length

theorem countIndex (xs : List Row) (condition : Row → Prop) [DecidablePred condition] :
    ((Finset.univ : Finset (Fin xs.length)).filter fun i => condition (xs.get i)).card =
      countWhere xs condition := by
  induction xs with
  | nil => simp [countWhere]
  | cons hd tl ih =>
    rw [Finset.card_filter]
    change (∑ i : Fin (tl.length + 1),
      if condition ((hd :: tl).get i) then (1 : ℕ) else 0) = countWhere (hd :: tl) condition
    rw [Fin.sum_univ_succ (f := fun i : Fin (tl.length+1) =>
      if condition ((hd :: tl).get i) then (1 : ℕ) else 0)]
    by_cases yes : condition hd <;>
      simp [countWhere, yes, List.get_eq_getElem, Nat.add_comm] <;>
      simpa only [countWhere, List.get_eq_getElem] using ih

theorem correctIndex (xs : List Row) (label out : Row → Bool) :
    correct (Finset.univ : Finset (Fin xs.length)) (fun i => label (xs.get i)) (fun i => out (xs.get i)) =
      (countWhere xs (fun r => out r = label r) : ℤ) := by
  unfold correct
  rw [← Finset.sum_filter]
  simpa using congrArg (fun k : ℕ => (k : ℤ)) (countIndex xs (fun r => out r = label r))

theorem listScore (soft : List Row) (base label : Row → Bool) (hit : Row → Edge → Prop)
    [∀ r e, Decidable (hit r e)] (edges : Finset Edge)
    (balance : ∀ part ⊆ edges, 2 ≤ part.card →
      countWhere soft (fun r => base r = false ∧ label r = true ∧ ∀ e ∈ part, hit r e) =
      countWhere soft (fun r => base r = false ∧ label r = false ∧ ∀ e ∈ part, hit r e)) :
    (countWhere soft (fun r => predicted base hit edges r = label r) : ℤ) =
      (countWhere soft (fun r => base r = label r) : ℤ) +
        (∑ e ∈ edges,
          ((countWhere soft (fun r => base r = false ∧ label r = true ∧ hit r e) : ℤ) -
          (countWhere soft (fun r => base r = false ∧ label r = false ∧ hit r e) : ℤ))) := by
  let base' := fun i : Fin soft.length => base (soft.get i)
  let label' := fun i : Fin soft.length => label (soft.get i)
  let hit' := fun (i : Fin soft.length) (e : Edge) => hit (soft.get i) e
  let : ∀ i e, Decidable (hit' i e) := fun _ _ => inferInstanceAs (Decidable (hit _ _))
  have balance' : ∀ part ⊆ edges, 2 ≤ part.card →
      ((Finset.univ : Finset (Fin soft.length)).filter fun i =>
        base' i = false ∧ label' i = true ∧ ∀ e ∈ part, hit' i e).card =
      ((Finset.univ : Finset (Fin soft.length)).filter fun i =>
        base' i = false ∧ label' i = false ∧ ∀ e ∈ part, hit' i e).card := by
    intro part sub big
    have pos := countIndex soft (fun r => base r = false ∧ label r = true ∧ ∀ e ∈ part, hit r e)
    have neg := countIndex soft (fun r => base r = false ∧ label r = false ∧ ∀ e ∈ part, hit r e)
    exact pos.trans ((balance part sub big).trans neg.symm)
  have order := scoreWithBalance base' label' hit' edges (Finset.univ : Finset (Fin soft.length)) balance'
  change correct _ (fun i => label (soft.get i))
    (fun i => predicted base hit edges (soft.get i)) =
      correct _ (fun i => label (soft.get i)) (fun i => base (soft.get i)) +
        ∑ e ∈ edges, allMass (scoreWeight base' label') hit' (Finset.univ : Finset (Fin soft.length)) {e} at order
  rw [correctIndex, correctIndex] at order
  rw [order]
  apply congrArg (fun z : ℤ => (countWhere soft (fun r => base r = label r) : ℤ) + z)
  apply Finset.sum_congr rfl
  intro e _
  rw [massByCard]
  unfold base' label' hit'
  rw [countIndex soft (fun r => base r = false ∧ label r = true ∧ ∀ j ∈ ({e} : Finset Edge), hit r j),
    countIndex soft (fun r => base r = false ∧ label r = false ∧ ∀ j ∈ ({e} : Finset Edge), hit r j)]
  simp

#print axioms listScore

end EqualityScore33619


open scoped BigOperators
open Finset

namespace EqualityScore33619

abbrev SoftRecord (n : ℕ) := (Finset (Fin n) × Finset (Fin n)) × Bool
abbrev Pair (n : ℕ) := Fin n × Fin n

def ends {n : ℕ} (e : Pair n) : Finset (Fin n) := {e.1,e.2}

def clash {n : ℕ} (t : SoftRecord n) : Bool := decide (¬ Disjoint t.1.1 t.1.2)

def sees {n : ℕ} (t : SoftRecord n) (e : Pair n) : Prop :=
  ends e ⊆ t.1.1 ∨ ends e ⊆ t.1.2

instance {n : ℕ} (t : SoftRecord n) (e : Pair n) : Decidable (sees t e) := by
  unfold sees
  infer_instance

theorem matchingScore {n : ℕ} (soft : List (SoftRecord n)) (E S : Finset (Pair n))
    (contained : S ⊆ E)
    (matching : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (ends e) (ends f))
    (balanced : ∀ T ⊆ E, 2 ≤ T.card →
      (∀ e ∈ T, ∀ f ∈ T, e ≠ f → Disjoint (ends e) (ends f)) →
      (soft.filter (fun t => t.2 && decide (Disjoint t.1.1 t.1.2 ∧ ∀ e ∈ T, sees t e))).length =
      (soft.filter (fun t => !t.2 && decide (Disjoint t.1.1 t.1.2 ∧ ∀ e ∈ T, sees t e))).length) :
    (countWhere soft (fun t => predicted clash sees S t = t.2) : ℤ) =
      (countWhere soft (fun t => clash t = t.2) : ℤ) +
        ∑ e ∈ S,
          ((countWhere soft (fun t => Disjoint t.1.1 t.1.2 ∧ t.2 = true ∧ sees t e) : ℤ) -
           (countWhere soft (fun t => Disjoint t.1.1 t.1.2 ∧ t.2 = false ∧ sees t e) : ℤ)) := by
  have clashFalse (t : SoftRecord n) : clash t = false ↔ Disjoint t.1.1 t.1.2 := by
    simp [clash]
  have atS (T : Finset (Pair n)) (sub : T ⊆ S) (big : 2 ≤ T.card) :
      countWhere soft (fun t => clash t = false ∧ t.2 = true ∧ ∀ e ∈ T, sees t e) =
      countWhere soft (fun t => clash t = false ∧ t.2 = false ∧ ∀ e ∈ T, sees t e) := by
    have source := balanced T (sub.trans contained) big
      (fun e he f hf different => matching e (sub he) f (sub hf) different)
    have yes : (fun t : SoftRecord n => decide (clash t = false ∧ t.2 = true ∧ ∀ e ∈ T, sees t e)) =
        (fun t => t.2 && decide (Disjoint t.1.1 t.1.2 ∧ ∀ e ∈ T, sees t e)) := by
      funext t
      cases ht : t.2 <;> simp [clashFalse]
    have no : (fun t : SoftRecord n => decide (clash t = false ∧ t.2 = false ∧ ∀ e ∈ T, sees t e)) =
        (fun t => !t.2 && decide (Disjoint t.1.1 t.1.2 ∧ ∀ e ∈ T, sees t e)) := by
      funext t
      cases ht : t.2 <;> simp [clashFalse]
    unfold countWhere
    rw [yes,no]
    exact source
  have scoring := listScore soft clash Prod.snd sees S (by
    intro T sub big
    convert atS T sub big using 1 <;>
      exact congrArg (@countWhere _ soft _) (Subsingleton.elim _ _))
  simpa only [clashFalse] using scoring

#print axioms matchingScore

end EqualityScore33619