import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.IncidenceFactorCount

open PEqualNP.CircuitLowerBounds

abbrev Bits (n : ℕ) := Fin n → Bool

def single {n : ℕ} (p : Fin n) : Bits n := fun q => decide (q = p)

def hits {n : ℕ} (f : Bits n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun p => f (single p) = true

def owned {n : ℕ} (S : Finset (Fin n)) (f : Bits n → Bool) : Prop :=
  hits f ⊆ S ∧ 2 ≤ (hits f).card

def upward {n : ℕ} (f : Bits n → Bool) : Prop :=
  ∀ p x, x p = true → f (single p) = true → f x = true

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

def wire {n : ℕ} (w : Bits n → List Bool) (j : ℕ) (x : Bits n) : Bool :=
  (w x).getD j false

def newGate {n : ℕ} (w : Bits n → List Bool) (g : Gate) (x : Bits n) : Bool :=
  g.op.eval (g.inputs.map fun j => wire w j x)

def ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem gate_mono {n : ℕ} {w : Bits n → List Bool} {g : Gate} (hg : ok g)
    (x y : Bits n) (h : ∀ j ∈ g.inputs, wire w j x = true → wire w j y = true) :
    newGate w g x = true → newGate w g y = true := by
  rcases hg.1 with hand | hor
  · simp only [newGate, hand, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx j hj => h j hj (hx j hj)
  · simp only [newGate, hor, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨j,hj,hy⟩
    exact ⟨j,hj,h j hj hy⟩

theorem snoc_wire {n l : ℕ} (w : Bits n → List Bool) (hl : ∀ x, (w x).length = l)
    (g : Gate) (j : ℕ) :
    wire (fun x => step (w x) g) j = if j = l then newGate w g else wire w j := by
  funext x
  have hw := hl x
  by_cases e : j = l
  · subst j
    simp [wire, step, newGate, ← hl x]
  · simp only [ite_eq_right e, wire, step]
    by_cases lt : j < (w x).length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default _ _ (by simp [hl x]; omega),
          List.getD_eq_default _ _ (by omega)]

def outside {n : ℕ} (S : Finset (Fin n)) : Bits n := fun p => decide (p ∉ S)

def covered {n : ℕ} (S : Finset (Fin n)) (w : Bits n → List Bool) (cost : ℕ) : Prop :=
  ∀ W : Finset ℕ, (∀ j ∈ W, wire w j (outside S) = false) →
    ∃ R : Finset (Fin n), R.card ≤ cost + W.card ∧ ∀ j ∈ W, hits (wire w j) ⊆ R

noncomputable def charge {n : ℕ} (S : Finset (Fin n)) (f : Bits n → Bool)
    (g : Gate) : ℕ :=
  @ite _ (g.op = GateOp.or ∧ owned S f) (Classical.propDecidable _) 1 0

theorem advance {n l t : ℕ} (S : Finset (Fin n)) (w : Bits n → List Bool)
    (hl : ∀ x, (w x).length = l) (g : Gate) (hg : ok g)
    (mon : upward (newGate w g)) (paid : covered S w t) :
    covered S (fun x => step (w x) g) (t + charge S (newGate w g) g) := by
  classical
  intro W low
  let V := W.erase l
  have old (j) (hj : j ∈ V) : wire w j (outside S) = false := by
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hj
    simpa [snoc_wire w hl,ne] using low j mem
  by_cases use : l ∈ W
  · have cardV : V.card + 1 = W.card := Finset.card_erase_add_one use
    have off : newGate w g (outside S) = false := by simpa [snoc_wire w hl] using low l use
    have sub : hits (newGate w g) ⊆ S := by
      intro p hp
      by_contra miss
      have := mon p (outside S) (by simp [outside,miss]) (Finset.mem_filter.mp hp).2
      simp [off] at this
    by_cases small : (hits (newGate w g)).card ≤ 1
    · obtain ⟨R,hr,h⟩ := paid V old
      have := Finset.card_union_le R (hits (newGate w g))
      refine ⟨R ∪ hits (newGate w g),by omega,?_⟩
      intro j hj
      rw [snoc_wire w hl]; split_ifs with e
      · exact Finset.subset_union_right
      · exact (h j (Finset.mem_erase.mpr ⟨e,hj⟩)).trans Finset.subset_union_left
    · rcases hg.1 with hand | hor
      · have ex : ∃ a ∈ g.inputs, wire w a (outside S) = false := by
          simpa [newGate,hand,GateOp.eval,List.all_eq_false] using off
        obtain ⟨a,ha,hfalse⟩ := ex
        obtain ⟨R,hr,h⟩ := paid (insert a V) (by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hv
          · exact hfalse
          · exact old j hv)
        have := Finset.card_insert_le a V
        refine ⟨R,by omega,?_⟩
        intro j hj
        rw [snoc_wire w hl]; split_ifs with e
        · intro p hp
          apply h a (by simp)
          have hh := (Finset.mem_filter.mp hp).2
          simp only [newGate,hand,GateOp.eval,List.all_map,List.all_eq_true,
            Function.comp_apply,id_eq] at hh
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh a ha⟩
        · exact h j (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,hj⟩))
      · let U := V ∪ g.inputs.toFinset
        have inputsOff : ∀ a ∈ g.inputs, wire w a (outside S) = false := by
          simpa [newGate,hor,GateOp.eval,List.any_eq_false] using off
        obtain ⟨R,hr,h⟩ := paid U (by
          intro j hj
          rcases Finset.mem_union.mp hj with hv | ha
          · exact old j hv
          · exact inputsOff j (List.mem_toFinset.mp ha))
        have charged : charge S (newGate w g) g = 1 := by
          have own : owned S (newGate w g) := ⟨sub,by omega⟩
          simp [charge,hor,own]
        have hu : U.card ≤ V.card + g.inputs.toFinset.card := Finset.card_union_le _ _
        have := (List.toFinset_card_le g.inputs).trans hg.2
        refine ⟨R,by omega,?_⟩
        intro j hj
        rw [snoc_wire w hl]; split_ifs with e
        · intro p hp
          have hh := (Finset.mem_filter.mp hp).2
          simp only [newGate,hor,GateOp.eval,List.any_map,List.any_eq_true,
            Function.comp_apply,id_eq] at hh
          obtain ⟨a,ha,on⟩ := hh
          exact h a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _,on⟩)
        · exact h j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hj⟩))
  · obtain ⟨R,hr,h⟩ := paid W (by
      intro j hj
      have ne : j ≠ l := fun e => use (e ▸ hj)
      simpa [snoc_wire w hl,ne] using low j hj)
    refine ⟨R,by omega,?_⟩
    intro j hj
    rw [snoc_wire w hl,ite_eq_right (show j ≠ l from fun e => use (e ▸ hj))]
    exact h j hj

noncomputable def orCost (g : Gate) : ℕ :=
  @ite _ (g.op = GateOp.or) (Classical.propDecidable _) 1 0

theorem total_charge {n m : ℕ} (S : Fin m → Finset (Fin n))
    (overlap : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (f : Bits n → Bool) (g : Gate) :
    ∑ i, charge (S i) f g ≤ orCost g := by
  classical
  let U := Finset.univ.filter (fun i => owned (S i) f)
  have hc : U.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    by_contra ne
    have small := overlap i j ne
    have sub : hits f ⊆ S i ∩ S j :=
      fun p hp => Finset.mem_inter.mpr ⟨hi'.1 hp, hj'.1 hp⟩
    have := Finset.card_le_card sub
    have := hi'.2
    omega
  by_cases hor : g.op = GateOp.or
  · simpa [U,charge,orCost,hor,Finset.sum_boole] using hc
  · simp [charge,orCost,hor]

theorem drive {n m : ℕ} (S : Fin m → Finset (Fin n))
    (overlap : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hok : ∀ g ∈ gs, ok g) (w : Bits n → List Bool) (l : ℕ)
    (hl : ∀ x, (w x).length = l) (hm : ∀ j, upward (wire w j))
    (cost : Fin m → ℕ) (hcost : ∀ i, covered (S i) w (cost i)) :
    ∃ d : Fin m → ℕ, (∑ i, d i) ≤ (∑ i, cost i) + (gs.map orCost).sum ∧
      ∀ i, covered (S i) (fun x => gs.foldl step (w x)) (d i) := by
  classical
  induction gs generalizing w l cost with
  | nil => exact ⟨cost, by simp, hcost⟩
  | cons g gs ih =>
    have hg := hok g List.mem_cons_self
    have mon : upward (newGate w g) :=
      fun p x hx => gate_mono hg _ _ (fun j _ => hm j p x hx)
    let w' := fun x => step (w x) g
    let c' := fun i => cost i + charge (S i) (newGate w g) g
    have hl' (x) : (w' x).length = l + 1 := by simp [w', step, hl]
    have hm' (j) : upward (wire w' j) := by
      rw [show wire w' j = _ from snoc_wire w hl g j]
      split_ifs
      · exact mon
      · exact hm j
    have hc' (i) : covered (S i) w' (c' i) :=
      advance _ w hl g hg mon (hcost i)
    obtain ⟨d, hd, hall⟩ := ih (fun g' h => hok g' (List.mem_cons_of_mem _ h))
      w' (l+1) hl' hm' c' hc'
    refine ⟨d, ?_, hall⟩
    have bound := total_charge S overlap (newGate w g) g
    simp only [c', Finset.sum_add_distrib] at hd
    simp only [List.map_cons,List.sum_cons]
    omega

theorem initial_up {n : ℕ} (j : ℕ) : upward (wire (fun x : Bits n => List.ofFn x) j) := by
  intro p x hx h
  by_cases hj : j < n
  · have e : (⟨j,hj⟩ : Fin n) = p := by simpa [wire, single, hj] using h
    simpa [wire, hj, e] using hx
  · simp [wire, hj] at h

theorem initial_covered {n : ℕ} (S : Finset (Fin n)) :
    covered S (fun x : Bits n => List.ofFn x) 0 := by
  classical
  intro W _
  let R := Finset.univ.filter (fun p : Fin n => p.val ∈ W)
  have sub : R.image Fin.val ⊆ W := by
    rintro _ h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hp).2
  have bound := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at bound
  refine ⟨R,by simpa using bound,?_⟩
  intro j hj p hp
  have on := (Finset.mem_filter.mp hp).2
  by_cases lt : j < n
  · have e : (⟨j,lt⟩ : Fin n) = p := by simpa [wire,single,lt] using on
    exact e ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
  · simp [wire,lt] at on

-- The outputs for each center may be different taps of one shared gate list.
theorem grouped_outputs {n m : ℕ} (S : Fin m → Finset (Fin n))
    (overlap : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (gates : ∀ g ∈ gs, ok g) (W : Fin m → Finset ℕ)
    (off : ∀ i, ∀ j ∈ W i, (Circuit.mk gs j).eval (List.ofFn (outside (S i))) = false) :
    (∑ i, ((W i).biUnion (fun j => hits (fun x : Bits n => (Circuit.mk gs j).eval (List.ofFn x)))).card)
      ≤ (gs.map orCost).sum + ∑ i, (W i).card := by
  classical
  obtain ⟨d,total,all⟩ := drive S overlap gs gates (fun x : Bits n => List.ofFn x) n
    (by simp) initial_up (fun _ => 0) (fun i => initial_covered (S i))
  have each (i : Fin m) :
      ((W i).biUnion (fun j => hits (fun x : Bits n => (Circuit.mk gs j).eval (List.ofFn x)))).card
        ≤ d i + (W i).card := by
    obtain ⟨R,hr,h⟩ := all i (W i) (off i)
    apply le_trans (Finset.card_le_card (t := R) ?_) hr
    intro p hp
    obtain ⟨j,hj,hp⟩ := Finset.mem_biUnion.mp hp
    exact h j hj hp
  have sumBound := Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)
  rw [Finset.sum_add_distrib] at sumBound
  exact sumBound.trans (Nat.add_le_add_right (by simpa using total) _)

end PEqualNP.Outside.IncidenceFactorCount
