import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1035_aux

open PEqualNP.CircuitLowerBounds

abbrev Bits (n : ℕ) := Fin n → Bool

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


abbrev Signal := Bits 6 → Bool
abbrev Wires := Bits 6 → List Bool

def positive : Bits 6 := fun i => decide (i.val ≠ 0)
def negative (k : Fin 5) : Bits 6 := fun i => decide (i.val ≠ k.val+1)
def sep (f : Signal) := Finset.univ.filter fun k => f positive = true ∧ f (negative k) = false

def available (w : Wires) (f : Signal) := ∃ j, wire w j = f
noncomputable def seen (A : Finset Signal) (w : Wires) := by
  classical
  exact A.filter (available w)
def budget (A : Finset Signal) (w : Wires) (t : Nat) :=
  ∀ S : Finset Signal, (∀ f ∈ S, available w f) →
    (S.biUnion sep).card + (seen A w).card ≤ S.card + t

theorem advance (A : Finset Signal) (empty : ∀ f ∈ A, sep f = ∅)
    (w : Wires) {l t : Nat} (hl : ∀ x, (w x).length = l) (g : Gate) (hg : ok g)
    (old : budget A w t) : budget A (fun x => step (w x) g) (t+1) := by
  classical
  let b := newGate w g
  let w' := fun x => step (w x) g
  have was (f) (h : available w' f) : f = b ∨ available w f := by
    obtain ⟨i,hi⟩ := h
    rw [show wire w' i = _ from snoc_wire w hl g i] at hi
    split_ifs at hi
    · exact Or.inl hi.symm
    · exact Or.inr ⟨i,hi⟩
  intro S hs
  have oldmem : ∀ f ∈ S.erase b, available w f := by
    intro f hf
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hf
    exact (was f (hs f mem)).resolve_left ne
  by_cases hb : b ∈ A
  · have sub : seen A w' ⊆ insert b (seen A w) := by
      intro f hf
      obtain ⟨fa,live⟩ := Finset.mem_filter.mp hf
      rcases was f live with e | prev
      · simp [e]
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨fa,prev⟩)
    have size := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
    have same : S.biUnion sep ⊆ (S.erase b).biUnion sep := by
      intro j hj
      obtain ⟨f,hf,hj⟩ := Finset.mem_biUnion.mp hj
      by_cases e : f = b
      · subst f
        simp [empty b hb] at hj
      · exact Finset.mem_biUnion.mpr ⟨f,Finset.mem_erase.mpr ⟨e,hf⟩,hj⟩
    have c := Finset.card_le_card same
    have e := Finset.card_le_card (Finset.erase_subset b S)
    have o := old _ oldmem
    change _ + (seen A w').card ≤ _
    omega
  · have sub : seen A w' ⊆ seen A w := by
      intro f hf
      obtain ⟨fa,live⟩ := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr ⟨fa,(was f live).resolve_left (fun e => hb (e ▸ fa))⟩
    have size := Finset.card_le_card sub
    by_cases hS : b ∈ S
    · let P := g.inputs.toFinset.image (wire w)
      have psize : P.card ≤ 2 := Finset.card_image_le.trans ((List.toFinset_card_le (l := g.inputs)).trans hg.2)
      have support : sep b ⊆ P.biUnion sep := by
        intro j hj
        obtain ⟨_,yes,no⟩ := Finset.mem_filter.mp hj
        by_contra bad
        have h := gate_mono hg positive (negative j) (fun i hi hp => by
          cases val : wire w i (negative j) with
          | true => rfl
          | false =>
            exact False.elim (bad (Finset.mem_biUnion.mpr ⟨_, Finset.mem_image.mpr ⟨i,List.mem_toFinset.mpr hi,rfl⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,val⟩⟩))) yes
        simp [b,h] at no
      have prev : ∀ f ∈ (S.erase b) ∪ P, available w f := by
        intro f hf
        rcases Finset.mem_union.mp hf with l | r
        · exact oldmem _ l
        · obtain ⟨i,_,e⟩ := Finset.mem_image.mp r
          exact ⟨i,e⟩
      have cover : S.biUnion sep ⊆ ((S.erase b) ∪ P).biUnion sep := by
        intro j hj
        obtain ⟨f,hf,hj⟩ := Finset.mem_biUnion.mp hj
        by_cases e : f = b
        · subst f
          obtain ⟨u,hu,hj⟩ := Finset.mem_biUnion.mp (support hj)
          exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_union_right _ hu,hj⟩
        · exact Finset.mem_biUnion.mpr ⟨f,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hf⟩),hj⟩
      have c := Finset.card_le_card cover
      have o := old _ prev
      have u := Finset.card_union_le (S.erase b) P
      have e := Finset.card_erase_add_one hS
      change _ + (seen A w').card ≤ _
      omega
    · have o := old S (fun f h => (was f (hs f h)).resolve_left (fun e => hS (e ▸ h)))
      change _ + (seen A w').card ≤ _
      omega

theorem drive (A : Finset Signal) (empty : ∀ f ∈ A, sep f = ∅)
    (gs : List Gate) (hok : ∀ g ∈ gs, ok g) (w : Wires) (l t : Nat)
    (hl : ∀ x, (w x).length = l) (base : budget A w t) :
    budget A (fun x => gs.foldl step (w x)) (t+gs.length) := by
  induction gs generalizing w l t with
  | nil => simpa using base
  | cons g gs ih =>
    have h := ih (fun a ha => hok a (List.mem_cons_of_mem _ ha))
      (fun x => step (w x) g) (l+1) (t+1) (fun x => by simp [step,hl])
      (advance A empty w hl g (hok g List.mem_cons_self) base)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def aux (j : Fin 14) (x : Bits 6) : Bool :=
  ![x 0 && x 1,
    x 0 && x 1 && x 2,
    x 0 && x 1 && x 2 && x 3,
    x 0 && x 1 && x 2 && x 3 && x 4,
    x 0 && x 1 && x 2 && x 3 && x 4 && x 5,
    x 0 || x 1,
    x 0 || x 2,
    x 0 || x 3,
    x 0 || x 4,
    x 0 || x 5,
    x 0 || (x 1 && x 2),
    x 0 || (x 1 && x 2 && x 3),
    x 0 || (x 1 && x 2 && x 3 && x 4),
    x 0 || (x 1 && x 2 && x 3 && x 4 && x 5)] j

def finalSignal (x : Bits 6) := x 1 && x 2 && x 3 && x 4 && x 5
def family (j : Fin 15) (x : Bits 6) :=
  if h : j.val < 14 then aux ⟨j.val,h⟩ x else finalSignal x
def inputAt (k : Fin 64) : Bits 6 := fun j => k.val.testBit j.val

def exampleGates : List Gate := [⟨.and,[0,1]⟩,
  ⟨.and,[6,2]⟩,
  ⟨.and,[7,3]⟩,
  ⟨.and,[8,4]⟩,
  ⟨.and,[9,5]⟩,
  ⟨.or,[0,1]⟩,
  ⟨.or,[0,2]⟩,
  ⟨.or,[0,3]⟩,
  ⟨.or,[0,4]⟩,
  ⟨.or,[0,5]⟩,
  ⟨.and,[11,12]⟩,
  ⟨.and,[16,13]⟩,
  ⟨.and,[17,14]⟩,
  ⟨.and,[18,15]⟩,
  ⟨.not,[0]⟩,
  ⟨.and,[19,20]⟩,
  ⟨.or,[10,21]⟩]
def output (j : Fin 15) := if j.val<14 then 6+j.val else 22

theorem aux_sep : ∀ i, sep (aux i) = ∅ := by decide +kernel
theorem final_sep : (sep finalSignal).card = 5 := by decide +kernel

theorem aux_inj : Function.Injective aux := by
  have finite : ∀ i j : Fin 14, i ≠ j → ∃ k : Fin 64, aux i (inputAt k) ≠ aux j (inputAt k) := by decide +kernel
  intro i j e
  by_contra ne
  obtain ⟨k,h⟩ := finite i j ne
  exact h (congrFun e _)

noncomputable def targets : Finset Signal := by
  classical
  exact Finset.univ.image aux

theorem targets_size : targets.card = 14 := by
  classical
  simp [targets,Finset.card_image_of_injective _ aux_inj]

theorem targets_empty (f : Signal) (hf : f ∈ targets) : sep f = ∅ := by
  classical
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
  exact aux_sep i

def initial : Wires := fun x => List.ofFn x

theorem initial_wire (j : Fin 6) : wire initial j.val = fun x => x j := by
  fin_cases j <;> rfl

theorem init_seen : seen targets initial = ∅ := by
  classical
  have dist : ∀ i : Fin 14, ∀ j : Fin 6, ∃ k : Fin 64, aux i (inputAt k) ≠ inputAt k j := by decide +kernel
  have top : ∀ i : Fin 14, aux i (fun _ => true) = true := by decide +kernel
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨mem,j,eq⟩ := Finset.mem_filter.mp hf
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp mem
  by_cases hj : j < 6
  · obtain ⟨k,bad⟩ := dist i ⟨j,hj⟩
    apply bad
    rw [initial_wire ⟨j,hj⟩] at eq
    exact (congrFun eq _).symm
  · have q := congrFun eq (fun _ => true)
    simp [wire,initial,hj,top] at q

theorem initial_budget : budget targets initial 0 := by
  intro S hS
  have cap : ∀ j : Fin 6, (sep (fun x : Bits 6 => x j)).card ≤ 1 := by decide +kernel
  have none : sep (fun _ => false) = ∅ := by decide +kernel
  have small (f) (hf : f ∈ S) : (sep f).card ≤ 1 := by
    obtain ⟨j, rfl⟩ := hS f hf
    by_cases h : j < 6
    · have eq := initial_wire ⟨j,h⟩
      rw [eq]; exact cap _
    · have eq : wire initial j = fun _ => false := by funext x; simp [wire,initial,h]
      simp [eq,none]
  rw [init_seen]
  simp only [Finset.card_empty,Nat.add_zero]
  have b := Finset.card_biUnion_le (s := S) (t := sep)
  exact b.trans (by simpa using Finset.sum_le_sum small)

def supported : GateOp → Bool
  | .and | .or | .not => true
  | _ => false
def isNot : GateOp → Bool
  | .not => true
  | _ => false

theorem example_ops : (∀ g ∈ exampleGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
    (∀ i j : Fin exampleGates.length, (exampleGates.get i).op = GateOp.not →
      (exampleGates.get j).op = GateOp.not → i=j) := by
  have valid : ∀ i : Fin exampleGates.length, supported (exampleGates.get i).op = true ∧
      (exampleGates.get i).inputs.length ≤ 2 := by decide +kernel
  have unique : ∀ i : Fin exampleGates.length, isNot (exampleGates.get i).op = true → i.val = 14 := by decide +kernel
  constructor
  · intro g hg
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hg
    subst g
    obtain ⟨tag,h⟩ := valid i
    refine ⟨?_,h⟩
    have usable (op : GateOp) (ht : supported op = true) : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by
      cases op <;> simp_all [supported]
    exact usable _ tag
  · intro i j hi hj
    apply Fin.ext
    exact (unique i (by rw [hi]; rfl)).trans (unique j (by rw [hj]; rfl)).symm

theorem example_eval : ∀ (j : Fin 15) (x : Bits 6),
    Circuit.eval ⟨exampleGates,output j⟩ (List.ofFn x) = family j x := by
  decide +kernel

theorem family_mono : ∀ (j : Fin 15) (x y : Bits 6), (∀ i, x i ≤ y i) → family j x ≤ family j y := by
  decide +kernel

theorem lower (gs : List Gate) (out : Fin 15 → Nat) (ops : ∀ g ∈ gs, ok g)
    (eval : ∀ j x, Circuit.eval ⟨gs,out j⟩ (List.ofFn x) = family j x) : 18 ≤ gs.length := by
  classical
  let work := fun x => gs.foldl step (initial x)
  have realized (j : Fin 15) : available work (family j) :=
    ⟨out j,funext fun x => eval j x⟩
  have haveTargets : seen targets work = targets := by
    apply Finset.filter_true_of_mem
    intro f hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
    have j := realized ⟨i.val,by omega⟩
    have e : family ⟨i.val,by omega⟩ = aux i := by funext x; simp [family,i.isLt]
    rwa [e] at j
  have last : available work finalSignal := by
    exact realized 14
  have b := drive targets targets_empty gs ops initial 6 0 (fun x => by simp [initial]) initial_budget
  have e := b {finalSignal} (fun f hf => by
    rw [Finset.mem_singleton.mp hf]
    exact last)
  change (({finalSignal} : Finset Signal).biUnion sep).card + (seen targets work).card ≤ _ at e
  simp [haveTargets,targets_size,final_sep] at e
  omega


def monotoneGates : List Gate := exampleGates.take 14 ++
  [⟨.and,[1,2]⟩,⟨.and,[20,3]⟩,⟨.and,[21,4]⟩,⟨.and,[22,5]⟩]
def monotoneOutput (j : Fin 15) := if j.val < 14 then 6+j.val else 23
def isPos : GateOp → Bool
  | .and | .or => true
  | _ => false

theorem upper : monotoneGates.length = 18 ∧ (∀ g ∈ monotoneGates, ok g) ∧
    ∀ (j : Fin 15) (x : Bits 6),
      Circuit.eval ⟨monotoneGates,monotoneOutput j⟩ (List.ofFn x) = family j x := by
  have valid : ∀ i : Fin monotoneGates.length, isPos (monotoneGates.get i).op = true ∧
      (monotoneGates.get i).inputs.length ≤ 2 := by decide +kernel
  refine ⟨by decide,?_,by decide +kernel⟩
  intro g hg
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hg
  subst g
  obtain ⟨ht,hl⟩ := valid i
  have good (op : GateOp) (h : isPos op = true) : op = GateOp.and ∨ op = GateOp.or := by
    cases op <;> simp_all [isPos]
  exact ⟨good _ ht,hl⟩

end PEqualNP.Outside.L_meta_1035_aux

theorem PEqualNP.Outside.L_meta_1035 : ¬ (∀ (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool), n ≤ 7 → (∀ (j : Fin m) (x y : Fin n → Bool), (∀ i : Fin n, x i ≤ y i) → f j x ≤ f j y) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out j⟩ (List.ofFn x) = f j x) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' j⟩ (List.ofFn x) = f j x) ∧ gates'.length ≤ gates.length) := by
  intro h
  obtain ⟨gs,out,ops,eval,price⟩ := h 6 15 PEqualNP.Outside.L_meta_1035_aux.family (by decide)
    PEqualNP.Outside.L_meta_1035_aux.family_mono PEqualNP.Outside.L_meta_1035_aux.exampleGates PEqualNP.Outside.L_meta_1035_aux.output
    ⟨PEqualNP.Outside.L_meta_1035_aux.example_ops.1, PEqualNP.Outside.L_meta_1035_aux.example_ops.2,
      PEqualNP.Outside.L_meta_1035_aux.example_eval⟩
  have bound := PEqualNP.Outside.L_meta_1035_aux.lower gs out ops eval
  have sz : PEqualNP.Outside.L_meta_1035_aux.exampleGates.length = 17 := by decide
  omega
