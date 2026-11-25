import Mathlib.Tactic
import PEqualNP.Defs.TopForm
import PEqualNP.Defs.BlindGate
import TightBinaryCircuit

namespace FanoFinalAnd
open PEqualNP.CircuitLowerBounds

def incident (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
instance (p l : Fin 7) : Decidable (incident p l) := by unfold incident; infer_instance

def target (x : Fin 14 → Bool) := ∃ p l : Fin 7, incident p l ∧
  x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true

def control : Circuit := ⟨[
  ⟨.or,[7,13]⟩,
  ⟨.or,[14,11]⟩,
  ⟨.and,[0,15]⟩,
  ⟨.or,[8,7]⟩,
  ⟨.or,[17,12]⟩,
  ⟨.and,[1,18]⟩,
  ⟨.or,[10,9]⟩,
  ⟨.or,[20,7]⟩,
  ⟨.and,[3,21]⟩,
  ⟨.or,[11,10]⟩,
  ⟨.or,[23,8]⟩,
  ⟨.and,[4,24]⟩,
  ⟨.or,[12,11]⟩,
  ⟨.or,[26,9]⟩,
  ⟨.and,[5,27]⟩,
  ⟨.or,[13,12]⟩,
  ⟨.or,[29,10]⟩,
  ⟨.and,[6,30]⟩,
  ⟨.or,[28,31]⟩,
  ⟨.or,[25,32]⟩,
  ⟨.or,[22,33]⟩,
  ⟨.or,[19,34]⟩,
  ⟨.or,[16,35]⟩,
  ⟨.or,[9,8]⟩,
  ⟨.or,[37,13]⟩,
  ⟨.or,[36,2]⟩,
  ⟨.or,[36,38]⟩,
  ⟨.and,[39,40]⟩],41⟩

def ors (a b : Bool) := GateOp.or.eval [a,b]
def both (a b : Bool) := GateOp.and.eval [a,b]

theorem orValue (a b : Bool) : ors a b = (a || b) := by cases a <;> cases b <;> rfl
theorem andValue (a b : Bool) : both a b = (a && b) := by cases a <;> cases b <;> rfl

def neighbors (p : Fin 7) (x : Fin 14 → Bool) :=
  ors (ors (x (Fin.natAdd 7 p)) (x (Fin.natAdd 7 (p-1)))) (x (Fin.natAdd 7 (p-3)))

def term (p : Fin 7) (x : Fin 14 → Bool) := both (x (Fin.castAdd 7 p)) (neighbors p x)

def rest (x : Fin 14 → Bool) := ors (term 0 x) (ors (term 1 x) (ors (term 3 x) (ors (term 4 x) (ors (term 5 x) (term 6 x)))))

theorem traceCorrect (base : ℕ) (gs : List Gate) (x f : ℕ → Bool)
    (agreeBefore : ∀ i<base, x i=f i)
    (steps : ∀ j (h : j<gs.length), (∀ w ∈ gs[j].inputs, w<base+j) ∧
      f (base+j)=gs[j].op.eval (gs[j].inputs.map f)) :
    ∀ i<base+gs.length, TightBinaryCircuit.run base x gs i=f i := by
  induction gs generalizing base x with
  | nil => simpa [TightBinaryCircuit.run] using agreeBefore
  | cons g gs ih =>
    obtain ⟨reads,eq⟩ := steps 0 (by simp)
    simp only [Nat.add_zero,List.getElem_cons_zero] at reads eq
    have h := ih (base+1) (TightBinaryCircuit.step base g x) (by
      intro i hi
      by_cases atEnd : i=base
      · subst i
        rw [TightBinaryCircuit.step,Function.update_self,eq]
        congr 1
        exact List.map_congr_left (fun w hw => agreeBefore w (reads w hw))
      · rw [TightBinaryCircuit.step,Function.update_of_ne atEnd]
        exact agreeBefore i (by omega)) (by
      intro j hj
      rw [show base+1+j=base+(j+1) by omega]
      exact steps (j+1) (by simpa using hj))
    simpa [TightBinaryCircuit.run,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def tape (x : Fin 14 → Bool) : ℕ → Bool :=
  let v14 := ors (x 7) (x 13)
  let v15 := ors v14 (x 11)
  let v16 := both (x 0) v15
  let v17 := ors (x 8) (x 7)
  let v18 := ors v17 (x 12)
  let v19 := both (x 1) v18
  let v20 := ors (x 10) (x 9)
  let v21 := ors v20 (x 7)
  let v22 := both (x 3) v21
  let v23 := ors (x 11) (x 10)
  let v24 := ors v23 (x 8)
  let v25 := both (x 4) v24
  let v26 := ors (x 12) (x 11)
  let v27 := ors v26 (x 9)
  let v28 := both (x 5) v27
  let v29 := ors (x 13) (x 12)
  let v30 := ors v29 (x 10)
  let v31 := both (x 6) v30
  let v32 := ors v28 v31
  let v33 := ors v25 v32
  let v34 := ors v22 v33
  let v35 := ors v19 v34
  let v36 := ors v16 v35
  let v37 := ors (x 9) (x 8)
  let v38 := ors v37 (x 13)
  let v39 := ors v36 (x 2)
  let v40 := ors v36 v38
  let v41 := both v39 v40
  fun i => match i with
    | 0 => (x 0)
    | 1 => (x 1)
    | 2 => (x 2)
    | 3 => (x 3)
    | 4 => (x 4)
    | 5 => (x 5)
    | 6 => (x 6)
    | 7 => (x 7)
    | 8 => (x 8)
    | 9 => (x 9)
    | 10 => (x 10)
    | 11 => (x 11)
    | 12 => (x 12)
    | 13 => (x 13)
    | 14 => v14
    | 15 => v15
    | 16 => v16
    | 17 => v17
    | 18 => v18
    | 19 => v19
    | 20 => v20
    | 21 => v21
    | 22 => v22
    | 23 => v23
    | 24 => v24
    | 25 => v25
    | 26 => v26
    | 27 => v27
    | 28 => v28
    | 29 => v29
    | 30 => v30
    | 31 => v31
    | 32 => v32
    | 33 => v33
    | 34 => v34
    | 35 => v35
    | 36 => v36
    | 37 => v37
    | 38 => v38
    | 39 => v39
    | 40 => v40
    | 41 => v41
    | _ => false

set_option maxRecDepth 8000 in
theorem output (x : Fin 14 → Bool) : control.eval (List.ofFn x) =
    both (ors (rest x) (x 2)) (ors (rest x) (neighbors 2 x)) := by
  have check : ∀ j : Fin 28,
      let g := control.gates.getD j.val ⟨.or,[]⟩
      (∀ w ∈ g.inputs, w<14+j.val) ∧ (tape x (14+j.val))=g.op.eval (g.inputs.map (tape x)) := by
    intro j
    fin_cases j <;> constructor
    all_goals first | rfl | (intro w hw; simp [control,List.getD_eq_getElem?_getD] at hw ⊢; omega)
  have preFin (j : Fin 14) : (List.ofFn x).getD j.val false = tape x j.val := by
    fin_cases j <;> rfl
  have pre (i) (hi : i<14) : (List.ofFn x).getD i false = tape x i := preFin ⟨i,hi⟩
  have steps (j) (hj : j<control.gates.length) := check (⟨j,hj⟩ : Fin 28)
  have h := traceCorrect 14 control.gates _ (tape x) pre (by
    intro j hj
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using steps j hj) 41 (by decide)
  have sim := congrFun (TightBinaryCircuit.simulate control.gates (List.ofFn x)) 41
  rw [List.length_ofFn] at sim
  exact sim.trans (h.trans (by rfl))

theorem starCorrect (p : Fin 7) (x : Fin 14 → Bool) :
    term p x=true ↔ ∃ l : Fin 7, incident p l ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true := by
  simp only [term,neighbors,andValue,orValue,Bool.and_eq_true,Bool.or_eq_true]
  constructor
  · rintro ⟨hp,(h|h)|h⟩
    · exact ⟨p,Or.inl rfl,hp,h⟩
    · exact ⟨p-1,Or.inr (Or.inl (by abel)),hp,h⟩
    · exact ⟨p-3,Or.inr (Or.inr (by abel)),hp,h⟩
  · rintro ⟨l,hl,hp,h⟩
    refine ⟨hp,?_⟩
    rcases hl with rfl | eq | eq
    · exact Or.inl (Or.inl h)
    · have e : p-1=l := by rw [eq]; abel
      exact Or.inl (Or.inr (e ▸ h))
    · have e : p-3=l := by rw [eq]; abel
      exact Or.inr (e ▸ h)

theorem controlCorrect (x : Fin 14 → Bool) : control.eval (List.ofFn x)=true ↔ target x := by
  have dist (a p b : Bool) : both (ors a p) (ors a b) = ors a (both p b) := by
    cases a <;> cases p <;> cases b <;> rfl
  rw [output,dist]
  change ors (rest x) (term 2 x)=true ↔ _
  simp only [rest,orValue,Bool.or_eq_true,starCorrect,target]
  constructor
  · grind
  · rintro ⟨p,l,h⟩
    fin_cases p <;> grind

theorem wiring : control.size=28 ∧
    (∀ j : Fin 28,
      let g := control.gates.getD j.val ⟨.or,[]⟩
      (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 ∧ g.inputs.Nodup ∧
                    ∀ w ∈ g.inputs, w<14+j.val) ∧
    control.output=41 ∧ control.gates[27]?=some ⟨.and,[39,40]⟩ := by
  refine ⟨rfl,?_,rfl,rfl⟩
  intro j
  fin_cases j <;> first | refine ⟨Or.inl rfl,rfl,by decide,?_⟩ | refine ⟨Or.inr rfl,rfl,by decide,?_⟩
  all_goals intro w hw; simp [control,List.getD_eq_getElem?_getD] at hw ⊢; omega

theorem blindInputs : ∀ i ∈ ([0,7] : List (Fin 14)),
    let x := fun j : Fin 14 => decide (j=i)
    PEqualNP.BlindGate.wireValue control 14 x 39=false ∧
    PEqualNP.BlindGate.wireValue control 14 x 40=false := by decide +kernel


-- The same graph on the fourteen numbered raw wires.
def near (i : Fin 14) : Finset (Fin 14) :=
  match i.val with
  | 0 => {7,11,13}
  | 1 => {7,8,12}
  | 2 => {8,9,13}
  | 3 => {7,9,10}
  | 4 => {8,10,11}
  | 5 => {9,11,12}
  | 6 => {10,12,13}
  | 7 => {0,1,3}
  | 8 => {1,2,4}
  | 9 => {2,3,5}
  | 10 => {3,4,6}
  | 11 => {4,5,0}
  | 12 => {5,6,1}
  | 13 => {6,0,2}
  | _ => ∅

def offPoints : Finset (Fin 14) := {2,4,5,6}
def offLines : Finset (Fin 14) := {8,9,10,12}
def free := offPoints ∪ offLines

theorem geometry :
    (∀ a b : Fin 14, b ∈ near a ↔ a ∈ near b) ∧
    (∀ a b : Fin 14, near a ⊆ near b → a=b) ∧
    (∀ a : Fin 14, (near a).card=3) ∧
    (∀ a : Fin 14, a ∈ free ↔ 0 ∉ near a ∧ 7 ∉ near a) := by decide +kernel

def picked (b2 b4 b5 b6 b8 b9 b10 b12 : Bool) : Finset (Fin 14) :=
  (if b2 then {2} else ∅) ∪ (if b4 then {4} else ∅) ∪ (if b5 then {5} else ∅) ∪ (if b6 then {6} else ∅) ∪ (if b8 then {8} else ∅) ∪ (if b9 then {9} else ∅) ∪ (if b10 then {10} else ∅) ∪ (if b12 then {12} else ∅)

theorem smallTable : ∀ b2 b4 b5 b6 b8 b9 b10 b12 : Bool,
    let O := picked b2 b4 b5 b6 b8 b9 b10 b12
    Disjoint O (O.biUnion near) → O.card≤4 ∧ (O.card=4 → O=offPoints ∨ O=offLines) := by
  decide +kernel

theorem octagon : ∀ O ∈ free.powerset, Disjoint O (O.biUnion near) →
    O.card≤4 ∧ (O.card=4 → O=offPoints ∨ O=offLines) := by
  intro O hO dis
  let bit (i : Fin 14) := decide (i ∈ O)
  let S := picked (bit 2) (bit 4) (bit 5) (bit 6) (bit 8) (bit 9) (bit 10) (bit 12)
  have sub := Finset.mem_powerset.mp hO
  have eq : S=O := by
    ext v
    have test (j : Fin 14) : v ∈ (if j ∈ O then {j} else (∅ : Finset (Fin 14))) ↔ j ∈ O ∧ v=j := by
      by_cases h : j ∈ O <;> simp [h]
    simp only [S,picked,Finset.mem_union,bit,decide_eq_true_eq,test]
    have sv : v ∈ O → v ∈ free := fun h => sub h
    simp only [free,offPoints,offLines,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at sv
    grind only
  have h := smallTable (bit 2) (bit 4) (bit 5) (bit 6) (bit 8) (bit 9) (bit 10) (bit 12)
  change Disjoint S (S.biUnion near) → S.card≤4 ∧ (S.card=4 → S=offPoints ∨ S=offLines) at h
  rw [eq] at h
  exact h dis

abbrev Input := Fin 14 → Bool
def single (a : Fin 14) : Input := fun i => decide (i=a)
def pair (a b : Fin 14) : Input := fun i => decide (i=a ∨ i=b)
def avoids (H : Input → Bool) (O : Finset (Fin 14)) := ∀ a ∈ O, ∀ x y : Input,
  (∀ i, i≠a → x i=y i) → H x=H y

theorem forcedNeighbor (H : Input → Bool) (O : Finset (Fin 14)) (absent : avoids H O)
    (flags : ∀ a b, b ∈ near a → H (pair a b)=true)
    {a b : Fin 14} (ha : a ∈ O) (hb : b ∈ near a) : H (single b)=true := by
  rw [← absent a ha (pair a b) (single b) (fun i hi => by simp [pair,single,hi])]
  exact flags a b hb

theorem omittedShape (H : Input → Bool) (O : Finset (Fin 14)) (absent : avoids H O)
    (flags : ∀ a b, b ∈ near a → H (pair a b)=true)
    (zero : H (fun _ => false)=false)
    (pins : H (single 0)=false ∧ H (single 7)=false) :
    O.card≤4 ∧ (O.card=4 → O=offPoints ∨ O=offLines) := by
  have sub : O ⊆ free := by
    intro a ha
    apply (geometry.2.2.2 a).mpr
    constructor
    · intro hb; have := forcedNeighbor H O absent flags ha hb; simp_all
    · intro hb; have := forcedNeighbor H O absent flags ha hb; simp_all
  apply octagon O (Finset.mem_powerset.mpr sub)
  apply Finset.disjoint_left.mpr
  intro b hb h
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp h
  have t := forcedNeighbor H O absent flags ha hn
  have e := absent b hb (single b) (fun _ => false) (fun i hi => by simp [single,hi])
  simp_all

theorem partnerSingleton (H K : Input → Bool) (O : Finset (Fin 14)) (absent : avoids H O)
    (flags : ∀ a b, b ∈ near a → H (pair a b)=true)
    (cross : ∀ a b, H (single a)=true → K (single b)=true → b ∈ near a)
    {a b} (ha : a ∈ O) (hb : K (single b)=true) : b=a := by
  symm
  apply geometry.2.1 a b
  intro t ht
  exact (geometry.1 t b).mp (cross t b (forcedNeighbor H O absent flags ha ht) hb)

theorem oneFullSupport (H K : Input → Bool) (O P : Finset (Fin 14))
    (omitH : avoids H O) (omitK : avoids K P)
    (flagsH : ∀ a b, b ∈ near a → H (pair a b)=true)
    (flagsK : ∀ a b, b ∈ near a → K (pair a b)=true)
    (cross : ∀ a b, H (single a)=true → K (single b)=true → b ∈ near a) :
    O=∅ ∨ P=∅ := by
  by_cases h : O=∅
  · exact Or.inl h
  right
  obtain ⟨o,ho⟩ := Finset.nonempty_iff_ne_empty.mpr h
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have all : near p ⊆ {o} := by
    intro v hv
    exact Finset.mem_singleton.mpr (partnerSingleton H K O omitH flagsH cross ho
      (forcedNeighbor K P omitK flagsK hp hv))
  have bound := Finset.card_le_card all
  simp [geometry.2.2.1 p] at bound


theorem legalControl : PEqualNP.TopForm.IsAO2 14 control ∧
    ∀ g ∈ control.gates, g.inputs.Nodup := by
  have atGate (j : ℕ) (hj : j<control.gates.length) := wiring.2.1 (⟨j,hj⟩ : Fin 28)
  have props (g : Gate) (hg : g ∈ control.gates) :
      (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 ∧ g.inputs.Nodup := by
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    have h := atGate j hj
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  exact ⟨⟨fun g hg => (props g hg).1,fun j hj => (atGate j hj).2.2.2,
    fun g hg => (props g hg).2.1⟩,fun g hg => (props g hg).2.2⟩

-- The desk's required tests, with the gate allowance increased by one.
theorem witness28 :
    ∃ (C : Circuit) (j u v : ℕ), C.size=28 ∧ PEqualNP.TopForm.IsAO2 14 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.output=14+j ∧
      C.gates[j]?=some ⟨.and,[u,v]⟩ ∧
      (∀ p l : Fin 7, incident p l → C.eval (List.ofFn (pair (Fin.castAdd 7 p) (Fin.natAdd 7 l)))=true) ∧
      (∀ x, Maximal (fun z => ¬target z) x → C.eval (List.ofFn x)=false) ∧
      ∀ i ∈ ([0,7] : List (Fin 14)), PEqualNP.BlindGate.wireValue C 14 (single i) u=false ∧
        PEqualNP.BlindGate.wireValue C 14 (single i) v=false := by
  refine ⟨control,27,39,40,rfl,legalControl.1,legalControl.2,rfl,rfl,?_,?_,blindInputs⟩
  · intro p l h
    apply (controlCorrect _).mpr
    exact ⟨p,l,h,by simp [pair],by simp [pair]⟩
  · intro x hm
    cases hx : control.eval (List.ofFn x) with
    | false => rfl
    | true => exact (hm.1 ((controlCorrect x).mp hx)).elim

-- Raising all omitted coordinates gives the weakest first operand compatible
-- with the target, while preserving the original second operand.
def raise (O : Finset (Fin 14)) (x : Input) : Input := fun i => decide (i ∈ O) || x i

theorem unchanged (H : Input → Bool) (O : Finset (Fin 14)) (h : avoids H O) (x : Input) :
    H (raise O x)=H x := by
  induction O using Finset.induction_on with
  | empty =>
    apply congrArg H
    funext i
    simp [raise]
  | @insert a S fresh ih =>
    have t := h a (Finset.mem_insert_self a S) (raise (insert a S) x) (raise S x)
      (fun i hi => by simp [raise,hi])
    exact t.trans (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem canonicalFactor (H K F : Input → Bool) (O : Finset (Fin 14)) (absent : avoids H O)
    (factorization : ∀ x, (H x && K x)=F x)
    (mono : ∀ x y : Input, (∀ i, x i=true → y i=true) → F x=true → F y=true)
    (x : Input) : (F (raise O x) && K x)=F x := by
  have up := mono x (raise O x) (fun i hi => by simp [raise,hi])
  have old := factorization x
  have large := factorization (raise O x)
  rw [unchanged H O absent x] at large
  cases hH : H x <;> cases hK : K x <;> cases hF : F x <;> cases hU : F (raise O x) <;> simp_all


instance (x : Input) : Decidable (target x) := by unfold target; infer_instance

theorem incidencePair : ∀ a b : Fin 14, target (pair a b) ↔ b ∈ near a := by decide +kernel

def growing (H : Input → Bool) := ∀ x y : Input, (∀ i, x i=true → y i=true) →
  H x=true → H y=true

theorem factorSupports (H K : Input → Bool) (O P : Finset (Fin 14))
    (omitH : avoids H O) (omitK : avoids K P) (monH : growing H) (monK : growing K)
    (blindH : H (single 0)=false ∧ H (single 7)=false)
    (blindK : K (single 0)=false ∧ K (single 7)=false)
    (product : ∀ x, (H x=true ∧ K x=true) ↔ target x) :
    (O=∅ ∨ P=∅) ∧ O.card≤4 ∧ P.card≤4 ∧
      (O.card=4 → O=offPoints ∨ O=offLines) ∧ (P.card=4 → P=offPoints ∨ P=offLines) := by
  have flags (a b : Fin 14) (h : b ∈ near a) :=
    (product (pair a b)).mpr ((incidencePair a b).mpr h)
  have cross (a b : Fin 14) (h : H (single a)=true) (k : K (single b)=true) : b ∈ near a := by
    apply (incidencePair a b).mp
    apply (product _).mp
    exact ⟨monH _ _ (by intro i hi; simp [single] at hi; simp [pair,hi]) h,
      monK _ _ (by intro i hi; simp [single] at hi; simp [pair,hi]) k⟩
  have zero (T : Input → Bool) (m : growing T) (pin : T (single 0)=false) :
      T (fun _ => false)=false := by
    cases e : T (fun _ => false) with
    | false => rfl
    | true => have z := m _ (single 0) (by simp) e; simp_all
  have h := omittedShape H O omitH (fun a b h => (flags a b h).1) (zero H monH blindH.1) blindH
  have k := omittedShape K P omitK (fun a b h => (flags a b h).2) (zero K monK blindK.1) blindK
  exact ⟨oneFullSupport H K O P omitH omitK (fun a b h => (flags a b h).1)
    (fun a b h => (flags a b h).2) cross,h.1,k.1,h.2,k.2⟩

end FanoFinalAnd
