import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic

open Finset

namespace EqualityFrontier33619

def advance {Wire : Type} [DecidableEq Wire] (dependencies : Wire → Finset Wire)
    (gate : Wire) (wires : Finset Wire) : Finset Wire :=
  if gate ∈ wires then wires.erase gate ∪ dependencies gate else wires

def unfoldFrontier {Wire : Type} [DecidableEq Wire] (dependencies : Wire → Finset Wire)
    (gates : List Wire) (wires : Finset Wire) : Finset Wire :=
  match gates with
  | [] => wires
  | gate :: rest => unfoldFrontier dependencies rest (advance dependencies gate wires)

def binaryFresh {Wire : Type} [DecidableEq Wire] (dependencies : Wire → Finset Wire)
    (gates : List Wire) (wires : Finset Wire) : Prop :=
  match gates with
  | [] => True
  | gate :: rest =>
    gate ∈ wires ∧ (dependencies gate).card = 2 ∧
      Disjoint (wires.erase gate) (dependencies gate) ∧
      binaryFresh dependencies rest (advance dependencies gate wires)

theorem advanceSize {Wire : Type} [DecidableEq Wire] (dependencies : Wire → Finset Wire)
    (gate : Wire) (wires : Finset Wire) (fanIn : (dependencies gate).card ≤ 2) :
    (advance dependencies gate wires).card ≤ wires.card + 1 := by
  by_cases active : gate ∈ wires
  · simp only [advance, ite_eq_left active]
    have undo := Finset.card_erase_add_one active
    have union := Finset.card_union_le (wires.erase gate) (dependencies gate)
    omega
  · simp [advance,active]

theorem frontierSize {Wire : Type} [DecidableEq Wire] (dependencies : Wire → Finset Wire)
    (fanIn : ∀ gate, (dependencies gate).card ≤ 2) (gates : List Wire) (wires : Finset Wire) :
    (unfoldFrontier dependencies gates wires).card ≤ wires.card + gates.length := by
  induction gates generalizing wires with
  | nil => simp [unfoldFrontier]
  | cons gate rest ih =>
    have step := advanceSize dependencies gate wires (fanIn gate)
    have tail := ih (advance dependencies gate wires)
    simp only [unfoldFrontier, List.length_cons]
    omega

theorem saturatedFrontier {Wire : Type} [DecidableEq Wire] (dependencies : Wire → Finset Wire)
    (fanIn : ∀ gate, (dependencies gate).card ≤ 2) (gates : List Wire) (wires : Finset Wire)
    (saturated : wires.card + gates.length ≤ (unfoldFrontier dependencies gates wires).card) :
    binaryFresh dependencies gates wires := by
  induction gates generalizing wires with
  | nil => trivial
  | cons gate rest ih =>
    have tail := frontierSize dependencies fanIn rest (advance dependencies gate wires)
    have step := advanceSize dependencies gate wires (fanIn gate)
    simp only [unfoldFrontier, List.length_cons] at saturated
    have equality : (advance dependencies gate wires).card = wires.card + 1 := by omega
    have active : gate ∈ wires := by
      by_contra inactive
      simp [advance,inactive] at equality
    have undo := Finset.card_erase_add_one active
    have balance := Finset.card_union_add_card_inter (wires.erase gate) (dependencies gate)
    have bound := fanIn gate
    simp only [advance, ite_eq_left active] at equality
    have arity : (dependencies gate).card = 2 := by omega
    have noCommon : ((wires.erase gate) ∩ dependencies gate).card = 0 := by omega
    have separated : Disjoint (wires.erase gate) (dependencies gate) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp noCommon)
    exact ⟨active,arity,separated,ih _ (by omega)⟩

#print axioms saturatedFrontier

end EqualityFrontier33619

open Finset

namespace EqualityFrontier33619

variable {Wire : Type} [DecidableEq Wire] {Value : Type}

def agreesOn (wires : Finset Wire) (x y : Wire → Value) : Prop :=
  ∀ wire ∈ wires, x wire = y wire

def evalGates (evaluate : Wire → (Wire → Value) → Value)
    (gates : List Wire) (initial : Wire → Value) : Wire → Value :=
  match gates with
  | [] => initial
  | gate :: rest =>
    let prior := evalGates evaluate rest initial
    Function.update prior gate (evaluate gate prior)

theorem agreementAfterUpdate (dependencies : Wire → Finset Wire)
    (evaluate : Wire → (Wire → Value) → Value)
    (locality : ∀ gate (x y : Wire → Value), agreesOn (dependencies gate) x y → evaluate gate x = evaluate gate y)
    (gate : Wire) (wires : Finset Wire) (x y : Wire → Value)
    (prior : agreesOn (advance dependencies gate wires) x y) :
    agreesOn wires (Function.update x gate (evaluate gate x)) (Function.update y gate (evaluate gate y)) := by
  intro wire member
  by_cases same : wire = gate
  · subst wire
    simp only [Function.update_self]
    apply locality
    intro i hi
    apply prior
    simp only [advance, ite_eq_left member]
    exact Finset.mem_union_right _ hi
  · simp only [Function.update_of_ne same]
    apply prior
    by_cases active : gate ∈ wires
    · simp only [advance, ite_eq_left active]
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨same,member⟩)
    · simpa [advance,active] using member

theorem agreementAfterGates (dependencies : Wire → Finset Wire)
    (evaluate : Wire → (Wire → Value) → Value)
    (locality : ∀ gate (x y : Wire → Value), agreesOn (dependencies gate) x y → evaluate gate x = evaluate gate y)
    (gates : List Wire) (wires : Finset Wire) (x y : Wire → Value)
    (prior : agreesOn (unfoldFrontier dependencies gates wires) x y) :
    agreesOn wires (evalGates evaluate gates x) (evalGates evaluate gates y) := by
  induction gates generalizing wires with
  | nil => exact prior
  | cons gate rest ih =>
    exact agreementAfterUpdate dependencies evaluate locality gate wires _ _
      (ih (advance dependencies gate wires) prior)

theorem necessaryInput (dependencies : Wire → Finset Wire)
    (evaluate : Wire → (Wire → Value) → Value)
    (locality : ∀ gate (x y : Wire → Value), agreesOn (dependencies gate) x y → evaluate gate x = evaluate gate y)
    (gates : List Wire) (output input : Wire) (x y : Wire → Value)
    (sameElsewhere : ∀ wire, wire ≠ input → x wire = y wire)
    (different : evalGates evaluate gates x output ≠ evalGates evaluate gates y output) :
    input ∈ unfoldFrontier dependencies gates {output} := by
  by_contra absent
  apply different
  exact agreementAfterGates dependencies evaluate locality gates {output} x y
    (fun wire hw => sameElsewhere wire (fun eq => absent (eq ▸ hw))) output (by simp)

#print axioms necessaryInput

end EqualityFrontier33619

open Finset

namespace EqualityFrontier33619

def descendingGates (inputs : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => (inputs+k) :: descendingGates inputs k

theorem numberOfGates (inputs gates : ℕ) : (descendingGates inputs gates).length = gates := by
  induction gates with
  | zero => rfl
  | succ k ih => simp [descendingGates,ih]

theorem advanceBelow (dependencies : ℕ → Finset ℕ)
    (earlier : ∀ gate, ∀ predecessor ∈ dependencies gate, predecessor < gate)
    (gate : ℕ) (wires : Finset ℕ) (bounded : ∀ wire ∈ wires, wire < gate+1) :
    ∀ wire ∈ advance dependencies gate wires, wire < gate := by
  intro wire member
  by_cases active : gate ∈ wires
  · rw [advance, ite_eq_left active] at member
    rcases Finset.mem_union.mp member with old | new
    · have oldPair := Finset.mem_erase.mp old
      have before := bounded wire oldPair.2
      omega
    · exact earlier gate wire new
  · rw [advance, ite_eq_right active] at member
    have different : wire ≠ gate := fun eq => active (eq ▸ member)
    have before := bounded wire member
    omega

theorem inputsOnly (dependencies : ℕ → Finset ℕ)
    (earlier : ∀ gate, ∀ predecessor ∈ dependencies gate, predecessor < gate)
    (inputs gates : ℕ) (wires : Finset ℕ)
    (bounded : ∀ wire ∈ wires, wire < inputs+gates) :
    ∀ wire ∈ unfoldFrontier dependencies (descendingGates inputs gates) wires, wire < inputs := by
  induction gates generalizing wires with
  | zero => simpa [descendingGates,unfoldFrontier] using bounded
  | succ k ih =>
    change ∀ wire ∈ unfoldFrontier dependencies (descendingGates inputs k)
      (advance dependencies (inputs+k) wires), wire < inputs
    exact ih _ (advanceBelow dependencies earlier (inputs+k) wires bounded)

theorem allStepsBinary (dependencies : ℕ → Finset ℕ)
    (fanIn : ∀ gate, (dependencies gate).card ≤ 2) (inputs gates output : ℕ)
    (budget : gates+1 ≤ inputs)
    (necessary : ∀ i < inputs, i ∈ unfoldFrontier dependencies (descendingGates inputs gates) {output}) :
    binaryFresh dependencies (descendingGates inputs gates) {output} := by
  have contain : Finset.range inputs ⊆ unfoldFrontier dependencies (descendingGates inputs gates) {output} := by
    intro i hi
    exact necessary i (Finset.mem_range.mp hi)
  have lower := Finset.card_le_card contain
  rw [Finset.card_range] at lower
  apply saturatedFrontier dependencies fanIn
  rw [Finset.card_singleton,numberOfGates]
  omega

#print axioms inputsOnly
#print axioms allStepsBinary

end EqualityFrontier33619

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset

namespace EqualityFrontier33619

def gateAt (C : Circuit) (inputs wire : ℕ) : Gate :=
  C.gates.getD (wire-inputs) ⟨.or, []⟩

def circuitDependencies (C : Circuit) (inputs wire : ℕ) : Finset ℕ :=
  (gateAt C inputs wire).inputs.toFinset.filter (fun i => i < wire)

def gateValue (C : Circuit) (inputs wire : ℕ) (values : ℕ → Bool) : Bool :=
  let gate := gateAt C inputs wire
  gate.op.eval (gate.inputs.map (fun i => if i < wire then values i else false))

theorem circuitLocality (C : Circuit) (inputs wire : ℕ) (x y : ℕ → Bool)
    (agreement : agreesOn (circuitDependencies C inputs wire) x y) :
    gateValue C inputs wire x = gateValue C inputs wire y := by
  apply congrArg (gateAt C inputs wire).op.eval
  apply List.map_congr_left
  intro i inList
  by_cases earlier : i < wire
  · have equal := agreement i (by simpa [circuitDependencies,earlier] using inList)
    simp [earlier,equal]
  · simp [earlier]

theorem gateInputs (C : Circuit) (mono : Monotone2 C) (inputs wire : ℕ) :
    (circuitDependencies C inputs wire).card ≤ 2 := by
  have arity : (gateAt C inputs wire).inputs.length ≤ 2 := by
    unfold gateAt
    by_cases inCircuit : wire-inputs < C.gates.length
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inCircuit] using
        (mono C.gates[wire-inputs] (List.getElem_mem _)).2
    · simp [List.getD, List.getElem?_eq_none (by omega : C.gates.length ≤ wire-inputs)]
  apply le_trans (Finset.card_filter_le _ _)
  exact (List.toFinset_card_le _).trans arity

def pushGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

theorem gateListLength (gs : List Gate) (x : List Bool) :
    (gs.foldl pushGate x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [pushGate]
    omega

theorem wireAppend (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = Function.update (fun j => w.getD j false) w.length v i := by
  by_cases before : i < w.length
  · rw [Function.update_of_ne (by omega : i ≠ w.length)]
    simp [List.getD, List.getElem?_append_left before]
  · rw [List.getD, List.getElem?_append_right (by omega : w.length ≤ i)]
    by_cases last : i = w.length
    · subst i
      simp
    · rw [Function.update_of_ne last]
      have beyond : 1 ≤ i-w.length := by omega
      rw [List.getD, List.getElem?_eq_none (by omega : w.length ≤ i),
        List.getElem?_eq_none (by simpa using beyond : [v].length ≤ i-w.length)]

theorem circuitPrefixValues (C : Circuit) (x : List Bool) (k : ℕ) (valid : k ≤ C.gates.length) :
    evalGates (gateValue C x.length) (descendingGates x.length k) (fun i => x.getD i false) =
      (fun i => ((C.gates.take k).foldl pushGate x).getD i false) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have prior : k ≤ C.gates.length := by omega
    have within : k < C.gates.length := by omega
    simp only [descendingGates, evalGates]
    rw [ih prior, List.take_succ_eq_append_getElem within, List.foldl_append]
    let w := (C.gates.take k).foldl pushGate x
    have lengthW : w.length = x.length+k := by
      simp [w, gateListLength, List.length_take, min_eq_left prior]
    let g : Gate := C.gates[k]
    have sameGate : gateAt C x.length (x.length+k) = g := by
      simp [gateAt,g,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem within]
    have masked : (g.inputs.map (fun i => if i < x.length+k then w.getD i false else false)) =
        g.inputs.map (fun i => w.getD i false) := by
      apply List.map_congr_left
      intro i _
      by_cases before : i < x.length+k
      · simp [before]
      · simp [before, List.getD, List.getElem?_eq_none (by omega : w.length ≤ i)]
    change Function.update (fun i => w.getD i false) (x.length+k)
      (gateValue C x.length (x.length+k) (fun i => w.getD i false)) =
      (fun i => (pushGate w g).getD i false)
    unfold gateValue pushGate
    simp only [sameGate, masked]
    funext i
    rw [wireAppend, lengthW]

theorem circuitOutput (C : Circuit) (x : List Bool) :
    evalGates (gateValue C x.length) (descendingGates x.length C.size) (fun i => x.getD i false) C.output =
      C.eval x := by
  obtain eq := congrFun (circuitPrefixValues C x C.size (by rfl)) C.output
  change _ = (C.gates.foldl pushGate x).getD C.output false
  simpa [Circuit.size] using eq

#print axioms circuitOutput

end EqualityFrontier33619

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace EqualityFrontier33619

theorem circuitBinaryFrontier (C : Circuit) (mono : Monotone2 C) (m : ℕ)
    (size : C.size+1 ≤ m)
    (essential : ∀ i < m, ∃ x y : List Bool, x.length = m ∧ y.length = m ∧
      (∀ j, j ≠ i → x.getD j false = y.getD j false) ∧ C.eval x ≠ C.eval y) :
    binaryFresh (circuitDependencies C m) (descendingGates m C.size) {C.output} := by
  apply allStepsBinary (circuitDependencies C m) (gateInputs C mono m) m C.size C.output size
  intro i hi
  obtain ⟨x,y,lx,ly,except,changed⟩ := essential i hi
  have left := circuitOutput C x
  have right := circuitOutput C y
  rw [lx] at left
  rw [ly] at right
  apply necessaryInput (circuitDependencies C m) (gateValue C m) (circuitLocality C m)
    (descendingGates m C.size) C.output i (fun j => x.getD j false) (fun j => y.getD j false) except
  rw [left,right]
  exact changed

#print axioms circuitBinaryFrontier

end EqualityFrontier33619
