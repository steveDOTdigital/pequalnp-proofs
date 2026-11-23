import Mathlib
import PEqualNP.Defs

namespace NineVertexSixStars

open PEqualNP.AndCount AndCountCircuit

def edges : List (Nat × Nat) :=
  [(0,1), (0,2), (1,3), (1,4), (2,5), (2,6), (3,5),
   (3,7), (4,6), (4,8), (5,7), (6,8), (7,8)]

abbrev graph := SimpleGraph.fromRel (fun a b : Fin 9 => (a.val,b.val) ∈ edges)

def center : Fin 6 → Fin 9 := ![0,2,3,4,6,7]

def circuit : AndCountCircuit 9 where
  size := 6
  leftVars i := {center i}
  rightVars i := Finset.univ.filter fun v => graph.Adj (center i) v
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

theorem wellFormed : circuit.WellFormed := by
  intro i
  constructor <;> intro j hj <;> exact False.elim (Finset.notMem_empty j hj)

theorem covers : ∀ u v, graph.Adj u v → (∃ i, center i = u) ∨ (∃ i, center i = v) := by
  decide +kernel

theorem computes (U : Finset (Fin 9)) :
    circuit.eval U = true ↔ ∃ a ∈ U, ∃ b ∈ U, graph.Adj a b := by
  have evaluated : circuit.eval U = true ↔
      ∃ i : Fin 6, center i ∈ U ∧ ∃ v ∈ U, graph.Adj (center i) v := by
    have gate (i : Fin 6) : circuit.gateVal U i = true ↔
        center i ∈ U ∧ ∃ v ∈ U, graph.Adj (center i) v := by
      change (sideTrue U {center i} ∅ i _ && sideTrue U
        (Finset.univ.filter fun v => graph.Adj (center i) v) ∅ i _) = true ↔ _
      simp only [Bool.and_eq_true, sideTrue, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, or_false,
        Finset.mem_singleton, exists_eq_left, Finset.mem_filter, Finset.mem_univ, true_and]
      grind
    rw [eval, decide_eq_true_eq]
    change ((∃ v ∈ (∅ : Finset (Fin 9)), v ∈ U) ∨
      ∃ i ∈ (Finset.univ : Finset (Fin 6)), circuit.gateVal U i = true) ↔ _
    simp [gate]
  rw [evaluated]
  constructor
  · rintro ⟨i, hc, v, hv, edge⟩
    exact ⟨center i, hc, v, hv, edge⟩
  · rintro ⟨a, ha, b, hb, edge⟩
    rcases covers a b edge with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨i, ha, b, hb, edge⟩
    · exact ⟨i, hb, a, ha, edge.symm⟩

theorem partial_spec (I : Finset (Fin 9))
    (independent : ∀ a ∈ I, ∀ b ∈ I, ¬ graph.Adj a b)
    (maximal : ∀ w, w ∉ I → ∃ a ∈ I, graph.Adj a w) :
    circuit.eval I = false ∧ ∀ w, w ∉ I → circuit.eval (insert w I) = true := by
  constructor
  · cases h : circuit.eval I with
    | false => rfl
    | true =>
      obtain ⟨a,ha,b,hb,edge⟩ := (computes I).mp h
      exact False.elim (independent a ha b hb edge)
  · intro w hw
    obtain ⟨a, ha, edge⟩ := maximal w hw
    exact (computes _).mpr ⟨a, Finset.mem_insert_of_mem ha, w, Finset.mem_insert_self _ _, edge⟩

theorem six_suffice : ∃ C : AndCountCircuit 9, C.size = 6 ∧ C.WellFormed ∧
    ∀ I : Finset (Fin 9), (∀ a ∈ I, ∀ b ∈ I, ¬ graph.Adj a b) →
      (∀ w, w ∉ I → ∃ a ∈ I, graph.Adj a w) →
        C.eval I = false ∧ ∀ w, w ∉ I → C.eval (insert w I) = true :=
  ⟨circuit, rfl, wellFormed, partial_spec⟩

end NineVertexSixStars
