import PEqualNP.Outside.L_meta_8451
import PEqualNP.Outside.L_meta_8515
import PEqualNP.Outside.L_meta_8517
import PEqualNP.Outside.L_meta_8525

namespace NineVertex11010
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8451.Bow
open PEqualNP.Outside.L_meta_8451.Maj.Helpers.Readers

def graph (x : Fin 9 → Bool) : Bool := (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 5 && x 8) || (x 6 && x 8)

def circuit : Circuit := ⟨[
  ⟨.or, [0,1]⟩,
  ⟨.and, [5,9]⟩,
  ⟨.or, [2,3]⟩,
  ⟨.and, [6,11]⟩,
  ⟨.or, [0,2]⟩,
  ⟨.or, [13,4]⟩,
  ⟨.and, [7,14]⟩,
  ⟨.or, [1,3]⟩,
  ⟨.or, [16,4]⟩,
  ⟨.or, [17,5]⟩,
  ⟨.or, [18,6]⟩,
  ⟨.and, [8,19]⟩,
  ⟨.or, [10,12]⟩,
  ⟨.or, [21,15]⟩,
  ⟨.or, [22,20]⟩], 23⟩

theorem upper : HasCircuitSize 9 graph 15 := by
  refine ⟨circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | decide +kernel
  · decide +kernel

def leaf (i : Fin 5) : Fin 9 := ⟨i.val, by omega⟩

def neighbor (i : Fin 5) : Fin 9 := ![5,5,6,6,7] i

theorem sensitive (i : Fin 5) : Dep graph (leaf i) := by
  refine ⟨fun j => decide (j = neighbor i), ?_⟩
  fin_cases i <;> decide +kernel

theorem pinNonconstant (i : Fin 5) (b : Bool) : ∃ x y : Fin 9 → Bool,
    graph (Function.update x (leaf i) b) ≠ graph (Function.update y (leaf i) b) := by
  refine ⟨fun _ => false, fun j => decide (j = 5 ∨ j = 8), ?_⟩
  fin_cases i <;> cases b <;> decide +kernel

theorem pin0 (s : ℕ) (h : HasCircuitSize 9 (fun x => graph (Function.update x 0 false)) s) : 13 ≤ s := by
  let labels : Fin 9 → Fin 8 := ![0, 3, 6, 2, 5, 4, 1, 7, 0]
  have smaller := relabel_size labels _ s h
  have eq : (fun x : Fin 8 → Bool => graph (Function.update (x ∘ labels) 0 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)) := by
    funext x
    simp [graph, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  exact PEqualNP.Outside.L_meta_8515 s smaller

theorem pin1 (s : ℕ) (h : HasCircuitSize 9 (fun x => graph (Function.update x 1 false)) s) : 13 ≤ s := by
  let labels : Fin 9 → Fin 8 := ![7, 0, 5, 2, 3, 4, 1, 6, 0]
  have smaller := relabel_size labels _ s h
  have eq : (fun x : Fin 8 → Bool => graph (Function.update (x ∘ labels) 1 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 6 && x 7)) := by
    funext x
    simp [graph, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  exact PEqualNP.Outside.L_meta_8525 s smaller

theorem pin2 (s : ℕ) (h : HasCircuitSize 9 (fun x => graph (Function.update x 2 false)) s) : 13 ≤ s := by
  let labels : Fin 9 → Fin 8 := ![6, 2, 0, 3, 5, 1, 4, 7, 0]
  have smaller := relabel_size labels _ s h
  have eq : (fun x : Fin 8 → Bool => graph (Function.update (x ∘ labels) 2 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)) := by
    funext x
    simp [graph, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  exact PEqualNP.Outside.L_meta_8515 s smaller

theorem pin3 (s : ℕ) (h : HasCircuitSize 9 (fun x => graph (Function.update x 3 false)) s) : 13 ≤ s := by
  let labels : Fin 9 → Fin 8 := ![5, 2, 7, 0, 3, 1, 4, 6, 0]
  have smaller := relabel_size labels _ s h
  have eq : (fun x : Fin 8 → Bool => graph (Function.update (x ∘ labels) 3 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 6 && x 7)) := by
    funext x
    simp [graph, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  exact PEqualNP.Outside.L_meta_8525 s smaller

theorem pin4 (s : ℕ) (h : HasCircuitSize 9 (fun x => graph (Function.update x 4 false)) s) : 13 ≤ s := by
  let labels : Fin 9 → Fin 8 := ![5, 2, 6, 4, 0, 1, 3, 7, 0]
  have smaller := relabel_size labels _ s h
  have eq : (fun x : Fin 8 → Bool => graph (Function.update (x ∘ labels) 4 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 7) || (x 6 && x 7)) := by
    funext x
    simp [graph, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  exact PEqualNP.Outside.L_meta_8517 s smaller

theorem lowPin (i : Fin 5) (s : ℕ) (h : HasCircuitSize 9 (fun x => graph (Function.update x (leaf i) false)) s) : 13 ≤ s := by
  fin_cases i
  · exact pin0 s h
  · exact pin1 s h
  · exact pin2 s h
  · exact pin3 s h
  · exact pin4 s h

theorem lower (s : ℕ) (h : HasCircuitSize 9 graph s) : 14 ≤ s := by
  obtain ⟨t, saved, pin⟩ := one_gate_at 8 graph (leaf 0) false s (sensitive 0) (pinNonconstant 0 false) h
  have := lowPin 0 t pin
  omega

theorem uniqueReader (gs : List Gate) (o : ℕ) (L : Least 9 graph gs o)
    (budget : gs.length ≤ 14) (i : Fin 5) : ∃! q : ℕ, Reads gs q (leaf i) := by
  obtain ⟨q, hq⟩ := L.dep_read (leaf i) (sensitive i) (pinNonconstant i)
  refine ⟨q, hq, ?_⟩
  intro p hp
  by_contra ne
  obtain ⟨s, paid, h⟩ := L.save2 (leaf i) false (pinNonconstant i false) p q ne
    (rc_input false hp) (rc_input false hq)
  have := lowPin i s h
  omega

#print axioms upper
#print axioms lower
#print axioms uniqueReader
end NineVertex11010
