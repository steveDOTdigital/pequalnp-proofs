import PEqualNP.Outside.L_meta_8439
import PEqualNP.Outside.L_meta_8451

namespace NineVertex10831
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8451.Bow

def graph (x : Fin 9 → Bool) : Bool := (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)

def circuit : Circuit := ⟨[
  ⟨.or, [4,6]⟩,
  ⟨.or, [9,7]⟩,
  ⟨.and, [0,10]⟩,
  ⟨.or, [5,6]⟩,
  ⟨.and, [1,12]⟩,
  ⟨.or, [6,8]⟩,
  ⟨.and, [2,14]⟩,
  ⟨.or, [3,4]⟩,
  ⟨.and, [7,16]⟩,
  ⟨.or, [3,5]⟩,
  ⟨.and, [8,18]⟩,
  ⟨.or, [11,13]⟩,
  ⟨.or, [20,15]⟩,
  ⟨.or, [21,17]⟩,
  ⟨.or, [22,19]⟩], 23⟩

theorem upper : HasCircuitSize 9 graph 15 := by
  refine ⟨circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | decide +kernel
  · decide +kernel

theorem lower (s : ℕ) (h : HasCircuitSize 9 graph s) : 14 ≤ s := by
  have dep : ∃ x : Fin 9 → Bool, graph (Function.update x 3 (!x 3)) ≠ graph x :=
    ⟨fun i => decide (i = 7), by decide +kernel⟩
  have nc : ∃ x y : Fin 9 → Bool,
      graph (Function.update x 3 false) ≠ graph (Function.update y 3 false) :=
    ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 4), by decide +kernel⟩
  obtain ⟨t, saved, pin⟩ := one_gate_at 8 graph 3 false s dep nc h
  let labels : Fin 9 → Fin 8 := ![0, 4, 5, 0, 1, 6, 3, 2, 7]
  have smaller := relabel_size labels _ t pin
  have eq : (fun x : Fin 8 → Bool => graph (Function.update (x ∘ labels) 3 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)) := by
    funext x
    simp [graph, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  have bound := PEqualNP.Outside.L_meta_8439 t smaller
  omega

def probe (j k : Fin 9) (b : Bool) (t : Fin 9) : Bool := decide (t = k) || (b && decide (t = j))

theorem raw_exposure : ∀ i j : Fin 9, i ≠ j → ∀ b : Bool, ∃ k : Fin 9,
    probe j k b j = b ∧ graph (Function.update (probe j k b) i true) ≠
      graph (Function.update (probe j k b) i false) := by decide +kernel

#print axioms raw_exposure
#print axioms lower
#print axioms upper
end NineVertex10831
