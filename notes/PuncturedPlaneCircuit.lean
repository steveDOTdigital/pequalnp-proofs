import PEqualNP.Defs
import FlagCrossRank
import FlagStarCircuit

namespace PuncturedPlaneCircuit
open FlagCrossRank FlagStarCircuit PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def flags : List (Fin 13 × Fin 11) := [(0,2), (0,8), (0,10), (1,3), (1,9), (2,0), (2,4), (2,10), (3,0), (3,1), (3,5), (4,1), (4,2), (4,6), (5,0), (5,2), (5,3), (5,7), (6,1), (6,3), (6,4), (6,8), (7,2), (7,4), (7,5), (7,9), (8,3), (8,5), (8,6), (8,10), (9,4), (9,6), (9,7), (10,5), (10,7), (10,8), (11,0), (11,6), (11,8), (11,9), (12,1), (12,7), (12,9), (12,10)]
def I (p : Fin 13) (l : Fin 11) := (p,l) ∈ flags
instance : DecidableRel I := fun _ _ => inferInstanceAs (Decidable (_ ∈ flags))

def target (x : (Fin 13 ⊕ Fin 11) → Bool) : Bool :=
  flags.any fun e => x (.inl e.1) && x (.inr e.2)

def fiber (v : Fin 13 ⊕ Fin 11) : Finset (Flag I) := v.elim
  (fun p => Finset.univ.filter fun e => e.val.1 = p)
  (fun l => Finset.univ.filter fun e => e.val.2 = l)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
theorem geometry :
    Fintype.card (Flag I) = 44 ∧ (∀ v, (fiber v).card ≤ 4) ∧
    (∀ e : Flag I, target (edgeBits e.val) = true) ∧
    (∀ e : Flag I, target (crossBits I e.val) = false) ∧
    (∀ v : Fin 13 ⊕ Fin 11, target (fun w => decide (w = v)) = false) := by decide +kernel

theorem formulaLower (T : FlagCrossRank.Tree (Fin 13 ⊕ Fin 11)) (correct : T.val = target) : 55 ≤ T.leaves := by
  obtain ⟨edgeCount, maxDegree, yes, cross, single⟩ := geometry
  rw [← correct] at yes cross single
  obtain ⟨K, cover, leaves⟩ := bipartiteFormula I I (fun _ _ h => h) T yes cross single
  have count := degreeCover K fiber 4 (fun v _ => maxDegree v) (by
    intro e
    rcases cover e with h | h
    · exact ⟨_, h, by simp [fiber]⟩
    · exact ⟨_, h, by simp [fiber]⟩)
  rw [edgeCount] at count leaves
  omega

def lineStar (l a b c d : Fin 24) : Expr 24 :=
  .gate false (.raw l) (.gate true (.gate true (.raw a) (.raw b)) (.gate true (.raw c) (.raw d)))

def witness : Expr 24 :=
  (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (lineStar 13 2 3 5 11) (lineStar 14 3 4 6 12)) (lineStar 15 0 4 5 7)) (lineStar 16 1 5 6 8)) (lineStar 17 2 6 7 9)) (lineStar 18 3 7 8 10)) (lineStar 19 4 8 9 11)) (lineStar 20 5 9 10 12)) (lineStar 21 0 6 10 11)) (lineStar 22 1 7 11 12)) (lineStar 23 0 2 8 12))

theorem witnessSize : witness.circuit.size = 54 := by decide +kernel
theorem witnessLegal : Monotone2 witness.circuit := by
  intro g hg
  exact ⟨(ao2 witness).1 g hg, le_of_eq ((ao2 witness).2.2 g hg)⟩

def rawTarget (x : Fin 24 → Bool) : Bool :=
  (x 0 && x 15) || (x 0 && x 21) || (x 0 && x 23) || (x 1 && x 16) || (x 1 && x 22) || (x 2 && x 13) || (x 2 && x 17) || (x 2 && x 23) || (x 3 && x 13) || (x 3 && x 14) || (x 3 && x 18) || (x 4 && x 14) || (x 4 && x 15) || (x 4 && x 19) || (x 5 && x 13) || (x 5 && x 15) || (x 5 && x 16) || (x 5 && x 20) || (x 6 && x 14) || (x 6 && x 16) || (x 6 && x 17) || (x 6 && x 21) || (x 7 && x 15) || (x 7 && x 17) || (x 7 && x 18) || (x 7 && x 22) || (x 8 && x 16) || (x 8 && x 18) || (x 8 && x 19) || (x 8 && x 23) || (x 9 && x 17) || (x 9 && x 19) || (x 9 && x 20) || (x 10 && x 18) || (x 10 && x 20) || (x 10 && x 21) || (x 11 && x 13) || (x 11 && x 19) || (x 11 && x 21) || (x 11 && x 22) || (x 12 && x 14) || (x 12 && x 20) || (x 12 && x 22) || (x 12 && x 23)

theorem upper (x : Fin 24 → Bool) : witness.circuit.eval (List.ofFn x) = rawTarget x := by
  change circuitFun 24 witness.circuit x = _
  rw [realBool]
  simp [witness, lineStar, rawTarget, Expr.val, op, GateOp.eval, Bool.and_or_distrib_right,
    Bool.and_or_distrib_left, Bool.and_comm]
  ac_rfl

end PuncturedPlaneCircuit
