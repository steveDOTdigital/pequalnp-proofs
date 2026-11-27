import PEqualNP.Defs
import FlagCrossRank
import FlagStarCircuit

namespace DeletedLine9763
open FlagCrossRank FlagStarCircuit PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def flags : List (Fin 13 × Fin 12) := [(0, 3), (0, 9), (0, 11), (1, 0), (1, 4), (1, 10), (2, 0), (2, 1), (2, 5), (2, 11), (3, 1), (3, 2), (3, 6), (4, 0), (4, 2), (4, 3), (4, 7), (5, 1), (5, 3), (5, 4), (5, 8), (6, 2), (6, 4), (6, 5), (6, 9), (7, 3), (7, 5), (7, 6), (7, 10), (8, 4), (8, 6), (8, 7), (8, 11), (9, 5), (9, 7), (9, 8), (10, 0), (10, 6), (10, 8), (10, 9), (11, 1), (11, 7), (11, 9), (11, 10), (12, 2), (12, 8), (12, 10), (12, 11)]
def I (p : Fin 13) (l : Fin 12) := (p,l) ∈ flags
instance : DecidableRel I := fun _ _ => inferInstanceAs (Decidable (_ ∈ flags))

def target (x : (Fin 13 ⊕ Fin 12) → Bool) : Bool :=
  flags.any fun e => x (.inl e.1) && x (.inr e.2)

def fiber (v : Fin 13 ⊕ Fin 12) : Finset (Flag I) := v.elim
  (fun p => Finset.univ.filter fun e => e.val.1 = p)
  (fun l => Finset.univ.filter fun e => e.val.2 = l)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
theorem geometry :
    Fintype.card (Flag I) = 48 ∧ (∀ v, (fiber v).card ≤ 4) ∧
    (∀ e : Flag I, target (edgeBits e.val) = true) ∧
    (∀ e : Flag I, target (crossBits I e.val) = false) ∧
    (∀ v : Fin 13 ⊕ Fin 12, target (fun w => decide (w = v)) = false) := by decide +kernel

theorem formulaLower (T : FlagCrossRank.Tree (Fin 13 ⊕ Fin 12)) (correct : T.val = target) : 60 ≤ T.leaves := by
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

def lineStar (l a b c d : Fin 25) : Expr 25 :=
  .gate false (.raw l) (.gate true (.gate true (.raw a) (.raw b)) (.gate true (.raw c) (.raw d)))

def witness : Expr 25 :=
  (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (lineStar 13 1 2 4 10) (lineStar 14 2 3 5 11)) (lineStar 15 3 4 6 12)) (lineStar 16 0 4 5 7)) (lineStar 17 1 5 6 8)) (lineStar 18 2 6 7 9)) (lineStar 19 3 7 8 10)) (lineStar 20 4 8 9 11)) (lineStar 21 5 9 10 12)) (lineStar 22 0 6 10 11)) (lineStar 23 1 7 11 12)) (lineStar 24 0 2 8 12))

theorem witnessSize : witness.circuit.size = 59 := by decide +kernel
theorem witnessLegal : Monotone2 witness.circuit := by
  intro g hg
  exact ⟨(ao2 witness).1 g hg, le_of_eq ((ao2 witness).2.2 g hg)⟩

def rawTarget (x : Fin 25 → Bool) : Bool :=
  (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 1 && x 13) || (x 1 && x 17) || (x 1 && x 23) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 5 && x 14) || (x 5 && x 16) || (x 5 && x 17) || (x 5 && x 21) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 8 && x 24) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23) || (x 12 && x 15) || (x 12 && x 21) || (x 12 && x 23) || (x 12 && x 24)

theorem upper (x : Fin 25 → Bool) : witness.circuit.eval (List.ofFn x) = rawTarget x := by
  change circuitFun 25 witness.circuit x = _
  rw [realBool]
  simp [witness, lineStar, rawTarget, Expr.val, op, GateOp.eval, Bool.and_or_distrib_right,
    Bool.and_or_distrib_left, Bool.and_comm]
  ac_rfl

theorem upper59 : HasCircuitSize 25 rawTarget 59 := by
  refine ⟨witness.circuit, ?_, Nat.le_of_eq witnessSize, upper⟩
  intro g hg
  have hop := (ao2 witness).1 g hg
  exact ⟨by rcases hop with h | h <;> simp [h], (witnessLegal g hg).2⟩

end DeletedLine9763
