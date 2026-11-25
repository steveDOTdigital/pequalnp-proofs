import PEqualNP.Defs
import FlagCrossRank
import FlagStarCircuit

namespace OrderFourPunctured9834
open FlagCrossRank FlagStarCircuit PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def flags : List (Fin 21 × Fin 19) := [(0,3), (0,5), (0,15), (0,18), (1,4), (1,6), (1,16), (2,0), (2,5), (2,7), (2,17), (3,0), (3,1), (3,6), (3,8), (3,18), (4,1), (4,2), (4,7), (4,9), (5,2), (5,3), (5,8), (5,10), (6,0), (6,3), (6,4), (6,9), (6,11), (7,1), (7,4), (7,5), (7,10), (7,12), (8,2), (8,5), (8,6), (8,11), (8,13), (9,3), (9,6), (9,7), (9,12), (9,14), (10,4), (10,7), (10,8), (10,13), (10,15), (11,5), (11,8), (11,9), (11,14), (11,16), (12,6), (12,9), (12,10), (12,15), (12,17), (13,7), (13,10), (13,11), (13,16), (13,18), (14,8), (14,11), (14,12), (14,17), (15,9), (15,12), (15,13), (15,18), (16,0), (16,10), (16,13), (16,14), (17,1), (17,11), (17,14), (17,15), (18,0), (18,2), (18,12), (18,15), (18,16), (19,1), (19,3), (19,13), (19,16), (19,17), (20,2), (20,4), (20,14), (20,17), (20,18)]
def I (p : Fin 21) (l : Fin 19) := (p,l) ∈ flags
instance : DecidableRel I := fun _ _ => inferInstanceAs (Decidable (_ ∈ flags))

def target (x : (Fin 21 ⊕ Fin 19) → Bool) : Bool :=
  flags.any fun e => x (.inl e.1) && x (.inr e.2)

def fiber (v : Fin 21 ⊕ Fin 19) : Finset (Flag I) := v.elim
  (fun p => Finset.univ.filter fun e => e.val.1 = p)
  (fun l => Finset.univ.filter fun e => e.val.2 = l)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
theorem geometry :
    Fintype.card (Flag I) = 95 ∧ (∀ v, (fiber v).card ≤ 5) ∧
    (∀ e : Flag I, target (edgeBits e.val) = true) ∧
    (∀ e : Flag I, target (crossBits I e.val) = false) ∧
    (∀ v : Fin 21 ⊕ Fin 19, target (fun w => decide (w = v)) = false) := by decide +kernel

theorem formulaLower (T : FlagCrossRank.Tree (Fin 21 ⊕ Fin 19)) (correct : T.val = target) : 114 ≤ T.leaves := by
  obtain ⟨edgeCount, maxDegree, yes, cross, single⟩ := geometry
  rw [← correct] at yes cross single
  obtain ⟨K, cover, leaves⟩ := bipartiteFormula I I (fun _ _ h => h) T yes cross single
  have count := degreeCover K fiber 5 (fun v _ => maxDegree v) (by
    intro e
    rcases cover e with h | h
    · exact ⟨_, h, by simp [fiber]⟩
    · exact ⟨_, h, by simp [fiber]⟩)
  rw [edgeCount] at count leaves
  omega

def lineStar (l a b c d e : Fin 40) : Expr 40 :=
  .gate false (.raw l) (.gate true (.gate true (.raw a) (.raw b))
    (.gate true (.raw c) (.gate true (.raw d) (.raw e))))

def witness : Expr 40 :=
  (.gate true (.gate true (.gate true (.gate true (lineStar 21 2 3 6 16 18) (lineStar 22 3 4 7 17 19)) (.gate true (lineStar 23 4 5 8 18 20) (lineStar 24 0 5 6 9 19))) (.gate true (.gate true (lineStar 25 1 6 7 10 20) (lineStar 26 0 2 7 8 11)) (.gate true (lineStar 27 1 3 8 9 12) (.gate true (lineStar 28 2 4 9 10 13) (lineStar 29 3 5 10 11 14))))) (.gate true (.gate true (.gate true (lineStar 30 4 6 11 12 15) (lineStar 31 5 7 12 13 16)) (.gate true (lineStar 32 6 8 13 14 17) (.gate true (lineStar 33 7 9 14 15 18) (lineStar 34 8 10 15 16 19)))) (.gate true (.gate true (lineStar 35 9 11 16 17 20) (lineStar 36 0 10 12 17 18)) (.gate true (lineStar 37 1 11 13 18 19) (.gate true (lineStar 38 2 12 14 19 20) (lineStar 39 0 3 13 15 20))))))

theorem witnessSize : witness.circuit.size = 113 := by decide +kernel
theorem witnessLegal : Monotone2 witness.circuit := by
  intro g hg
  exact ⟨(ao2 witness).1 g hg, le_of_eq ((ao2 witness).2.2 g hg)⟩

def rawTarget (x : Fin 40 → Bool) : Bool :=
  (x 0 && x 24) || (x 0 && x 26) || (x 0 && x 36) || (x 0 && x 39) || (x 1 && x 25) || (x 1 && x 27) || (x 1 && x 37) || (x 2 && x 21) || (x 2 && x 26) || (x 2 && x 28) || (x 2 && x 38) || (x 3 && x 21) || (x 3 && x 22) || (x 3 && x 27) || (x 3 && x 29) || (x 3 && x 39) || (x 4 && x 22) || (x 4 && x 23) || (x 4 && x 28) || (x 4 && x 30) || (x 5 && x 23) || (x 5 && x 24) || (x 5 && x 29) || (x 5 && x 31) || (x 6 && x 21) || (x 6 && x 24) || (x 6 && x 25) || (x 6 && x 30) || (x 6 && x 32) || (x 7 && x 22) || (x 7 && x 25) || (x 7 && x 26) || (x 7 && x 31) || (x 7 && x 33) || (x 8 && x 23) || (x 8 && x 26) || (x 8 && x 27) || (x 8 && x 32) || (x 8 && x 34) || (x 9 && x 24) || (x 9 && x 27) || (x 9 && x 28) || (x 9 && x 33) || (x 9 && x 35) || (x 10 && x 25) || (x 10 && x 28) || (x 10 && x 29) || (x 10 && x 34) || (x 10 && x 36) || (x 11 && x 26) || (x 11 && x 29) || (x 11 && x 30) || (x 11 && x 35) || (x 11 && x 37) || (x 12 && x 27) || (x 12 && x 30) || (x 12 && x 31) || (x 12 && x 36) || (x 12 && x 38) || (x 13 && x 28) || (x 13 && x 31) || (x 13 && x 32) || (x 13 && x 37) || (x 13 && x 39) || (x 14 && x 29) || (x 14 && x 32) || (x 14 && x 33) || (x 14 && x 38) || (x 15 && x 30) || (x 15 && x 33) || (x 15 && x 34) || (x 15 && x 39) || (x 16 && x 21) || (x 16 && x 31) || (x 16 && x 34) || (x 16 && x 35) || (x 17 && x 22) || (x 17 && x 32) || (x 17 && x 35) || (x 17 && x 36) || (x 18 && x 21) || (x 18 && x 23) || (x 18 && x 33) || (x 18 && x 36) || (x 18 && x 37) || (x 19 && x 22) || (x 19 && x 24) || (x 19 && x 34) || (x 19 && x 37) || (x 19 && x 38) || (x 20 && x 23) || (x 20 && x 25) || (x 20 && x 35) || (x 20 && x 38) || (x 20 && x 39)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem upper (x : Fin 40 → Bool) : witness.circuit.eval (List.ofFn x) = rawTarget x := by
  change circuitFun 40 witness.circuit x = _
  rw [realBool]
  simp [witness, lineStar, rawTarget, Expr.val, op, GateOp.eval, Bool.and_or_distrib_right,
    Bool.and_or_distrib_left, Bool.and_comm]
  ac_rfl

theorem formulaTarget (x : Fin 40 → Bool) :
    target (Sum.elim (fun p => x ⟨p.val, by omega⟩)
      (fun l => x ⟨21 + l.val, by omega⟩)) = rawTarget x := by
  simp [target, flags, rawTarget, List.any_cons, Bool.or_assoc]

end OrderFourPunctured9834
