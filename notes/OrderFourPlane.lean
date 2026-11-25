import PEqualNP.Defs
import FlagCrossRank
import FlagStarCircuit
import OneShorePairRank

set_option maxRecDepth 64000
set_option maxHeartbeats 8000000

namespace OrderFourPlane
open FlagCrossRank FlagStarCircuit PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def flags : List (Fin 21 × Fin 20) := [(0,4), (0,6), (0,16), (0,19), (1,0), (1,5), (1,7), (1,17), (2,0), (2,1), (2,6), (2,8), (2,18), (3,1), (3,2), (3,7), (3,9), (3,19), (4,2), (4,3), (4,8), (4,10), (5,0), (5,3), (5,4), (5,9), (5,11), (6,1), (6,4), (6,5), (6,10), (6,12), (7,2), (7,5), (7,6), (7,11), (7,13), (8,3), (8,6), (8,7), (8,12), (8,14), (9,4), (9,7), (9,8), (9,13), (9,15), (10,5), (10,8), (10,9), (10,14), (10,16), (11,6), (11,9), (11,10), (11,15), (11,17), (12,7), (12,10), (12,11), (12,16), (12,18), (13,8), (13,11), (13,12), (13,17), (13,19), (14,9), (14,12), (14,13), (14,18), (15,0), (15,10), (15,13), (15,14), (15,19), (16,1), (16,11), (16,14), (16,15), (17,0), (17,2), (17,12), (17,15), (17,16), (18,1), (18,3), (18,13), (18,16), (18,17), (19,2), (19,4), (19,14), (19,17), (19,18), (20,3), (20,5), (20,15), (20,18), (20,19)]
def pointMask : Fin 21 → Nat := ![589904, 131233, 262467, 524934, 1292, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 274944, 549889, 51202, 102405, 204810, 409620, 819240]
def I (p : Fin 21) (l : Fin 20) := (pointMask p).testBit l.val = true
instance : DecidableRel I := fun _ _ => inferInstanceAs (Decidable (_ = true))

def target (x : (Fin 21 ⊕ Fin 20) → Bool) : Bool :=
  flags.any fun e => x (.inl e.1) && x (.inr e.2)

def fiber (v : Fin 21 ⊕ Fin 20) : Finset (Flag I) := v.elim
  (fun p => Finset.univ.filter fun e => e.val.1 = p)
  (fun l => Finset.univ.filter fun e => e.val.2 = l)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
theorem geometry :
    Fintype.card (Flag I) = 100 ∧ (∀ v, (fiber v).card ≤ 5) ∧
    (∀ e : Flag I, target (edgeBits e.val) = true) ∧
    (∀ e : Flag I, target (crossBits I e.val) = false) ∧
    (∀ v : Fin 21 ⊕ Fin 20, target (fun w => decide (w = v)) = false) := by decide +kernel

theorem formulaLower (T : FlagCrossRank.Tree (Fin 21 ⊕ Fin 20)) (correct : T.val = target) : 120 ≤ T.leaves := by
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

def lineStar (l a b c d e : Fin 41) : Expr 41 :=
  .gate false (.raw l) (.gate true (.gate true (.raw a) (.raw b)) (.gate true (.raw c) (.gate true (.raw d) (.raw e))))

def witness : Expr 41 :=
  (.gate true (.gate true (.gate true (.gate true (.gate true (lineStar 21 1 2 5 15 17) (lineStar 22 2 3 6 16 18)) (lineStar 23 3 4 7 17 19)) (.gate true (lineStar 24 4 5 8 18 20) (lineStar 25 0 5 6 9 19))) (.gate true (.gate true (.gate true (lineStar 26 1 6 7 10 20) (lineStar 27 0 2 7 8 11)) (lineStar 28 1 3 8 9 12)) (.gate true (lineStar 29 2 4 9 10 13) (lineStar 30 3 5 10 11 14)))) (.gate true (.gate true (.gate true (.gate true (lineStar 31 4 6 11 12 15) (lineStar 32 5 7 12 13 16)) (lineStar 33 6 8 13 14 17)) (.gate true (lineStar 34 7 9 14 15 18) (lineStar 35 8 10 15 16 19))) (.gate true (.gate true (.gate true (lineStar 36 9 11 16 17 20) (lineStar 37 0 10 12 17 18)) (lineStar 38 1 11 13 18 19)) (.gate true (lineStar 39 2 12 14 19 20) (lineStar 40 0 3 13 15 20)))))

theorem witnessSize : witness.circuit.size = 119 := by decide +kernel
theorem witnessLegal : Monotone2 witness.circuit := by
  intro g hg
  exact ⟨(ao2 witness).1 g hg, le_of_eq ((ao2 witness).2.2 g hg)⟩

def rawTarget (x : Fin 41 → Bool) : Bool :=
  (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 0 && x 40) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 3 && x 40) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 13 && x 40) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 15 && x 40) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39) || (x 20 && x 24) || (x 20 && x 26) || (x 20 && x 36) || (x 20 && x 39) || (x 20 && x 40)

theorem upper (x : Fin 41 → Bool) : witness.circuit.eval (List.ofFn x) = rawTarget x := by
  change circuitFun 41 witness.circuit x = _
  rw [realBool]
  simp [witness, lineStar, rawTarget, Expr.val, op, GateOp.eval, Bool.and_or_distrib_right,
    Bool.and_or_distrib_left, Bool.and_comm]
  ac_rfl


def index : Fin 21 ⊕ Fin 20 → Fin 41 := Sum.elim
  (fun p => ⟨p.val, by omega⟩) (fun l => ⟨21 + l.val, by omega⟩)

theorem indexedTarget (x : Fin 41 → Bool) : target (x ∘ index) = rawTarget x := by
  simp only [target, flags, List.any_cons, List.any_nil, Bool.or_false,
    index, Function.comp_apply, Sum.elim_inl, Sum.elim_inr, rawTarget]
  ac_rfl

def rawPairs : List (Fin 41 × Fin 41) := flags.map (fun e => (index (.inl e.1),index (.inr e.2)))

theorem targetAny (x : Fin 41 → Bool) : rawTarget x =
    rawPairs.any (fun e => x e.1 && x e.2) := by
  rw [← indexedTarget]
  simp [target,rawPairs,List.any_map,Function.comp_def]

theorem postedEdges (x : Fin 41 → Bool) : witness.circuit.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 41, (u.val,v.val) ∈ rawPairs.map (fun e => (e.1.val,e.2.val)) ∧
      x u = true ∧ x v = true := by
  rw [upper,targetAny,List.any_eq_true]
  constructor
  · rintro ⟨⟨u,v⟩,mem,truth⟩
    exact ⟨u,v,List.mem_map.mpr ⟨(u,v),mem,rfl⟩,Bool.and_eq_true_iff.mp truth⟩
  · rintro ⟨u,v,mem,hu,hv⟩
    obtain ⟨⟨p,l⟩,ok,eq⟩ := List.mem_map.mp mem
    have hp : p = u := Fin.ext (congrArg Prod.fst eq)
    have hl : l = v := Fin.ext (congrArg Prod.snd eq)
    exact ⟨(u,v),hp ▸ hl ▸ ok,Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩

theorem squareFree : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k := by
  decide +kernel

def matchedPoint (l : Fin 20) : Fin 21 := ⟨l.val + 1, by omega⟩

theorem matchedIncidence : ∀ l, I (matchedPoint l) l := by decide +kernel

theorem cover [DecidableEq H] (K : Finset (OneShorePairRank.Label (Fin 21) (Fin 20) H))
    (hit : ∀ p l, I p l → Sum.inl p ∈ K ∨ Sum.inr (Sum.inl l) ∈ K) : 20 ≤ K.card := by
  classical
  let chosen (l : Fin 20) : K := if yes : Sum.inl (matchedPoint l) ∈ K then ⟨_,yes⟩
    else ⟨_,(hit _ _ (matchedIncidence l)).resolve_left yes⟩
  let read : OneShorePairRank.Label (Fin 21) (Fin 20) H → Nat :=
    Sum.elim (fun p => p.val - 1) (Sum.elim Fin.val (fun _ => 0))
  have value (l : Fin 20) : read (chosen l).val = l.val := by
    dsimp [chosen]
    split <;> simp [read,matchedPoint]
  have inj : Function.Injective chosen := by
    intro a b eq
    exact Fin.ext (by rw [← value a,← value b,eq])
  simpa using Fintype.card_le_of_injective chosen inj

theorem pointPairLower {H : Type} [Fintype H] [DecidableEq H] (u v : H → Fin 21)
    [DecidableRel (OneShorePairRank.kept I u v)] (proper : ∀ h, u h ≠ v h)
    (T : FlagCrossRank.Tree (OneShorePairRank.Label (Fin 21) (Fin 20) H))
    (correct : ∀ X Y, T.val (OneShorePairRank.bits u v X Y) = true ↔ ∃ p l, I p l ∧ X p ∧ Y l)
    (shared : 2 * Fintype.card H ≤ T.cost (fun w => if OneShorePairRank.physical w then 0 else 1))
    (s : Nat) (size : T.leaves + Fintype.card H ≤ s + 1) : 119 ≤ s := by
  have c := OneShorePairRank.circuitBound I u v squareFree proper T correct 20 cover shared s size
  rw [geometry.1] at c
  omega

#print axioms postedEdges
#print axioms pointPairLower
#print axioms formulaLower
#print axioms upper
end OrderFourPlane
