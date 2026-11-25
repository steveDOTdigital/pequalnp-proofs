import PEqualNP.Defs
import FlagCrossRank
import FlagStarCircuit
import OneShorePairRank

set_option maxRecDepth 64000
set_option maxHeartbeats 8000000

namespace BalancedPlane9796
open FlagCrossRank FlagStarCircuit PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def flags : List (Fin 12 × Fin 12) := [(0,0), (0,4), (0,10), (1,1), (1,5), (1,11), (2,0), (2,1), (2,2), (2,6), (3,2), (3,3), (3,7), (4,1), (4,3), (4,4), (4,8), (5,2), (5,4), (5,5), (5,9), (6,3), (6,5), (6,6), (6,10), (7,4), (7,6), (7,7), (7,11), (8,0), (8,5), (8,7), (8,8), (9,6), (9,8), (9,9), (10,1), (10,7), (10,9), (10,10), (11,2), (11,8), (11,10), (11,11)]
def pointMask : Fin 12 → Nat := ![1041, 2082, 71, 140, 282, 564, 1128, 2256, 417, 832, 1666, 3332]

def I (p : Fin 12) (l : Fin 12) := (pointMask p).testBit l.val = true
instance : DecidableRel I := fun _ _ => inferInstanceAs (Decidable (_ = true))

def target (x : (Fin 12 ⊕ Fin 12) → Bool) : Bool :=
  flags.any fun e => x (.inl e.1) && x (.inr e.2)

def fiber (v : Fin 12 ⊕ Fin 12) : Finset (Flag I) := v.elim
  (fun p => Finset.univ.filter fun e => e.val.1 = p)
  (fun l => Finset.univ.filter fun e => e.val.2 = l)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
theorem geometry :
    Fintype.card (Flag I) = 44 ∧ (∀ v, (fiber v).card ≤ 4) ∧
    (∀ e : Flag I, target (edgeBits e.val) = true) ∧
    (∀ e : Flag I, target (crossBits I e.val) = false) ∧
    (∀ v : Fin 12 ⊕ Fin 12, target (fun w => decide (w = v)) = false) := by decide +kernel

def matchedPoint : Fin 12 → Fin 12 := ![8, 1, 11, 3, 5, 6, 2, 10, 4, 9, 0, 7]
def matchedLine : Fin 12 → Fin 12 := ![10, 1, 6, 3, 8, 4, 5, 11, 0, 9, 7, 2]

theorem matchedIncidence : ∀ l, I (matchedPoint l) l := by decide +kernel
theorem inverseMatch : ∀ l, matchedLine (matchedPoint l) = l := by decide +kernel

theorem formulaLower (T : FlagCrossRank.Tree (Fin 12 ⊕ Fin 12)) (correct : T.val = target) : 56 ≤ T.leaves := by
  obtain ⟨edgeCount, _, yes, cross, single⟩ := geometry
  rw [← correct] at yes cross single
  obtain ⟨K, cover, leaves⟩ := bipartiteFormula I I (fun _ _ h => h) T yes cross single
  classical
  let chosen (l : Fin 12) : K := if yes : Sum.inl (matchedPoint l) ∈ K then ⟨_,yes⟩
    else ⟨_,(cover ⟨(matchedPoint l,l),matchedIncidence l⟩).resolve_left yes⟩
  let read : Fin 12 ⊕ Fin 12 → Fin 12 := Sum.elim matchedLine id
  have value (l : Fin 12) : read (chosen l).val = l := by
    dsimp [chosen]
    split <;> simp [read,inverseMatch]
  have inj : Function.Injective chosen := by
    intro a b eq
    rw [← value a,← value b,eq]
  have count : 12 ≤ K.card := by simpa using Fintype.card_le_of_injective chosen inj
  rw [edgeCount] at leaves
  omega

def witness : Expr 24 :=
  (.gate true (.gate true (.gate true (.gate false (.raw 12) (.gate true (.raw 0) (.gate true (.raw 2) (.raw 8)))) (.gate true (.gate false (.raw 13) (.gate true (.gate true (.raw 1) (.raw 2)) (.gate true (.raw 4) (.raw 10)))) (.gate false (.raw 14) (.gate true (.gate true (.raw 2) (.raw 3)) (.gate true (.raw 5) (.raw 11)))))) (.gate true (.gate false (.raw 15) (.gate true (.raw 3) (.gate true (.raw 4) (.raw 6)))) (.gate true (.gate false (.raw 16) (.gate true (.gate true (.raw 0) (.raw 4)) (.gate true (.raw 5) (.raw 7)))) (.gate false (.raw 17) (.gate true (.gate true (.raw 1) (.raw 5)) (.gate true (.raw 6) (.raw 8))))))) (.gate true (.gate true (.gate false (.raw 18) (.gate true (.gate true (.raw 2) (.raw 6)) (.gate true (.raw 7) (.raw 9)))) (.gate true (.gate false (.raw 19) (.gate true (.gate true (.raw 3) (.raw 7)) (.gate true (.raw 8) (.raw 10)))) (.gate false (.raw 20) (.gate true (.gate true (.raw 4) (.raw 8)) (.gate true (.raw 9) (.raw 11)))))) (.gate true (.gate false (.raw 21) (.gate true (.raw 5) (.gate true (.raw 9) (.raw 10)))) (.gate true (.gate false (.raw 22) (.gate true (.gate true (.raw 0) (.raw 6)) (.gate true (.raw 10) (.raw 11)))) (.gate false (.raw 23) (.gate true (.raw 1) (.gate true (.raw 7) (.raw 11))))))))

theorem witnessSize : witness.circuit.size = 55 := by decide +kernel
theorem witnessLegal : Monotone2 witness.circuit := by
  intro g hg
  exact ⟨(ao2 witness).1 g hg, le_of_eq ((ao2 witness).2.2 g hg)⟩

def rawTarget (x : Fin 24 → Bool) : Bool :=
  (x 0 && x 12) || (x 0 && x 16) || (x 0 && x 22) || (x 1 && x 13) || (x 1 && x 17) || (x 1 && x 23) || (x 2 && x 12) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 5 && x 14) || (x 5 && x 16) || (x 5 && x 17) || (x 5 && x 21) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 12) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23)

theorem upper (x : Fin 24 → Bool) : witness.circuit.eval (List.ofFn x) = rawTarget x := by
  change circuitFun 24 witness.circuit x = _
  rw [realBool]
  simp [witness, rawTarget, Expr.val, op, GateOp.eval, Bool.and_or_distrib_right,
    Bool.and_or_distrib_left, Bool.and_comm]
  ac_rfl


def index : Fin 12 ⊕ Fin 12 → Fin 24 := Sum.elim
  (fun p => ⟨p.val, by omega⟩) (fun l => ⟨12 + l.val, by omega⟩)

theorem indexedTarget (x : Fin 24 → Bool) : target (x ∘ index) = rawTarget x := by
  simp only [target, flags, List.any_cons, List.any_nil, Bool.or_false,
    index, Function.comp_apply, Sum.elim_inl, Sum.elim_inr, rawTarget]
  ac_rfl

def rawPairs : List (Fin 24 × Fin 24) := flags.map (fun e => (index (.inl e.1),index (.inr e.2)))

theorem targetAny (x : Fin 24 → Bool) : rawTarget x =
    rawPairs.any (fun e => x e.1 && x e.2) := by
  rw [← indexedTarget]
  simp [target,rawPairs,List.any_map,Function.comp_def]

theorem postedEdges (x : Fin 24 → Bool) : witness.circuit.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 24, (u.val,v.val) ∈ rawPairs.map (fun e => (e.1.val,e.2.val)) ∧
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

theorem cover [DecidableEq H] (K : Finset (OneShorePairRank.Label (Fin 12) (Fin 12) H))
    (hit : ∀ p l, I p l → Sum.inl p ∈ K ∨ Sum.inr (Sum.inl l) ∈ K) : 12 ≤ K.card := by
  classical
  let chosen (l : Fin 12) : K := if yes : Sum.inl (matchedPoint l) ∈ K then ⟨_,yes⟩
    else ⟨_,(hit _ _ (matchedIncidence l)).resolve_left yes⟩
  let read : OneShorePairRank.Label (Fin 12) (Fin 12) H → Fin 12 :=
    Sum.elim matchedLine (Sum.elim id (fun _ => 0))
  have value (l : Fin 12) : read (chosen l).val = l := by
    dsimp [chosen]
    split <;> simp [read,inverseMatch]
  have inj : Function.Injective chosen := by
    intro a b eq
    rw [← value a,← value b,eq]
  simpa using Fintype.card_le_of_injective chosen inj

theorem pointPairLower {H : Type} [Fintype H] [DecidableEq H] (u v : H → Fin 12)
    [DecidableRel (OneShorePairRank.kept I u v)] (proper : ∀ h, u h ≠ v h)
    (T : FlagCrossRank.Tree (OneShorePairRank.Label (Fin 12) (Fin 12) H))
    (correct : ∀ X Y, T.val (OneShorePairRank.bits u v X Y) = true ↔ ∃ p l, I p l ∧ X p ∧ Y l)
    (shared : 2 * Fintype.card H ≤ T.cost (fun w => if OneShorePairRank.physical w then 0 else 1))
    (s : Nat) (size : T.leaves + Fintype.card H ≤ s + 1) : 55 ≤ s := by
  have c := OneShorePairRank.circuitBound I u v squareFree proper T correct 12 cover shared s size
  rw [geometry.1] at c
  omega

theorem labels : rawPairs.map (fun e => (e.1.val,e.2.val)) = ([(0,12), (0,16), (0,22), (1,13), (1,17), (1,23), (2,12), (2,13), (2,14), (2,18), (3,14), (3,15), (3,19), (4,13), (4,15), (4,16), (4,20), (5,14), (5,16), (5,17), (5,21), (6,15), (6,17), (6,18), (6,22), (7,16), (7,18), (7,19), (7,23), (8,12), (8,17), (8,19), (8,20), (9,18), (9,20), (9,21), (10,13), (10,19), (10,21), (10,22), (11,14), (11,20), (11,22), (11,23)] : List (Nat × Nat)) := by decide +kernel

#print axioms labels
#print axioms postedEdges
#print axioms pointPairLower
#print axioms formulaLower
#print axioms upper
end BalancedPlane9796
