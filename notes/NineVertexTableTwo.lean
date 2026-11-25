import PEqualNP.Defs.MetaComplexity
import FlagStarCircuit
import PetersenRawNormal
import PetersenSignedInputs

namespace NineVertexTableTwo
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FlagStarCircuit

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)

def witness : Expr 9 :=
  (.gate true (.gate true (.gate true (.gate true (.gate false (.raw 0) (.gate true (.gate true (.raw 4) (.raw 5)) (.raw 7))) (.gate false (.raw 1) (.gate true (.raw 5) (.raw 8)))) (.gate false (.raw 6) (.gate true (.gate true (.raw 2) (.raw 3)) (.raw 8)))) (.gate false (.raw 7) (.gate true (.raw 2) (.raw 4)))) (.gate false (.raw 8) (.gate true (.raw 3) (.raw 5))))

theorem upper : HasCircuitSize 9 target 16 := by
  refine ⟨witness.circuit,?_,by decide +kernel,?_⟩
  · intro g hg
    refine ⟨?_,le_of_eq ((ao2 witness).2.2 g hg)⟩
    rcases (ao2 witness).1 g hg with h | h <;> simp [h]
  · intro x
    change circuitFun 9 witness.circuit x = _
    rw [realBool]
    simp [target,witness,Expr.val,op,GateOp.eval,Bool.and_or_distrib_left]
    ac_rfl

def signedValue (p : List (ℕ × ℕ)) (o : ℕ) (x : Fin 9 → Bool) : Bool :=
  (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
    w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false

theorem ordinaryLower
    (signed : ∀ p o, (∀ x, signedValue p o x = target x) → 15 ≤ p.length)
    (positive : ∀ C : Circuit,
      (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
      (∀ x, circuitFun 9 C x = target x) → 16 ≤ C.size) :
    ∀ t : ℕ, HasCircuitSize 9 target t → 16 ≤ t := by
  rintro t ⟨C,legal,small,correct⟩
  rcases PetersenRawNormal.normalize 9 C legal with binary | ⟨p,o,short,eval⟩
  · exact le_trans (positive C binary correct) small
  · have floor := signed p o (fun x => (eval x).trans (correct x))
    omega


/-- The signed exclusion alone suffices once it reaches size sixteen. -/
theorem ordinaryFromSigned
    (signed : ∀ p o, (∀ x, signedValue p o x = target x) → 16 ≤ p.length) :
    ∀ t : ℕ, HasCircuitSize 9 target t → 16 ≤ t := by
  rintro t ⟨C, legal, small, correct⟩
  let raw := List.ofFn (fun i : Fin 9 => fun x : Fin 9 → Bool => x i)
  let pool := [(fun _ : Fin 9 → Bool => false), (fun _ : Fin 9 → Bool => true)] ++
    raw ++ raw.map (fun f x => !(f x))
  have constants (b : Bool) : (fun _ : Fin 9 → Bool => b) ∈ pool := by
    cases b <;> simp [pool]
  have pins : ∀ u ∈ raw, u ∈ pool ∧ (fun x => !(u x)) ∈ pool := by
    intro u hu
    exact ⟨List.mem_append_left _ (List.mem_append_right _ hu),
      List.mem_append_right _ (List.mem_map_of_mem hu)⟩
  obtain ⟨p, o, bound, sim⟩ := PetersenSignedInputs.compile _ C legal pool raw constants pins
  apply le_trans (signed p o ?_) (bound.trans small)
  intro x
  have eq := sim x
  simpa only [signedValue, pool, raw, List.map_append, List.map_cons, List.map_nil,
    List.map_ofFn, List.map_map, Function.comp_def, circuitFun] using eq.trans (correct x)

end NineVertexTableTwo
