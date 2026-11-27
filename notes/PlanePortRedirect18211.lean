import PlaneFirstOr18211

namespace PlanePortRedirect18211

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PlaneFirstOr18211

def redirected (target slot : Nat) : Nat :=
  if slot = 26 then target else slot

def mapGate (target : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (redirected target)⟩

def mapTail (target : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mapGate target), redirected target C.output⟩

theorem mapTailSize (target : Nat) (C : Circuit) :
    (mapTail target C).size = C.size := by simp [mapTail,Circuit.size]

theorem mapTailMono (target : Nat) (C : Circuit) (ok : Monotone2 C) :
    Monotone2 (mapTail target C) := by
  intro g mem
  change g ∈ C.gates.map (mapGate target) at mem
  obtain ⟨h,hC,rfl⟩ := List.mem_map.mp mem
  simpa [mapGate] using ok h hC

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

theorem readAbsent (w : List Bool) (i : Nat) (outside : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none outside]
  rfl

theorem runRedirect (gs : List Gate) (target : Nat) (left right : List Bool)
    (len : left.length = right.length)
    (raw : 27 ≤ right.length)
    (stable : target < 26 ∨ right.length + gs.length ≤ target)
    (agree : ∀ j, left.getD j false = right.getD (redirected target j) false) :
    ∀ j, (run gs left).getD j false =
      (run (gs.map (mapGate target)) right).getD (redirected target j) false := by
  induction gs generalizing left right with
  | nil => exact agree
  | cons g gs ih =>
    let next := g.op.eval (g.inputs.map fun i => left.getD i false)
    have nextSame :
        (mapGate target g).op.eval ((mapGate target g).inputs.map fun i => right.getD i false) = next := by
      change g.op.eval ((g.inputs.map (redirected target)).map fun i => right.getD i false) = _
      rw [List.map_map]
      unfold next
      congr 1
      apply List.map_congr_left
      intro j _
      exact (agree j).symm
    simp only [run, List.foldl_cons, List.map_cons, nextSame]
    change ∀ j, (run gs (left ++ [next])).getD j false =
      (run (gs.map (mapGate target)) (right ++ [next])).getD (redirected target j) false
    apply ih
    · simp [len]
    · simp only [List.length_append,List.length_singleton]; omega
    · simp only [List.length_append,List.length_cons,List.length_nil] at stable ⊢
      omega
    · intro j
      by_cases special : j = 26
      · subst j
        have leftRaw : 26 < left.length := by omega
        rw [List.getD_append _ _ _ _ leftRaw, agree 26]
        simp only [redirected, ite_true]
        rcases stable with small | far
        · exact (List.getD_append _ _ _ _ (show target < right.length by omega)).symm
        · rw [readAbsent right target (by simp only [List.length_cons] at far; omega),
              readAbsent (right ++ [next]) target
                (by simp only [List.length_cons,List.length_append,List.length_nil] at far ⊢; omega)]
      · simp only [redirected, special, ite_false]
        by_cases inside : j < left.length
        · have insideR : j < right.length := len ▸ inside
          rw [List.getD_append _ _ _ _ inside, List.getD_append _ _ _ _ insideR]
          simpa [redirected,special] using agree j
        · have pastL := Nat.le_of_not_gt inside
          have pastR : right.length ≤ j := len ▸ pastL
          rw [List.getD_append_right _ _ _ _ pastL, List.getD_append_right _ _ _ _ pastR, len]

theorem firstRead (raw : List Bool) (value : Bool) :
    (raw ++ [value]).getD raw.length false = value := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

theorem replaceWithAlias (first newFirst : Gate) (C : Circuit) (target : Nat)
    (stable : target < 26 ∨ 27 + C.size ≤ target)
    (aliasValue : ∀ x : Fin 26 → Bool, firstValue first x =
      (List.ofFn x ++ [firstValue newFirst x]).getD target false)
    (x : Fin 26 → Bool) :
    C.eval (List.ofFn x ++ [firstValue first x]) =
      (mapTail target C).eval (List.ofFn x ++ [firstValue newFirst x]) := by
  let A := List.ofFn x ++ [firstValue first x]
  let B := List.ofFn x ++ [firstValue newFirst x]
  have lenA : A.length = 27 := by simp [A]
  have lenB : B.length = 27 := by simp [B]
  have agree (j : Nat) : A.getD j false = B.getD (redirected target j) false := by
    by_cases special : j = 26
    · subst j
      have v : A.getD 26 false = firstValue first x := by
        change (List.ofFn x ++ [firstValue first x]).getD 26 false = _
        simpa only [List.length_ofFn] using firstRead (List.ofFn x) (firstValue first x)
      rw [v]
      change firstValue first x = B.getD target false
      exact aliasValue x
    · simp only [redirected,special,ite_false]
      by_cases small : j < 26
      · have lt : j < (List.ofFn x).length := by simpa using small
        exact (List.getD_append _ _ _ _ lt).trans (List.getD_append _ _ _ _ lt).symm
      · have big : 27 ≤ j := by omega
        rw [readAbsent A j (by simpa only [lenA] using big),
          readAbsent B j (by simpa only [lenB] using big)]
  exact runRedirect C.gates target A B (lenA.trans lenB.symm) (by omega)
    (by simpa [Circuit.size,lenB] using stable) agree C.output

theorem firstEmpty (first : Gate) (isOr : first.op = GateOp.or)
    (empty : rawPorts first = ∅) (x : Fin 26 → Bool) :
    firstValue first x = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  have witness := (rawPortRead first x isOr).mp yes
  simp [empty] at witness

theorem firstSingleton (first : Gate) (isOr : first.op = GateOp.or)
    (slot : Nat) (one : rawPorts first = {slot}) (x : Fin 26 → Bool) :
    firstValue first x = (List.ofFn x).getD slot false := by
  have vals := rawPortRead first x isOr
  rw [one] at vals
  have both : firstValue first x = true ↔ (List.ofFn x).getD slot false = true := by
    simpa using vals
  cases h : firstValue first x <;> cases h' : (List.ofFn x).getD slot false <;> simp_all

theorem emptyPrefix (first newFirst : Gate) (C : Circuit)
    (isOr : first.op = GateOp.or) (empty : rawPorts first = ∅) (x : Fin 26 → Bool) :
    C.eval (List.ofFn x ++ [firstValue first x]) =
      (mapTail (27 + C.size) C).eval (List.ofFn x ++ [firstValue newFirst x]) := by
  apply replaceWithAlias first newFirst C _ (Or.inr (Nat.le_refl _)) ?_ x
  intro y
  rw [firstEmpty first isOr empty, readAbsent]
  simp

theorem singletonPrefix (first newFirst : Gate) (C : Circuit)
    (isOr : first.op = GateOp.or) (slot : Nat) (small : slot < 26)
    (one : rawPorts first = {slot}) (x : Fin 26 → Bool) :
    C.eval (List.ofFn x ++ [firstValue first x]) =
      (mapTail slot C).eval (List.ofFn x ++ [firstValue newFirst x]) := by
  apply replaceWithAlias first newFirst C slot (Or.inl small) ?_ x
  intro y
  rw [firstSingleton first isOr slot one, List.getD_append _ _ _ _ (by simpa using small)]

#print axioms emptyPrefix
#print axioms singletonPrefix
#print axioms mapTailMono

end PlanePortRedirect18211
