import PlaneSensitivity18211
import PlanePortRedirect18211

namespace PlaneBypass18211

open PEqualNP.CircuitLowerBounds
open PlaneFirstOr18211
open PlanePortRedirect18211
open PlaneSensitivity18211

def activate (w q : Nat) : Nat := w ||| 2 ^ q

theorem activateOther {w q i : Nat} (outside : i ≠ q) :
    bits (activate w q) i = bits w i := by
  simp [bits,activate,Nat.testBit_or,Nat.testBit_two_pow,Ne.symm outside]

def rawWord (w : Nat) : Fin 26 → Bool := fun j => bits w j

theorem rawAt (w : Nat) (i : Fin 26) :
    (List.ofFn (rawWord w)).getD i.val false = bits w i.val := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
    List.getElem_ofFn]
  rfl

def firstPair (p q : Fin 26) : Gate := ⟨GateOp.or,[p.val,q.val]⟩

def pairTape (p q : Fin 26) (w : Nat) : List Bool :=
  List.ofFn (rawWord w) ++ [firstValue (firstPair p q) (rawWord w)]

theorem firstHigh (p q : Fin 26) (row : Nat) (active : bits row p.val = true) :
    firstValue (firstPair p q) (rawWord row) = true := by
  change ([(List.ofFn (rawWord row)).getD p.val false,
    (List.ofFn (rawWord row)).getD q.val false]).any id = true
  rw [rawAt row p, active]
  rfl

theorem pairTapeAgree (p q : Fin 26) (different : p ≠ q) (row : Nat)
    (active : bits row p.val = true) (i : Nat) (outside : i ≠ q.val) :
    (pairTape p q row).getD i false =
      (pairTape p q (activate row q.val)).getD i false := by
  have unequal : p.val ≠ q.val := fun same => different (Fin.ext same)
  have activeNew : bits (activate row q.val) p.val = true :=
    (activateOther unequal).trans active
  by_cases raw : i < 26
  · let j : Fin 26 := ⟨i,raw⟩
    have hi w : i < (List.ofFn (rawWord w)).length := by simpa only [List.length_ofFn]
    unfold pairTape
    rw [List.getD_append _ _ _ _ (hi _),List.getD_append _ _ _ _ (hi _)]
    change (List.ofFn (rawWord row)).getD j.val false =
      (List.ofFn (rawWord (activate row q.val))).getD j.val false
    rw [rawAt row j,rawAt _ j]
    exact (activateOther outside).symm
  · by_cases helper : i = 26
    · subst i
      have old := firstRead (List.ofFn (rawWord row)) (firstValue (firstPair p q) (rawWord row))
      have new := firstRead (List.ofFn (rawWord (activate row q.val)))
        (firstValue (firstPair p q) (rawWord (activate row q.val)))
      simp only [List.length_ofFn] at old new
      unfold pairTape
      exact old.trans ((firstHigh p q row active).trans
        ((firstHigh p q _ activeNew).symm.trans new.symm))
    · have allOut w : (pairTape p q w).length ≤ i := by simp [pairTape]; omega
      rw [readAbsent _ _ (allOut row), readAbsent _ _ (allOut _)]

theorem mustReadOtherOperand (C : Circuit) (p q : Fin 26) (different : p ≠ q)
    (reject : ∀ row ∈ samples, C.eval (pairTape p q row) = false)
    (acceptRaised : ∀ row ∈ samples, bits row q.val = false → completes row q.val = true →
      C.eval (pairTape p q (activate row q.val)) = true)
    (notRawOutput : C.output ≠ q.val) :
    ∃ g ∈ C.gates, q.val ∈ g.inputs := by
  obtain ⟨row,member,_,pinned,off,flag⟩ := hasWitness p q different true
  have separates : C.eval (pairTape p q row) ≠
      C.eval (pairTape p q (activate row q.val)) := by
    rw [reject row member,acceptRaised row member off flag]
    decide
  exact (differingEvalRequiresRead C q.val _ _ (by simp [pairTape])
    (pairTapeAgree p q different row pinned) separates).resolve_left notRawOutput

#print axioms mustReadOtherOperand

end PlaneBypass18211
