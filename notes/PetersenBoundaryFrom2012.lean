import PEqualNP.Outside.L_meta_2012
import PetersenBoundaryComplete

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenBoundaryComplete

-- The previously merged certificate supplies the ordinary circuit lower bound.
theorem PetersenBoundaryComplete.exactPacked (p : List (Bool × ℕ × ℕ)) (o : ℕ) (hp : p.length ≤ 14) :
    ∃ j : Fin 24, ((p.foldl PetersenPackedBoundary.packed
      [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968]).getD o 0).testBit j.val ≠ decide (j.val < 12) := by
  apply exclusion _ p o hp
  have old := PEqualNP.Outside.L_meta_2012
  dsimp only at old
  exact old
