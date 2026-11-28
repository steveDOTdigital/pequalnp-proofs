import PEqualNP.Defs.CircuitMoves

namespace PlaneThreeCover8059

theorem sourceBudget (s r g w : Nat) (flags : s ≤ 52)
    (gates : (52-s)+r+g ≤ 63) (live : w ≤ g+1) :
    w+r ≤ s+12 := by omega

theorem thirteenCenters (s r g w : Nat) (flags : s ≤ 52)
    (gates : (52-s)+r+g ≤ 63) (live : w ≤ g+1) (centers : 13 ≤ r) :
    w ≤ s-1 := by omega

theorem saturatedSources (s g w : Nat) (positive : 0 < s)
    (budget : g ≤ s-1) (raw : s ≤ w) (live : w ≤ g+1) :
    g = s-1 ∧ w = s := by omega

theorem fiveClauseForm (a b y g x p q : Bool) :
    ((((a && b) || y) && (g || (x && (p && q))))) =
      (((y || a) && (y || b)) && ((g || x) && (g || p) && (g || q))) := by
  cases a <;> cases b <;> cases y <;> cases g <;> cases x <;> cases p <;> cases q <;> rfl

theorem moveCommonLower (h y g p : Bool) :
    ((((h || y) && g) || (h && p))) =
      ((h && (g || p)) || (y && g)) := by
  cases h <;> cases y <;> cases g <;> cases p <;> rfl

theorem fourClauseForm (a b g p q : Bool) :
    (((a && b) && (g || (p && q)))) =
      ((a && b) && ((g || p) && (g || q))) := by
  cases a <;> cases b <;> cases g <;> cases p <;> cases q <;> rfl

#print axioms sourceBudget
#print axioms thirteenCenters
#print axioms saturatedSources
#print axioms fiveClauseForm
#print axioms moveCommonLower
#print axioms fourClauseForm
end PlaneThreeCover8059
