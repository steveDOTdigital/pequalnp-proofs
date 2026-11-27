import PEqualNP.Defs
import Mathlib.Data.Finset.Card

namespace PlaneDegreeThree7915

def omitted : List ℕ := [46, 89, 114, 177, 263, 356, 450, 531, 553, 586, 736, 780, 802, 912, 1046, 1091, 1220, 1313, 1360, 1416, 1541, 1560, 2076, 2117, 2186, 2212, 2321, 2344, 2566, 2689, 3081, 3120, 3648, 4107, 4133, 4152, 4242, 4289, 4372, 4424, 4688, 4740, 5132, 5154, 5888, 6240, 6402, 7296]

def bitCard (mask : ℕ) : ℕ :=
  ((List.range 13).filter fun i => mask.testBit i).length

def incident (p l : ℕ) : Bool :=
  ([0,1,3,9] : List ℕ).contains ((p+13-l) % 13)

def omissionValid (mask : ℕ) : Bool :=
  decide (mask < 8192 ∧ bitCard mask = 4) &&
    (List.range 13).all (fun p =>
      decide (((List.range 13).filter fun l => mask.testBit l && incident p l).length ≤ 2)) &&
    omitted.all (fun other => (mask == other) || decide (bitCard (mask &&& other) ≤ 2))

theorem packingCard : omitted.length = 48 := rfl

theorem packingNoDuplicates : omitted.Nodup := by decide +kernel

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
theorem packingVerified (i : Fin 48) : omissionValid (omitted.getD i.val 0) = true := by
  fin_cases i <;> decide +kernel

theorem chooseExtension {P : Type} [DecidableEq P]
    (outside selected forbidden : Finset P)
    (four : outside.card = 4) (small : selected.card ≤ 2) (removed : forbidden.card ≤ 1) :
    ∃ p ∈ outside, p ∉ selected ∧ p ∉ forbidden := by
  by_contra none
  have sub : outside ⊆ selected ∪ forbidden := by
    intro p hp
    by_cases used : p ∈ selected
    · exact Finset.mem_union_left _ used
    · have forbiddenPoint : p ∈ forbidden := by
        by_contra allowed
        exact none ⟨p,hp,used,allowed⟩
      exact Finset.mem_union_right _ forbiddenPoint
  have total := Finset.card_le_card sub
  have bound := Finset.card_union_le selected forbidden
  omega

#print axioms packingVerified
#print axioms chooseExtension

end PlaneDegreeThree7915