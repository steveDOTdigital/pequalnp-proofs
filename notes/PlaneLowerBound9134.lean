import PEqualNP.Defs

namespace PlaneLowerBound9134

theorem finiteOrders (q : ℕ) (lo : 299 ≤ q) (hi : q ≤ 379) :
    (q^2+q+1)*(q+1) + 5*(760*(q+1)+2*q*(q-19)) ≤ 400*(q^2+q+1) := by
  interval_cases q <;> decide

theorem restrictedOrderBound (q s : ℕ) (lo : 299 ≤ q) (hi : q ≤ 379)
    (deletionBound : 80*(q^2+q+1) ≤ 20*s+760*(q+1)+2*q*(q-19)) :
    (q^2+q+1)*(q+1) ≤ 100*s := by
  have arithmetic := finiteOrders q lo hi
  omega

#print axioms restrictedOrderBound

end PlaneLowerBound9134