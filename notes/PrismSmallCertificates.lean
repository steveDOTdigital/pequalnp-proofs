import PrismFrontierData

namespace PrismSignedFrontier

namespace House

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem check5 : feasible target negative 5 raw = false := by decide +kernel

theorem lower (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) :
    6 ≤ p.length :=
  from_check target nonzero raw initial (by decide +kernel) start negative neg essential 5 check5 p o hit

end House

namespace Prism

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem check7 : feasible target negative 7 raw = false := by decide +kernel

theorem lowerEight (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) :
    8 ≤ p.length :=
  from_check target nonzero raw initial (by decide +kernel) start negative neg essential 7 check7 p o hit

end Prism

end PrismSignedFrontier
