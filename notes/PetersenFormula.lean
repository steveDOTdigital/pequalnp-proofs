import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PetersenFormula

def control : DMFormula 9 := (.or (.or (.or (.or (.and (.lit 0 true) (.or (.or (.lit 1 true) (.lit 4 true)) (.lit 5 true))) (.and (.lit 2 true) (.or (.or (.lit 1 true) (.lit 3 true)) (.lit 7 true)))) (.and (.lit 3 true) (.or (.lit 4 true) (.lit 8 true)))) (.and (.lit 5 true) (.or (.lit 7 true) (.lit 8 true)))) (.and (.lit 6 true) (.or (.lit 1 true) (.lit 8 true))))

theorem control_cost : control.leaves = 17 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
theorem control_rows : ∀ r : Fin 512,
    control.eval (fun i => r.val.testBit i.val) =
      (([18440827511444797640,18441957826578283724,18446744073709222136,18446744073709485308,18446744073708175304,18446744073709551615,18446744073709223928,18446744073709551615] : List ℕ).getD (r.val/64) 0).testBit (r.val%64) := by decide +kernel

-- A variable with one positive and one negative occurrence can lose the
-- negative literal. The three unary maps model its branches and outer context.
theorem eliminate_negative : ∀ (useOr p0 p1 n0 n1 c0 c1 : Bool),
    let combine := fun a b => if useOr then a || b else a && b
    let ctx := fun (v : Bool) => if v then c1 else c0
    p0 ≤ p1 → n0 ≤ n1 → c0 ≤ c1 →
    ctx (combine p0 n1) ≤ ctx (combine p1 n0) →
    let fixed := if useOr then n1 else n0
    ctx (combine p0 fixed) = ctx (combine p0 n1) ∧
    ctx (combine p1 fixed) = ctx (combine p1 n0) := by decide

end PetersenFormula
