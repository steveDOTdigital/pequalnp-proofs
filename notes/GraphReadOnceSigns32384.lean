import Mathlib.Data.Bool.Basic

namespace GraphSynthesis32384

theorem eliminateSignAcrossAnd {A B : Type} (positive : A → Bool → Bool)
    (negative : B → Bool → Bool)
    (monotone : ∀ a b, (positive a false && negative b true) ≤
      (positive a true && negative b false))
    (live : ∃ b, negative b false = false ∧ negative b true = true)
    (a : A) (b : B) (x : Bool) :
    (positive a x && negative b (!x)) = (positive a x && negative b false) := by
  obtain ⟨test,low,high⟩ := live
  have forced := monotone a test
  simp only [low,high,Bool.and_true,Bool.and_false] at forced
  have zero : positive a false = false := by
    cases value : positive a false with
    | false => rfl
    | true => exact ((by decide : ¬ true ≤ false) (value ▸ forced)).elim
  cases x <;> simp [zero]

theorem eliminateSignAcrossOr {A B : Type} (positive : A → Bool → Bool)
    (negative : B → Bool → Bool)
    (monotone : ∀ a b, (positive a false || negative b true) ≤
      (positive a true || negative b false))
    (live : ∃ b, negative b false = false ∧ negative b true = true)
    (a : A) (b : B) (x : Bool) :
    (positive a x || negative b (!x)) = (positive a x || negative b true) := by
  obtain ⟨test,low,high⟩ := live
  have forced := monotone a test
  simp only [low,high,Bool.or_true,Bool.or_false] at forced
  have one : positive a true = true := by
    cases value : positive a true with
    | false => exact ((by decide : ¬ true ≤ false) (value ▸ forced)).elim
    | true => rfl
  cases x <;> simp [one]

#print axioms eliminateSignAcrossAnd
#print axioms eliminateSignAcrossOr

end GraphSynthesis32384