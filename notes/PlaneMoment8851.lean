import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace PlaneMoment8851

def penalty (d : Int) : Int := if d = 0 then 2 else if d = 1 then 1 else 0

theorem arbitraryStop {N : Nat} (d : Fin N → Int) (q k r s : Int)
    (nonnegative : 0 ≤ k*(k+1))
    (first : ∑ l, d l = r*(q+1))
    (second : ∑ l, d l*(d l-1) = r*(r-1))
    (localBound : ∀ l, penalty (d l)*(k*(k+1)) ≤ 2*((d l-k)*(d l-k-1)))
    (deletion : 4*(N:Int)-2*r-(∑ l, penalty (d l)) ≤ s) :
    (4*(N:Int)-2*r-s)*(k*(k+1)) ≤
      2*(r*(r-1)-2*k*r*(q+1)+(N:Int)*k*(k+1)) := by
  have moment :
      ∑ l, (d l-k)*(d l-k-1) = r*(r-1)-2*k*r*(q+1)+(N:Int)*k*(k+1) := by
    calc
      _ = ∑ l, (d l*(d l-1) - (2*k)*d l + k*(k+1)) := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,first,second]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
  have summed : (∑ l, penalty (d l))*(k*(k+1)) ≤
      2*(r*(r-1)-2*k*r*(q+1)+(N:Int)*k*(k+1)) := by
    rw [Finset.sum_mul,← moment,Finset.mul_sum]
    classical
    have compare (R : Finset (Fin N)) :
        (∑ i ∈ R, penalty (d i)*(k*(k+1))) ≤
          ∑ i ∈ R, 2*((d i-k)*(d i-k-1)) := by
      induction R using Finset.induction_on with
      | empty => simp
      | @insert a B absent induct =>
        simp only [Finset.sum_insert absent]
        exact add_le_add (localBound a) induct
    exact compare Finset.univ
  have loss : 4*(N:Int)-2*r-s ≤ ∑ l, penalty (d l) := by omega
  exact (mul_le_mul_of_nonneg_right loss nonnegative).trans summed

theorem improved380 (s : Int)
    (bound : (4*(144781:Int)-2*7047-s)*(19*(19+1)) ≤
      2*(7047*(7047-1)-2*19*7047*(380+1)+144781*19*(19+1))) :
    551117 ≤ s := by
  norm_num at bound
  omega

theorem smallSquares : ∀ a b : Fin 20,
    a.val^2+b.val^2 ≠ 381 ∧ a.val^2+b.val^2 ≠ 382 := by
  decide +kernel

theorem noSquares381or382 (a b : Nat) :
    a^2+b^2 ≠ 381 ∧ a^2+b^2 ≠ 382 := by
  by_cases ar : a < 20
  · by_cases br : b < 20
    · exact smallSquares ⟨a,ar⟩ ⟨b,br⟩
    · have large : 400 ≤ b*b := Nat.mul_le_mul (Nat.le_of_not_gt br) (Nat.le_of_not_gt br)
      simp only [pow_two]
      omega
  · have large : 400 ≤ a*a := Nat.mul_le_mul (Nat.le_of_not_gt ar) (Nat.le_of_not_gt ar)
    simp only [pow_two]
    omega

#print axioms arbitraryStop
#print axioms improved380
#print axioms noSquares381or382

end PlaneMoment8851
