import PlaneOrPadding8851
import PlaneMinimalJunk8851

namespace PlaneTransfer8851

open PEqualNP.CircuitLowerBounds
open PEqualNP.GenericRejection
open PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PlaneOrPadding8851

def Rich {N : Nat} (S : Fin N → Finset (Fin N)) (D : Circuit) : Prop :=
  ∃ j < D.size, (gateAt D j).op = .or ∧
    ∃ lines : Finset (Fin N), 100 < lines.card ∧
      Set.InjOn (profile (N := N) D j) (lines : Set (Fin N)) ∧
      ∀ l ∈ lines, 1 < (profile (N := N) D j l).card ∧
        profile D j l ⊆ S l ∧
        wireValue D (incidenceInput (S l)ᶜ {l}) (N+N+j) = false

def PostedBound (q N : Nat) (S : Fin N → Finset (Fin N)) : Prop :=
  ∀ (D : Circuit) (J : Finset (Finset (Fin N) × Finset (Fin N))),
    IsAO2 (N+N) D → D.output < N+N+D.size →
    (∀ j ∈ J, q < j.2.card ∧ IsFalseInput S j.1 j.2) →
    (∀ j ∈ J, ∀ k ∈ J, k.1 ⊆ j.1 → k.2 ⊆ j.2 → k = j) →
    Model S D J → Rich S D → N*q ≤ 100*D.size

theorem oneGateSlack {q N : Nat} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (qLarge : 100 < q) (order : N = q^2+q+1)
    (sizeLine : ∀ l, (S l).card = q+1)
    (unique : ∀ a b : Fin N, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l)
    (oldLegal : IsAO2 (N+N) C) (oldOutput : C.output < N+N+C.size)
    (up : ∀ A B X Y : Finset (Fin N), A ⊆ X → B ⊆ Y →
      C.eval (incidenceInput A B) = true → C.eval (incidenceInput X Y) = true)
    (flag : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    (posted : PostedBound q N S) :
    N*q ≤ 100*(C.size+1) := by
  have allIncident (X Y : Finset (Fin N)) (edge : incidenceFun S X Y = true) :
      C.eval (incidenceInput X Y) = true := by
    obtain ⟨p,hp,l,hl,hit⟩ : ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l := by
      simpa [incidenceFun] using edge
    exact up {p} {l} X Y (Finset.singleton_subset_iff.mpr hp)
      (Finset.singleton_subset_iff.mpr hl) (flag l p hit)
  obtain ⟨J,long,antichain,model⟩ :=
    PlaneMinimalJunk8851.normalForm S (fun X Y => C.eval (incidenceInput X Y) = true)
      q up allIncident (by
        intro X Y small independent
        rw [sound X Y small independent]
        decide)
  have Nlarge : 100 < N := by omega
  let D := pad (N+N) C
  have valid : D.output < N+N+D.size := by
    change N+N+C.size < N+N+(pad (N+N) C).size
    rw [padSize]
    omega
  have result := posted D J (padLegal _ C oldLegal oldOutput) valid long antichain
    (padModel S C J model)
    (paddedRichOr S C J qLarge Nlarge sizeLine unique (fun j hj => (long j hj).1) model)
  change N*q ≤ 100*(pad (N+N) C).size at result
  simpa only [padSize] using result

#print axioms oneGateSlack

end PlaneTransfer8851
