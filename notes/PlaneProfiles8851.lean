import Mathlib.Data.Finset.Card

namespace PlaneProfiles8851

theorem profilesInjOn {Point Line : Type*} [DecidableEq Point]
    (on : Line → Finset Point)
    (unique : ∀ a b : Point, a ≠ b → ∃! l, a ∈ on l ∧ b ∈ on l)
    (select : Set Line) (profile : Line → Finset Point)
    (clean : ∀ l ∈ select, 1 < (profile l).card ∧ profile l ⊆ on l) :
    Set.InjOn profile select := by
  intro l hl m hm same
  obtain ⟨a,ha,b,hb,diff⟩ := Finset.one_lt_card.mp (clean l hl).1
  have am : a ∈ profile m := same ▸ ha
  have bm : b ∈ profile m := same ▸ hb
  obtain ⟨_,_,only⟩ := unique a b diff
  exact (only l ⟨(clean l hl).2 ha,(clean l hl).2 hb⟩).trans
    (only m ⟨(clean m hm).2 am,(clean m hm).2 bm⟩).symm

#print axioms profilesInjOn

end PlaneProfiles8851
