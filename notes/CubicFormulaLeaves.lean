import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Independent.CubicFormulaLeaves

/-- At most two pairwise incomparable subsets of a two-element set. -/
theorem twoBits : ∀ a b c : Fin 4,
    (a.val &&& b.val)=a.val ∨ (a.val &&& b.val)=b.val ∨
    (a.val &&& c.val)=a.val ∨ (a.val &&& c.val)=c.val ∨
    (b.val &&& c.val)=b.val ∨ (b.val &&& c.val)=c.val := by decide

/-- A nonempty ordered pair of reports cannot propagate to opposite
endpoints of the same cell in the formula partition. -/
theorem conflictingReports {T E V : Type*} (reports : T → E → V → Prop)
    (single : ∀ s e u v, reports s e u → reports s e v → u=v)
    {a b e : E} {v w : V} (different : v≠w)
    (atV : ∀ s, reports s a v → reports s e v)
    (atW : ∀ s, reports s b w → reports s e w)
    (witness : ∃ s, reports s a v ∧ reports s b w) : False := by
  obtain ⟨s,h,k⟩ := witness
  exact different (single s e v w (atV s h) (atW s k))

theorem negativeWitness {V : Type*} (G : SimpleGraph V) {a b v w : V}
    (vw : G.Adj v w) (vb : G.Adj v b) (wa : G.Adj w a)
    (aw' : a≠v) (bw' : b≠w)
    (linear : ∀ x y, x≠y → ∀ i j, G.Adj x i → G.Adj y i → G.Adj x j → G.Adj y j → i=j) :
    ¬ G.Adj a b := by
  intro ab
  exact bw' (linear v a aw'.symm b w vb ab vw wa.symm)

/-- Count all leaves from the sum of degrees. The saving vertices and
one endpoint per uncovered edge form a cover. -/
theorem chargeCount {m leaves savingVertices savings uncovered tau : ℕ}
    (uses : 2*m ≤ leaves+savings)
    (capacity : savings+savingVertices+uncovered ≤ m)
    (cover : tau ≤ savingVertices+uncovered) : m+tau ≤ leaves := by omega

/-- An OR separating the only positive occurrence from a selected negative
occurrence permits setting that negative occurrence to true. -/
theorem liftNegativeOr (T₀ T₁ : Bool → Bool) (L₀ L₁ R₀ R₁ Rnew : Bool)
    (up₀ : Monotone T₀) (outer : ∀ x, T₀ x ≤ T₁ x)
    (neg : R₁ ≤ Rnew) (otherNeg : Rnew ≤ R₀)
    (increasing : T₁ (L₀ || R₀) ≤ T₀ (L₁ || R₁)) :
    T₀ (L₁ || Rnew) = T₀ (L₁ || R₁) := by
  have impossiblePin : ¬ ((true : Bool) ≤ false) := by decide
  apply le_antisymm
  · cases L₁ <;> cases Rnew <;> cases R₀ <;> cases R₁ <;> simp_all <;> grind
  · apply up₀
    cases L₁ <;> simp_all

/-- At an AND separating the occurrences the negative occurrence can be
set to false. The other negative occurrences can only fall as x rises. -/
theorem dropNegativeAnd (T₀ T₁ : Bool → Bool) (L₀ L₁ R₀ R₁ Rnew : Bool)
    (up₁ : Monotone T₁) (outer : ∀ x, T₀ x ≤ T₁ x)
    (neg : Rnew ≤ R₀) (otherNeg : R₁ ≤ Rnew)
    (increasing : T₁ (L₀ && R₀) ≤ T₀ (L₁ && R₁)) :
    T₁ (L₀ && Rnew) = T₁ (L₀ && R₀) := by
  have impossiblePin : ¬ ((true : Bool) ≤ false) := by decide
  apply le_antisymm
  · apply up₁
    cases L₀ <;> simp_all
  · cases L₀ <;> cases Rnew <;> cases R₀ <;> cases R₁ <;> simp_all <;> grind

theorem removePaidNegations {m k restM restK leaves restLeaves bad paid : ℕ}
    (removedEdges : m ≤ restM + 3*bad) (removedCover : k ≤ restK+bad)
    (pricedRest : restM+restK ≤ restLeaves) (manyUses : restLeaves+3*bad ≤ leaves)
    (enough : bad ≤ paid) : m+k ≤ leaves+paid := by omega

end Independent.CubicFormulaLeaves
