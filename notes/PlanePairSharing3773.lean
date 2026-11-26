import FlagCrossRank

namespace PlanePairSharing3773

/-- A row outside the missing diagonals can force one further leaf, even
when no retained diagonal reports this vertex. Use the common forcing
column as that extra row's own comparison column. -/
theorem extraRowPrice {E V T B : Type*} [DecidableEq E] [DecidableEq V] [Fintype B]
    (label : B → V) (select : E → T → B) (row : B → E → Bool) (col : B → T → Bool)
    (rect : ∀ e t b, select e t = b ↔ row b e = true ∧ col b t = true)
    (cross : E → T) (v : V) (s : Finset E) (w : E) (base : T)
    (fresh : w ∉ s)
    (missing : ∀ e ∈ s, label (select e (cross e)) ≠ v)
    (off : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → label (select a (cross b)) = v)
    (extra : ∀ b ∈ s, label (select w (cross b)) = v)
    (common : ∀ a ∈ insert w s, label (select a base) = v) :
    s.card + 1 ≤ Fintype.card {b // label b = v} := by
  classical
  let changed := fun e => if e = w then base else cross e
  have unique (a : E) (ha : a ∈ insert w s) (reported : label (select a (changed a)) = v) : a = w := by
    by_contra ne
    have mem := (Finset.mem_insert.mp ha).resolve_left ne
    exact missing a mem (by simpa [changed, ne] using reported)
  have bound := FlagCrossRank.restrictedPrice label select row col rect changed v (insert w s) (by
    intro a ha b hb ne
    by_cases hit : b = w
    · simpa [changed, hit] using common a ha
    · have bm := (Finset.mem_insert.mp hb).resolve_left hit
      rcases Finset.mem_insert.mp ha with rfl | am
      · simpa [changed, hit] using extra b bm
      · simpa [changed, hit] using off a am b bm ne)
    (fun a ha b hb ar br => (unique a ha ar).trans (unique b hb br).symm)
    (fun e he => ⟨base, common e he⟩)
  simpa [Finset.card_insert_of_notMem fresh] using bound

/-- A retained-edge cover enlarged by the opposite endpoints of every
deleted edge covers the original graph, including a matching of size n. -/
theorem coverOriginal {E V : Type*} [DecidableEq V]
    (left right : E → V) (keep : E → Prop) (reported damaged : Finset V)
    (good : ∀ e, keep e → left e ∈ reported ∨ right e ∈ reported)
    (bad : ∀ e, ¬keep e → right e ∈ damaged)
    (n : ℕ) (lower : ∀ K : Finset V, (∀ e, left e ∈ K ∨ right e ∈ K) → n ≤ K.card) :
    n ≤ (reported ∪ damaged).card := by
  classical
  apply lower
  intro e
  by_cases h : keep e
  · rcases good e h with p | l
    · exact Or.inl (Finset.mem_union_left _ p)
    · exact Or.inr (Finset.mem_union_left _ l)
  · exact Or.inr (Finset.mem_union_right _ (bad e h))

/-- Expand the opposite-shore helper reads, then exchange shores.
The optional mixed helpers each cost one physical leaf in either estimate. -/
theorem bothShores (flags cover raw pointPairs linePairs mixed
    pointReads lineReads mixedReads gates : ℕ)
    (pointBound : flags + cover ≤ raw + 2 * lineReads + mixedReads + 2 * pointPairs + mixed)
    (lineBound : flags + cover ≤ raw + 2 * pointReads + mixedReads + 2 * linePairs + mixed)
    (count : raw + pointReads + lineReads + mixedReads + pointPairs + linePairs + mixed ≤ gates + 1) :
    flags + cover ≤ gates + 1 := by omega

end PlanePairSharing3773
#print axioms PlanePairSharing3773.extraRowPrice
