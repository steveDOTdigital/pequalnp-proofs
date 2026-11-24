import PEqualNP.Defs

namespace PlaneClauseGeometry

-- Intersecting an unselected line with k selected lines covers at most k of its points.
theorem uncovered (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ l, Fintype.card {p // I p l} = q + 1)
    (uniqueLine : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (T : Finset (Fin n)) (small : T.card ≤ q) (l : Fin n) (outside : l ∉ T) :
    ∃ p, I p l ∧ ∀ k ∈ T, ¬ I p k := by
  classical
  by_contra! covered
  have chooseLine (p : {p // I p l}) : ∃ k : ↥T, I p.val k.val := by
    obtain ⟨k, hk, hp⟩ := covered p.val p.property
    exact ⟨⟨k, hk⟩, hp⟩
  choose f hit using chooseLine
  have inj : Function.Injective f := by
    intro a b eq
    by_contra ne
    have diff : a.val ≠ b.val := fun h => ne (Subtype.ext h)
    obtain ⟨s, _, only⟩ := uniqueLine _ _ diff
    have hb : I b.val (f a).val := eq ▸ hit b
    have same := (only l ⟨a.property, b.property⟩).trans
      (only (f a).val ⟨hit a, hb⟩).symm
    exact outside (same ▸ (f a).property)
  have bound := Fintype.card_le_of_injective f inj
  rw [degree, Fintype.card_coe] at bound
  omega

-- A positive clause is given by its selected point and line variables.
-- To pass every incident pair its selected variables must form a vertex cover.
theorem forcedClause {q n : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]
    (degree : ∀ l, Fintype.card {p // I p l} = q + 1)
    (uniqueLine : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (T : Finset (Fin n)) (small : T.card ≤ q)
    (points lines : Finset (Fin n))
    (cover : ∀ p l, I p l → p ∈ points ∨ l ∈ lines)
    (pointZero : ∀ p ∈ points, ∃ l ∈ T, I p l)
    (lineZero : Disjoint lines T) :
    points = Finset.univ.filter (fun p => ∃ l ∈ T, I p l) ∧ lines = Tᶜ := by
  classical
  have dis := Finset.disjoint_left.mp lineZero
  constructor
  · ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact pointZero p
    · rintro ⟨l, hl, hp⟩
      exact (cover p l hp).resolve_right (fun hc => dis hc hl)
  · ext l
    rw [Finset.mem_compl]
    constructor
    · exact fun hl => dis hl
    · intro hl
      obtain ⟨p, hp, free⟩ := uncovered q n I degree uniqueLine T small l hl
      apply (cover p l hp).resolve_left
      intro included
      obtain ⟨k, hk, hpk⟩ := pointZero p included
      exact free k hk hpk

theorem clause (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ l, Fintype.card {p // I p l} = q + 1)
    (uniqueLine : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (T : Finset (Fin n)) (small : T.card ≤ q) (A B : Fin n → Prop)
    (cover : ∀ p l, I p l → A p ∨ B l)
    (pointZero : ∀ p, A p → ∃ l ∈ T, I p l) (lineZero : ∀ l ∈ T, ¬ B l) :
    (∀ p, A p ↔ ∃ l ∈ T, I p l) ∧ (∀ l, B l ↔ l ∉ T) := by
  classical
  let P := Finset.univ.filter A
  let L := Finset.univ.filter B
  have hP (p : Fin n) : p ∈ P ↔ A p := by simp [P]
  have hL (l : Fin n) : l ∈ L ↔ B l := by simp [L]
  obtain ⟨points, lines⟩ := forcedClause degree uniqueLine T small P L
    (fun p l h => Or.imp (hP p).mpr (hL l).mpr (cover p l h))
    (fun p h => pointZero p ((hP p).mp h))
    (Finset.disjoint_left.mpr (fun {_} hl ht => lineZero _ ht ((hL _).mp hl)))
  constructor
  · intro p
    rw [← hP, points]
    simp
  · intro l
    rw [← hL, lines, Finset.mem_compl]

-- Different selected line sets must use different clauses, even in a CNF
-- with repeated computations and redundant clauses.
theorem count (q n : ℕ) (out : Finset (Finset (Fin (n+n))))
    (covers : ∀ T : Finset (Fin n), T.card ≤ q → ∃ t ∈ out,
      ∀ l, Fin.natAdd n l ∈ t ↔ l ∉ T) :
    (((Finset.univ : Finset (Fin n)).powerset).filter (fun T => T.card ≤ q)).card ≤ out.card := by
  classical
  let choices := ((Finset.univ : Finset (Fin n)).powerset).filter (fun T => T.card ≤ q)
  have pick (T : ↥choices) : ∃ t : ↥out, ∀ l, Fin.natAdd n l ∈ t.val ↔ l ∉ T.val := by
    obtain ⟨t, ht, agrees⟩ := covers T.val (Finset.mem_filter.mp T.property).2
    exact ⟨⟨t,ht⟩, agrees⟩
  choose f spec using pick
  have inj : Function.Injective f := by
    intro A B eq
    apply Subtype.ext
    ext l
    have same : (l ∉ A.val) ↔ (l ∉ B.val) := by
      rw [← spec A l, ← spec B l, eq]
    exact not_iff_not.mp same
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj

end PlaneClauseGeometry
