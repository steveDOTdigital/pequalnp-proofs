import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Support

namespace PEqualNP.Outside.L_meta_606

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers

def edgeFunction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : Bool :=
  decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)

-- An edge incident to i gives two inputs differing only at i.
private lemma detects {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {i j : Fin n} (adj : G.Adj i j) :
    ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ edgeFunction G x ≠ edgeFunction G y := by
  let x := fun k : Fin n => decide (k = j)
  let y := fun k : Fin n => decide (k = i ∨ k = j)
  refine ⟨x, y, ?_, ?_⟩
  · intro k h
    simp [x, y, h]
  · have off : edgeFunction G x = false := by
      apply decide_eq_false
      rintro ⟨u, v, huv, hu, hv⟩
      simp [x] at hu hv
      exact huv.ne (hu.trans hv.symm)
    have on : edgeFunction G y = true := decide_eq_true ⟨i, j, adj, by simp [y], by simp [y]⟩
    simp [off, on]

-- Isolated vertices are free to remain unread. Every other vertex must
-- belong to the actual output's backwards support, even with unused gates.
lemma active_vertices {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (ok : FanInTwo D) (correct : circuitFun n D = edgeFunction G) :
    G.support.ncard ≤ D.size + 1 := by
  classical
  let S := (suppsFrom D.gates (inputSupps n)).getD D.output ∅
  have sub : G.support.toFinset ⊆ S := by
    intro i hi
    obtain ⟨j, adj⟩ := G.mem_support.mp (Set.mem_toFinset.mp hi)
    obtain ⟨x, y, same, changes⟩ := detects adj
    by_contra absent
    apply changes
    rw [← correct]
    exact (agree_wiresFrom x y D.gates _ _ _ (agree_inputs x y)).2.2 D.output
      (fun k hk => same k (fun e => absent (e ▸ hk)))
  have size := cnt_suppsFrom D.gates 0 (inputSupps n) ok cnt_inputs {D.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at size
  rw [Set.ncard_eq_toFinset_card']
  exact (Finset.card_le_card sub).trans size

-- Isolates on the designated line side do not contribute to its degree sum.
lemma bounded_line_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lines points : Finset (Fin n)) (bip : G.IsBipartiteWith lines points)
    (d : ℕ) (bound : ∀ v ∈ lines, G.degree v ≤ d)
    (D : Circuit) (ok : FanInTwo D) (correct : circuitFun n D = edgeFunction G) :
    G.edgeFinset.card ≤ d * (D.size + 1) := by
  classical
  let active := lines ∩ G.support.toFinset
  have restrict : ∑ v ∈ active, G.degree v = ∑ v ∈ lines, G.degree v := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro v hv missing
    apply (G.degree_eq_zero_iff_notMem_support v).mpr
    exact fun h => missing (Finset.mem_inter.mpr ⟨hv, Set.mem_toFinset.mpr h⟩)
  have card : active.card ≤ D.size + 1 := by
    apply (Finset.card_le_card (show active ⊆ G.support.toFinset from Finset.inter_subset_right)).trans
    rw [← Set.ncard_eq_toFinset_card']
    exact active_vertices G D ok correct
  calc
    G.edgeFinset.card = ∑ v ∈ active, G.degree v :=
      (restrict.trans (G.isBipartiteWith_sum_degrees_eq_card_edges bip)).symm
    _ ≤ ∑ _v ∈ active, d := Finset.sum_le_sum fun v hv => bound v (Finset.mem_inter.mp hv).1
    _ = d * active.card := by simp [Nat.mul_comm]
    _ ≤ d * (D.size + 1) := Nat.mul_le_mul_left _ card

open PEqualNP.LowMerge

-- A line sum has one greatest false input: all off-line points on.
-- If an AND at the output equals that sum, one entire factor already
-- computes it on this restriction. The choice may depend on the line.
lemma and_line_factor {P L : ℕ} (inc : Fin P → Fin L → Bool) (w : Fin L)
    (f g : (Fin P → Bool) → Bool) (mf : Monotone f) (mg : Monotone g)
    (exactLine : ∀ x, (f x && g x) = lineSum P L inc w x) :
    f = lineSum P L inc w ∨ g = lineSum P L inc w := by
  let outside : Fin P → Bool := fun p => !(inc p w)
  have zero : lineSum P L inc w outside = false := by
    apply decide_eq_false
    rintro ⟨p, onLine, h⟩
    simp [outside, onLine] at h
  have below {x : Fin P → Bool} (hx : lineSum P L inc w x = false) : x ≤ outside := by
    intro p
    by_cases hp : inc p w = true
    · have off : x p = false := by
        cases h : x p
        · rfl
        · have yes : lineSum P L inc w x = true := decide_eq_true ⟨p, hp, h⟩
          simp [yes] at hx
      simp [off]
    · simp [outside, Bool.eq_false_iff.mpr hp]
  have factor (h : (Fin P → Bool) → Bool) (mh : Monotone h)
      (no : h outside = false) (yes : ∀ x, lineSum P L inc w x = true → h x = true) :
      h = lineSum P L inc w := by
    funext x
    cases hs : lineSum P L inc w x with
    | false =>
      have rel := mh (below hs)
      rw [no] at rel
      exact le_antisymm rel (Bool.false_le _)
    | true => exact yes x hs
  have meet := (exactLine outside).trans zero
  have pass (x) (hx : lineSum P L inc w x = true) := Bool.and_eq_true_iff.mp ((exactLine x).trans hx)
  cases hf : f outside with
  | false => exact Or.inl (factor f mf hf (fun x hx => (pass x hx).1))
  | true =>
    have hg : g outside = false := by simpa [hf] using meet
    exact Or.inr (factor g mg hg (fun x hx => (pass x hx).2))

private lemma lineSum_singleton {P L : ℕ} (inc : Fin P → Fin L → Bool)
    (w : Fin L) (p : Fin P) :
    lineSum P L inc w (fun q => decide (q = p)) = inc p w := by
  cases hp : inc p w <;> simp [lineSum, hp]

-- When one factor ignores line inputs, the other factor must compute the
-- entire line sum on all but at most one line with two or more points.
lemma independent_factor_exception {P L : ℕ} (inc : Fin P → Fin L → Bool)
    (unique : ∀ p q w v, p ≠ q → inc p w = true → inc q w = true →
      inc p v = true → inc q v = true → w = v)
    (f : (Fin P → Bool) → Bool) (g : Fin L → (Fin P → Bool) → Bool)
    (mf : Monotone f) (mg : ∀ w, Monotone (g w))
    (correct : ∀ w x, (f x && g w x) = lineSum P L inc w x)
    {w v : Fin L} (failsW : g w ≠ lineSum P L inc w)
    (failsV : g v ≠ lineSum P L inc v)
    {p q : Fin P} (distinct : p ≠ q) (hp : inc p w = true) (hq : inc q w = true) :
    w = v := by
  have fw := (and_line_factor inc w f (g w) mf (mg w) (correct w)).resolve_right failsW
  have fv := (and_line_factor inc v f (g v) mf (mg v) (correct v)).resolve_right failsV
  have same (i : Fin P) : inc i w = inc i v := by
    simpa only [lineSum_singleton] using congrFun (fw.symm.trans fv) (fun j => decide (j = i))
  exact unique p q w v distinct hp hq ((same p).symm.trans hp) ((same q).symm.trans hq)

end PEqualNP.Outside.L_meta_606
