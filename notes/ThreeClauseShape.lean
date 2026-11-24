import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace ThreeClauseShape

abbrev Mask := Fin 8
def hit (a b : Mask) := a.val ||| b.val = 7
instance (a b : Mask) : Decidable (hit a b) := by unfold hit; infer_instance
private theorem symm : ∀ a b : Mask, hit a b → hit b a := by decide +kernel

-- Vertices carry the three-bit membership masks of a product of raw clauses.
-- If the ambient edge function has girth at least five, every accepted edge
-- belongs to a graph without loops, triangles or four-cycles.
variable {α : Type*} (L : α → Mask)

theorem path_centers
    (noLoop : ∀ z, ¬hit (L z) (L z))
    (tri : ∀ x y z, hit (L x) (L y) → hit (L y) (L z) → ¬hit (L x) (L z))
    (sq : ∀ x y a b, x≠y → a≠b → hit (L x) (L a) → hit (L x) (L b) →
      hit (L y) (L a) → ¬hit (L y) (L b))
    (u v a b : α) (av : a ≠ v) (ub : u ≠ b)
    (ua : hit (L u) (L a)) (uv : hit (L u) (L v)) (vb : hit (L v) (L b)) :
    ∀ x y, hit (L x) (L y) → x=u ∨ y=u ∨ x=v ∨ y=v := by
  have ab : ¬hit (L a) (L b) := by
    intro h
    exact sq a v u b av ub (symm _ _ ua) h (symm _ _ uv) vb
  have pattern : ∀ U V A B : Mask,
      hit U A → hit U V → hit V B → ¬hit U B → ¬hit V A → ¬hit A B →
      ∀ X Y : Mask, ¬hit X X → ¬hit Y Y → ¬(hit X U ∧ hit X V) → ¬(hit Y U ∧ hit Y V) →
      hit X Y → X=U ∨ Y=U ∨ X=V ∨ Y=V := by decide +kernel
  have oneU (t : α) (eq : L t=L u) : t=u := by
    by_contra ne
    exact sq t u a v ne av (eq ▸ ua) (eq ▸ uv) ua uv
  have oneV (t : α) (eq : L t=L v) : t=v := by
    by_contra ne
    exact sq t v u b ne ub (eq ▸ symm _ _ uv) (eq ▸ vb) (symm _ _ uv) vb
  have clean (x : α) : ¬(hit (L x) (L u) ∧ hit (L x) (L v)) :=
    fun h => tri x u v h.1 uv h.2
  intro x y xy
  rcases pattern _ _ _ _ ua uv vb (tri u v b uv vb) (tri v u a (symm _ _ uv) ua)
    ab _ _ (noLoop x) (noLoop y) (clean x) (clean y) xy with h|h|h|h
  · exact Or.inl (oneU _ h)
  · exact Or.inr (Or.inl (oneU _ h))
  · exact Or.inr (Or.inr (Or.inl (oneV _ h)))
  · exact Or.inr (Or.inr (Or.inr (oneV _ h)))

-- Two disjoint accepted edges force at least one crossing without assuming
-- the graph was presented with a bipartition.
theorem cross : ∀ a b c d : Mask, hit a b → hit c d →
    hit a c ∨ hit a d ∨ hit b c ∨ hit b d := by decide +kernel

theorem arm_bits : ∀ U V A B : Mask,
    hit U A → hit U V → hit V B → ¬hit U B → ¬hit V A → ¬hit A B →
    ∃ i j k : Fin 3, i≠j ∧ i≠k ∧ j≠k ∧ U.val.testBit k.val=true ∧ V.val.testBit k.val=true ∧
      (∀ x : Mask, hit U x ↔ x.val.testBit i.val=true) ∧
      (∀ x : Mask, hit V x ↔ x.val.testBit j.val=true) := by decide +kernel

theorem gate_count (edges mass terminals branches excess preprocessing ordinary stars doubles size : ℕ)
    (coverage : edges ≤ mass) (forest : mass ≤ branches + terminals)
    (duplicates : branches ≤ preprocessing + excess) (leafPairs : 4*excess ≤ mass)
    (terminalsUsed : terminals ≤ ordinary + stars + 2*doubles)
    (top : preprocessing + 2*(ordinary+stars+doubles) ≤ size+1) :
    3*edges ≤ 4*(size+1) := by omega

-- Mixed edges between two vertex sets. An ordered pair of distinct points
-- has at most one common neighbor, so the off-diagonals below are disjoint.
theorem pair_moment {α β : Type*} [DecidableEq α] (A : Finset α) (B : Finset β)
    (N : β → Finset α) (sub : ∀ b ∈ B, N b ⊆ A)
    (sq : ∀ b ∈ B, ∀ c ∈ B, b ≠ c → ∀ x ∈ N b, ∀ y ∈ N b, x≠y →
      x ∈ N c → y ∈ N c → False) :
    (∑ b ∈ B, (N b).card)^2 ≤ B.card * (A.offDiag.card + ∑ b ∈ B, (N b).card) := by
  classical
  have disj : (B : Set β).PairwiseDisjoint (fun b => (N b).offDiag) := by
    intro b hb c hc bc
    apply Finset.disjoint_left.mpr
    intro xy h hb'
    obtain ⟨x,y,ne⟩ := Finset.mem_offDiag.mp h
    obtain ⟨u,v,_⟩ := Finset.mem_offDiag.mp hb'
    exact sq b hb c hc bc xy.1 x xy.2 y ne u v
  have incl : B.biUnion (fun b => (N b).offDiag) ⊆ A.offDiag := by
    intro xy mem
    obtain ⟨b,hb,hpair⟩ := Finset.mem_biUnion.mp mem
    obtain ⟨x,y,ne⟩ := Finset.mem_offDiag.mp hpair
    exact Finset.mem_offDiag.mpr ⟨sub b hb x,sub b hb y,ne⟩
  have total := Finset.card_le_card incl
  rw [Finset.card_biUnion disj] at total
  have split : (∑ b ∈ B, (N b).card^2) =
      (∑ b ∈ B, (N b).offDiag.card) + ∑ b ∈ B, (N b).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.offDiag_card,pow_two]
    cases (N b).card with
    | zero => rfl
    | succ n => simp [Nat.mul_succ]
  calc
    _ ≤ B.card * (∑ b ∈ B, (N b).card^2) := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := Nat.mul_le_mul_left _ (split ▸ Nat.add_le_add_right total _)

theorem edge_density (n e : ℕ) (hn : 0 < n)
    (moment : e^2 ≤ n^2 * (n^4 + e)) : e < n^2*(n+1) := by
  by_contra! high
  obtain ⟨z,rfl⟩ := Nat.exists_eq_add_of_le high
  have pos : 0 < n^5 := pow_pos hn _
  have expansion : (n^2*(n+1)+z)^2 =
      n^2*(n^4+(n^2*(n+1)+z))+n^5+2*n^3*z+n^2*z+z^2 := by ring
  rw [expansion] at moment
  omega

end ThreeClauseShape
