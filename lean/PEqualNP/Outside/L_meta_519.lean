module

public import Mathlib

public section

namespace PEqualNP.Outside.L_meta_519

variable {α : Type*} [DecidableEq α] (G : SimpleGraph α)

-- S is the support of an assignment. The output is true exactly when
-- the subgraph induced by S contains an edge.
def hasEdge (S : Finset α) : Prop := ∃ i ∈ S, ∃ j ∈ S, G.Adj i j

def extend (S : Finset α) (u : α) (bit : Bool) : Finset α :=
  if bit then insert u S else S

def residual (u v : α) (S : Finset α) (x y : Bool) : Prop :=
  hasEdge G (extend (extend S u x) v y)

private lemma insert_edge (S : Finset α) (u : α) :
    hasEdge G (insert u S) ↔ hasEdge G S ∨ ∃ i ∈ S, G.Adj u i := by
  simp only [hasEdge, Finset.exists_mem_insert, G.loopless.irrefl, false_or]
  constructor
  · rintro (h | ⟨i, hi, h | h⟩)
    · exact Or.inr h
    · exact Or.inr ⟨i, hi, h.symm⟩
    · exact Or.inl ⟨i, hi, h⟩
  · rintro (⟨i, hi, h⟩ | h)
    · exact Or.inr ⟨i, hi, Or.inr h⟩
    · exact Or.inl h

-- Every restriction at an adjacent pair has a three-bit description:
-- an outside edge, an active neighbor of u, and an active neighbor of v.
theorem describe (u v : α) (uv : G.Adj u v) (S : Finset α) (x y : Bool) :
    residual G u v S x y ↔ hasEdge G S ∨
      (x = true ∧ ∃ i ∈ S, G.Adj u i) ∨
      (y = true ∧ ∃ i ∈ S, G.Adj v i) ∨ (x = true ∧ y = true) := by
  cases x <;> cases y <;>
    simp [residual, extend, insert_edge, uv.symm]

private def row (t : Fin 5) (x y : Bool) : Bool :=
  ![x && y, x, y, x || y, true] t

private theorem rows_separate : ∀ i j : Fin 5,
    (∀ x y, row i x y = row j x y) → i = j := by decide

-- The four vertices a,u,v,b induce a path. Any further edge with
-- endpoints outside {u,v} supplies the constantly true restriction.
-- A two-bit message from outside cannot distinguish all five rows.
theorem no_two_bit_encoding (a u v b k l : α)
    (au : G.Adj a u) (uv : G.Adj u v) (vb : G.Adj v b)
    (av : ¬ G.Adj a v) (ub : ¬ G.Adj u b) (ab : ¬ G.Adj a b)
    (ku : k ≠ u) (kv : k ≠ v) (lu : l ≠ u) (lv : l ≠ v) (kl : G.Adj k l)
    (encode : Finset α → Bool × Bool) (decode : Bool × Bool → Bool → Bool → Bool) :
    ¬ ∀ S, u ∉ S → v ∉ S → ∀ x y,
      (decode (encode S) x y = true ↔ residual G u v S x y) := by
  intro correct
  let supports : Fin 5 → Finset α := ![∅, {a}, {b}, {a,b}, {k,l}]
  have ua : u ≠ a := au.ne.symm
  have vb_ne : v ≠ b := vb.ne
  have va : v ≠ a := by rintro rfl; exact ab vb
  have bu : u ≠ b := by rintro rfl; exact ab au
  have outside (i : Fin 5) : u ∉ supports i ∧ v ∉ supports i := by
    fin_cases i <;> simp [supports, ua, vb_ne, va, bu, Ne.symm ku, Ne.symm kv,
      Ne.symm lu, Ne.symm lv]
  have rows (i : Fin 5) (x y : Bool) :
      residual G u v (supports i) x y ↔ row i x y = true := by
    rw [describe G u v uv]
    fin_cases i <;> cases x <;> cases y <;>
      simp [supports, row, hasEdge, au.symm, vb,
        ub, ab, mt SimpleGraph.Adj.symm av, mt SimpleGraph.Adj.symm ab, kl]
  have inj : Function.Injective (fun i => encode (supports i)) := by
    intro i j same
    apply rows_separate
    intro x y
    have hi := (correct _ (outside i).1 (outside i).2 x y).trans (rows i x y)
    have hj := (correct _ (outside j).1 (outside j).2 x y).trans (rows j x y)
    change encode (supports i) = encode (supports j) at same
    rw [same] at hi
    have both := hi.symm.trans hj
    cases h : row i x y <;> cases h' : row j x y <;> simp_all only [Bool.false_eq_true, iff_false, iff_true, not_true_eq_false]
  have bound := Fintype.card_le_of_injective _ inj
  simp at bound

end PEqualNP.Outside.L_meta_519
