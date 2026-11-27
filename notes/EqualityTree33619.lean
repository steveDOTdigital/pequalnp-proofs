import PEqualNP.Defs
import PEqualNP.Defs.DeMorganFormula

open PEqualNP.MetaComplexity
open Finset

namespace EqualityTree33619

variable {n : ℕ}

def positive : DMFormula n → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

def support : DMFormula n → Finset (Fin n)
  | .lit i _ => {i}
  | .and a b => support a ∪ support b
  | .or a b => support a ∪ support b

def on (s : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ s)

theorem evalSupport (tree : DMFormula n) (x y : Fin n → Bool)
    (same : ∀ i ∈ support tree, x i = y i) : tree.eval x = tree.eval y := by
  induction tree with
  | lit i b =>
    have eq : x i = y i := same i (by simp [support])
    simp [DMFormula.eval, eq]
  | and a b ha hb =>
    exact congrArg₂ (· && ·)
      (ha (fun i hi => same i (by simpa [support] using Or.inl hi)))
      (hb (fun i hi => same i (by simpa [support] using Or.inr hi)))
  | or a b ha hb =>
    exact congrArg₂ (· || ·)
      (ha (fun i hi => same i (by simpa [support] using Or.inl hi)))
      (hb (fun i hi => same i (by simpa [support] using Or.inr hi)))

theorem evalZero (tree : DMFormula n) (ok : positive tree) :
    tree.eval (fun _ => false) = false := by
  induction tree with
  | lit i b =>
    have h : b = true := ok
    simp [DMFormula.eval, h]
  | and a b ha hb =>
    exact congrArg₂ (· && ·) (ha ok.1) (hb ok.2)
  | or a b ha hb =>
    exact congrArg₂ (· || ·) (ha ok.1) (hb ok.2)

theorem evalMonotone (tree : DMFormula n) (ok : positive tree) (x y : Fin n → Bool)
    (ordered : ∀ i, x i ≤ y i) : tree.eval x ≤ tree.eval y := by
  induction tree with
  | lit i b =>
    have h : b = true := ok
    simpa [DMFormula.eval, h] using ordered i
  | and a b ha hb =>
    have one := ha ok.1
    have two := hb ok.2
    change (a.eval x && b.eval x) ≤ (a.eval y && b.eval y)
    cases ax : a.eval x <;> cases bx : b.eval x <;>
      cases ay : a.eval y <;> cases byy : b.eval y <;>
      simp_all [show ¬ true ≤ false by decide]
  | or a b ha hb =>
    have one := ha ok.1
    have two := hb ok.2
    change (a.eval x || b.eval x) ≤ (a.eval y || b.eval y)
    cases ax : a.eval x <;> cases bx : b.eval x <;>
      cases ay : a.eval y <;> cases byy : b.eval y <;>
      simp_all [show ¬ true ≤ false by decide]

theorem evalOfSingletons (tree : DMFormula n) (ok : positive tree)
    (all : ∀ i ∈ support tree, tree.eval (on {i}) = true) (s : Finset (Fin n)) :
    tree.eval (on s) = decide (∃ i ∈ support tree, i ∈ s) := by
  by_cases overlap : ∃ i ∈ support tree, i ∈ s
  · obtain ⟨i,hi,si⟩ := overlap
    have lift (j : Fin n) : on {i} j ≤ on s j := by
      by_cases eq : j = i
      · subst j
        simp [on,si]
      · simp [on,eq]
    have accepts := evalMonotone tree ok (on {i}) (on s) lift
    rw [all i hi] at accepts
    have yes : tree.eval (on s) = true := by
      cases val : tree.eval (on s) with
      | false => exact False.elim ((by decide : ¬ true ≤ false) (val ▸ accepts))
      | true => rfl
    rw [yes]
    symm
    exact decide_eq_true ⟨i,hi,si⟩
  · have equal : tree.eval (on s) = tree.eval (fun _ => false) := by
      apply evalSupport
      intro i hi
      have no : i ∉ s := fun si => overlap ⟨i,hi,si⟩
      simp [on,no]
    rw [equal, evalZero tree ok]
    simp [overlap]

theorem splitCardAtMostTwo {I : Type} [DecidableEq I] (indices : Finset I)
    (side : I → Bool) (different : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j → side i ≠ side j) :
    indices.card ≤ 2 := by
  let embed : {i // i ∈ indices} → Bool := fun i => side i.val
  have inj : Function.Injective embed := by
    intro a b e
    apply Subtype.ext
    by_contra contrary
    exact different a.val a.property b.val b.property contrary e
  simpa using Fintype.card_le_of_injective embed inj

#print axioms evalOfSingletons
#print axioms splitCardAtMostTwo

end EqualityTree33619


open PEqualNP.MetaComplexity
open Finset

namespace EqualityTree33619

variable {n : ℕ}

theorem seesInput (tree : DMFormula n) (ok : positive tree) (s : Finset (Fin n))
    (accepted : tree.eval (on s) = true) : ∃ i ∈ support tree, i ∈ s := by
  by_contra no
  have equal : tree.eval (on s) = tree.eval (fun _ => false) := by
    apply evalSupport
    intro i hi
    have absent : i ∉ s := fun member => no ⟨i,hi,member⟩
    simp [on,absent]
  rw [equal, evalZero tree ok] at accepted
  contradiction

theorem andPairSplit (a b : DMFormula n) (pa : positive a) (pb : positive b)
    (separate : Disjoint (support a) (support b)) (i j : Fin n)
    (accepted : (a.and b).eval (on {i,j}) = true) :
    (i ∈ support a ∧ j ∈ support b) ∨ (j ∈ support a ∧ i ∈ support b) := by
  change (a.eval (on {i,j}) && b.eval (on {i,j})) = true at accepted
  have both := Bool.and_eq_true_iff.mp accepted
  obtain ⟨x,xa,xPair⟩ := seesInput a pa {i,j} both.1
  obtain ⟨y,yb,yPair⟩ := seesInput b pb {i,j} both.2
  have unequal : x ≠ y := fun equal => Finset.disjoint_left.mp separate xa (equal.symm ▸ yb)
  simp only [Finset.mem_insert, Finset.mem_singleton] at xPair yPair
  rcases xPair with rfl | rfl
  · rcases yPair with rfl | rfl
    · exact (unequal rfl).elim
    · exact Or.inl ⟨xa,yb⟩
  · rcases yPair with rfl | rfl
    · exact Or.inr ⟨xa,yb⟩
    · exact (unequal rfl).elim

theorem singletonFromPair (a : DMFormula n) (i j : Fin n) (absent : j ∉ support a)
    (accepted : a.eval (on {i,j}) = true) : a.eval (on {i}) = true := by
  rw [← accepted]
  apply evalSupport
  intro x hx
  have unequal : x ≠ j := fun h => absent (h ▸ hx)
  simp [on,unequal]

theorem andBlockAtMostTwo {I : Type} [DecidableEq I] (indices : Finset I)
    (left right : I → Fin n) (a b : DMFormula n) (pa : positive a) (pb : positive b)
    (separate : Disjoint (support a) (support b))
    (diagonal : ∀ i ∈ indices, (a.and b).eval (on {left i,right i}) = true)
    (offDiagonal : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      (a.and b).eval (on {left i,right j}) = false) :
    indices.card ≤ 2 := by
  have split (i : I) (hi : i ∈ indices) :=
    andPairSplit a b pa pb separate (left i) (right i) (diagonal i hi)
  have hdiag (i : I) (hi : i ∈ indices) :
      a.eval (on {left i,right i}) = true ∧ b.eval (on {left i,right i}) = true := by
    simpa only [DMFormula.eval, Bool.and_eq_true_iff] using diagonal i hi
  have flip (i : I) : ({right i,left i} : Finset (Fin n)) = {left i,right i} := by
    ext x
    simp [or_comm]
  have lift (tree : DMFormula n) (positiveTree : positive tree) (i j : Fin n)
      (accepted : tree.eval (on {i}) = true) : tree.eval (on {i,j}) = true := by
    cases value : tree.eval (on {i,j}) with
    | true => rfl
    | false =>
      have ordered := evalMonotone tree positiveTree (on {i}) (on {i,j}) (by
        intro k
        by_cases eq : k = i <;> simp [on,eq])
      rw [accepted,value] at ordered
      exact False.elim ((show ¬ true ≤ false by decide) ordered)
  apply splitCardAtMostTwo indices (fun i => decide (left i ∈ support a))
  intro i hi j hj different same
  have reject := offDiagonal i hi j hj different
  have forbidden (aa : a.eval (on {left i,right j}) = true)
      (bb : b.eval (on {left i,right j}) = true) : False := by
    simp [DMFormula.eval,aa,bb] at reject
  rcases split i hi with ih | ih <;> rcases split j hj with jh | jh
  · have ia := singletonFromPair a (left i) (right i)
      (fun h => Finset.disjoint_left.mp separate h ih.2) (hdiag i hi).1
    have jb := singletonFromPair b (right j) (left j)
      (fun h => Finset.disjoint_left.mp separate jh.1 h) (by rw [flip]; exact (hdiag j hj).2)
    exact forbidden (lift a pa _ _ ia) (by
      have yes := lift b pb (right j) (left i) jb
      rwa [show ({right j,left i} : Finset (Fin n)) = {left i,right j} by ext; simp [or_comm]] at yes)
  · have absent : left j ∉ support a := fun h => Finset.disjoint_left.mp separate h jh.2
    simp [ih.1,absent] at same
  · have absent : left i ∉ support a := fun h => Finset.disjoint_left.mp separate h ih.2
    simp [jh.1,absent] at same
  · have ib := singletonFromPair b (left i) (right i)
      (fun h => Finset.disjoint_left.mp separate ih.1 h) (hdiag i hi).2
    have ja := singletonFromPair a (right j) (left j)
      (fun h => Finset.disjoint_left.mp separate h jh.2) (by rw [flip]; exact (hdiag j hj).1)
    exact forbidden (by
      have yes := lift a pa (right j) (left i) ja
      rwa [show ({right j,left i} : Finset (Fin n)) = {left i,right j} by ext; simp [or_comm]] at yes)
      (lift b pb _ _ ib)

#print axioms andBlockAtMostTwo

end EqualityTree33619