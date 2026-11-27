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

open PEqualNP.MetaComplexity
open Finset

namespace EqualityTree33619

variable {n : ℕ}

theorem orRejected (a b : DMFormula n) (s : Finset (Fin n))
    (reject : (a.or b).eval (on s) = false) :
    a.eval (on s) = false ∧ b.eval (on s) = false := by
  cases aa : a.eval (on s) <;> cases bb : b.eval (on s) <;>
    simp_all [DMFormula.eval]

theorem orPairPartition (a b : DMFormula n) (i j : Fin n)
    (first : (a.or b).eval (on {i}) = false)
    (second : (a.or b).eval (on {j}) = false)
    (accepted : (a.or b).eval (on {i,j}) = true) :
    (i ∈ support a ∧ j ∈ support a) ∨ (i ∈ support b ∧ j ∈ support b) := by
  have bothIn (tree : DMFormula n) (noI : tree.eval (on {i}) = false)
      (noJ : tree.eval (on {j}) = false) (yes : tree.eval (on {i,j}) = true) :
      i ∈ support tree ∧ j ∈ support tree := by
    constructor
    · by_contra absent
      have swapped := yes
      rw [show ({i,j} : Finset (Fin n)) = {j,i} by ext; simp [or_comm]] at swapped
      rw [singletonFromPair tree j i absent swapped] at noJ
      contradiction
    · by_contra absent
      rw [singletonFromPair tree i j absent yes] at noI
      contradiction
  have onlyI := orRejected a b {i} first
  have onlyJ := orRejected a b {j} second
  change (a.eval (on {i,j}) || b.eval (on {i,j})) = true at accepted
  rcases Bool.or_eq_true_iff.mp accepted with yes | yes
  · exact Or.inl (bothIn a onlyI.1 onlyJ.1 yes)
  · exact Or.inr (bothIn b onlyI.2 onlyJ.2 yes)

#print axioms orPairPartition

end EqualityTree33619

open PEqualNP.MetaComplexity
open Finset

namespace EqualityTree33619

variable {n : ℕ}

theorem onPairComm (i j : Fin n) :
    ({i,j} : Finset (Fin n)) = {j,i} := by
  ext k
  simp [or_comm]

theorem firstChildSingleton (a b : DMFormula n) (pa : positive a) (pb : positive b)
    (separate : Disjoint (support a) (support b)) (i j x : Fin n)
    (member : x ∈ support a) (fromPair : x = i ∨ x = j)
    (accepted : (a.and b).eval (on {i,j}) = true) :
    a.eval (on {x}) = true := by
  have chosen := andPairSplit a b pa pb separate i j accepted
  have aa : a.eval (on {i,j}) = true := by
    change (a.eval (on {i,j}) && b.eval (on {i,j})) = true at accepted
    exact (Bool.and_eq_true_iff.mp accepted).1
  rcases fromPair with equal | equal <;> subst x
  · rcases chosen with placement | placement
    · exact singletonFromPair a i j (fun h => Finset.disjoint_left.mp separate h placement.2) aa
    · exact (Finset.disjoint_left.mp separate member placement.2).elim
  · rcases chosen with placement | placement
    · exact (Finset.disjoint_left.mp separate member placement.2).elim
    · exact singletonFromPair a j i (fun h => Finset.disjoint_left.mp separate h placement.2) (by
        rwa [onPairComm])

theorem andBlockChildren {I : Type} [DecidableEq I] (indices : Finset I)
    (left right : I → Fin n) (a b : DMFormula n) (pa : positive a) (pb : positive b)
    (separate : Disjoint (support a) (support b))
    (coverage : ∀ x ∈ support a ∪ support b, ∃ i ∈ indices, x = left i ∨ x = right i)
    (diagonal : ∀ i ∈ indices, (a.and b).eval (on {left i,right i}) = true)
    (s : Finset (Fin n)) :
    (a.and b).eval (on s) = true ↔
      (∃ x ∈ support a, x ∈ s) ∧ (∃ y ∈ support b, y ∈ s) := by
  have one (x : Fin n) (hx : x ∈ support a) : a.eval (on {x}) = true := by
    obtain ⟨i, hi, pair⟩ := coverage x (Finset.mem_union_left _ hx)
    exact firstChildSingleton a b pa pb separate (left i) (right i) x hx pair (diagonal i hi)
  have two (x : Fin n) (hx : x ∈ support b) : b.eval (on {x}) = true := by
    obtain ⟨i, hi, pair⟩ := coverage x (Finset.mem_union_right _ hx)
    apply firstChildSingleton b a pb pa separate.symm (left i) (right i) x hx pair
    simpa [DMFormula.eval, Bool.and_comm] using diagonal i hi
  change (a.eval (on s) && b.eval (on s)) = true ↔ _
  rw [Bool.and_eq_true_iff, evalOfSingletons a pa one, evalOfSingletons b pb two]
  simp

def diagonalHit {I : Type} (indices : Finset I) (left right : I → Fin n)
    (s : Finset (Fin n)) : Prop :=
  ∃ i ∈ indices, left i ∈ s ∧ right i ∈ s

def sameBankHit {I : Type} (indices : Finset I) (bank : I → Fin n)
    (s : Finset (Fin n)) : Prop :=
  ∃ i ∈ indices, ∃ j ∈ indices, i ≠ j ∧ bank i ∈ s ∧ bank j ∈ s

theorem andBlockEvaluation {I : Type} [DecidableEq I] (indices : Finset I)
    (left right : I → Fin n) (a b : DMFormula n) (pa : positive a) (pb : positive b)
    (separate : Disjoint (support a) (support b))
    (coverage : ∀ x ∈ support a ∪ support b, ∃ i ∈ indices, x = left i ∨ x = right i)
    (diagonal : ∀ i ∈ indices, (a.and b).eval (on {left i,right i}) = true)
    (offDiagonal : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      (a.and b).eval (on {left i,right j}) = false)
    (s : Finset (Fin n)) :
    (a.and b).eval (on s) = true ↔
      diagonalHit indices left right s ∨ sameBankHit indices left s ∨ sameBankHit indices right s := by
  have childView := fun t => andBlockChildren indices left right a b pa pb separate coverage diagonal t
  have split := fun i hi => andPairSplit a b pa pb separate (left i) (right i) (diagonal i hi)
  have invalid (i j : I) (hi : i ∈ indices) (hj : j ∈ indices) (hij : i ≠ j)
      (x y : Fin n) (ha : x ∈ support a) (hb : y ∈ support b)
      (hx : x ∈ ({left i,right j} : Finset (Fin n)))
      (hy : y ∈ ({left i,right j} : Finset (Fin n))) : False := by
    have yes := (childView {left i,right j}).mpr ⟨⟨x,ha,hx⟩,⟨y,hb,hy⟩⟩
    rw [offDiagonal i hi j hj hij] at yes
    contradiction
  have leftHits (i j : I) (hi : i ∈ indices) (hj : j ∈ indices) (hij : i ≠ j)
      (hitI : left i ∈ s) (hitJ : left j ∈ s) :
      (∃ x ∈ support a, x ∈ s) ∧ (∃ y ∈ support b, y ∈ s) := by
    rcases split i hi with si | si <;> rcases split j hj with sj | sj
    · exact (invalid i j hi hj hij (left i) (right j) si.1 sj.2 (by simp) (by simp)).elim
    · exact ⟨⟨_, si.1, hitI⟩, ⟨_, sj.2, hitJ⟩⟩
    · exact ⟨⟨_, sj.1, hitJ⟩, ⟨_, si.2, hitI⟩⟩
    · exact (invalid i j hi hj hij (right j) (left i) sj.1 si.2 (by simp) (by simp)).elim
  have rightHits (i j : I) (hi : i ∈ indices) (hj : j ∈ indices) (hij : i ≠ j)
      (hitI : right i ∈ s) (hitJ : right j ∈ s) :
      (∃ x ∈ support a, x ∈ s) ∧ (∃ y ∈ support b, y ∈ s) := by
    rcases split i hi with si | si <;> rcases split j hj with sj | sj
    · exact (invalid i j hi hj hij (left i) (right j) si.1 sj.2 (by simp) (by simp)).elim
    · exact ⟨⟨_, sj.1, hitJ⟩, ⟨_, si.2, hitI⟩⟩
    · exact ⟨⟨_, si.1, hitI⟩, ⟨_, sj.2, hitJ⟩⟩
    · exact (invalid i j hi hj hij (right j) (left i) sj.1 si.2 (by simp) (by simp)).elim
  rw [childView]
  constructor
  · rintro ⟨⟨x,ha,hx⟩,⟨y,hb,hy⟩⟩
    obtain ⟨i,hi,xPair⟩ := coverage x (Finset.mem_union_left _ ha)
    obtain ⟨j,hj,yPair⟩ := coverage y (Finset.mem_union_right _ hb)
    have different : x ≠ y := fun e => Finset.disjoint_left.mp separate ha (e.symm ▸ hb)
    rcases xPair with rfl | rfl <;> rcases yPair with rfl | rfl
    · exact Or.inr (Or.inl ⟨i,hi,j,hj,fun eq => different (congrArg left eq),hx,hy⟩)
    · by_cases eq : i = j
      · subst j
        exact Or.inl ⟨i,hi,hx,hy⟩
      · exact (invalid i j hi hj eq _ _ ha hb (by simp) (by simp)).elim
    · by_cases eq : j = i
      · subst j
        exact Or.inl ⟨i,hi,hy,hx⟩
      · exact (invalid j i hj hi eq _ _ ha hb (by simp) (by simp)).elim
    · exact Or.inr (Or.inr ⟨i,hi,j,hj,fun eq => different (congrArg right eq),hx,hy⟩)
  · rintro (⟨i,hi,hx,hy⟩ | ⟨i,hi,j,hj,ne,hx,hy⟩ | ⟨i,hi,j,hj,ne,hx,hy⟩)
    · rcases split i hi with si | si
      · exact ⟨⟨_,si.1,hx⟩,⟨_,si.2,hy⟩⟩
      · exact ⟨⟨_,si.1,hy⟩,⟨_,si.2,hx⟩⟩
    · exact leftHits i j hi hj ne hx hy
    · exact rightHits i j hi hj ne hx hy

#print axioms andBlockEvaluation

end EqualityTree33619

open PEqualNP.MetaComplexity
open Finset

namespace EqualityTree33619

variable {n : ℕ} {I : Type}

def pairSupport (tree : DMFormula n) (indices : Finset I) (left right : I → Fin n) : Prop :=
  ∀ x, x ∈ support tree ↔ ∃ i ∈ indices, x = left i ∨ x = right i

structure equalityTests (tree : DMFormula n) (indices : Finset I) (left right : I → Fin n) : Prop where
  rejectsLeft : ∀ i ∈ indices, tree.eval (on {left i}) = false
  rejectsRight : ∀ i ∈ indices, tree.eval (on {right i}) = false
  acceptsDiagonal : ∀ i ∈ indices, tree.eval (on {left i,right i}) = true
  rejectsOffDiagonal : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
    tree.eval (on {left i,right j}) = false

def childPairs (indices : Finset I) (left : I → Fin n) (tree : DMFormula n) : Finset I :=
  indices.filter fun i => left i ∈ support tree

theorem orBranchProfile (a b : DMFormula n) (separate : Disjoint (support a) (support b))
    (indices : Finset I) (left right : I → Fin n)
    (coverage : pairSupport (a.or b) indices left right)
    (tests : equalityTests (a.or b) indices left right) :
    pairSupport a (childPairs indices left a) left right ∧
      equalityTests a (childPairs indices left a) left right := by
  have placement (i : I) (hi : i ∈ indices) :=
    orPairPartition a b (left i) (right i)
      (tests.rejectsLeft i hi) (tests.rejectsRight i hi) (tests.acceptsDiagonal i hi)
  have records (i : I) (hi : i ∈ childPairs indices left a) :
      i ∈ indices ∧ left i ∈ support a ∧ right i ∈ support a := by
    obtain ⟨inIndices, inA⟩ := Finset.mem_filter.mp hi
    rcases placement i inIndices with aa | bb
    · exact ⟨inIndices,aa.1,aa.2⟩
    · exact (Finset.disjoint_left.mp separate inA bb.1).elim
  constructor
  · intro x
    constructor
    · intro hx
      have union : x ∈ support (a.or b) := Finset.mem_union_left _ hx
      obtain ⟨i, hi, pair⟩ := (coverage x).mp union
      have leftIn : left i ∈ support a := by
        rcases placement i hi with aa | bb
        · exact aa.1
        · rcases pair with equal | equal <;> subst x
          · exact (Finset.disjoint_left.mp separate hx bb.1).elim
          · exact (Finset.disjoint_left.mp separate hx bb.2).elim
      exact ⟨i,Finset.mem_filter.mpr ⟨hi,leftIn⟩,pair⟩
    · rintro ⟨i, hi, pair⟩
      obtain ⟨_, leftIn, rightIn⟩ := records i hi
      rcases pair with equal | equal <;> subst x <;> assumption
  · constructor
    · intro i hi
      exact (orRejected a b {left i} (tests.rejectsLeft i (records i hi).1)).1
    · intro i hi
      exact (orRejected a b {right i} (tests.rejectsRight i (records i hi).1)).1
    · intro i hi
      obtain ⟨inIndices,leftIn,rightIn⟩ := records i hi
      have noB : b.eval (on {left i,right i}) = b.eval (on {left i}) := by
        apply evalSupport
        intro x hx
        have notRight : x ≠ right i := fun h => Finset.disjoint_left.mp separate rightIn (h ▸ hx)
        simp [on,notRight]
      have accepts := tests.acceptsDiagonal i inIndices
      change (a.eval (on {left i,right i}) || b.eval (on {left i,right i})) = true at accepts
      rw [noB, (orRejected a b {left i} (tests.rejectsLeft i inIndices)).2, Bool.or_false] at accepts
      exact accepts
    · intro i hi j hj different
      exact (orRejected a b {left i,right j}
        (tests.rejectsOffDiagonal i (records i hi).1 j (records j hj).1 different)).1

theorem orProfilePartition (a b : DMFormula n) (separate : Disjoint (support a) (support b))
    (indices : Finset I) (left right : I → Fin n)
    (coverage : pairSupport (a.or b) indices left right)
    (tests : equalityTests (a.or b) indices left right) :
    let P := childPairs indices left a
    let Q := childPairs indices left b
    (pairSupport a P left right ∧ equalityTests a P left right) ∧
    (pairSupport b Q left right ∧ equalityTests b Q left right) ∧
    Disjoint P Q ∧ (∀ i, i ∈ indices ↔ i ∈ P ∨ i ∈ Q) := by
  dsimp
  have swappedCoverage : pairSupport (b.or a) indices left right := by
    simpa only [pairSupport, support, Finset.union_comm] using coverage
  have swappedTests : equalityTests (b.or a) indices left right := by
    constructor
    · intro i hi
      simpa only [DMFormula.eval, Bool.or_comm] using tests.rejectsLeft i hi
    · intro i hi
      simpa only [DMFormula.eval, Bool.or_comm] using tests.rejectsRight i hi
    · intro i hi
      simpa only [DMFormula.eval, Bool.or_comm] using tests.acceptsDiagonal i hi
    · intro i hi j hj different
      simpa only [DMFormula.eval, Bool.or_comm] using tests.rejectsOffDiagonal i hi j hj different
  refine ⟨orBranchProfile a b separate indices left right coverage tests,
    orBranchProfile b a separate.symm indices left right swappedCoverage swappedTests, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hj
    exact Finset.disjoint_left.mp separate (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  · intro i
    constructor
    · intro hi
      rcases orPairPartition a b (left i) (right i) (tests.rejectsLeft i hi)
        (tests.rejectsRight i hi) (tests.acceptsDiagonal i hi) with aa | bb
      · exact Or.inl (Finset.mem_filter.mpr ⟨hi,aa.1⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hi,bb.1⟩)
    · rintro (hi | hi) <;> exact (Finset.mem_filter.mp hi).1

#print axioms orProfilePartition

end EqualityTree33619

open PEqualNP.MetaComplexity
open Finset

namespace EqualityTree33619

variable {n : ℕ} {I : Type} [DecidableEq I]

def disjointChildren : DMFormula n → Prop
  | .lit _ _ => True
  | .and a b => (disjointChildren a ∧ disjointChildren b) ∧ Disjoint (support a) (support b)
  | .or a b => (disjointChildren a ∧ disjointChildren b) ∧ Disjoint (support a) (support b)

def isMatching (indices : Finset I) (edges : Finset (Finset I)) : Prop :=
  (∀ e ∈ edges, e.card = 2 ∧ e ⊆ indices) ∧
    (∀ e ∈ edges, ∀ f ∈ edges, e ≠ f → Disjoint e f)

def matchingHit (edges : Finset (Finset I)) (left right : I → Fin n) (s : Finset (Fin n)) : Prop :=
  ∃ e ∈ edges, (∀ i ∈ e, left i ∈ s) ∨ (∀ i ∈ e, right i ∈ s)

theorem matchingFromAnd (a b : DMFormula n) (pa : positive a) (pb : positive b)
    (separate : Disjoint (support a) (support b)) (indices : Finset I)
    (left right : I → Fin n) (coverage : pairSupport (a.and b) indices left right)
    (tests : equalityTests (a.and b) indices left right) :
    ∃ edges, isMatching indices edges ∧ ∀ s : Finset (Fin n),
      (a.and b).eval (on s) = true ↔ diagonalHit indices left right s ∨ matchingHit edges left right s := by
  have localCoverage : ∀ x ∈ support a ∪ support b, ∃ i ∈ indices, x = left i ∨ x = right i :=
    fun x hx => (coverage x).mp hx
  have evaluation := andBlockEvaluation indices left right a b pa pb separate localCoverage
    tests.acceptsDiagonal tests.rejectsOffDiagonal
  by_cases pair : ∃ i ∈ indices, ∃ j ∈ indices, i ≠ j
  · obtain ⟨i,hi,j,hj,ne⟩ := pair
    have allPairs (u v : I) (hu : u ∈ indices) (hv : v ∈ indices) (different : u ≠ v) :
        ({u,v} : Finset I) = indices := by
      have upper := andBlockAtMostTwo indices left right a b pa pb separate
        tests.acceptsDiagonal tests.rejectsOffDiagonal
      have sub : ({u,v} : Finset I) ⊆ indices := by
        intro x hx
        rcases Finset.mem_insert.mp hx with hx | hx
        · exact hx ▸ hu
        · exact (Finset.mem_singleton.mp hx) ▸ hv
      exact Finset.eq_of_subset_of_card_le sub (by simpa [different] using upper)
    have edgeCard : indices.card = 2 := by
      rw [← allPairs i j hi hj ne]
      simp [ne]
    refine ⟨{indices}, ⟨?_,?_⟩,?_⟩
    · intro e he
      rw [Finset.mem_singleton.mp he]
      exact ⟨edgeCard,Finset.Subset.refl indices⟩
    · intro e he f hf diff
      exact (diff ((Finset.mem_singleton.mp he).trans (Finset.mem_singleton.mp hf).symm)).elim
    · intro s
      have bank (f : I → Fin n) : sameBankHit indices f s ↔ ∀ u ∈ indices, f u ∈ s := by
        constructor
        · rintro ⟨u,hu,v,hv,distinct,su,sv⟩ x hx
          rw [← allPairs u v hu hv distinct] at hx
          simpa [Finset.mem_insert, Finset.mem_singleton] using
            (show x ∈ ({u,v} : Finset I) → f x ∈ s from by
              intro mem
              simp only [Finset.mem_insert, Finset.mem_singleton] at mem
              rcases mem with eq | eq
              · exact eq ▸ su
              · exact eq ▸ sv) hx
        · intro all
          exact ⟨i,hi,j,hj,ne,all i hi,all j hj⟩
      simpa only [bank, matchingHit, Finset.mem_singleton, exists_eq_left] using evaluation s
  · refine ⟨∅,⟨by simp, by simp⟩,?_⟩
    intro s
    have emptyBank (f : I → Fin n) : ¬ sameBankHit indices f s := by
      rintro ⟨i,hi,j,hj,ne,_,_⟩
      exact pair ⟨i,hi,j,hj,ne⟩
    simpa [emptyBank, matchingHit] using evaluation s

theorem treeHasMatching (tree : DMFormula n) (indices : Finset I) (left right : I → Fin n)
    (pos : positive tree) (once : disjointChildren tree)
    (coverage : pairSupport tree indices left right) (tests : equalityTests tree indices left right) :
    ∃ edges, isMatching indices edges ∧ ∀ s : Finset (Fin n),
      tree.eval (on s) = true ↔ diagonalHit indices left right s ∨ matchingHit edges left right s := by
  induction tree generalizing indices with
  | lit x sign =>
    have hsign : sign = true := pos
    have inSupport : x ∈ support (.lit x sign) := by simp [support]
    obtain ⟨i,hi,bank⟩ := (coverage x).mp inSupport
    rcases bank with eq | eq <;> subst x
    · have rejected := tests.rejectsLeft i hi
      simp [DMFormula.eval, hsign, on] at rejected
    · have rejected := tests.rejectsRight i hi
      simp [DMFormula.eval, hsign, on] at rejected
  | and a b _ _ =>
    exact matchingFromAnd a b pos.1 pos.2 once.2 indices left right coverage tests
  | or a b ihA ihB =>
    obtain ⟨profileA, profileB, separated, partition⟩ :=
      orProfilePartition a b once.2 indices left right coverage tests
    obtain ⟨edgesA,hA,evalA⟩ := ihA _ pos.1 once.1.1 profileA.1 profileA.2
    obtain ⟨edgesB,hB,evalB⟩ := ihB _ pos.2 once.1.2 profileB.1 profileB.2
    have shapeA (e) (he : e ∈ edgesA) : e.card = 2 ∧ e ⊆ indices :=
      ⟨(hA.1 e he).1, fun i hi => (partition i).mpr (Or.inl ((hA.1 e he).2 hi))⟩
    have shapeB (e) (he : e ∈ edgesB) : e.card = 2 ∧ e ⊆ indices :=
      ⟨(hB.1 e he).1, fun i hi => (partition i).mpr (Or.inr ((hB.1 e he).2 hi))⟩
    have across (e) (he : e ∈ edgesA) (f) (hf : f ∈ edgesB) : Disjoint e f :=
      separated.mono (hA.1 e he).2 (hB.1 f hf).2
    refine ⟨edgesA ∪ edgesB, ⟨?_,?_⟩, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact shapeA e he
      · exact shapeB e he
    · intro e he f hf different
      rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
      · exact hA.2 e he f hf different
      · exact across e he f hf
      · exact (across f hf e he).symm
      · exact hB.2 e he f hf different
    · intro s
      have combinedDiag : diagonalHit indices left right s ↔
          diagonalHit (childPairs indices left a) left right s ∨
          diagonalHit (childPairs indices left b) left right s := by
        constructor
        · rintro ⟨i,hi,hl,hr⟩
          rcases (partition i).mp hi with hi | hi
          · exact Or.inl ⟨i,hi,hl,hr⟩
          · exact Or.inr ⟨i,hi,hl,hr⟩
        · rintro (⟨i,hi,hl,hr⟩ | ⟨i,hi,hl,hr⟩)
          · exact ⟨i,(partition i).mpr (Or.inl hi),hl,hr⟩
          · exact ⟨i,(partition i).mpr (Or.inr hi),hl,hr⟩
      have combinedMatch : matchingHit (edgesA ∪ edgesB) left right s ↔
          matchingHit edgesA left right s ∨ matchingHit edgesB left right s := by
        constructor
        · rintro ⟨e,he,hit⟩
          rcases Finset.mem_union.mp he with he | he
          · exact Or.inl ⟨e,he,hit⟩
          · exact Or.inr ⟨e,he,hit⟩
        · rintro (⟨e,he,hit⟩ | ⟨e,he,hit⟩)
          · exact ⟨e,Finset.mem_union_left _ he,hit⟩
          · exact ⟨e,Finset.mem_union_right _ he,hit⟩
      change (a.eval (on s) || b.eval (on s)) = true ↔ _
      rw [Bool.or_eq_true_iff, evalA, evalB, combinedDiag, combinedMatch]
      tauto

#print axioms treeHasMatching

end EqualityTree33619

open PEqualNP.MetaComplexity
open Finset

namespace EqualityTree33619

variable {n : ℕ} {I : Type} [DecidableEq I]

theorem recoverEdge (tree : DMFormula n) (indices : Finset I) (edges : Finset (Finset I))
    (left right : I → Fin n) (leftInj : Function.Injective left)
    (differentBanks : ∀ i j, left i ≠ right j) (shape : isMatching indices edges)
    (evaluation : ∀ s : Finset (Fin n),
      tree.eval (on s) = true ↔ diagonalHit indices left right s ∨ matchingHit edges left right s)
    (pair : Finset I) (size : pair.card = 2) :
    tree.eval (on (pair.image left)) = true ↔ pair ∈ edges := by
  have rightAbsent (i : I) : right i ∉ pair.image left := by
    intro member
    obtain ⟨j,_,equal⟩ := Finset.mem_image.mp member
    exact differentBanks j i equal
  rw [evaluation]
  constructor
  · rintro (⟨i,_,_,present⟩ | ⟨found,foundMem,occurs⟩)
    · exact (rightAbsent i present).elim
    · rcases occurs with fromLeft | fromRight
      · have contained : found ⊆ pair := by
          intro i hi
          obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp (fromLeft i hi)
          exact leftInj eq ▸ hj
        have eq := Finset.eq_of_subset_of_card_le contained (by rw [size, (shape.1 found foundMem).1])
        exact eq ▸ foundMem
      · obtain ⟨i,hi⟩ := Finset.card_pos.mp (by rw [(shape.1 found foundMem).1]; decide : 0 < found.card)
        exact (rightAbsent i (fromRight i hi)).elim
  · intro mem
    exact Or.inr ⟨pair,mem,Or.inl (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩)⟩

theorem uniqueMatching (tree : DMFormula n) (indices : Finset I) (left right : I → Fin n)
    (leftInj : Function.Injective left) (differentBanks : ∀ i j, left i ≠ right j)
    (S T : Finset (Finset I)) (shapeS : isMatching indices S) (shapeT : isMatching indices T)
    (evalS : ∀ s, tree.eval (on s) = true ↔ diagonalHit indices left right s ∨ matchingHit S left right s)
    (evalT : ∀ s, tree.eval (on s) = true ↔ diagonalHit indices left right s ∨ matchingHit T left right s) :
    S = T := by
  ext e
  constructor
  · intro eS
    have ec := (shapeS.1 e eS).1
    exact (recoverEdge tree indices T left right leftInj differentBanks shapeT evalT e ec).mp
      ((recoverEdge tree indices S left right leftInj differentBanks shapeS evalS e ec).mpr eS)
  · intro eT
    have ec := (shapeT.1 e eT).1
    exact (recoverEdge tree indices S left right leftInj differentBanks shapeS evalS e ec).mp
      ((recoverEdge tree indices T left right leftInj differentBanks shapeT evalT e ec).mpr eT)

#print axioms uniqueMatching

end EqualityTree33619
