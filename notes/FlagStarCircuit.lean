import PEqualNP.Defs.ReadK
import PEqualNP.Defs.TopForm
import FlagCrossRank
import Mathlib.Tactic

namespace FlagStarCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK

inductive Expr (n : ℕ) where
  | raw (v : Fin n)
  | gate (isOr : Bool) (a b : Expr n)

def op (isOr : Bool) := if isOr then GateOp.or else GateOp.and

def Expr.cost {n} : Expr n → ℕ
  | .raw _ => 0
  | .gate _ a b => a.cost + b.cost + 1

def Expr.wire {n} : Expr n → ℕ → ℕ
  | .raw v, _ => v.val
  | .gate _ a b, base => base + a.cost + b.cost

def Expr.emit {n} : Expr n → ℕ → List Gate
  | .raw _, _ => []
  | .gate k a b, base => a.emit base ++ b.emit (base+a.cost) ++
      [⟨op k,[a.wire base,b.wire (base+a.cost)]⟩]

theorem emitLen {n} (t : Expr n) (base) : (t.emit base).length = t.cost := by
  induction t generalizing base with
  | raw => rfl
  | gate k a b ha hb => simp [Expr.emit,Expr.cost,ha,hb,Nat.add_assoc]

theorem wireLt {n} (t : Expr n) (base) (h : n ≤ base) : t.wire base < base+t.cost := by
  cases t with
  | raw v => exact lt_of_lt_of_le v.isLt (by simp [Expr.cost,h])
  | gate k a b => simp [Expr.wire,Expr.cost]; omega

def legal (base : ℕ) : List Gate → Prop
  | [] => True
  | g :: gs => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      (∀ w ∈ g.inputs, w < base) ∧ legal (base+1) gs

theorem legalAppend {a b : List Gate} {base} (ha : legal base a)
    (hb : legal (base+a.length) b) : legal base (a++b) := by
  induction a generalizing base with
  | nil => simpa using hb
  | cons g gs ih =>
    exact ⟨ha.1,ha.2.1,ha.2.2.1,ih ha.2.2.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem emitLegal {n} (t : Expr n) (base) (h : n ≤ base) : legal base (t.emit base) := by
  induction t generalizing base with
  | raw => trivial
  | gate k a b ha hb =>
    dsimp only [Expr.emit]
    apply legalAppend
    · apply legalAppend (ha base h)
      rw [emitLen]; exact hb _ (by omega)
    · simp only [List.length_append,emitLen]
      refine ⟨by cases k <;> simp [op],rfl,?_,trivial⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · have := wireLt a base h; omega
      · have e := List.mem_singleton.mp hw
        subst w
        have := wireLt b (base+a.cost) (by omega)
        omega

theorem legalAt {gs : List Gate} {base : ℕ} (ok : legal base gs) (j : ℕ) (hj : j < gs.length)
    (d : Gate) :
    let g := gs.getD j d
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      ∀ w ∈ g.inputs, w < base+j := by
  induction gs generalizing j base with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simpa using And.intro ok.1 (And.intro ok.2.1 ok.2.2.1)
    | succ j =>
      have h := ih ok.2.2.2 j (by simpa using hj)
      simpa [List.getD_eq_getElem?_getD,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def Expr.circuit {n} (t : Expr n) : Circuit := ⟨t.emit n,t.wire n⟩

theorem ao2 {n} (t : Expr n) : PEqualNP.TopForm.IsAO2 n t.circuit := by
  let gs := t.emit n
  have h := emitLegal t n (le_refl n)
  have all (g : Gate) (hg : g ∈ gs) : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨a,b,_⟩ := legalAt h j hj g
    have same : gs.getD j g = g := by simp [List.getD_eq_getElem?_getD,hj,eq]
    change (gs.getD j g).op = _ ∨ _ at a
    change (gs.getD j g).inputs.length = 2 at b
    rw [same] at a b; exact ⟨a,b⟩
  exact ⟨fun g hg => (all g hg).1,fun j hj => (legalAt h j hj _).2.2,fun g hg => (all g hg).2⟩

-- Compile once and interpret the very same gate list in any register algebra.
def run {α : Type} (d : α) (alg : GateOp → List α → α) (gs : List Gate) (xs : List α) :=
  gs.foldl (fun u g => u ++ [alg g.op (g.inputs.map fun i => u.getD i d)]) xs

def Expr.val {α : Type} {n} (alg : GateOp → List α → α) (raw : Fin n → α) : Expr n → α
  | .raw v => raw v
  | .gate k a b => alg (op k) [a.val alg raw,b.val alg raw]

theorem runPrefix {α : Type} (d : α) (alg : GateOp → List α → α) (gs : List Gate) (xs : List α) :
    ∃ tail, run d alg gs xs = xs ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing xs with
  | nil => exact ⟨[],by simp [run],rfl⟩
  | cons g gs ih =>
    let v := alg g.op (g.inputs.map fun i => xs.getD i d)
    obtain ⟨tail,ht,len⟩ := ih (xs++[v])
    exact ⟨v::tail,by simpa [run,v,List.append_assoc] using ht,by simp [len]⟩

theorem runRead {α : Type} {n} (d : α) (alg : GateOp → List α → α) (t : Expr n)
    (xs : List α) (raw : Fin n → α) (hn : n ≤ xs.length)
    (hr : ∀ i : Fin n, xs.getD i.val d = raw i) :
    (run d alg (t.emit xs.length) xs).getD (t.wire xs.length) d = t.val alg raw := by
  induction t generalizing xs with
  | raw i => exact hr i
  | gate k a b ha hb =>
    let A := run d alg (a.emit xs.length) xs
    obtain ⟨ta,eqA,lenA⟩ := runPrefix d alg (a.emit xs.length) xs
    have eA : A = xs ++ ta := eqA
    have la : A.length = xs.length+a.cost := by simp [eA,lenA,emitLen]
    have va := ha xs hn hr
    let B := run d alg (b.emit A.length) A
    obtain ⟨tb,eqB,lenB⟩ := runPrefix d alg (b.emit A.length) A
    have eB : B = A ++ tb := eqB
    have lb : B.length = xs.length + a.cost + b.cost := by simp [eB,lenB,emitLen,la]
    have vb := hb A (by omega) (fun i => by rw [eA,List.getD_append _ _ _ _ (by omega)]; exact hr i)
    have first : B.getD (a.wire xs.length) d = a.val alg raw := by
      rw [eB,List.getD_append _ _ _ _ (by rw [la]; exact wireLt a _ hn)]; exact va
    have second : B.getD (b.wire (xs.length+a.cost)) d = b.val alg raw := by
      rw [←la]; exact vb
    change (run d alg ((a.emit xs.length ++ b.emit (xs.length+a.cost)) ++ [_]) xs).getD _ d = _
    simp only [run, List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (run d alg (b.emit (xs.length+a.cost)) A ++
      [alg (op k) ([a.wire xs.length,b.wire (xs.length+a.cost)].map
        fun i => (run d alg (b.emit (xs.length+a.cost)) A).getD i d)]).getD
      (xs.length+a.cost+b.cost) d = _
    have same : run d alg (b.emit (xs.length+a.cost)) A = B := by rw [←la]
    rw [same,←lb,List.getD_append_right _ _ _ _ (le_refl _)]
    simp only [Nat.sub_self,List.map_cons,List.map_nil,List.getD_cons_zero,first,second,Expr.val]

theorem realBool {n} (t : Expr n) (x : Fin n → Bool) :
    circuitFun n t.circuit x = t.val GateOp.eval x := by
  have ht := runRead false GateOp.eval t (List.ofFn x) x (by simp)
    (fun i => by simp [List.getD_eq_getElem?_getD,i.isLt])
  simpa only [List.length_ofFn,circuitFun,Expr.circuit,Circuit.eval,Circuit.wires,run] using ht

def vecAlg (S : List ℕ) (k : ℕ) (g : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match g with
  | .or => ins.foldl (fun acc a => a.foldl insertNew acc) []
  | .and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

theorem realVec {n} (t : Expr n) (S : List ℕ) (k) :
    (readVectors t.circuit n S k).getD t.circuit.output [] =
      t.val (vecAlg S k) (fun i => leafVectors S k i.val) := by
  let start := (List.range n).map (leafVectors S k)
  have ht := runRead [] (vecAlg S k) t start (fun i => leafVectors S k i.val)
    (by simp [start]) (fun i => by simp [start,List.getD_eq_getElem?_getD,i.isLt])
  have len : start.length = n := by simp [start]
  rw [len] at ht
  rw [← ht]
  apply congrArg (fun step : List (List (List ℕ)) → Gate → List (List (List ℕ)) =>
    ((t.emit n).foldl step start).getD (t.wire n) [])
  funext u g
  obtain ⟨cmd,ins⟩ := g
  cases cmd <;> rfl

theorem memInsert (a b : List ℕ) (xs : List (List ℕ)) :
    a ∈ insertNew xs b ↔ a ∈ xs ∨ a=b := by
  by_cases h : b ∈ xs <;> simp [insertNew,h]
  grind

theorem memFold (a : List ℕ) (ys xs : List (List ℕ)) :
    a ∈ ys.foldl insertNew xs ↔ a ∈ xs ∨ a ∈ ys := by
  induction ys generalizing xs with
  | nil => simp
  | cons y ys ih => simp only [List.foldl_cons,ih,memInsert,List.mem_cons]; tauto

theorem orVec (S : List ℕ) (k) (u : List ℕ) (A B : List (List ℕ)) :
    u ∈ vecAlg S k .or [A,B] ↔ u ∈ A ∨ u ∈ B := by simp [vecAlg,memFold]

theorem andVec (k) {u v : List ℕ} {A B : List (List ℕ)} (hu : u ∈ A) (hv : v ∈ B) :
    capAdd k u v ∈ andStep k A B := by
  simp only [andStep,memFold,List.not_mem_nil,false_or,List.mem_flatMap,List.mem_map]
  exact ⟨u,hu,v,hv,rfl⟩

def unitAt (S : List ℕ) (p : ℕ) := S.map fun j => if j=p then 1 else 0

theorem leafOn (S : List ℕ) (k p : ℕ) (h : p ∈ S) : unitAt S p ∈ leafVectors S k p := by
  simp [leafVectors,h,unitAt]

theorem unitCap (S : List ℕ) (p l k : ℕ) (pos : 1 ≤ k) (ne : p ≠ l) :
    (capAdd k (capAdd k (S.map fun _ => 0) (unitAt S p)) (unitAt S l)).all
      (fun a => decide (a ≤ k)) = true := by
  induction S with
  | nil => rfl
  | cons x xs ih =>
    cases eqp : decide (x=p) <;> cases eql : decide (x=l) <;>
      simp_all [capAdd,unitAt,min_def]

def foldOr {n} (first : Expr n) (tail : List (Expr n)) : Expr n :=
  tail.foldl (Expr.gate true) first

def anyExpr {n} (xs : List (Expr n)) (h : xs ≠ []) : Expr n :=
  match xs with
  | [] => False.elim (h rfl)
  | a :: rest => foldOr a rest

theorem foldCost {n} (tail : List (Expr n)) (a : Expr n) :
    (foldOr a tail).cost = a.cost + (tail.map (fun t => t.cost+1)).sum := by
  induction tail generalizing a with
  | nil => simp [foldOr]
  | cons b bs ih =>
    change (foldOr (.gate true a b) bs).cost = _
    rw [ih]; simp [Expr.cost,Nat.add_assoc]

theorem anyCost {n} (xs : List (Expr n)) (h : xs ≠ []) :
    (anyExpr xs h).cost+1 = (xs.map fun t => t.cost+1).sum := by
  cases xs with
  | nil => contradiction
  | cons a as => simp [anyExpr,foldCost]; omega

theorem foldBool {n} (tail : List (Expr n)) (a : Expr n) (x : Fin n → Bool) :
    (foldOr a tail).val GateOp.eval x = true ↔
      a.val GateOp.eval x = true ∨ ∃ t ∈ tail, t.val GateOp.eval x = true := by
  induction tail generalizing a with
  | nil => simp [foldOr]
  | cons b bs ih =>
    change (foldOr (.gate true a b) bs).val _ _ = true ↔ _
    rw [ih]; simp [Expr.val,op,GateOp.eval]; tauto

theorem anyBool {n} (xs : List (Expr n)) (h : xs ≠ []) (x : Fin n → Bool) :
    (anyExpr xs h).val GateOp.eval x = true ↔ ∃ t ∈ xs, t.val GateOp.eval x = true := by
  cases xs with
  | nil => contradiction
  | cons a as => simp [anyExpr,foldBool]

theorem foldVec {n} (tail : List (Expr n)) (a : Expr n) (S : List ℕ) (k)
    (x : Fin n → List (List ℕ)) (u : List ℕ) :
    u ∈ (foldOr a tail).val (vecAlg S k) x ↔
      u ∈ a.val (vecAlg S k) x ∨ ∃ t ∈ tail, u ∈ t.val (vecAlg S k) x := by
  induction tail generalizing a with
  | nil => simp [foldOr]
  | cons b bs ih =>
    change u ∈ (foldOr (.gate true a b) bs).val _ _ ↔ _
    rw [ih]; simp [Expr.val,op,orVec]; tauto

theorem anyVec {n} (xs : List (Expr n)) (h : xs ≠ []) (S : List ℕ) (k)
    (x : Fin n → List (List ℕ)) (u : List ℕ) :
    u ∈ (anyExpr xs h).val (vecAlg S k) x ↔ ∃ t ∈ xs, u ∈ t.val (vecAlg S k) x := by
  cases xs with
  | nil => contradiction
  | cons a as => simp [anyExpr,foldVec]

def pointRaw {N : ℕ} (p : Fin N) : Expr (N+N) := .raw (Fin.castAdd N p)
def lineRaw {N : ℕ} (l : Fin N) : Expr (N+N) := .raw (Fin.natAdd N l)

def star {N} (l : Fin N) (ps : List (Fin N)) (h : ps ≠ []) : Expr (N+N) :=
  .gate false (anyExpr (ps.map pointRaw) (by simpa using h)) (lineRaw l)

theorem starCost {N} (l : Fin N) (ps : List (Fin N)) (h : ps ≠ []) :
    (star l ps h).cost = ps.length := by
  have a := anyCost (ps.map pointRaw) (by simpa using h)
  simpa [star,Expr.cost,pointRaw,lineRaw,List.map_map,Function.comp_def] using a

theorem starBool {N} (l : Fin N) (ps : List (Fin N)) (h : ps ≠ []) (x : Fin (N+N) → Bool) :
    (star l ps h).val GateOp.eval x = true ↔
      (∃ p ∈ ps, x (Fin.castAdd N p) = true) ∧ x (Fin.natAdd N l) = true := by
  simp [star,Expr.val,op,GateOp.eval,anyBool,pointRaw,lineRaw]

theorem setListMem {n : ℕ} (S : Finset (Fin n)) {i : Fin n} (hi : i ∈ S) :
    i.val ∈ setList S := by
  simp only [setList,List.mem_map,List.mem_filter]
  exact ⟨i,⟨List.mem_finRange i,decide_eq_true hi⟩,rfl⟩

theorem starVec {N} (l p : Fin N) (ps : List (Fin N)) (h : ps ≠ [])
    (S : List ℕ) (k) (hp : p ∈ ps) (pin : p.val ∈ S) (lin : N+l.val ∈ S) :
    let u := unitAt S p.val
    let v := unitAt S (N+l.val)
    capAdd k (capAdd k (S.map fun _ => 0) u) v ∈
      (star l ps h).val (vecAlg S k) (fun i => leafVectors S k i.val) := by
  dsimp only [star,Expr.val,op,Bool.false_eq_true,ite_false,lineRaw,vecAlg,
    List.foldl_cons,List.foldl_nil]
  apply andVec _ _ (leafOn _ _ _ lin)
  apply andVec _ (List.mem_singleton_self _) _
  apply (anyVec _ _ S k _ _).mpr
  exact ⟨pointRaw p,List.mem_map.mpr ⟨p,hp,rfl⟩,leafOn _ _ _ pin⟩

noncomputable section

def points {N} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) :=
  (Finset.univ.filter (fun p => I p l)).toList

theorem pointsNe {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) (l : Fin N) :
    points I l ≠ [] := by
  intro e
  have h := congrArg List.length e
  simp [points,degree] at h

def allStars {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) (pos : 0 < N) :
    Expr (N+N) :=
  anyExpr ((List.finRange N).map fun l => star l (points I l) (pointsNe I degree l))
    (by intro e; have := congrArg List.length e; simp at this; omega)

theorem allCost {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) (pos : 0 < N) :
    (allStars I degree pos).cost + 1 = N*(q+2) := by
  unfold allStars
  rw [anyCost]
  simp [List.map_map,Function.comp_def,starCost,points,degree]

theorem allBool {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) (pos : 0 < N)
    (x : Fin (N+N) → Bool) :
    (allStars I degree pos).val GateOp.eval x = true ↔ ∃ p l, I p l ∧
      x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
  unfold allStars
  rw [anyBool]
  constructor
  · rintro ⟨t,mem,yes⟩
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp mem
    obtain ⟨⟨p,hp,xp⟩,xl⟩ := (starBool _ _ _ _).mp yes
    exact ⟨p,l,by simpa [points] using hp,xp,xl⟩
  · rintro ⟨p,l,ip,xp,xl⟩
    exact ⟨_,List.mem_map.mpr ⟨l,List.mem_finRange l,rfl⟩,
      (starBool _ _ _ _).mpr ⟨⟨p,by simpa [points] using ip,xp⟩,xl⟩⟩

theorem allRead {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) (pos : 0 < N)
    (k : ℕ) (hk : 1 ≤ k) : IsReadK (N+N) (allStars I degree pos).circuit k := by
  intro A prime
  have yes := prime.1
  rw [realBool,allBool] at yes
  obtain ⟨p,l,ip,xp,xl⟩ := yes
  let S := setList A
  have pin : p.val ∈ S := setListMem A (i := Fin.castAdd N p) (of_decide_eq_true xp)
  have lin : N+l.val ∈ S := setListMem A (i := Fin.natAdd N l) (of_decide_eq_true xl)
  let u := capAdd k (capAdd k (S.map fun _ => 0) (unitAt S p.val)) (unitAt S (N+l.val))
  unfold readsAtMost
  rw [realVec,List.any_eq_true]
  refine ⟨u,?_,unitCap S _ _ k hk (by omega)⟩
  unfold allStars
  apply (anyVec _ _ S k _ _).mpr
  refine ⟨star l (points I l) (pointsNe I degree l),
    List.mem_map.mpr ⟨l,List.mem_finRange l,rfl⟩,?_⟩
  exact starVec l p _ _ S k (by simpa [points] using ip) pin lin

-- This is the large-budget part of the desk statement, with the actual
-- binary circuit and the project's joint proof-vector definition.
theorem withinBudget (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (pos : 0 < N)
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (budget : N*(q+2) ≤ C.size+1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N+N) D ∧
    (∀ y : Fin (N+N) → Bool, circuitFun (N+N) D y =
      decide (∃ p l, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
    D.size ≤ C.size ∧ IsReadK (N+N) D 2 := by
  let t := allStars I degree pos
  refine ⟨t.circuit,ao2 t,?_,?_,allRead I degree pos 2 (by decide)⟩
  · intro y
    apply Bool.eq_iff_iff.mpr
    rw [realBool,decide_eq_true_iff]
    exact allBool I degree pos y
  · have h := allCost I degree pos
    change (t.emit (N+N)).length ≤ C.size
    rw [emitLen]; dsimp only [t]; omega

def asTree {N} : Expr (N+N) → FlagCrossRank.Tree (Fin N ⊕ Fin N)
  | .raw i => .raw (finSumFinEquiv.symm i)
  | .gate k a b => .gate k (asTree a) (asTree b)

theorem asTreeLeaves {N} (t : Expr (N+N)) : (asTree t).leaves = t.cost+1 := by
  induction t with
  | raw => rfl
  | gate k a b ha hb => simp [asTree,FlagCrossRank.Tree.leaves,Expr.cost,ha,hb]; omega

theorem asTreeVal {N} (t : Expr (N+N)) (x : Fin N ⊕ Fin N → Bool) :
    (asTree t).val x = t.val GateOp.eval (fun i => x (finSumFinEquiv.symm i)) := by
  induction t with
  | raw => rfl
  | gate k a b ha hb => cases k <;> simp [asTree,FlagCrossRank.Tree.val,Expr.val,op,GateOp.eval,ha,hb]

-- Both sides of this result now use the desk's actual circuit and joint read bound.
theorem formulaCase (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (order : N = q^2 + q + 1)
    (degree : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (unique : ∀ p a, p ≠ a → ∃! l, I p l ∧ I a l) (t : Expr (N+N))
    (correct : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) t.circuit z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N+N) D ∧
    (∀ y : Fin (N+N) → Bool, circuitFun (N+N) D y =
      decide (∃ p l, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
    D.size ≤ t.circuit.size ∧ IsReadK (N+N) D 2 := by
  have eval (x : Fin N ⊕ Fin N → Bool) : (asTree t).val x =
      decide (∃ p l, I p l ∧ x (.inl p) = true ∧ x (.inr l) = true) := by
    rw [asTreeVal,←realBool,correct]
    simp only [finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd]
  have bound := FlagCrossRank.planeCrossOnly q N I order hq degree unique (asTree t)
    (by
      intro e
      rw [eval,decide_eq_true_iff]
      exact ⟨e.val.1,e.val.2,e.property,by simp [FlagCrossRank.edgeBits],
        by simp [FlagCrossRank.edgeBits]⟩)
    (by
      intro e
      rw [eval,decide_eq_false_iff_not]
      rintro ⟨p,l,edge,hp,hl⟩
      have ap : I p e.val.2 ∧ p ≠ e.val.1 := of_decide_eq_true hp
      have bl : I e.val.1 l ∧ l ≠ e.val.2 := of_decide_eq_true hl
      exact FlagCrossRank.crossNegative I (FlagCrossRank.planeSquareFree I unique)
        e.property ap bl edge)
  apply withinBudget q N I t.circuit (by omega) degree
  change N*(q+2) ≤ (t.emit (N+N)).length + 1
  simpa [emitLen,asTreeLeaves] using bound

end
end FlagStarCircuit
