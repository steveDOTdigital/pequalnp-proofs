import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

namespace FiveLineAttachment

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


theorem goodEmitted {n : ℕ} (t : Expr n) (base : ℕ) (g : Gate) (hg : g ∈ t.emit base) :
    g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction t generalizing base with
  | raw _ => simp [Expr.emit] at hg
  | gate k a b ha hb =>
    simp only [Expr.emit,List.mem_append,List.mem_singleton] at hg
    rcases hg with (h|h)|rfl
    · exact ha base h
    · exact hb _ h
    · cases k <;> simp [op]

def term {n} (P L : Fin 21 → Expr n) (p : Fin 21) : Expr n :=
  .gate false (P p) (.gate true (.gate true (.gate true (.gate true
    (L p) (L (p-1))) (L (p-4))) (L (p-14))) (L (p-16)))

def heavy : List (Fin 21) := [0,3,6,9,12,15,18]

def bank {n} (P L : Fin 21 → Expr n) (old : Expr n) (A : List (Fin 21)) :=
  A.foldl (fun t p => Expr.gate true t (term P L p)) old

theorem bankValue {n} (P L : Fin 21 → Expr n) (old : Expr n) (A : List (Fin 21))
    (x : Fin n → Bool) :
    (bank P L old A).val GateOp.eval x = (old.val GateOp.eval x || A.any (fun p => (term P L p).val GateOp.eval x)) := by
  induction A generalizing old with
  | nil => simp [bank]
  | cons p tail ih =>
    change (bank P L (.gate true old (term P L p)) tail).val _ _ = _
    rw [ih]
    simp [Expr.val,op,GateOp.eval,Bool.or_assoc]

theorem attach : let S := fun l : Fin 21 => ({l,l+1,l+4,l+14,l+16} : Finset (Fin 21))
    ∀ C : Circuit, Monotone2 C → C.size ≤ 82 → C.output < 42+C.size →
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 124 ∧ ∀ X Y : Finset (Fin 21),
    D.eval (incidenceInput X Y) = (C.eval (incidenceInput X Y) ||
      decide (∃ p ∈ X, p.val % 3 = 0 ∧ ∃ l ∈ Y, p ∈ S l)) := by
  classical
  let S := fun l : Fin 21 => ({l,l+1,l+4,l+14,l+16} : Finset (Fin 21))
  change ∀ C : Circuit, Monotone2 C → C.size ≤ 82 → C.output < 42+C.size →
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 124 ∧ ∀ X Y : Finset (Fin 21),
    D.eval (incidenceInput X Y) = (C.eval (incidenceInput X Y) ||
      decide (∃ p ∈ X, p.val % 3 = 0 ∧ ∃ l ∈ Y, p ∈ S l))
  intro C mc bound valid
  let n := 42+C.size
  let P (p : Fin 21) : Expr n := .raw ⟨p.val,by dsimp [n]; omega⟩
  let L (l : Fin 21) : Expr n := .raw ⟨21+l.val,by dsimp [n]; omega⟩
  let old : Expr n := .raw ⟨C.output,valid⟩
  let t := bank P L old heavy
  let D : Circuit := ⟨C.gates++t.emit n,t.wire n⟩
  have cost : t.cost=42 := by simp [t,bank,heavy,term,Expr.cost,old,P,L]
  have legal : Monotone2 D := by
    intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact mc g h
    · exact goodEmitted t n g h
  refine ⟨D,legal,?_,?_⟩
  · change (C.gates++t.emit n).length≤124
    rw [List.length_append,emitLen,cost]
    change C.size+42≤124
    omega
  intro X Y
  let input := incidenceInput X Y
  let tape := C.wires input
  obtain ⟨tail,append,len⟩ := runPrefix false GateOp.eval C.gates input
  change tape = input++tail at append
  have ilen : input.length=42 := by simp [input,incidenceInput]
  have tlen : tape.length=n := by simp [append,ilen,len,n,Circuit.size]
  let x (i : Fin n) := tape.getD i.val false
  have point (p : Fin 21) : (P p).val GateOp.eval x = decide (p∈X) := by
    change tape.getD p.val false = _
    rw [append,List.getD_append _ _ _ _ (by rw [ilen]; omega)]
    change (List.ofFn (fun i => decide (i∈X)) ++ List.ofFn (fun j => decide (j∈Y))).getD p.val false = _
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using p.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using p.isLt),List.getElem_ofFn]
  have line (l : Fin 21) : (L l).val GateOp.eval x = decide (l∈Y) := by
    change tape.getD (21+l.val) false = _
    rw [append,List.getD_append _ _ _ _ (by rw [ilen]; omega)]
    change (List.ofFn (fun p => decide (p∈X)) ++ List.ofFn (fun j => decide (j∈Y))).getD (21+l.val) false = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn,Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using l.isLt),List.getElem_ofFn]
  have inc : ∀ p l : Fin 21, p∈S l ↔ l=p ∨ l=p-1 ∨ l=p-4 ∨ l=p-14 ∨ l=p-16 := by decide
  have atTerm (p : Fin 21) : (term P L p).val GateOp.eval x = true ↔
      p∈X ∧ ∃ l∈Y,p∈S l := by
    simp only [term,Expr.val,op,Bool.false_eq_true,ite_false,ite_true,GateOp.eval,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false,point,line,
      Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,inc]
    grind
  have atHeavy : ∀ p : Fin 21, p∈heavy ↔ p.val%3=0 := by decide
  have value : D.eval input = t.val GateOp.eval x := by
    change (run false GateOp.eval (C.gates++t.emit n) input).getD (t.wire n) false = _
    simp only [run,List.foldl_append]
    change (run false GateOp.eval (t.emit n) tape).getD (t.wire n) false = _
    have ht := runRead false GateOp.eval t tape x (by omega) (fun _ => rfl)
    rwa [tlen] at ht
  change D.eval input = _
  rw [value]
  change (bank P L old heavy).val GateOp.eval x = _
  rw [bankValue]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,atTerm,atHeavy,decide_eq_true_eq]
  grind

end FiveLineAttachment
