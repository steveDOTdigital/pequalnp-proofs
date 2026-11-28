import EightVertexOneNot34477
import PetersenSignedSlice

namespace EightVertexOneNot34477

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Input := Fin 7 → Bool

def insertFalse (x : Input) : Fin 8 → Bool :=
  Fin.cases (x 0) (Fin.cases false (fun j : Fin 6 => x j.succ))

def cofactor (x : Input) : Bool := posted (insertFalse x)

def start (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not

def signed (p : List (Nat × Nat)) (o : Nat) (x : Input) : Bool :=
  (p.foldl PetersenSignedSlice.addPair (start x)).getD o false

theorem restrictOne (C : Circuit) (ok : FanInTwo C)
    (hit : ∀ x, C.eval (List.ofFn x) = posted x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = cofactor x := by
  let raw := List.ofFn (fun j : Fin 7 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let row := fun j : Fin 8 =>
    (fun x : Input => insertFalse x j, decide (j = 4), decide (j = 1 ∨ j = 4))
  let v := List.ofFn row
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have original (i : Fin 7) : (fun x : Input => x i) ∈ pool ∧
      (fun x : Input => !(x i)) ∈ pool := by
    have pos : (fun x : Input => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
    exact ⟨List.mem_append_left _ (List.mem_append_right _ pos),
      List.mem_append_right _ (List.mem_map_of_mem pos)⟩
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    refine Fin.cases ?_ (fun i => ?_) j
    · exact ⟨(original 0).1,(original 0).2,Or.inr (by decide)⟩
    · refine Fin.cases ?_ (fun k => ?_) i
      · exact ⟨constants false,constants true,Or.inl ⟨false,fun _ => rfl⟩⟩
      · refine ⟨(original k.succ).1,(original k.succ).2,Or.inr ?_⟩
        have notOne : k.succ.succ ≠ (1 : Fin 8) := by
          intro eq
          have index := congrArg Fin.val eq
          change k.val+1+1 = 1 at index
          omega
        simp [row,notOne]
  have slice (x : Input) : C.eval (v.map fun a => a.1 x) = cofactor x := by
    simpa [v,row,cofactor,List.map_ofFn,Function.comp_def] using hit (insertFalse x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input, C.eval (v.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : cofactor (fun _ => false) ≠ cofactor (fun _ => true))
      (first.trans second.symm)
  have diff : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2) := by
    have a := hit (fun j => decide (j = 4))
    have b := hit (fun j => decide (j = 1 ∨ j = 4))
    simp only [v,row,List.map_ofFn,Function.comp_def] at a b ⊢
    rw [a,b]
    decide +kernel
  obtain ⟨p,o,small,eval⟩ := PetersenSignedSlice.compile Input C ok pool v constants pins varies diff
  refine ⟨p,o,small,fun x => ?_⟩
  change (p.foldl PetersenSignedSlice.addPair (start x)).getD o false = cofactor x
  have eq : pool.map (fun u => u x) = start x := by
    simp only [pool,raw,start,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← eq]
  exact (eval x).trans (slice x)

theorem replaceFromSignedLower
    (lower : ∀ p o, (∀ x, signed p o x = cofactor x) → 12 ≤ p.length)
    (C : Circuit) (legalC : FanInTwo C) (hit : ∀ x, C.eval (List.ofFn x) = posted x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, D.eval (List.ofFn x) = posted x := by
  by_cases already : Monotone2 C
  · exact ⟨C,already,le_rfl,hit⟩
  obtain ⟨p,o,small,run⟩ := restrictOne C legalC hit
  have paid (gs : List Gate) : (gs.map PetersenSignedSlice.Paid).sum ≤ gs.length ∧
      ((gs.map PetersenSignedSlice.Paid).sum = gs.length →
        ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) → (g.op = .and ∨ g.op = .or)) := by
    induction gs with
    | nil => simp
    | cons g t ih =>
      have cap : PetersenSignedSlice.Paid g ≤ 1 := by
        unfold PetersenSignedSlice.Paid
        split <;> (first | decide | split <;> decide)
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      refine ⟨by omega,?_⟩
      intro eq u mem kind
      rcases List.mem_cons.mp mem with rfl | tail
      · rcases kind with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have := ih.1
          simp [PetersenSignedSlice.Paid,h,GateOp.eval] at eq
          omega
      · exact ih.2 (by omega) _ tail kind
  obtain ⟨cap,full⟩ := paid C.gates
  have strict : (C.gates.map PetersenSignedSlice.Paid).sum < C.gates.length := by
    by_contra! fail
    apply already
    intro g mem
    exact ⟨full (by omega) _ mem (legalC g mem).1,(legalC g mem).2⟩
  have bound := lower p o run
  exact ⟨control,legal,by rw [size]; change 14 ≤ C.gates.length; omega,value⟩

#print axioms restrictOne
#print axioms replaceFromSignedLower

end EightVertexOneNot34477
