import EightVertexOneNot32365
import PetersenSignedSlice

namespace PinThree32365

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Input := Fin 7 → Bool

def insertZero (x : Input) (i : Fin 8) : Bool :=
  match i.val with
  | 0 => x 0
  | 1 => x 1
  | 2 => x 2
  | 3 => false
  | 4 => x 3
  | 5 => x 4
  | 6 => x 5
  | _ => x 6

def pinned (x : Input) : Bool := EightVertexOneNot32365.posted (insertZero x)

def signedStart (x : Input) := [false, true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not

def signed (p : List (Nat × Nat)) (o : Nat) (x : Input) : Bool :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

theorem signedRestriction (C : Circuit) (ok : FanInTwo C)
    (hit : ∀ x : Fin 8 → Bool, circuitFun 8 C x = EightVertexOneNot32365.posted x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = pinned x := by
  let raw := List.ofFn (fun i : Fin 7 => fun x : Input => x i)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let rowLo := fun i : Fin 8 => decide (i = 5)
  let rowHi := fun i : Fin 8 => decide (i = 3 ∨ i = 5)
  let vectors := List.ofFn (fun i : Fin 8 => (fun x : Input => insertZero x i, rowLo i, rowHi i))
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have normal (i : Fin 7) (b : Bool) :
      (fun x : Input => x i) ∈ pool ∧ (fun x : Input => !(x i)) ∈ pool ∧
        ((∃ a, ∀ x : Input, x i = a) ∨ b = b) := by
    have pos : (fun x : Input => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
    exact ⟨List.mem_append_left _ (List.mem_append_right _ pos),
      List.mem_append_right _ (List.mem_map_of_mem pos), Or.inr rfl⟩
  have pins : ∀ a ∈ vectors, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    fin_cases j
    · exact normal 0 false
    · exact normal 1 false
    · exact normal 2 false
    · exact ⟨constants false, constants true, Or.inl ⟨false, fun _ => rfl⟩⟩
    · exact normal 3 false
    · exact normal 4 true
    · exact normal 5 false
    · exact normal 6 false
  have slice (x : Input) : C.eval (vectors.map fun a => a.1 x) = pinned x := by
    simpa [vectors, pinned, circuitFun, List.map_ofFn, Function.comp_def] using hit (insertZero x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input, C.eval (vectors.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : pinned (fun _ => false) ≠ pinned (fun _ => true))
      (first.trans second.symm)
  have diff : C.eval (vectors.map fun a => a.2.1) ≠ C.eval (vectors.map fun a => a.2.2) := by
    have a := hit rowLo
    have b := hit rowHi
    simp only [vectors, List.map_ofFn, Function.comp_def, circuitFun] at a b ⊢
    rw [a,b]
    decide +kernel
  obtain ⟨p,o,small,eval⟩ := PetersenSignedSlice.compile Input C ok pool vectors constants pins varies diff
  refine ⟨p,o,small,fun x => ?_⟩
  change (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false = pinned x
  have start : pool.map (fun u => u x) = signedStart x := by
    simp only [pool,raw,signedStart,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← start]
  exact (eval x).trans (slice x)

private theorem paidBound (gs : List Gate) :
    (gs.map PetersenSignedSlice.Paid).sum ≤ gs.length ∧
      ((gs.map PetersenSignedSlice.Paid).sum = gs.length →
        ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) →
          (g.op = .and ∨ g.op = .or)) := by
  induction gs with
  | nil => simp
  | cons g t ih =>
    have cap : PetersenSignedSlice.Paid g ≤ 1 := by
      unfold PetersenSignedSlice.Paid
      split <;> (first | decide | split <;> decide)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    refine ⟨by omega, ?_⟩
    intro eq u mem kind
    rcases List.mem_cons.mp mem with rfl | tail
    · rcases kind with a | a | a
      · exact Or.inl a
      · exact Or.inr a
      · have := ih.1
        simp [PetersenSignedSlice.Paid, a, GateOp.eval] at eq
        omega
    · exact ih.2 (by omega) _ tail kind

/-- The signed bound would give a same-size monotone replacement even for an
arbitrary number of NOT gates. -/
theorem replacement
    (lower : ∀ p o, (∀ x, signed p o x = pinned x) → 13 ≤ p.length)
    (C : Circuit) (ok : FanInTwo C)
    (hit : ∀ x : Fin 8 → Bool, circuitFun 8 C x = EightVertexOneNot32365.posted x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
      ∀ x : Fin 8 → Bool, circuitFun 8 D x = EightVertexOneNot32365.posted x := by
  by_cases mono : Monotone2 C
  · exact ⟨C, mono, le_rfl, hit⟩
  · obtain ⟨p,o,small,ev⟩ := signedRestriction C ok hit
    obtain ⟨cap, full⟩ := paidBound C.gates
    have strict : (C.gates.map PetersenSignedSlice.Paid).sum < C.gates.length := by
      by_contra! fail
      apply mono
      intro g hg
      exact ⟨full (by omega) _ hg (ok g hg).1, (ok g hg).2⟩
    have needed := lower p o ev
    refine ⟨EightVertexOneNot32365.control, EightVertexOneNot32365.legal, ?_,
      EightVertexOneNot32365.value⟩
    rw [EightVertexOneNot32365.size]
    change 15 ≤ C.gates.length
    omega

#print axioms signedRestriction
#print axioms replacement

end PinThree32365
