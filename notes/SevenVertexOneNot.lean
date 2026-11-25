import PEqualNP.Defs
import FlagStarCircuit
import PetersenSignedSlice

namespace SevenVertexOneNot
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FlagStarCircuit

def target (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)

def edges : List ℕ := [0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6]
def posted (x : Fin 7 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

theorem table : ∀ x, posted x = target x := by decide +kernel

def either (a b : Expr 7) := Expr.gate true a b
def both (a b : Expr 7) := Expr.gate false a b
def pair (a b : Fin 7) := either (.raw a) (.raw b)
def triple (a b c : Fin 7) := either (pair a b) (.raw c)

def witness := either (either (both (.raw 5) (pair 1 3))
    (both (triple 4 5 6) (pair 0 2))) (both (triple 0 1 6) (pair 3 4))

theorem size : witness.circuit.size = 12 := by decide +kernel
theorem legal : Monotone2 witness.circuit := by
  intro g hg
  exact ⟨(ao2 witness).1 g hg, le_of_eq ((ao2 witness).2.2 g hg)⟩

theorem value (x : Fin 7 → Bool) : circuitFun 7 witness.circuit x = posted x := by
  rw [table,realBool]
  simp [witness, target, pair, triple, both, either, Expr.val, op, GateOp.eval,
    Bool.and_or_distrib_left, Bool.and_or_distrib_right, Bool.and_comm]
  ac_rfl

abbrev Input := Fin 6 → Bool
def lift (x : Input) : Fin 7 → Bool := Fin.cases false x
def prism (x : Input) := target (lift x)
def signedStart (x : Input) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def signed (p : List (ℕ × ℕ)) (o : ℕ) (x : Input) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false

/-- Pinning input zero saves a paid binary gate, including when a NOT appears elsewhere. -/
theorem prismSlice (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 7 C x = target x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed p o x = prism x := by
  let raw := List.ofFn (fun j : Fin 6 => fun x : Input => x j)
  let pool := [(fun _ : Input => false), (fun _ : Input => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let pin := fun j : Fin 7 => (fun x : Input => lift x j, decide (j = 3), decide (j = 0 ∨ j = 3))
  let v := List.ofFn pin
  have constants (b : Bool) : (fun _ : Input => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    refine Fin.cases ?_ (fun i => ?_) j
    · exact ⟨constants false, constants true, Or.inl ⟨false, fun _ => rfl⟩⟩
    · have pos : (fun x : Input => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
      refine ⟨List.mem_append_left _ (List.mem_append_right _ pos),
        List.mem_append_right _ (List.mem_map_of_mem pos), Or.inr ?_⟩
      simp [pin]
  have slice (x : Input) : C.eval (v.map fun a => a.1 x) = prism x := by
    simpa [v, pin, prism, circuitFun, List.map_ofFn, Function.comp_def] using hit (lift x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input, C.eval (v.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : prism (fun _ => false) ≠ prism (fun _ => true)) (first.trans second.symm)
  have diff : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2) := by
    have a := hit (fun j => decide (j = 3))
    have b := hit (fun j => decide (j = 0 ∨ j = 3))
    simp only [v,pin,List.map_ofFn,Function.comp_def,circuitFun] at a b ⊢
    rw [a,b]
    decide +kernel
  obtain ⟨p,o,small,eval⟩ := PetersenSignedSlice.compile Input C ok pool v constants pins varies diff
  refine ⟨p,o,small,fun x => ?_⟩
  change (p.foldl PetersenSignedSlice.addPair (signedStart x)).getD o false = prism x
  have start : pool.map (fun u => u x) = signedStart x := by
    simp only [pool,raw,signedStart,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← start]
  exact (eval x).trans (slice x)

theorem replacement
    (prismLower : ∀ p o, (∀ x, signed p o x = prism x) → 10 ≤ p.length)
    (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 7 C x = target x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 7 D x = posted x := by
  by_cases mono : Monotone2 C
  · exact ⟨C, mono, le_rfl, fun x => (hit x).trans (table x).symm⟩
  · obtain ⟨p,o,sz,ev⟩ := prismSlice C ok hit
    have paid (gs : List Gate) : (gs.map PetersenSignedSlice.Paid).sum ≤ gs.length ∧
        ((gs.map PetersenSignedSlice.Paid).sum = gs.length →
          ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) →
            (g.op = .and ∨ g.op = .or)) := by
      induction gs with
      | nil => simp
      | cons g t ih =>
        have cap : PetersenSignedSlice.Paid g ≤ 1 := by unfold PetersenSignedSlice.Paid; split <;> (first | decide | split <;> decide)
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        refine ⟨by omega, ?_⟩
        intro eq u mem kind
        rcases List.mem_cons.mp mem with rfl | tail
        · rcases kind with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · have := ih.1
            simp [PetersenSignedSlice.Paid, h, GateOp.eval] at eq
            omega
        · exact ih.2 (by omega) _ tail kind
    obtain ⟨cap, full⟩ := paid C.gates
    have strict : (C.gates.map PetersenSignedSlice.Paid).sum < C.gates.length := by
      by_contra! fail
      apply mono
      intro g hg
      exact ⟨full (by omega) _ hg (ok g hg).1, (ok g hg).2⟩
    have := prismLower p o ev
    exact ⟨witness.circuit, legal, by rw [size]; change 12 ≤ C.gates.length; omega, value⟩

end SevenVertexOneNot
