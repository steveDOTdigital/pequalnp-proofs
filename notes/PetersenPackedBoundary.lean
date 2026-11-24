import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenPackedBoundary

abbrev Op := Bool × ℕ × ℕ

def packed (w : List ℕ) (g : Op) : List ℕ :=
  let a := w.getD g.2.1 0
  let b := w.getD g.2.2 0
  w ++ [ite (g.1 = true) (a ||| b) (a &&& b)]

def code (g : Gate) : Op :=
  (g.op.eval [true,false], g.inputs.getD 0 0, g.inputs.getD 1 0)

def scalar (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

private theorem bitGet (w : List ℕ) (j i : ℕ) :
    (w.getD j 0).testBit i = (w.map (fun u => u.testBit i)).getD j false := by
  simp only [List.getD,List.getElem?_map]
  cases w[j]? <;> simp

private theorem gate (w : List ℕ) (g : Gate) (h : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (i : ℕ) :
    (packed w (code g)).map (fun u => u.testBit i) = scalar (w.map (fun u => u.testBit i)) g := by
  obtain ⟨op,sz⟩ := h
  obtain ⟨a,b,inputs⟩ : ∃ a b, g.inputs = [a,b] := by
    cases h : g.inputs with
    | nil => simp [h] at sz
    | cons a tail =>
      cases tail with
      | nil => simp [h] at sz
      | cons b tail =>
        have size : (a :: b :: tail).length = 2 := h ▸ sz
        have empty : tail = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at size; omega)
        exact ⟨a,b,by rw [empty]⟩
  rcases op with op | op
  · simp only [packed,code,scalar,op,inputs,List.map_append,List.map_cons,List.map_nil]
    congr 2
    change (w.getD a 0 &&& w.getD b 0).testBit i = _
    rw [Nat.testBit_and,bitGet,bitGet]
    simp [GateOp.eval]
  · simp only [packed,code,scalar,op,inputs,List.map_append,List.map_cons,List.map_nil]
    congr 2
    change (w.getD a 0 ||| w.getD b 0).testBit i = _
    rw [Nat.testBit_or,bitGet,bitGet]
    simp [GateOp.eval]

private theorem fold (gs : List Gate) (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (s : List ℕ) (i : ℕ) :
    ((gs.map code).foldl packed s).map (fun u => u.testBit i) = gs.foldl scalar (s.map (fun u => u.testBit i)) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [ih (fun k hk => h k (List.mem_cons_of_mem g hk)),gate s g (h g (by simp)) i]

theorem compile (C : Circuit) (h : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    ∃ p : List (Bool × ℕ × ℕ), p.length = C.size ∧ ∀ (s : List ℕ) (i : ℕ),
      ((p.foldl (fun w g =>
        let a := w.getD g.2.1 0
        let b := w.getD g.2.2 0
        w ++ [ite (g.1 = true) (a ||| b) (a &&& b)]) s).getD C.output 0).testBit i =
      C.eval (s.map fun u => u.testBit i) := by
  refine ⟨C.gates.map code,by simp [Circuit.size],?_⟩
  intro s i
  change (((C.gates.map code).foldl packed s).getD C.output 0).testBit i = _
  rw [bitGet,fold C.gates h]
  rfl

end PetersenPackedBoundary
