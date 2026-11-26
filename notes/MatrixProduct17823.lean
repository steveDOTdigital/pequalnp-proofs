import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace MatrixProduct17823

/-- Each consecutive triple computes one entry of the Boolean product. -/
def schoolbook : Circuit :=
  ⟨[⟨.and, [0, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [12, 13]⟩,
    ⟨.and, [0, 7]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [15, 16]⟩,
    ⟨.and, [0, 8]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [18, 19]⟩,
    ⟨.and, [2, 6]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [21, 22]⟩,
    ⟨.and, [2, 7]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [24, 25]⟩,
    ⟨.and, [2, 8]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [27, 28]⟩,
    ⟨.and, [4, 6]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [30, 31]⟩,
    ⟨.and, [4, 7]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [33, 34]⟩,
    ⟨.and, [4, 8]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [36, 37]⟩], 38⟩

def port (i : Fin 9) : Nat := 14 + 3 * i.val


/-- The value on every wire, in evaluation order. -/
def table (x : Fin 12 → Bool) : List Bool :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11,
   x 0 && x 6, x 1 && x 9, (x 0 && x 6 || x 1 && x 9),
   x 0 && x 7, x 1 && x 10, (x 0 && x 7 || x 1 && x 10),
   x 0 && x 8, x 1 && x 11, (x 0 && x 8 || x 1 && x 11),
   x 2 && x 6, x 3 && x 9, (x 2 && x 6 || x 3 && x 9),
   x 2 && x 7, x 3 && x 10, (x 2 && x 7 || x 3 && x 10),
   x 2 && x 8, x 3 && x 11, (x 2 && x 8 || x 3 && x 11),
   x 4 && x 6, x 5 && x 9, (x 4 && x 6 || x 5 && x 9),
   x 4 && x 7, x 5 && x 10, (x 4 && x 7 || x 5 && x 10),
   x 4 && x 8, x 5 && x 11, (x 4 && x 8 || x 5 && x 11)]

def tick (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem tickAnd (w : List Bool) (a b : Nat) :
    tick w ⟨.and, [a,b]⟩ = w ++ [w.getD a false && w.getD b false] := by
  simp [tick, GateOp.eval]

private theorem tickOr (w : List Bool) (a b : Nat) :
    tick w ⟨.or, [a,b]⟩ = w ++ [w.getD a false || w.getD b false] := by
  simp [tick, GateOp.eval]

private def entry (n : Nat) : Gate := schoolbook.gates.getD n ⟨.and, []⟩

private theorem grows (n : Nat) (hn : n < 27) :
    schoolbook.gates.take (n+1) = schoolbook.gates.take n ++ [entry n] := by
  have casesN : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 := by omega
  rcases casesN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 8000 in
private theorem next (x : Fin 12 → Bool) (n : Nat) (hn : n < 27) :
    tick ((table x).take (12+n)) (entry n) = (table x).take (12+(n+1)) := by
  have casesN : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 := by omega
  rcases casesN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | (apply Eq.trans (tickAnd _ _ _); rfl) | (apply Eq.trans (tickOr _ _ _); rfl)

private theorem wirePrefix (x : Fin 12 → Bool) (n : Nat) (hn : n ≤ 27) :
    (schoolbook.gates.take n).foldl tick (List.ofFn x) = (table x).take (12+n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : n < 27 := by omega
    rw [grows n h, List.foldl_append, ih (by omega)]
    exact next x n h

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem upper : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 9 → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 27 ∧ ∀ x : Fin 12 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 && x 6 || x 1 && x 9) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 && x 7 || x 1 && x 10) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 && x 8 || x 1 && x 11) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 2 && x 6 || x 3 && x 9) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 2 && x 7 || x 3 && x 10) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 && x 8 || x 3 && x 11) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 4 && x 6 || x 5 && x 9) ∧ (C.wires (List.ofFn x)).getD (o 7) false = (x 4 && x 7 || x 5 && x 10) ∧ (C.wires (List.ofFn x)).getD (o 8) false = (x 4 && x 8 || x 5 && x 11) := by
  refine ⟨schoolbook, port, ?_, by decide, ?_⟩
  · intro g hg
    simp [schoolbook] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have h : schoolbook.wires (List.ofFn x) = table x := wirePrefix x 27 (by decide)
    rw [h]
    exact ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩

end MatrixProduct17823
