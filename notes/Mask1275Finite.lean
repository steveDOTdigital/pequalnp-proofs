import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds

namespace Mask1275

def graph (u : Fin 3) (v : Fin 5) : Bool :=
  (1275 : Nat).testBit (5 * u.val + v.val)

def circuit : Circuit :=
  { gates := [⟨.or, [4, 5]⟩, ⟨.and, [1, 8]⟩,
              ⟨.or, [6, 7]⟩, ⟨.or, [4, 10]⟩,
              ⟨.and, [0, 11]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [13, 12]⟩],
    output := 14 }

theorem seven : PEqualNP.Represents.RepSizeAtMost graph 7 := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

def raw (pin : Nat) : Nat :=
  ((List.range 15).filter fun k => pin == k / 5 || pin == 3 + k % 5).foldl
    (fun acc k => acc + 2 ^ k) 0

def positives := (List.range 15).filter (1275 : Nat).testBit
def negatives := (List.range 15).filter (fun k => !(1275 : Nat).testBit k)

def possible (ws : List Nat) : Bool :=
  positives.all fun i => negatives.all fun j =>
    ws.any fun w => w.testBit i && !(w.testBit j)

def leaves := (List.range 8).map raw

theorem indispensable :
    (List.range 8).filter (fun i => !possible (leaves.eraseIdx i)) = [0,1,3,4,5,6,7] := by
  decide +kernel

-- Choose two current sibling subtrees and consume both in their parent.
def steps (ws : List Nat) : List (List Nat) := do
  let i ← List.range ws.length
  let j ← List.range i
  let x := ws[i]!
  let y := ws[j]!
  let rest := (ws.eraseIdx i).eraseIdx j
  let merged ← [x &&& y, x ||| y]
  let next := merged :: rest
  guard (possible next)
  pure next

def frontier : Nat → List (List Nat)
  | 0 => [leaves.eraseIdx 2]
  | k+1 => (frontier k).flatMap steps

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem noFourthMerge : frontier 4 = [] := by decide +kernel

end Mask1275
