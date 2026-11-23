import Mathlib

namespace PEqualNP.Outside.PetersenNonedgeOr

-- Each half contains eight four-bit tables on the two endpoints.
-- The high half replaces the distinguished OR wire by true.
def pack (a b : Nat) := a + (b <<< 32)

def leaves : List Nat :=
  [pack 0xCCCCCCCC 0xCCCCCCCC, pack 0xAAAAAAAA 0xAAAAAAAA,
   pack 0xEEEEEEEE 0xFFFFFFFF, pack 0xF0F0F0F0 0xF0F0F0F0,
   pack 0xFF00FF00 0xFF00FF00, pack 0xFFFF0000 0xFFFF0000]

-- A table entry contains every read-once formula on exactly that leaf mask.
-- Both halves of a binary partition have already been computed.
def extend (previous : Array (List Nat)) (mask : Nat) : Array (List Nat) :=
  let entry := if mask &&& (mask - 1) == 0 then
    [leaves[mask.log2]!]
  else
    (List.range mask).flatMap fun left =>
      let right := mask ^^^ left
      if left != 0 && left < right && left &&& mask == left then
        (previous[left]!).flatMap fun a =>
          (previous[right]!).flatMap fun b => [a &&& b, a ||| b]
      else []
  previous.push entry

def formulas := ((List.range 63).foldl (fun table i => extend table (i+1)) #[[]])[63]!

def fiveRows (t : Nat) : Bool :=
  [0, 10, 12, 14, 15].all fun row =>
    (List.range 8).any fun i => ((t >>> (4*i)) &&& 15) == row

-- For every successful formula the replacement preserves all 32 rows,
-- even on combinations of outside signals never attained by the graph.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
theorem enumeration :
    formulas.length = 30240 ∧ (formulas.filter fiveRows).length = 162 ∧
    (formulas.filter fiveRows).all (fun t => (t &&& 0xFFFFFFFF) == t >>> 32) = true := by
  decide +kernel

def outsideEdge (x : Fin 10 → Bool) :=
  (x 3 && x 4) || (x 1 && x 6) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def seven (x : Fin 10 → Bool) (q : Bool) :=
  let a := x 1 || x 4 || x 5
  let b := x 1 || x 3 || x 7
  outsideEdge x || (q && (a || b) && ((x 0 || b) && (x 2 || a)))

theorem sharp (x : Fin 10 → Bool) :
    seven x (x 0 || x 2) =
    ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
     (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
     (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
     (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
  unfold seven outsideEdge
  grind

theorem essential :
    ∃ x : Fin 10 → Bool, seven x true ≠ seven x (x 0 || x 2) := by
  exact ⟨fun i => decide (i.val = 1), by decide⟩

end PEqualNP.Outside.PetersenNonedgeOr
