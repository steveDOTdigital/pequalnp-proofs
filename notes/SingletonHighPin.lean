import Mathlib
import PEqualNP.MetaComplexity.Helpers.Elim

namespace SingletonHighPin

-- Gate positions are topologically ordered. Bit j*(j-1)/2+i represents
-- the read from i to j, with i < j. Unused positions can be padded cold.
private def positions : List Nat := [0, 1, 2, 3, 4]

private def readEdge (edges : BitVec 10) (i j : Nat) : Bool :=
  decide (i < j) && edges.getLsbD (j * (j-1) / 2 + i)

private def twice (edges : BitVec 10) (i : Nat) : Bool :=
  positions.any fun a => positions.any fun b =>
    decide (a < b) && readEdge edges i a && readEdge edges i b

private def legal (edges : BitVec 10) (lit : BitVec 5) : Bool :=
  positions.all fun j =>
    ((!lit.getLsbD j) || positions.any (readEdge edges j)) &&
    positions.all fun a => positions.all fun b =>
      ((!decide (a < b)) || !(readEdge edges a j) || !(readEdge edges b j)) ||
      (((!lit.getLsbD a) || (!lit.getLsbD b) || lit.getLsbD j) &&
       positions.all fun c => (!decide (b < c)) || !(readEdge edges c j))

private def obstruction (edges : BitVec 10) (lit : BitVec 5) : Bool :=
  positions.any fun u => positions.any fun v => positions.any fun h =>
    decide (u < v ∧ v < h) && lit.getLsbD u && lit.getLsbD v && lit.getLsbD h &&
    twice edges u && twice edges v && !(readEdge edges u v)

-- On at most five affected gates this configuration is impossible even if
-- the two paths to the later hot AND are omitted from the test.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem fiveSlots (edges : BitVec 10) (lit : BitVec 5) :
    (legal edges lit && obstruction edges lit) = false := by
  simp [legal,obstruction,twice,positions,readEdge, List.any_cons, List.all_cons,
    List.any_nil,List.all_nil]
  bv_decide

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

-- When the other raw variables start false, a true Boolean tape position
-- is represented by constant true under the high pin on the chosen input.
-- The two local steps give propagation and the counted saving together.
theorem orTrue (m : Nat) (s : Stat) :
    simplify GateOp.or m [Stat.const true, s] = (none, Stat.const true) ∧
    simplify GateOp.or m [s, Stat.const true] = (none, Stat.const true) := by
  cases s with
  | const b => cases b <;> exact ⟨rfl, rfl⟩
  | wire i => exact ⟨rfl, rfl⟩

theorem andTrue (m : Nat) :
    simplify GateOp.and m [Stat.const true, Stat.const true] =
      (none, Stat.const true) := rfl

theorem readerSkipped (op : GateOp) (m : Nat) (a b : Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hh : a = Stat.const true ∨ b = Stat.const true) :
    (simplify op m [a,b]).1 = none := by
  apply simplify_count op m [a,b] (hop.imp_right Or.inl) (by simp)
  · rcases hop with rfl | rfl <;> simp
  · refine ⟨true, ?_⟩
    rcases hh with rfl | rfl <;> simp

private def hotStatus : Stat → Bool
  | .const b => b
  | .wire _ => false

-- Free input wires start false on the singleton. Hot statuses follow the
-- original binary gate's Boolean evaluation at that input.
theorem hotStep (op : GateOp) (m : Nat) (a b : Stat)
    (mono : op = GateOp.and ∨ op = GateOp.or) :
    hotStatus (simplify op m [a,b]).2 = op.eval [hotStatus a, hotStatus b] := by
  rcases mono with rfl | rfl <;> cases a <;> cases b <;>
    first | rfl | (rename_i c d; cases c <;> cases d <;> rfl)

private def hits (acc : List Stat × List Gate) (g : Gate) : Bool :=
  g.inputs.any fun i => hotStatus (acc.1.getD i (.const false))

def affectedCount (n : Nat) : List Gate → List Stat × List Gate → Nat
  | [], _ => 0
  | g :: gs, acc => (if hits acc g then 1 else 0) +
      affectedCount n gs (elimStep n acc g)

theorem compiledSaving (n : Nat) (gs : List Gate) (acc : List Stat × List Gate)
    (ok : ∀ g ∈ gs, NOk g) :
    (elim n gs acc).2.length + affectedCount n gs acc ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim, affectedCount]
  | cons g gs ih =>
    let next := elimStep n acc g
    have rest := ih next (fun h hh => ok h (List.mem_cons_of_mem _ hh))
    change (elim n gs next).2.length + affectedCount n (g :: gs) acc ≤ _
    by_cases hit : hits acc g = true
    · obtain ⟨i, hi, hot⟩ := List.any_eq_true.mp hit
      have identifies : ∀ t : Stat, hotStatus t = true → t = .const true := by
        intro t
        cases t with
        | const b => cases b <;> simp [hotStatus]
        | wire j => simp [hotStatus]
      have identified := identifies _ hot
      have hg := ok g List.mem_cons_self
      have skipped : (simplify g.op (n+acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.const false))).1 = none :=
        simplify_count _ _ _ hg.1.1 (by simpa using hg.1.2)
          (fun h => by simpa using hg.2 h) ⟨true, List.mem_map.mpr ⟨i,hi,identified⟩⟩
      have len : next.2.length = acc.2.length := by
        change (acc.2 ++ (simplify g.op (n+acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.const false))).1.toList).length = _
        rw [skipped]; simp
      simp only [affectedCount,hit,ite_true,List.length_cons]
      change _ + (1 + affectedCount n gs next) ≤ _
      omega
    · have one := toList_length_le (simplify g.op (n+acc.2.length)
          (g.inputs.map fun w => acc.1.getD w (.const false))).1
      have len : next.2.length ≤ acc.2.length+1 := by
        dsimp [next,elimStep]; rw [List.length_append]; omega
      simp only [affectedCount,ite_eq_right hit,Nat.zero_add,List.length_cons]
      change _ + affectedCount n gs next ≤ _
      omega

-- A minimum circuit which would beat a clean upper bound by at least one
-- cannot spend six gates at an input whose high cofactor is this expensive.
theorem noHit {budget upper restricted : Nat} (smaller : budget < upper)
    (cofactor : upper ≤ restricted+6) : ¬ restricted+6 ≤ budget := by omega

-- Each core line is covered by selecting the line itself or all its points.
-- A four-bit counter suffices for all thirteen vertices.
private def masks : List Nat := [7,9,10,12,17,18,20,24]

private def coreCover (bits : BitVec 13) (drop : BitVec 3) : Bool :=
  (List.range 8).all fun j =>
    drop == BitVec.ofNat 3 j || bits.getLsbD (5+j) ||
      (bits &&& BitVec.ofNat 13 (masks.getD j 0)) == BitVec.ofNat 13 (masks.getD j 0)

private def count13 (bits : BitVec 13) : BitVec 4 :=
  (List.range 13).foldl (fun n i =>
    n + (if bits.getLsbD i then 1 else 0)) 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem uniqueCoreCover (bits : BitVec 13) (drop : BitVec 3)
    (cover : coreCover bits drop = true) (size : count13 bits ≤ 5) :
    bits = 31 := by
  unfold coreCover count13 at *
  norm_num [masks, List.range_succ, List.all_append, List.all_cons,
    List.all_nil, List.foldl_append, List.foldl_cons] at *
  bv_decide

-- Two additional ORs may be hot at a given marked point. If both are hot,
-- their common AND consumes a second internal arc, reducing the exit count.
theorem threeExits (u v : Bool) (exits : Nat)
    (balance : exits + (if u && v then 1 else 0) ≤
        2 + (if u then 1 else 0) + (if v then 1 else 0)) : exits ≤ 3 := by
  cases u <;> cases v <;> simp_all <;> omega

end SingletonHighPin
