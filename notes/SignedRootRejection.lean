import SignedRootSplit

namespace PrismSignedFrontier.RootSplit

-- Both row witnesses can be found by intersecting 64-bit truth tables.
-- A nonempty intersection supplies an opposite-colored row that agrees on
-- every wire on that side of the proposed partition.
def kills (g : W) (a b : List W) (color : Bool) : Bool :=
  let other := if color then ~~~g else g
  (List.range 64).any fun r => g.getLsbD r == color &&
    survivors r a other != 0 && survivors r b other != 0

private theorem witness {w : W} (nonzero : w ≠ 0) : ∃ j : Fin 64, w.getLsbD j.val = true := by
  by_contra! bad
  apply nonzero
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simpa using bad ⟨j,hj⟩

theorem kills_sound (g : W) (a b : List W) (color : Bool) (ok : kills g a b color = true) :
    obstruction g a.toFinset b.toFinset color := by
  obtain ⟨r,hr,checks⟩ := List.any_eq_true.mp ok
  obtain ⟨lhs,rhs⟩ := Bool.and_eq_true_iff.mp checks
  obtain ⟨colorR,partA⟩ := Bool.and_eq_true_iff.mp lhs
  have lt := List.mem_range.mp hr
  let other := if color then ~~~g else g
  have side (x : List W) (yes : survivors r x other != 0) :
      ∃ j : Fin 64, g.getLsbD j.val = !color ∧ Agrees x.toFinset ⟨r,lt⟩ j := by
    obtain ⟨j,on⟩ := witness (bne_iff_ne.mp yes)
    obtain ⟨hit,same⟩ := survivor_sound r j.val j.isLt x other on
    refine ⟨j,?_,fun w hw => same w (List.mem_toFinset.mp hw)⟩
    cases color <;> simpa [other,j.isLt] using hit
  obtain ⟨i,hi,ai⟩ := side a partA
  obtain ⟨j,hj,bj⟩ := side b rhs
  exact ⟨⟨r,lt⟩,i,j,beq_iff_eq.mp colorR,hi,hj,ai,bj⟩

def partitions : List W → List (List W × List W)
  | [] => [([],[])]
  | x :: xs =>
    let ps := partitions xs
    ps.map (fun p => (x :: p.1,p.2)) ++ ps.map (fun p => (p.1,x :: p.2))

theorem filters_mem (s : List W) (f : W → Bool) :
    (s.filter f,s.filter (fun w => !(f w))) ∈ partitions s := by
  induction s with
  | nil => simp [partitions]
  | cons w ws ih =>
    cases h : f w
    · apply List.mem_append_right _ (List.mem_map.mpr ⟨_,ih,?_⟩)
      simp [List.filter_cons,h]
    · apply List.mem_append_left _ (List.mem_map.mpr ⟨_,ih,?_⟩)
      simp [List.filter_cons,h]

def reject (g : W) (k : Nat) (s : List W) : Bool :=
  decide (s.length = k+1 ∧ 1 < s.length) &&
    (partitions s).all fun p => p.1.isEmpty || p.2.isEmpty ||
      (kills g p.1 p.2 false && kills g p.1 p.2 true)

theorem reject_sound (g : W) (s : List W) (unique : s.Nodup) (k j : Nat)
    (budget : j ≤ k) (run : Cone g j s.toFinset) : reject g k s = false := by
  by_contra! bad
  obtain ⟨dimensions,all⟩ := Bool.and_eq_true_iff.mp (show reject g k s = true by simpa using bad)
  have length := of_decide_eq_true dimensions
  have card := List.toFinset_card_of_nodup unique
  have live := run.size
  obtain ⟨A,sub,ha,hb,one⟩ := necessary run (by omega) (by omega)
  let a := s.filter fun w => decide (w ∈ A)
  let b := s.filter fun w => !decide (w ∈ A)
  have mem : (a,b) ∈ partitions s := filters_mem s _
  have eqA : a.toFinset = A := by
    ext w
    simp only [a,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun h => List.mem_toFinset.mp (sub h)
  have eqB : b.toFinset = s.toFinset \ A := by
    ext w
    simp [b]
  have na : a.isEmpty = false := by
    cases e : a with
    | nil => simp [e] at eqA; simp [←eqA] at ha
    | cons => rfl
  have nb : b.isEmpty = false := by
    cases e : b with
    | nil => simp [e] at eqB; simp [←eqB] at hb
    | cons => rfl
  have tests := List.all_eq_true.mp all _ mem
  simp only [na,nb,Bool.false_or,Bool.and_eq_true] at tests
  have lo := kills_sound g a b false tests.1
  have hi := kills_sound g a b true tests.2
  rw [eqA,eqB] at lo hi
  exact one.elim (fun h => h lo) (fun h => h hi)

end PrismSignedFrontier.RootSplit
