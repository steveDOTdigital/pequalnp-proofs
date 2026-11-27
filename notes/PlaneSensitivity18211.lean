import PlaneFirstOr18211

namespace PlaneSensitivity18211

open PEqualNP.CircuitLowerBounds

def bits (row : Nat) (i : Nat) : Bool := row.testBit i

def near (p l : Nat) : Bool :=
  let d := Fin.ofNat 13 p - Fin.ofNat 13 l
  decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9)

def adjacent (i j : Nat) : Bool :=
  if i < 13 then
    if j < 13 then false else near i (j-13)
  else if j < 13 then near j (i-13) else false

def complement (hits : Nat → Nat → Bool) (keep : Nat → Bool) (i : Nat) : Bool :=
  !(List.range 13).any (fun j => keep j && hits j i)

def isCap (hits : Nat → Nat → Bool) (keep : Nat → Bool) : Bool :=
  (List.range 13).all fun i =>
    decide (((List.range 13).filter fun j => keep j && hits j i).length ≤ 2)

def hasFour (keep : Nat → Bool) : Bool :=
  decide (((List.range 13).filter keep).length = 4)

def validNegative (w : Nat) : Bool :=
  let P := bits w
  let L := fun j => bits w (13+j)
  let transpose := fun l p => near p l
  (hasFour P && isCap near P && (List.range 13).all (fun l => L l == complement near P l)) ||
  (hasFour L && isCap transpose L && (List.range 13).all (fun p => P p == complement transpose L p))

def completes (w q : Nat) : Bool :=
  (List.range 26).any (fun i => bits w i && adjacent i q)

def samples : List Nat :=
  [724226,23330829,41960104,51388528,2274368,12616082,
    1333761,25239844,2641961,33916544,6422606]

theorem checkedNegatives : samples.all validNegative = true := by decide +kernel

theorem checkedMaximal : samples.all (fun row =>
    (List.range 26).all (fun q => bits row q || completes row q)) = true := by
  decide +kernel

def hitsPin (p q : Nat) (value : Bool) (row : Nat) : Bool :=
  (bits row p == value) && !(bits row q)

theorem checkedPins : (List.range 26).all (fun p =>
    (List.range 26).all (fun q =>
      if p = q then true else
        samples.any (hitsPin p q false) && samples.any (hitsPin p q true))) = true := by
  decide +kernel

theorem hasWitness (p q : Fin 26) (different : p ≠ q) (value : Bool) :
    ∃ row ∈ samples, validNegative row = true ∧ bits row p.val = value ∧
      bits row q.val = false ∧ completes row q.val = true := by
  have outer := List.all_eq_true.mp checkedPins p.val (List.mem_range.mpr p.isLt)
  have pair := List.all_eq_true.mp outer q.val (List.mem_range.mpr q.isLt)
  have uneq : p.val ≠ q.val := fun e => different (Fin.ext e)
  simp only [uneq, ite_false, Bool.and_eq_true_iff] at pair
  have available : samples.any (hitsPin p.val q.val value) = true := by
    cases value
    · exact pair.1
    · exact pair.2
  obtain ⟨row,member,flags⟩ := List.any_eq_true.mp available
  have negative := List.all_eq_true.mp checkedNegatives row member
  have maximalRows := List.all_eq_true.mp checkedMaximal row member
  have more := List.all_eq_true.mp maximalRows q.val (List.mem_range.mpr q.isLt)
  simp only [hitsPin, Bool.and_eq_true_iff, beq_iff_eq, Bool.not_eq_true'] at flags
  exact ⟨row,member,negative,flags.1,flags.2,by simpa [flags.2] using more⟩

theorem foldKeepsAgreement (gs : List Gate) (slot : Nat) (left right : List Bool)
    (sameLength : left.length = right.length)
    (noReads : ∀ g ∈ gs, slot ∉ g.inputs)
    (agree : ∀ i, i ≠ slot → left.getD i false = right.getD i false) :
    ∀ i, i ≠ slot →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) left).getD i false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) right).getD i false := by
  induction gs generalizing left right with
  | nil => exact agree
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun j => left.getD j false)
    have goodMap : g.inputs.map (fun j => left.getD j false) =
        g.inputs.map (fun j => right.getD j false) := by
      apply List.map_congr_left
      intro j member
      apply agree
      intro eq
      exact noReads g (List.mem_cons_self ..) (eq ▸ member)
    simp only [List.foldl_cons]
    rw [← goodMap]
    change ∀ i, i ≠ slot →
      (gs.foldl _ (left ++ [v])).getD i false = (gs.foldl _ (right ++ [v])).getD i false
    apply ih
    · simp [sameLength]
    · intro h hm
      exact noReads h (List.mem_cons_of_mem _ hm)
    · intro i outside
      by_cases old : i < left.length
      · have other : i < right.length := sameLength ▸ old
        rw [List.getD_append _ _ _ _ old,List.getD_append _ _ _ _ other]
        exact agree i outside
      · have far := Nat.le_of_not_gt old
        have other : right.length ≤ i := sameLength ▸ far
        rw [List.getD_append_right _ _ _ _ far,List.getD_append_right _ _ _ _ other,sameLength]

theorem differingEvalRequiresRead (C : Circuit) (slot : Nat) (left right : List Bool)
    (sameLength : left.length = right.length)
    (agree : ∀ i, i ≠ slot → left.getD i false = right.getD i false)
    (different : C.eval left ≠ C.eval right) :
    C.output = slot ∨ ∃ g ∈ C.gates, slot ∈ g.inputs := by
  by_cases output : C.output = slot
  · exact Or.inl output
  · right
    by_contra none
    have noReads : ∀ g ∈ C.gates, slot ∉ g.inputs :=
      fun g hg uses => none ⟨g,hg,uses⟩
    exact different (foldKeepsAgreement C.gates slot left right sameLength
      noReads agree C.output output)

#print axioms hasWitness
#print axioms differingEvalRequiresRead

end PlaneSensitivity18211
