import PlaneOrPadding8851
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Defs.NestedCoverCircuit

namespace PlaneTwoOutputs17653

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def value (tape : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => tape.getD i false)

def bounded (size : Nat) (g : Gate) : Gate :=
  if (g.inputs.all (fun i => decide (i < size))) then g
  else match g.op with
    | .and => ⟨.or, []⟩
    | _ => ⟨g.op, g.inputs.filter (fun i => decide (i < size))⟩

theorem boundedInputs (size : Nat) (g : Gate) : ∀ i ∈ (bounded size g).inputs, i < size := by
  intro i mem
  unfold bounded at mem
  split at mem
  · rename_i allIn
    simpa using (List.all_eq_true.mp allIn i mem)
  · split at mem
    · simp at mem
    · exact of_decide_eq_true (List.mem_filter.mp mem).2

theorem boundedMono (size : Nat) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (bounded size g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (bounded size g).inputs.length ≤ 2 := by
  unfold bounded
  split
  · exact hg
  · split
    · simp
    · exact ⟨hg.1, (List.length_filter_le ..).trans hg.2⟩

theorem filterOr (tape : List Bool) (is : List Nat) :
    ((is.filter (fun i => decide (i < tape.length))).map
       (fun i => tape.getD i false)).any id =
    (is.map (fun i => tape.getD i false)).any id := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    by_cases hi : i < tape.length
    · simpa [hi, List.filter_cons] using
        congrArg (fun q => tape.getD i false || q) ih
    · have hv : tape.getD i false = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      simpa [hi, hv, List.filter_cons] using ih

theorem boundedValue (tape tail : List Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    value (tape ++ tail) (bounded tape.length g) = value tape g := by
  have args : ((bounded tape.length g).inputs.map fun i => (tape ++ tail).getD i false) =
      ((bounded tape.length g).inputs.map fun i => tape.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact List.getD_append _ _ _ _ (boundedInputs _ _ i hi)
  unfold value
  rw [args]
  unfold bounded
  split
  · rfl
  · rename_i bad
    have modes : g.op = .and ∨ g.op = .or := by simpa using hg
    rcases modes with andOp | orOp
    · rw [andOp]
      change false = (g.inputs.map fun i => tape.getD i false).all id
      symm
      cases eq : (g.inputs.map fun i => tape.getD i false).all id
      · rfl
      · exfalso
        apply bad
        apply List.all_eq_true.mpr
        intro i mem
        have hi := List.all_eq_true.mp eq _ (List.mem_map.mpr ⟨i,mem,rfl⟩)
        by_contra out
        simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa using out)] at hi
    · rw [orOp]
      exact filterOr tape g.inputs

def join (n : Nat) (C : Circuit) (g h : Gate) : Circuit :=
  let m := n+C.size
  ⟨C.gates ++ [bounded m g,bounded m h,⟨.or,[m,m+1]⟩], m+2⟩

theorem joinSize (n : Nat) (C : Circuit) (g h : Gate) : (join n C g h).size = C.size+3 := by
  simp [join,Circuit.size]

theorem joinMono (n : Nat) (C : Circuit) (g h : Gate) (core : Monotone2 C)
    (terminals : Monotone2 (⟨[g,h],0⟩ : Circuit)) : Monotone2 (join n C g h) := by
  intro k mem
  change _ ∈ C.gates ++ [bounded (n+C.size) g,bounded (n+C.size) h,
    (⟨.or,[n+C.size,n+C.size+1]⟩ : Gate)] at mem
  rcases List.mem_append.mp mem with old | now
  · exact core k old
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at now
    rcases now with rfl | rfl | rfl
    · exact boundedMono _ _ (terminals g (by simp))
    · exact boundedMono _ _ (terminals h (by simp))
    · simp

theorem joinReadsBack (n : Nat) (C : Circuit) (g h : Gate)
    (core : NestedCover.ReadsBack n C) : NestedCover.ReadsBack n (join n C g h) := by
  intro j valid i
  let m := n + C.size
  change j < (C.gates ++ [bounded m g,bounded m h,(⟨.or,[m,m+1]⟩ : Gate)]).length at valid
  change i ∈ ((C.gates ++ [bounded m g,bounded m h,(⟨.or,[m,m+1]⟩ : Gate)]).getD
    j ⟨.or,[]⟩).inputs → _
  by_cases old : j < C.gates.length
  · rw [List.getD_append _ _ _ _ old]
    exact core j old i
  · simp only [List.length_append,List.length_cons,List.length_nil] at valid
    have rel : C.gates.length ≤ j := Nat.le_of_not_gt old
    rw [List.getD_append_right _ _ _ _ rel]
    have idx : j - C.gates.length = 0 ∨ j - C.gates.length = 1 ∨ j - C.gates.length = 2 := by omega
    have hm : m ≤ n + j := by simp only [m,Circuit.size]; omega
    rcases idx with idx | idx | idx
    · rw [idx]
      exact fun hi => (boundedInputs _ _ i hi).trans_le hm
    · rw [idx]
      exact fun hi => (boundedInputs _ _ i hi).trans_le hm
    · rw [idx]
      intro hi
      change i ∈ [m,m+1] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      dsimp [m,Circuit.size] at hi
      omega

theorem joinEval (n : Nat) (C : Circuit) (g h : Gate) (x : List Bool) (len : x.length = n)
    (terminals : Monotone2 (⟨[g,h],0⟩ : Circuit)) :
    (join n C g h).eval x = (value (C.wires x) g || value (C.wires x) h) := by
  let tape := C.wires x
  have width : tape.length = n+C.size := by
    change (C.wires x).length = _
    rw [Circuit.wires,PlaneOrPadding8851.foldLength,len]
    rfl
  let a := value tape g
  let b := value tape h
  have first : value tape (bounded (n+C.size) g) = a := by
    rw [← width]
    simpa only [List.append_nil] using boundedValue tape [] g (terminals g (by simp)).1
  have second : value (tape ++ [a]) (bounded (n+C.size) h) = b := by
    rw [← width]
    exact boundedValue tape [a] h (terminals h (by simp)).1
  have left : ((tape ++ [a]) ++ [b]).getD (n+C.size) false = a := by
    rw [← width,List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self]
    rfl
  have right : ((tape ++ [a]) ++ [b]).getD (n+C.size+1) false = b := by
    have pos : (tape ++ [a]).length = n+C.size+1 := by simp [width]
    rw [← pos,List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self]
    rfl
  unfold join Circuit.eval
  change ((C.gates ++ [bounded (n+C.size) g,bounded (n+C.size) h,
    (⟨.or,[n+C.size,n+C.size+1]⟩ : Gate)]).foldl (fun w g => w ++ [value w g]) x).getD (n+C.size+2) false = (a || b)
  rw [List.foldl_append]
  change (((tape ++ [value tape (bounded (n+C.size) g)]) ++
    [value (tape ++ [value tape (bounded (n+C.size) g)]) (bounded (n+C.size) h)]) ++
    [value (((tape ++ [value tape (bounded (n+C.size) g)]) ++
      [value (tape ++ [value tape (bounded (n+C.size) g)]) (bounded (n+C.size) h)]))
      (⟨.or,[n+C.size,n+C.size+1]⟩ : Gate)]).getD (n+C.size+2) false = _
  rw [first,second]
  have third : value ((tape ++ [a]) ++ [b]) (⟨.or,[n+C.size,n+C.size+1]⟩ : Gate) = (a || b) := by
    change ([_ , _] : List Bool).any id = _
    dsimp only
    rw [left,right]
    cases a <;> cases b <;> rfl
  rw [third]
  have pos : ((tape ++ [a]) ++ [b]).length = n+C.size+2 := by
    simp only [List.length_append,List.length_cons,List.length_nil,width]
  rw [← pos,List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self]
  rfl

#print axioms joinEval
#print axioms joinMono
#print axioms joinReadsBack

end PlaneTwoOutputs17653
