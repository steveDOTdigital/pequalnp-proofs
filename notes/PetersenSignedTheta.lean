import PEqualNP.Outside.L_meta_2960

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenSignedTheta

abbrev Program := List (ℕ × ℕ)
def signedStep (w : List Bool) (ij : ℕ × ℕ) :=
  let z := w.getD ij.1 false && w.getD ij.2 false
  w ++ [z,!z]

def evalStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def neg (i : ℕ) : Gate := ⟨.not,[i]⟩
noncomputable def charged (g : Gate) : Bool :=
  GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op

-- All fixtures and both phases of each raw input use only NOT gates.
-- Zero and four are the two isolated vertices of the restricted nine-input graph.
def setupGates : List Gate :=
  [⟨.not,[]⟩,neg 7,neg 0,neg 1,neg 2,neg 3,neg 4,neg 5,neg 6] ++
  [7,8, 7,9,10,11,7,12,13,14,15, 8,0,1,2,8,3,4,5,6].map neg

def extend (y : Fin 7 → Bool) : Fin 9 → Bool :=
  ![false,y 0,y 1,y 2,false,y 3,y 4,y 5,y 6]

def base (x : Fin 9 → Bool) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def auxBits (y : Fin 7 → Bool) := List.ofFn y ++ [true,false] ++ (List.ofFn y).map Bool.not
def target (y : Fin 7 → Bool) :=
  ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] : List (Fin 7 × Fin 7)).any
    (fun e => y e.1 && y e.2)

theorem prefixRows (y : Fin 7 → Bool) :
    setupGates.foldl evalStep (List.ofFn y) = auxBits y ++ base (extend y) := by
  have finite : ∀ y : Fin 7 → Bool, setupGates.foldl evalStep (List.ofFn y) = auxBits y ++ base (extend y) := by decide +kernel
  exact finite y

-- Each signed instruction becomes an AND and a free NOT. The sixteen-wire
-- offset preserves the default-false semantics even for an invalid source.
def emit : ℕ → Program → List Gate
  | _, [] => []
  | n, g::p => ⟨.and,[16+g.1,16+g.2]⟩ :: neg (16+n) :: emit (n+2) p

private theorem offsetRead (a w : List Bool) (len : a.length = 16) (i : ℕ) :
    (a++w).getD (16+i) false = w.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

private theorem readNew (v : List Bool) (z : Bool) : (v++[z]).getD v.length false = z := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem emitRows (a w : List Bool) (p : Program) (len : a.length=16) :
    (emit w.length p).foldl evalStep (a++w) = a ++ p.foldl signedStep w := by
  induction p generalizing w with
  | nil => rfl
  | cons g p ih =>
    let z := w.getD g.1 false && w.getD g.2 false
    have first : evalStep (a++w) ⟨.and,[16+g.1,16+g.2]⟩ = (a++w)++[z] := by
      change (a++w)++[((a++w).getD (16+g.1) false && ((a++w).getD (16+g.2) false && true))] = _
      rw [offsetRead a w len,offsetRead a w len,Bool.and_true]
    have next : evalStep ((a++w)++[z]) (neg (16+w.length)) = a++signedStep w g := by
      have sz : (a++w).length = 16+w.length := by simp [len]
      have last := readNew (a++w) z
      rw [sz] at last
      change ((a++w)++[z])++[!(((a++w)++[z]).getD (16+w.length) false)] = _
      rw [last]
      simp only [signedStep,List.append_assoc,z,List.singleton_append]
    have size : (signedStep w g).length = w.length+2 := by simp [signedStep]
    simp only [emit,List.foldl_cons,first,next]
    rw [← size]
    exact ih _

def legal (g : Gate) := g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem prefixLegal : ∀ g ∈ setupGates, legal g := by
  simp [setupGates,legal,neg]
theorem prefixCost : setupGates.countP charged = 0 := by decide

theorem emitLegal (n : ℕ) (p : Program) : ∀ g ∈ emit n p, legal g := by
  induction p generalizing n with
  | nil => simp [emit]
  | cons z p ih =>
    intro g hg
    simp only [emit,List.mem_cons] at hg
    rcases hg with rfl | rfl | h
    · simp [legal]
    · simp [legal,neg]
    · exact ih _ _ h

theorem emitCost (n : ℕ) (p : Program) : (emit n p).countP charged = p.length := by
  induction p generalizing n with
  | nil => rfl
  | cons g p ih => simp only [emit,List.countP_cons,charged,neg,ite_true,Bool.false_eq_true,ite_false,List.length_cons,ih]

/-- Transfer the published seven-input non-NOT lower bound to the exact
signed-program statement on nine input slots emitted for L-meta-3196. -/
theorem transfer (lower : ∀ C : Circuit, FanInTwo C → circuitFun 7 C = target →
    11 ≤ C.gates.countP charged) : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 10 → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠ ([(1,2),(2,3),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) := by
  intro p o small
  by_contra! hit
  let C : Circuit := ⟨setupGates ++ emit 20 p,16+o⟩
  have fan : FanInTwo C := by
    intro g hg
    rcases List.mem_append.mp hg with pre | post
    · exact prefixLegal g pre
    · exact emitLegal 20 p g post
  have computes : circuitFun 7 C = target := by
    funext y
    have len : (auxBits y).length = 16 := by simp [auxBits]
    have sz : (base (extend y)).length = 20 := by simp [base]
    have e := emitRows (auxBits y) (base (extend y)) p len
    rw [sz] at e
    change (((setupGates ++ emit 20 p).foldl evalStep (List.ofFn y)).getD (16+o) false) = target y
    rw [List.foldl_append,prefixRows,e,offsetRead _ _ len]
    exact hit (extend y)
  have bound := lower C fan computes
  change 11 ≤ (setupGates ++ emit 20 p).countP charged at bound
  rw [List.countP_append,prefixCost,emitCost] at bound
  omega

-- The numerical certificate is due to errornesttorn, project PR 5972.
theorem excluded : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 10 → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠ ([(1,2),(2,3),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) :=
  transfer PEqualNP.Outside.L_meta_2960

end PetersenSignedTheta
