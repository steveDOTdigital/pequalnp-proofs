import PetersenPackedBoundary
import PetersenFinalNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenBoundaryComplete

abbrev Bits := Fin 9 → Bool
def graph (x : Bits) : Bool := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
def row (j : Fin 24) (i : Fin 9) : Bool :=
  ([5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968] : List ℕ).getD i.val 0 |>.testBit j.val
def below (x y : Bits) : Prop := ∀ i, x i = true → y i = true
instance (x y : Bits) : Decidable (below x y) := inferInstanceAs (Decidable (∀ i, x i = true → y i = true))

-- Pick a contained edge or a containing maximal independent set on each row.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem covered : ∀ r : Fin 512,
    let x : Bits := fun i => r.val.testBit i.val
    (graph x = true → ∃ j : Fin 24, j.val < 12 ∧ below (row j) x) ∧
    (graph x = false → ∃ j : Fin 24, 12 ≤ j.val ∧ below x (row j)) := by decide +kernel

theorem complete (F : Bits → Bool)
    (mono : ∀ x y, below x y → F x = true → F y = true)
    (pass : ∀ j : Fin 24, F (row j) = decide (j.val < 12)) : F = graph := by
  funext x
  let b := BitVec.ofBoolListLE (List.ofFn x)
  let r : Fin 512 := ⟨b.toNat,by have h := b.isLt; simpa [b] using h⟩
  have rep : (fun i : Fin 9 => r.val.testBit i.val) = x := by
    funext i
    change b.getLsbD i.val = x i
    simp only [b,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]
  have proof := covered r
  dsimp only at proof
  rw [rep] at proof
  cases eq : graph x with
  | true =>
    obtain ⟨j,hj,le⟩ := proof.1 eq
    exact mono _ _ le (by simp [pass,hj])
  | false =>
    obtain ⟨j,hj,le⟩ := proof.2 eq
    cases fx : F x with
    | false => rfl
    | true =>
      have impossible := mono _ _ le fx
      simp [pass,Nat.not_lt.mpr hj] at impossible

def decode (g : PetersenPackedBoundary.Op) : Gate :=
  ⟨ite (g.1 = true) .or .and, [g.2.1,g.2.2]⟩

theorem liftProgram (p : List (Bool × ℕ × ℕ)) (o : ℕ)
    (pass : ∀ j : Fin 24, ((p.foldl PetersenPackedBoundary.packed
      [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968]).getD o 0).testBit j.val = decide (j.val < 12)) :
    ∃ C : Circuit, FanInTwo C ∧ C.size = p.length ∧ circuitFun 9 C = graph := by
  let C : Circuit := ⟨p.map decode,o⟩
  have law (g : PetersenPackedBoundary.Op) : ((decode g).op = .and ∨ (decode g).op = .or) ∧ (decode g).inputs.length = 2 := by
    rcases g with ⟨b,i,j⟩
    cases b <;> simp [decode]
  have ordinary : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
    intro g mem
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp mem
    exact law z
  have full : FanInTwo C := by
    intro g mem
    obtain ⟨op,sz⟩ := ordinary g mem
    exact ⟨op.imp_right Or.inl,by omega⟩
  have inverse (g : PetersenPackedBoundary.Op) : PetersenPackedBoundary.code (decode g) = g := by
    rcases g with ⟨b,i,j⟩
    cases b <;> rfl
  have mapped : C.gates.map PetersenPackedBoundary.code = p := by
    change (p.map decode).map PetersenPackedBoundary.code = _
    simp only [List.map_map,Function.comp_def,inverse]
    exact List.map_id' p
  refine ⟨C,full,by simp [C,Circuit.size],complete _ ?_ ?_⟩
  · intro x y le yes
    have order : FinalNotWires.WireLE (List.ofFn x) (List.ofFn y) := by
      intro i
      by_cases h : i < 9
      · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h)]
        simpa only [List.getElem_ofFn] using le ⟨i,h⟩
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h : (List.ofFn x).length ≤ i)]
        simp
    exact FinalNotWires.fold_mono C.gates _ _ (fun g mem => (ordinary g mem).1) (by simp) order C.output yes
  · intro j
    let masks : List ℕ := [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968]
    have run := PetersenPackedBoundary.fold C.gates ordinary masks j.val
    rw [mapped] at run
    have atOut := congrArg (fun l : List Bool => l.getD o false) run
    rw [← PetersenPackedBoundary.bitGet] at atOut
    exact atOut.symm.trans (pass j)

theorem exclusion (known : ¬HasCircuitSize 9 graph 14) (p : List (Bool × ℕ × ℕ)) (o : ℕ) (hp : p.length ≤ 14) :
    ∃ j : Fin 24, ((p.foldl PetersenPackedBoundary.packed
      [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968]).getD o 0).testBit j.val ≠ decide (j.val < 12) := by
  by_contra! pass
  obtain ⟨C,hc,size,eq⟩ := liftProgram p o pass
  exact known ⟨C,hc,by omega,fun x => congrFun eq x⟩

end PetersenBoundaryComplete
