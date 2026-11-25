import PEqualNP.Defs

namespace CycleComplement10466

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)
def assignment (r : Fin 128) (j : Fin 7) := r.val.testBit j.val
def witness : Circuit := ⟨[
  ⟨.or, [0,1]⟩,
  ⟨.or, [6,7]⟩,
  ⟨.or, [0,4]⟩,
  ⟨.or, [3,4]⟩,
  ⟨.or, [5,6]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.or, [3,12]⟩,
  ⟨.and, [11,13]⟩,
  ⟨.and, [8,10]⟩,
  ⟨.and, [9,2]⟩,
  ⟨.and, [5,7]⟩,
  ⟨.or, [17,14]⟩,
  ⟨.or, [18,15]⟩,
  ⟨.or, [19,16]⟩], 20⟩

theorem upper : witness.size = 14 ∧ Monotone2 witness ∧
    ∀ x : Fin 7 → Bool, circuitFun 7 witness x = target x := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;>
    first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel

theorem covers : ∀ x : Fin 7 → Bool, ∃ r : Fin 128, assignment r = x := by
  decide +kernel

def paid (g : Gate) : Nat := match g.op with
  | .not => 0
  | _ => 1

theorem paid_le (gs : List Gate) : (gs.map paid).sum ≤ gs.length ∧
    ((gs.map paid).sum = gs.length → ∀ g ∈ gs, g.op ≠ .not) := by
  induction gs with
  | nil => simp
  | cons g t ih =>
    have cap : paid g ≤ 1 := by cases h : g.op <;> simp [paid,h]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    refine ⟨by omega,?_⟩
    intro eq u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · intro h
      have z : paid u = 0 := by simp [paid,h]
      omega
    · exact ih.2 (by omega) u hu

/-- The finite search supplies the first hypothesis. The conclusion uses the
actual evaluator and also covers empty gates and out-of-range references. -/
theorem replacement
    (exclude : ∀ (gs : List Gate) (out : Nat), FanInTwo (⟨gs,out⟩ : Circuit) →
      (∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) →
      (gs.map paid).sum ≤ 12 → ∃ r : Fin 128,
        circuitFun 7 ⟨gs,out⟩ (assignment r) ≠ target (assignment r))
    (C : Circuit) (ok : FanInTwo C)
    (single : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not →
      (C.gates.get j).op = .not → i = j)
    (hit : ∀ x, circuitFun 7 C x = target x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 7 D x = target x := by
  by_cases mono : Monotone2 C
  · exact ⟨C,mono,le_rfl,hit⟩
  have strict : (C.gates.map paid).sum < C.gates.length := by
    obtain ⟨cap,full⟩ := paid_le C.gates
    by_contra! bad
    apply mono
    intro g hg
    obtain ⟨choice,arity⟩ := ok g hg
    refine ⟨?_,arity⟩
    rcases choice with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (full (by omega) g hg h)
  have lower : 13 ≤ (C.gates.map paid).sum := by
    by_contra! bad
    obtain ⟨r,wrong⟩ := exclude C.gates C.output ok single (by omega)
    exact wrong (hit _)
  exact ⟨witness,upper.2.1,by rw [upper.1]; change 14 ≤ C.gates.length; omega,upper.2.2⟩

end CycleComplement10466
