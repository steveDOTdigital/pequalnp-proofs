import Mathlib.Data.Nat.Bitwise

namespace PackingTrace8221

structure Domain where
  mask : Nat
  patterns : List Nat

structure Problem where
  conflicts : Array Nat
  domains : Array Domain

structure Partial where
  chosen : Nat
  rejected : Nat

def Extends (value : Nat) (state : Partial) : Prop :=
  (∀ j, state.chosen.testBit j = true → value.testBit j = true) ∧
  (∀ j, state.rejected.testBit j = true → value.testBit j = false)

def Agrees (value : Nat) (domain : Domain) (pattern : Nat) : Prop :=
  ∀ j, domain.mask.testBit j = true → pattern.testBit j = value.testBit j

def Solves (problem : Problem) (value : Nat) : Prop :=
  (∀ j, value.testBit j = true → ∀ k,
    (problem.conflicts.getD j 0).testBit k = true → value.testBit k = false) ∧
  ∀ (i : Nat) domain, problem.domains[i]? = some domain →
    ∃ pattern ∈ domain.patterns, Agrees value domain pattern

def compatible (state : Partial) (domain : Domain) (pattern : Nat) : Bool :=
  let must := state.chosen &&& domain.mask
  let forbid := state.rejected &&& domain.mask
  ((must &&& pattern) == must) && ((forbid &&& pattern) == 0)

theorem compatible_of_agrees {value : Nat} {state : Partial} {domain : Domain} {pattern : Nat}
    (ext : Extends value state) (agree : Agrees value domain pattern) :
    compatible state domain pattern = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply beq_iff_eq.mpr
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and]
    cases h₁ : state.chosen.testBit j <;> cases h₂ : domain.mask.testBit j <;> simp [h₁, h₂]
    exact (agree j h₂).trans (ext.1 j h₁)
  · apply beq_iff_eq.mpr
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and]
    cases h₁ : state.rejected.testBit j <;> cases h₂ : domain.mask.testBit j <;> simp [h₁, h₂]
    exact (agree j h₂).trans (ext.2 j h₁)

def move (problem : Problem) (state : Partial) (slot : Nat) (polarity : Bool) : Partial :=
  if polarity then
    ⟨state.chosen ||| 2 ^ slot, state.rejected ||| problem.conflicts.getD slot 0⟩
  else ⟨state.chosen, state.rejected ||| 2 ^ slot⟩

theorem move_extends {problem : Problem} {value : Nat} {state : Partial}
    (sol : Solves problem value) (ext : Extends value state) (j : Nat) (b : Bool)
    (bit : value.testBit j = b) : Extends value (move problem state j b) := by
  cases b
  · refine ⟨ext.1, ?_⟩
    intro k h
    simp only [move, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | rfl
    · exact ext.2 k h
    · exact bit
  · constructor
    · intro k h
      simp only [move, ite_true, Nat.testBit_or, Nat.testBit_two_pow,
        Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | rfl
      · exact ext.1 k h
      · exact bit
    · intro k h
      simp only [move, ite_true, Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ext.2 k h
      · exact sol.1 j bit k h

theorem consistent {value : Nat} {state : Partial} (ext : Extends value state) :
    state.chosen &&& state.rejected = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and]
  cases h₁ : state.chosen.testBit k <;> cases h₂ : state.rejected.testBit k <;> simp [h₁, h₂]
  exact (Bool.noConfusion ((ext.1 k h₁).symm.trans (ext.2 k h₂)))

def certificate (problem : Problem) (code : Array Nat) :
    Nat → Nat → Partial → Bool
  | 0, _, _ => false
  | fuel + 1, ip, state =>
    match code.getD ip 4 with
    | 0 => state.chosen &&& state.rejected != 0
    | 1 =>
      match problem.domains[code.getD (ip + 1) 0]? with
      | none => false
      | some domain => domain.patterns.all (fun p => !(compatible state domain p))
    | 2 =>
      match problem.domains[code.getD (ip + 1) 0]? with
      | none => false
      | some domain =>
        let slot := code.getD (ip + 2) 0
        let polarity := code.getD (ip + 3) 0 == 1
        domain.mask.testBit slot &&
        domain.patterns.all (fun p => !(compatible state domain p) || p.testBit slot == polarity) &&
        certificate problem code fuel (ip + 4) (move problem state slot polarity)
    | 3 =>
      let slot := code.getD (ip + 1) 0
      certificate problem code fuel (code.getD (ip + 2) 0) (move problem state slot true) &&
      certificate problem code fuel (code.getD (ip + 3) 0) (move problem state slot false)
    | _ => false

theorem certificate_sound (problem : Problem) (code : Array Nat) (fuel ip : Nat)
    (state : Partial) (value : Nat) (sol : Solves problem value) (ext : Extends value state)
    (checked : certificate problem code fuel ip state = true) : False := by
  induction fuel generalizing ip state with
  | zero => simp [certificate] at checked
  | succ fuel ih =>
    simp only [certificate] at checked
    split at checked
    · simp [consistent ext] at checked
    · split at checked
      · contradiction
      · rename_i domain found
        obtain ⟨pattern, member, agree⟩ := sol.2 _ _ found
        have h := List.all_eq_true.mp checked pattern member
        simp [compatible_of_agrees ext agree] at h
    · split at checked
      · contradiction
      · rename_i domain found
        simp only [Bool.and_eq_true_iff, Array.getD_eq_getD_getElem?] at checked
        obtain ⟨⟨onMask, rule⟩, more⟩ := checked
        obtain ⟨pattern, member, agree⟩ := sol.2 _ _ found
        have conclusion := List.all_eq_true.mp rule pattern member
        simp [compatible_of_agrees ext agree] at conclusion
        have bit := (agree _ onMask).symm.trans conclusion
        exact ih _ _ (move_extends sol ext _ _ bit) more
    · obtain ⟨yes, no⟩ := Bool.and_eq_true_iff.mp checked
      cases v : value.testBit (code.getD (ip + 1) 0)
      · exact ih _ _ (move_extends sol ext _ false v) no
      · exact ih _ _ (move_extends sol ext _ true v) yes
    · contradiction

theorem unsat_of_certificate (problem : Problem) (code : Array Nat) (fuel : Nat)
    (checked : certificate problem code fuel 0 ⟨0, 0⟩ = true) (value : Nat) :
    ¬ Solves problem value := by
  intro sol
  apply certificate_sound problem code fuel 0 ⟨0, 0⟩ value sol ?_ checked
  constructor <;> intro j bit <;> simp at bit

#print axioms unsat_of_certificate

end PackingTrace8221
