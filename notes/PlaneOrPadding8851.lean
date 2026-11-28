import PEqualNP.Defs.TopForm
import PEqualNP.Defs.GenericRejection
import PlaneProfiles8851

namespace PlaneOrPadding8851

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open PEqualNP.GenericRejection

def copyGate (C : Circuit) : Gate := ⟨.or,[C.output,C.output]⟩

def pad (n : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates ++ [copyGate C], n+C.size⟩

theorem padSize (n : Nat) (C : Circuit) : (pad n C).size = C.size + 1 := by
  simp [pad,Circuit.size]

theorem oldGate (n : Nat) (C : Circuit) (j : Nat) (prior : j < C.size) :
    gateAt (pad n C) j = gateAt C j := by
  unfold gateAt pad
  exact List.getD_append _ _ _ _ prior

theorem lastGate (n : Nat) (C : Circuit) : gateAt (pad n C) C.size = copyGate C := by
  unfold gateAt pad Circuit.size
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
  rfl

theorem padLegal (n : Nat) (C : Circuit) (ok : IsAO2 n C)
    (oldOutput : C.output < n+C.size) : IsAO2 n (pad n C) := by
  refine ⟨?_,?_,?_⟩
  · intro g mem
    change g ∈ C.gates ++ [copyGate C] at mem
    rcases List.mem_append.mp mem with original | appended
    · exact ok.1 g original
    · have equal : g = copyGate C := by simpa using appended
      subst g
      exact Or.inr rfl
  · intro j bound i read
    have endBound : j < (pad n C).size := bound
    rw [padSize] at endBound
    by_cases early : j < C.size
    · rw [oldGate n C j early] at read
      exact ok.2.1 j early i read
    · have equal : j = C.size := by omega
      subst j
      rw [lastGate] at read
      have equal : i = C.output := by simpa [copyGate] using read
      simpa only [equal] using oldOutput
  · intro g mem
    change g ∈ C.gates ++ [copyGate C] at mem
    rcases List.mem_append.mp mem with original | appended
    · exact ok.2.2 g original
    · have equal : g = copyGate C := by simpa using appended
      subst g
      rfl

theorem foldLength (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons,ih]
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

theorem padWires (n : Nat) (C : Circuit) (x : List Bool) :
    (pad n C).wires x = C.wires x ++ [C.eval x] := by
  simp [pad,Circuit.wires,Circuit.eval,copyGate,List.foldl_append,GateOp.eval]

theorem lastValue (n : Nat) (C : Circuit) (x : List Bool) (length : x.length = n) :
    wireValue (pad n C) x (n+C.size) = C.eval x := by
  change ((pad n C).wires x).getD (n+C.size) false = C.eval x
  rw [padWires]
  have prev : (C.wires x).length = n + C.size := by
    rw [Circuit.wires,foldLength,length]
    rfl
  rw [← prev, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
  rfl

theorem padEval (n : Nat) (C : Circuit) (x : List Bool) (length : x.length = n) :
    (pad n C).eval x = C.eval x := by
  exact lastValue n C x length

def Model {N : Nat} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (junk : Finset (Finset (Fin N) × Finset (Fin N))) : Prop :=
  ∀ X Y : Finset (Fin N), C.eval (incidenceInput X Y) = true ↔
    incidenceFun S X Y = true ∨ ∃ j ∈ junk, j.1 ⊆ X ∧ j.2 ⊆ Y

theorem incidenceLen {N : Nat} (X Y : Finset (Fin N)) :
    (incidenceInput X Y).length = N + N := by
  simp [incidenceInput]

theorem padModel {N : Nat} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (junk : Finset (Finset (Fin N) × Finset (Fin N)))
    (model : Model S C junk) : Model S (pad (N+N) C) junk := by
  intro X Y
  rw [padEval _ _ _ (incidenceLen X Y)]
  exact model X Y

theorem singletonLine {N q : Nat} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (junk : Finset (Finset (Fin N) × Finset (Fin N)))
    (long : ∀ j ∈ junk, q < j.2.card) (qLarge : 100 < q)
    (model : Model S C junk) (X : Finset (Fin N)) (l : Fin N) :
    C.eval (incidenceInput X {l}) = true ↔ ∃ p ∈ X, p ∈ S l := by
  have noJunk : ¬ ∃ j ∈ junk, j.1 ⊆ X ∧ j.2 ⊆ ({l} : Finset (Fin N)) := by
    rintro ⟨j, mem, _, subset⟩
    have small : j.2.card ≤ 1 := by simpa using Finset.card_le_card subset
    have big := long j mem
    omega
  exact (model X {l}).trans ((or_iff_left noJunk).trans (by simp [incidenceFun]))

def profile {N : Nat} (C : Circuit) (j : Nat) (l : Fin N) : Finset (Fin N) :=
  {p | wireValue C (incidenceInput {p} {l}) (N+N+j) = true}

theorem padProfile {N q : Nat} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (junk : Finset (Finset (Fin N) × Finset (Fin N)))
    (long : ∀ j ∈ junk, q < j.2.card) (qLarge : 100 < q)
    (model : Model S C junk) (l : Fin N) :
    profile (pad (N+N) C) C.size l = S l := by
  ext p
  simp only [profile,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [lastValue _ _ _ (incidenceLen {p} {l})]
  simpa using singletonLine S C junk long qLarge model {p} l

theorem paddedRichOr {N q : Nat} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (junk : Finset (Finset (Fin N) × Finset (Fin N))) (qLarge : 100 < q)
    (Nlarge : 100 < N)
    (sizeLine : ∀ l, (S l).card = q+1)
    (unique : ∀ a b : Fin N, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l)
    (long : ∀ j ∈ junk, q < j.2.card) (model : Model S C junk) :
    ∃ j < (pad (N+N) C).size, (gateAt (pad (N+N) C) j).op = .or ∧
      ∃ lines : Finset (Fin N), 100 < lines.card ∧
        Set.InjOn (profile (N := N) (pad (N+N) C) j) (lines : Set (Fin N)) ∧
        ∀ l ∈ lines, 1 < (profile (pad (N+N) C) j l).card ∧
          profile (pad (N+N) C) j l ⊆ S l ∧
          wireValue (pad (N+N) C) (incidenceInput (S l)ᶜ {l}) (N+N+j) = false := by
  refine ⟨C.size,by simp [padSize],by rw [lastGate];rfl,Finset.univ,by simpa using Nlarge,?_,?_⟩
  · apply PlaneProfiles8851.profilesInjOn S unique
    intro l _
    rw [padProfile S C junk long qLarge model l,sizeLine l]
    exact ⟨by omega,Finset.Subset.refl _⟩
  · intro l _
    rw [padProfile S C junk long qLarge model l,sizeLine l,
      lastValue _ _ _ (incidenceLen (S l)ᶜ {l})]
    refine ⟨by omega,Finset.Subset.refl _,?_⟩
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨p,hp,hin⟩ := (singletonLine S C junk long qLarge model (S l)ᶜ l).mp yes
    exact (Finset.mem_compl.mp hp) hin

#print axioms padLegal
#print axioms padModel
#print axioms paddedRichOr

end PlaneOrPadding8851
