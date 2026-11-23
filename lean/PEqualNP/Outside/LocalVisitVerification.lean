import Mathlib

namespace PEqualNP.Outside.LocalVisitVerification

-- Assigning an integer boundary to a tape move costs at most one crossing
-- across all offsets. At least one width-B partition meets the average.
theorem cheap_offset {B T : ℕ} (hB : 0 < B) (crossings : Fin B → ℕ)
    (total : ∑ j, crossings j ≤ T) : ∃ j, crossings j ≤ T / B := by
  by_contra! bad
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin B)))
    (fun j _ => show T / B + 1 ≤ crossings j from bad j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  have hi : T / B < T / B + 1 := by omega
  have impossible := (Nat.div_lt_iff_lt_mul hB).mp hi
  rw [Nat.mul_comm B] at h
  omega

-- A checkpoint after every H local steps costs at most T/H slots in all.
theorem local_checkpoints {ι : Type*} [Fintype ι] (visits : ι → ℕ) (H T : ℕ)
    (positive : 0 < H) (total : ∑ i, visits i ≤ T) :
    ∑ i, visits i / H ≤ T / H := by
  apply (Nat.le_div_iff_mul_le positive).2
  rw [Finset.sum_mul]
  exact (Finset.sum_le_sum (fun i _ => Nat.div_mul_le_self (visits i) H)).trans total

-- An event contains a public block identifier and visit record. Its private
-- update touches just that block. Failure remains visible in the final state.
def applyVisit {ι E S : Type*} [DecidableEq ι] (step : ι → S → E → Option S)
    (st : ι → Option S) (e : ι × E) : ι → Option S :=
  Function.update st e.1 ((st e.1).bind (fun s => step e.1 s e.2))

def records {ι E : Type*} [DecidableEq ι] (i : ι) (events : List (ι × E)) : List E :=
  events.filterMap (fun e => if e.1 = i then some e.2 else none)

theorem replay_projection {ι E S : Type*} [DecidableEq ι] (step : ι → S → E → Option S)
    (events : List (ι × E)) (st : ι → Option S) (i : ι) :
    (events.foldl (applyVisit step) st) i =
      (records i events).foldl (fun acc e => acc.bind (fun s => step i s e)) (st i) := by
  induction events generalizing st with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨j,e⟩ := head
    rw [List.foldl_cons,ih]
    by_cases eq : j = i
    · subst j
      simp [records,applyVisit]
    · simp [records,applyVisit,eq,Ne.symm eq]

-- After the first chunk, both endpoints are in the public commitment.
def validChain {E S : Type*} (step : S → E → Option S) (start : S) :
    List (List E × S) → Prop
  | [] => True
  | (es, out) :: rest =>
    es.foldl (fun st e => st.bind (fun v => step v e)) (some start) = some out ∧
      validChain step out rest

theorem checked_chunks {E S : Type*} (step : S → E → Option S)
    (chunks : List (List E × S)) (start : S) (checks : validChain step start chunks) :
    (chunks.flatMap Prod.fst).foldl (fun st e => st.bind (fun v => step v e)) (some start) =
      some (chunks.foldl (fun _ chunk => chunk.2) start) := by
  induction chunks generalizing start with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨es,out⟩ := head
    obtain ⟨transition,tail⟩ := checks
    simpa [List.foldl_append,transition] using ih out tail

end PEqualNP.Outside.LocalVisitVerification
