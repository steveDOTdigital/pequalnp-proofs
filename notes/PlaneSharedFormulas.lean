import Mathlib.Tactic

namespace PlaneSharedFormulas

inductive Formula (α : Type*) where
  | leaf (a : α)
  | join (l r : Formula α)
  | meet (l r : Formula α)

namespace Formula

def value (t : Formula α) (x : α → Bool) : Bool :=
  match t with
  | .leaf a => x a
  | .join l r => value l x || value r x
  | .meet l r => value l x && value r x

def route (t : Formula α) (p n : α → Bool) : List Bool :=
  match t with
  | .leaf _ => []
  | .join l r => if value l p then false :: route l p n else true :: route r p n
  | .meet l r => if value l n then true :: route r p n else false :: route l p n

def label (t : Formula α) (path : List Bool) : Option α :=
  match t, path with
  | .leaf a, [] => some a
  | .join l _, false::rest | .meet l _, false::rest => label l rest
  | .join _ r, true::rest | .meet _ r, true::rest => label r rest
  | _, _ => none

theorem separates (t : Formula α) (p n : α → Bool)
    (on : value t p = true) (off : value t n = false) :
    ∃ a, label t (route t p n) = some a ∧ p a = true ∧ n a = false := by
  induction t with
  | leaf a => exact ⟨a,rfl,on,off⟩
  | join l r il ir =>
    cases h : value l p with
    | false =>
      have z : value r p = true := by simpa [value,h] using on
      have z' : value r n = false := (Bool.or_eq_false_iff.mp off).2
      simpa [route,h,label] using ir z z'
    | true =>
      have z : value l n = false := (Bool.or_eq_false_iff.mp off).1
      simpa [route,h,label] using il h z
  | meet l r il ir =>
    cases h : value l n with
    | false =>
      have z : value l p = true := (Bool.and_eq_true_iff.mp on).1
      simpa [route,h,label] using il z h
    | true =>
      have z : value r n = false := by simpa [value,h] using off
      have z' : value r p = true := (Bool.and_eq_true_iff.mp on).2
      simpa [route,h,label] using ir z' z

/-- Each individual leaf occurrence receives a rectangle of raw rows and columns.
The valuation vectors may satisfy arbitrary correlations among formula inputs. -/
theorem rectangle (t : Formula α) (p q n m : α → Bool)
    (same : route t p n = route t q m) : route t p m = route t p n := by
  induction t with
  | leaf a => rfl
  | join l r il ir =>
    cases hl : value l p <;> cases hq : value l q <;>
      simp_all [route]
  | meet l r il ir =>
    cases hn : value l n <;> cases hm : value l m <;>
      simp_all [route]

end Formula

/-- The bound after cutting the circuit at every shared internal wire. -/
theorem charge {g raw excess filterRaw proofRaw edges residual cover subCover lost : ℕ}
    (fanout : g+1 = raw+excess) (slots : filterRaw+proofRaw ≤ raw)
    (damage : edges ≤ residual+filterRaw) (matching : cover ≤ subCover+lost)
    (price : residual+subCover ≤ proofRaw) (spare : lost ≤ excess) :
    edges+cover ≤ g+1 := by omega

theorem equalityLoss {g raw excess filterRaw proofRaw edges residual cover subCover lost : ℕ}
    (fanout : g+1 = raw+excess) (slots : filterRaw+proofRaw ≤ raw)
    (damage : edges ≤ residual+filterRaw) (matching : cover ≤ subCover+lost)
    (price : residual+subCover ≤ proofRaw) (spare : lost < excess) :
    edges+cover ≤ g := by omega

/-- Double charges on exceptional edges can occur only between two saving vertices.
The uncovered normal edges outside their endpoints still pay for a cover. -/
theorem exceptionalPrice {endpoints exceptional selected inside outside missing touched
    uncoveredExceptional uncoveredNormal doubled coverOutside : ℕ}
    (partition : selected = inside+outside)
    (total : touched+missing=2*exceptional)
    (endpointCharge : endpoints ≤ inside+missing)
    (edgeCharge : touched+uncoveredExceptional=exceptional+doubled)
    (residualCover : coverOutside ≤ outside+uncoveredNormal) :
    endpoints+coverOutside+doubled ≤ selected+uncoveredNormal+uncoveredExceptional+exceptional := by omega

/-- Six or fewer vertices cannot have three pair collisions per vertex. -/
theorem smallExpansion (k : ℕ) (pos : 0 < k) (small : k ≤ 6) :
    k*(k-1) < 6*k := by interval_cases k <;> decide

end PlaneSharedFormulas
