import PEqualNP.Defs.MetaComplexity
import FlagStarCircuit
import PlaneSharedFormulas

namespace HeawoodSignedFormulas
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FlagStarCircuit

def star (p a b c : Fin 14) : Expr 14 :=
  .gate false (.raw p) (.gate true (.gate true (.raw a) (.raw b)) (.raw c))

def witness : Expr 14 :=
  (.gate true (.gate true (.gate true (.gate true (.gate true (.gate true (star 0 7 8 10) (star 1 7 9 13)) (star 2 8 12 13)) (star 3 7 11 12)) (star 4 10 11 13)) (star 5 9 10 12)) (star 6 8 9 11))

theorem upper : PEqualNP.MetaComplexity.HasCircuitSize 14 (fun x : Fin 14 → Bool => (x 0 && x 7) || (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)) 27 := by
  refine ⟨witness.circuit,?_,by decide +kernel,?_⟩
  · intro g hg
    refine ⟨?_,le_of_eq ((ao2 witness).2.2 g hg)⟩
    rcases (ao2 witness).1 g hg with h | h <;> simp [h]
  · intro x
    change circuitFun 14 witness.circuit x = _
    rw [realBool]
    simp [witness,star,Expr.val,op,GateOp.eval,Bool.and_or_distrib_left,Bool.or_assoc]

open PlaneSharedFormulas

/-- The sign bit is true for a negative literal. -/
def literal {V : Type*} (x : V → Bool) (a : V × Bool) : Bool :=
  if a.2 then !(x a.1) else x a.1

theorem forcedPositive {V : Type*} (t : Formula (V × Bool)) (edge col : V → Bool)
    (bad : V → Prop) (signed : ∀ path v, t.label path = some (v,true) → bad v)
    (yes : t.value (literal edge) = true) (no : t.value (literal col) = false)
    (forced : ∀ v, bad v → col v = true → edge v = true) :
    ∃ v, t.label (t.route (literal edge) (literal col)) = some (v,false) ∧
      edge v = true ∧ col v = false := by
  obtain ⟨⟨v,sign⟩,hit,ep,cn⟩ := t.separates _ _ yes no
  cases sign with
  | false => exact ⟨v,hit,ep,cn⟩
  | true =>
    have up : col v = true := by simpa [literal] using cn
    have down : edge v = false := by simpa [literal] using ep
    have h := forced v (signed _ _ hit) up
    simp [down] at h

/-- Membership in the row side of a nonempty leaf rectangle extends the route
from any reached row to the same column on another row in its support. -/
theorem carryRoute {A : Type*} (t : Formula A) (other edge n m : A → Bool)
    (rowMem : t.route other n = t.route edge m) : t.route edge n = t.route other n := by
  rw [rowMem]
  exact t.rectangle edge other m n rowMem.symm

/-- Two different vertex labels cannot both inherit the comparison for one row. -/
theorem noDouble {A : Type*} (t : Formula A) (f g e n : A → Bool) (p l : A)
    (hp : t.label (t.route f n) = some p) (hl : t.label (t.route g n) = some l)
    (left : t.route e n = t.route f n) (right : t.route e n = t.route g n) (ne : p ≠ l) : False := by
  rw [←left] at hp
  rw [←right,hp] at hl
  exact ne (Option.some.inj hl)

end HeawoodSignedFormulas
