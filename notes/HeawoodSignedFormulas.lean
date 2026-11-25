import PEqualNP.Defs.MetaComplexity
import FlagStarCircuit
import PlaneSharedFormulas
import PetersenRawNormal

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

def target (x : Fin 14 → Bool) : Bool :=
  (x 0 && x 7) || (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)

def bits (xs : List (Fin 14)) (i : Fin 14) := decide (i ∈ xs)

set_option maxHeartbeats 500000 in
/-- Every other raw vertex can change the target on either slice of the
representative nonincident raw-pair OR. The witnesses use at most three bits. -/
theorem essentialAfterFirstOr : ∀ c : Fin 14, c ≠ 0 → c ≠ 9 → ∀ t : Bool,
    ∃ d : Fin 14, let base : List (Fin 14) := if t then [0,d] else [d]
      bits base c = false ∧ (bits base 0 || bits base 9) = t ∧
      target (bits base) = false ∧ target (bits (c::base)) = true := by
  decide +kernel

def signedValue (p : List (ℕ × ℕ)) (o : ℕ) (x : Fin 14 → Bool) : Bool :=
  (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
    w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false

/-- Combine the external signed binary and monotone lower bounds using the desk's
actual evaluator, including its default wires and gates of arity below two. -/
theorem ordinaryLower (s : ℕ)
    (signed : ∀ p o, (∀ x, signedValue p o x = target x) → s ≤ p.length)
    (monotone : ∀ C : Circuit,
      (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
      (∀ x, circuitFun 14 C x = target x) → s < C.size) :
    ¬HasCircuitSize 14 target s := by
  rintro ⟨C,legal,small,correct⟩
  rcases PetersenRawNormal.normalize 14 C legal with binary | ⟨p,o,short,eval⟩
  · exact (Nat.not_lt_of_ge small) (monotone C binary correct)
  · have floor := signed p o (fun x => (eval x).trans (correct x))
    omega

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
