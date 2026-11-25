import Mathlib.Tactic
import PEqualNP.Defs.MetaComplexityLgpMono

namespace Independent.NinePlaneStars
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The live values at a cut must distinguish every accepted/rejected pair. -/
theorem liveSeparates {W : Type*} [Fintype W] (suffix : (W → Bool) → Bool)
    (up : ∀ a b, (∀ w, a w=true → b w=true) → suffix a=true → suffix b=true)
    (yes no : W → Bool) (hy : suffix yes=true) (hn : suffix no=false) :
    ∃ w, yes w=true ∧ no w=false := by
  classical
  by_contra h
  have le (w : W) (on : yes w=true) : no w=true := by
    cases eq : no w with
    | false => exact False.elim (h ⟨w,on,eq⟩)
    | true => rfl
  have bad := up yes no le hy
  rw [hn] at bad
  contradiction

/-- A gate consumes its two last-use operands, and adds back each operand
that is kept for a later read along with its own output. -/
theorem budget (live remaining kept : ℕ) (two : 2 ≤ live)
    (gates : live+kept ≤ remaining+2) :
    (remaining+1)-(live-2+kept+1) = (remaining+2-live)-kept := by omega

def quad : Circuit := ⟨[
  ⟨.or,[4,5]⟩, ⟨.or,[4,7]⟩, ⟨.or,[5,7]⟩, ⟨.or,[6,8]⟩,
  ⟨.or,[6,10]⟩, ⟨.or,[8,11]⟩, ⟨.or,[9,12]⟩, ⟨.or,[9,13]⟩,
  ⟨.and,[0,14]⟩, ⟨.and,[1,15]⟩, ⟨.and,[2,16]⟩, ⟨.and,[3,17]⟩,
  ⟨.or,[18,19]⟩, ⟨.or,[20,21]⟩, ⟨.or,[22,23]⟩],24⟩

theorem quadSize : quad.size=15 ∧ Monotone2 quad := by
  constructor
  · rfl
  · intro g hg
    simp only [quad,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem quadEval (u v w t a b c d e f : Bool) :
    quad.eval [u,v,w,t,a,b,c,d,e,f] =
      (((u && (c || (a || b))) || (v && (e || (a || d)))) ||
       ((w && (f || (b || d))) || (t && (f || (c || e))))) := by
  simp [quad,Circuit.eval,Circuit.wires,GateOp.eval]

end Independent.NinePlaneStars
