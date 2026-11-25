import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Independent.PseudoforestCharge

variable {V W : Type*} (G : SimpleGraph V)

/-- A four-cycle exists exactly when two distinct vertices have two distinct common neighbors. -/
def LinearNeighbors : Prop :=
  ∀ v u, v ≠ u → ∀ a b, G.Adj v a → G.Adj u a → G.Adj v b → G.Adj u b → a = b

def BranchVertex (v : V) : Prop := ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b

theorem distinguishes (linear : LinearNeighbors G) {v u : V} (diff : v ≠ u)
    (degree : BranchVertex G v) : ∃ w, G.Adj v w ∧ ¬ G.Adj u w := by
  obtain ⟨a,b,va,vb,ab⟩ := degree
  by_cases ua : G.Adj u a
  · exact ⟨b,vb,fun ub => ab (linear v u diff a b va ua vb ub)⟩
  · exact ⟨a,va,ua⟩

def Hits (s : Finset V) := ∃ u ∈ s, ∃ v ∈ s, G.Adj u v

theorem pairFree [DecidableEq V] {u w : V} (missing : ¬ G.Adj u w) : ¬ Hits G {u,w} := by
  rintro ⟨a,ha,b,hb,ab⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact G.loopless.irrefl _ ab
  · exact missing ab
  · exact missing ab.symm
  · exact G.loopless.irrefl _ ab

/-- A wire through which every path from v passes cannot accept a different
singleton if saturating that wire masks additions of v. -/
theorem purePrefix [DecidableEq V] (linear : LinearNeighbors G) {v : V} (degree : BranchVertex G v)
    (wire : Finset V → Prop) (rising : ∀ S T, S ⊆ T → wire S → wire T)
    (mask : ∀ S, v ∉ S → wire S → (Hits G S ↔ Hits G (insert v S))) :
    ∀ u, wire {u} → u=v := by
  intro u hot
  by_contra diff
  obtain ⟨w,vw,uw⟩ := distinguishes G linear (Ne.symm diff) degree
  have absent : v ∉ ({u,w} : Finset V) := by simp [Ne.symm diff,vw.ne]
  have on : wire {u,w} := rising _ _ (by simp) hot
  exact pairFree G uw ((mask _ absent on).mpr ⟨v,by simp,w,by simp,vw⟩)

/-- The other operand of a first cold AND is hot on all neighbors. These two
prefix properties force every edge between degree-two-or-more vertices to
have a marked endpoint. -/
theorem coversCore (marked : V → Prop) (hot : W → V → Prop)
    (coldOperand : ∀ v, BranchVertex G v → ¬ marked v →
      ∃ w, ∀ u, G.Adj v u → hot w u)
    (privateHot : ∀ u, BranchVertex G u → ¬ marked u → ∀ w, hot w u →
      ∀ t, hot w t → t = u) {u v : V}
    (du : BranchVertex G u) (dv : BranchVertex G v) (uv : G.Adj u v) :
    marked u ∨ marked v := by
  classical
  by_contra both
  push Not at both
  obtain ⟨w,neigh⟩ := coldOperand u du both.1
  obtain ⟨a,b,ua,ub,ab⟩ := du
  have only := privateHot v dv both.2 w (neigh v uv)
  exact ab ((only a (neigh a ua)).trans (only b (neigh b ub)).symm)

/-- Distinct pendant centers cannot be charged the same two-neighbor signal. -/
theorem pairOwner (linear : LinearNeighbors G) {p q a b : V} (ab : a ≠ b)
    (pa : G.Adj p a) (pb : G.Adj p b) (qa : G.Adj q a) (qb : G.Adj q b) : p=q := by
  by_contra pq
  exact ab (linear p q pq a b pa qa pb qb)

end Independent.PseudoforestCharge
