import Mathlib

namespace FinalNot

abbrev Bits (n : ℕ) := Fin n → Bool

def below {n : ℕ} (x y : Bits n) := ∀ i, x i = true → y i = true

-- A monotone suffix can turn one inverted bit into the complement of f
-- only if that bit before inversion already computes the whole of f.
theorem one_inversion {n : ℕ} (f g : Bits n → Bool) (suffix : Bits n → Bool → Bool)
    (mono : ∀ x y, below x y → ∀ a b : Bool, (a = true → b = true) →
      suffix x a = true → suffix y b = true)
    (empty : f (fun _ => false) = false) (full : f (fun _ => true) = true)
    (computed : ∀ x, suffix x (!(g x)) = !(f x)) : ∀ x, g x = f x := by
  intro x
  cases hf : f x <;> cases hg : g x <;> try rfl
  · have on : suffix x false = true := by simpa [hg,hf] using computed x
    have top := mono x (fun _ => true) (fun _ _ => rfl) false (!(g (fun _ => true))) (by simp) on
    rw [computed,full] at top
    contradiction
  · have on : suffix (fun _ => false) (!(g (fun _ => false))) = true := by
      simpa [empty] using computed (fun _ => false)
    have here := mono (fun _ => false) x (fun _ h => by cases h) _ true (fun _ => rfl) on
    have off : suffix x true = false := by simpa [hg,hf] using computed x
    rw [off] at here
    contradiction

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def graph (x : Bits 9) := edges.any fun e => x e.1 && x e.2

def row (e : Fin 9 × Fin 9) (i : Fin 9) := decide (i=e.1 ∨ i=e.2)

theorem endpoints : graph (fun _ => false) = false ∧ graph (fun _ => true) = true := by
  decide +kernel

-- The extra raw AND is false on every minimal true input. Turning it off
-- everywhere therefore preserves the output of any monotone realization.
theorem discard_nonedge (suffix : Bits 9 → Bool → Bool)
    (mono : ∀ x y, below x y → ∀ a b : Bool, (a = true → b = true) →
      suffix x a = true → suffix y b = true)
    (computed : ∀ x, suffix x (x 4 && x 6) = graph x) : ∀ x, suffix x false = graph x := by
  have nonedge : ∀ e ∈ edges, (row e 4 && row e 6) = false := by decide +kernel
  intro x
  cases hx : graph x with
  | false =>
    cases hs : suffix x false with
    | false => rfl
    | true =>
      have h := mono x x (fun _ hv => hv) false (x 4 && x 6) (by simp) hs
      rw [computed,hx] at h
      contradiction
  | true =>
    obtain ⟨e,he,ha,hb⟩ := (by simpa [graph,List.any_eq_true] using hx :
        ∃ e ∈ edges, x e.1=true ∧ x e.2=true)
    have pos : graph (row e) = true := by
      apply List.any_eq_true.mpr
      exact ⟨e,he,by simp [row]⟩
    have on := computed (row e)
    rw [nonedge e he,pos] at on
    apply mono (row e) x _ false false (fun h => h) on
    intro i hi
    rcases of_decide_eq_true hi with h|h
    · exact h ▸ ha
    · exact h ▸ hb

end FinalNot
