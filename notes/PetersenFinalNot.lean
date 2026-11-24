import PEqualNP.Defs

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

open PEqualNP.CircuitLowerBounds
namespace FinalNotWires
def WireLE (a b : List Bool) := ∀ i, a.getD i false = true → b.getD i false = true
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def fold (gs : List Gate) (w : List Bool) := gs.foldl step w
def mono (gs : List Gate) := ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

theorem gate_mono (g : Gate) (a b : List Bool) (h : WireLE a b) (kind : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases kind with hk|hk
  · simp only [hk,GateOp.eval,List.all_eq_true,List.mem_map,id_eq,forall_exists_index,and_imp]
    intro ha v i hi e
    subst v
    exact h i (ha _ i hi rfl)
  · simp only [hk,GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
    rintro ⟨v,⟨i,hi,rfl⟩,ok⟩
    exact ⟨_,⟨i,hi,rfl⟩,h i ok⟩

theorem append_mono (a b : List Bool) (hlen : a.length=b.length) (h : WireLE a b)
    (x y : Bool) (hxy : x=true → y=true) : WireLE (a++[x]) (b++[y]) := by
  intro i hi
  by_cases inA : i<a.length
  · rw [List.getD_append _ _ _ _ inA] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    rw [← hlen]
    by_cases atEnd : i=a.length
    · simpa [atEnd] using hxy (by simpa [atEnd] using hi)
    · have hbound : [x].length ≤ i-a.length := by simp; omega
      rw [List.getD_eq_default _ _ hbound] at hi
      contradiction

theorem fold_mono (gs : List Gate) (a b : List Bool) (m : mono gs)
    (hl : a.length=b.length) (h : WireLE a b) : WireLE (fold gs a) (fold gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    change WireLE (fold gs (step a g)) (fold gs (step b g))
    apply ih _ _ (fun z hz => m z (List.mem_cons_of_mem _ hz))
    · simp [step,hl]
    · exact append_mono a b hl h _ _ (gate_mono g a b h (m g (by simp)))

theorem fold_length (gs : List Gate) (w : List Bool) : (fold gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [fold]
  | cons g gs ih =>
    change (fold gs (step w g)).length=_
    rw [ih]
    simp [step,Nat.add_comm,Nat.add_left_comm]


open FinalNot

def raw (x : Bits 9) (t : Bool) := List.ofFn x ++ [t]

theorem inputs_mono (x y : Bits 9) (h : below x y) : WireLE (List.ofFn x) (List.ofFn y) := by
  intro i hit
  by_cases hi : i<9
  · rw [List.getD_eq_getElem _ _ (by simpa),List.getElem_ofFn] at hit ⊢
    exact h ⟨i,hi⟩ hit
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hit
    contradiction

theorem normalize_one (pre post : List Gate) (mPre : mono pre) (mPost : mono post) (arg out : ℕ)
    (realizes : ∀ x : Bits 9, let w := fold pre (raw x (x 4 && x 6))
      (fold post (w ++ [!(w.getD arg false)])).getD out false = !(graph x)) :
    ∀ x : Bits 9, (fold pre (raw x false)).getD arg false = graph x := by
  let old (x : Bits 9) := fold pre (raw x (x 4 && x 6))
  let g (x : Bits 9) := (old x).getD arg false
  let k (x : Bits 9) (v : Bool) := (fold post (old x ++ [v])).getD out false
  have rawLE (x y : Bits 9) (xy : below x y) (p q : Bool) (hpq : p=true → q=true) :
      WireLE (raw x p) (raw y q) :=
    append_mono _ _ (by simp) (inputs_mono _ _ xy) _ _ hpq
  have size (x y : Bits 9) : (old x).length = (old y).length := by
    simp [old,fold_length,raw]
  have natural (x y : Bits 9) (xy : below x y) : WireLE (old x) (old y) := by
    apply fold_mono pre _ _ mPre (by simp [raw])
    apply rawLE x y xy
    simp only [Bool.and_eq_true]
    exact fun h => ⟨xy 4 h.1,xy 6 h.2⟩
  have know : ∀ x, g x = graph x := by
    apply one_inversion graph g k _ endpoints.1 endpoints.2 realizes
    intro x y xy a b ab
    exact fold_mono post _ _ mPost (by simp [size x y]) (append_mono _ _ (size x y) (natural x y xy) _ _ ab) out
  apply discard_nonedge (fun x v => (fold pre (raw x v)).getD arg false) _ know
  intro x y xy a b ab
  exact fold_mono pre _ _ mPre (by simp [raw]) (rawLE _ _ xy _ _ ab) arg


open PEqualNP.MetaComplexity in
theorem normalization_child : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ A B : Circuit, Monotone2 A → Monotone2 B →
        (∀ x : Fin 9 → Bool, let w := A.wires (List.ofFn x ++ [x 4 && x 6])
          B.eval (w ++ [!(w.getD A.output false)]) = !(f x)) →
        ∀ x : Fin 9 → Bool, A.eval (List.ofFn x ++ [false]) = f x := by
  intro f A B a b h
  have same : ∀ x : Bits 9, f x = graph x := by
    decide +kernel
  have ma : mono A.gates := fun g hg => (a g hg).1
  have mb : mono B.gates := fun g hg => (b g hg).1
  have realization : ∀ x : Bits 9, let w := fold A.gates (raw x (x 4 && x 6))
      (fold B.gates (w ++ [!(w.getD A.output false)])).getD B.output false = !(graph x) := by
    intro x
    exact (h x).trans (congrArg Bool.not (same x))
  intro x
  exact (normalize_one A.gates B.gates ma mb A.output B.output realization x).trans (same x).symm

end FinalNotWires
