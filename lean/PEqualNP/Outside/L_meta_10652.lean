import Mathlib
import PEqualNP.Defs

-- The certified eight-input lower bound is from merged L_meta_8519.
-- The pin and relabel lemmas are from the Bow section of merged L_meta_8451.
-- The nine-input reduction and vertex map are by steveDOTdigital.
namespace PEqualNP.Outside.L_meta_10652_aux.Deletion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp
def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]
theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _
def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}
def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false
theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj
theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card
theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega
theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this
theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g
theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega
theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]
abbrev Stat := Sum Bool ℕ
def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false
def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)
def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])
theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega
def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g
theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg
theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]
theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega
theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp
theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega
theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h
theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]
theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)
theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩
theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp
theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj
theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]
theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this
theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false
theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩
theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]
theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj
theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1
theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false
theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)
theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this
theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]
theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''
end PEqualNP.Outside.L_meta_10652_aux.Deletion


namespace PEqualNP.Outside.L_meta_10652_aux.Base_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
      P s (negD d a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then andD d a b else orD d a b) ≠ 0 →
      (if c then andD d a b else orD d a b) ≠ d →
      (if c then andD d a b else orD d a b) ∉ (a :: b :: r) →
      P s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {d y : Nat}

theorem Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then andD d a b else orD d a b) ≠ 0)
      (hd : (if c then andD d a b else orD d a b) ≠ d)
      (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
      (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h0 hd hm h))
    {t ws} (h : RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def availB (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m)

theorem availB_iff (d : Nat) (bank : List Nat) (w : Nat) :
    availB d bank w = true ↔ Avail d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

def Lower (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach d roots p bank → Avail d bank T → L ≤ p

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem negD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (a : Nat) :
    negD d1 a &&& d = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> simp_all

theorem andD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    andD d1 a b &&& d = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [andD, Nat.testBit_and] at *
  cases hi : d.testBit i <;> simp_all

theorem orD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    orD d1 a b &&& d = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [orD, Nat.testBit_and, Nat.testBit_or] at *
  cases hi : d.testBit i <;> simp_all

theorem negD_const {d : Nat} (hd : d &&& mask256 = d) {a : Nat} (hc : IsConst d a) :
    IsConst d (negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
    (binD d op a b &&& d = 0) ∨ (binD d op a b &&& d = d) ∨ (binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

theorem avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD d1 T s ws) {roots p bank}
    (hp : NatReach d roots p bank) (hs : ∀ w ∈ ws, Avail d bank w) :
    ∃ q next, NatReach d roots q next ∧ Avail d next T ∧
      q + ws.countP (isConstB d) ≤ p + s := by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false := by
      cases hc : isConstB d T with
      | false => rfl
      | true => exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p, bank, hp, hs T (by simp), by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q, next, hq, ht, hle⟩ := ih hp (fun w hw => hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q, next, hq, ht, hle⟩
  | @one s a r save _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    by_cases hca : IsConst d a
    · have hc_neg : IsConst d (negD d1 a) := by
        have e := negD_and_sub hd hsub a
        rcases negD_const hd hca with h0 | h1
        · exact Or.inl (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h0))
        · exact Or.inr (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h1))
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact Or.inl hc_neg
        · exact hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw])
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have h1 : isConstB d (negD d1 a) = true := (isConstB_iff _ _).2 hc_neg
      have h2 : isConstB d a = true := (isConstB_iff _ _).2 hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h1, h2, ite_true] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hreach' : NatReach d roots (p + 1) (negD d a :: bank) := Or.inl ⟨bank, a, rfl, hp, ha⟩
      have hneg_av : Avail d (negD d a :: bank) (negD d1 a) :=
        Or.inr ⟨negD d a, List.mem_cons_self, by rw [negD_and_sub hd hsub a]; simp [negD, Nat.and_assoc, Nat.and_self]⟩
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d (negD d a :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hneg_av
        · exact avail_cons _ _ (hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw]))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have h2 : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd ((isConstB_iff _ _).1 h) hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h2, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
  | @two s a b r conj ka kb _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := if conj then andD d1 a b else orD d1 a b
    set z0 := binD d (!conj) a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      cases conj
      · simp only [z1, z0, Bool.false_eq_true, ite_false, Bool.not_false, binD, ite_true]
        rw [orD_and_sub hsub]; simp [orD, Nat.and_assoc, Nat.and_self]
      · simp only [z1, z0, ite_true, Bool.not_true, Bool.false_eq_true, binD, ite_false]
        rw [andD_and_sub hsub]; simp [andD, Nat.and_assoc, Nat.and_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases binD_const_left (!conj) hca with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
        · dsimp only [z0]; rw [binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0) := by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true := (isConstB_iff _ _).2 hca
          rcases binD_const_left (!conj) hca with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by
              simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = binD d (!conj) b a &&& d := by rw [hz_eq, binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by
              simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach d roots (p + 1) (z0 :: bank) := Or.inr ⟨bank, a, b, !conj, rfl, hp, ha, hb⟩
      have hz_av : Avail d (z0 :: bank) z1 := Or.inr ⟨z0, List.mem_cons_self, hz_eq.symm⟩
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d (z0 :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons, hna, hnb, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩

-- Backward extraction: NatReach d roots p bank + Avail d bank T -> RunD d (T &&& d) s ws!
theorem mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_assoc, Nat.and_self]

theorem negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem pull_one {d Y k ws} (hd : d &&& mask256 = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Avail d b a) (hsub : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hc
        rcases negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h1)
      obtain ⟨v, hv, hve⟩ := ha.resolve_left ha_nc
      set a' := a &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨v, hv, hve⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : negD d a' = z := negD_mask d a
      have h1 : RunD d Y k (negD d a' :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      have hne0 : negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : RunD d Y k (negD d a' :: kept true a' (rest.erase a')) :=
          Run.perm (hp2.cons _) h1
        have hnm : negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Run.perm hp2.symm (Run.one true hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hne0 hned hnm h2⟩
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_prop
          · exact hrest_prop w hw
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_mem
          · exact hrest_sub w hw
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Avail d b a) (hc : Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, binD, andD, orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hca
        rcases binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hz' : z = binD d op c a := binD_comm d op a c
        rcases binD_const_left op hcc with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans (by rw [hz']; exact h0))
        · exact hzp.2 (hz_mask.symm.trans (by rw [hz']; exact h1))
        · rcases ha with hca | ⟨v, hv, hve⟩
          · exact absurd hca ha_nc
          · have he' : z &&& d = a &&& d := hz'.symm ▸ he
            exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he'.symm.trans hz_mask)⟩)
      obtain ⟨va, hva, hvae⟩ := ha.resolve_left ha_nc
      obtain ⟨vc, hvc, hvce⟩ := hc.resolve_left hc_nc
      set a' := a &&& d
      set c' := c &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨va, hva, hvae⟩
      have hc'_mem : c' ∈ b.map (· &&& d) := List.mem_map.2 ⟨vc, hvc, hvce⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := ⟨fun e => hc_nc (Or.inl e), fun e => hc_nc (Or.inr e)⟩
      have hne_ac : a' ≠ c' := by
        intro heq
        dsimp only [a', c'] at heq
        have hz_eq : z = a' := by
          cases op
          · simp only [z, binD, Bool.false_eq_true, ite_false]; rw [← andD_mask, ← heq]; simp [andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, binD, ite_true]; rw [← orD_mask, ← heq]; simp [orD, a', Nat.and_assoc, Nat.and_self]
        exact hzb (hz_eq ▸ ha'_mem)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : (if !op then andD d a' c' else orD d a' c') = z := by
        cases op
        · simp [z, binD, a', c', andD_mask]
        · simp [z, binD, a', c', orD_mask]
      have h1 : RunD d Y k ((if !op then andD d a' c' else orD d a' c') :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail := by
        rw [mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept, mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then andD d a' c' else orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then andD d a' c' else orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then andD d a' c' else orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD d Y (k + 1) (a' :: c' :: tail) := Run.two (!op) ka kb hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac, hna_tail], List.nodup_cons.2 ⟨hnc_tail, htail_nd⟩⟩
      refine ⟨k + 1, a' :: c' :: tail, le_rfl, hnd3, ?_, ?_, h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& mask256 = d)
    (hr : NatReach d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (· &&& d)) ∧ RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : binD d op a c &&& d = binD d op a c := by cases op <;> simp [binD, andD, orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& mask256 = d)
    (hnc : ¬ IsConst d T) (hr : NatReach d roots p bank) (ha : Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

-- Essential variable lemma + lower_slice + lower_base + lower_iso!
theorem runD_bits {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [andD, orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem runD_bits_le {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem lower_base {d : Nat} {roots : List Nat} {T : Nat} (h : availB d roots T = false) :
    Lower d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

-- moveBits & lower_iso!
def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_zero (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) : moveBits tag d 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK256 (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) && (moveBits p.1 p.2 mask256 == mask256)

theorem applyMoves_hom (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b, applyMoves ms (a &&& b) = applyMoves ms a &&& applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ||| b) = applyMoves ms a ||| applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ^^^ b) = applyMoves ms a ^^^ applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256 := by
  induction ms with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    obtain ⟨⟨hz, hm⟩, hps⟩ := hok
    obtain ⟨hand, hor, hxor, h0, h256⟩ := ih hps
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves, List.foldl_cons, move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves, List.foldl_cons, hm]; exact h256

theorem move_invol (tag d w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1, ite_true, moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false := by
      have htd := congrArg (fun v : Nat => v.testBit (d + i)) h
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at htd
      have hge : d ≤ d + i := Nat.le_add_right d i
      have hsub : d + i - d = i := Nat.add_sub_cancel_left d i
      simp [hge, hsub, h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_right, Nat.add_sub_cancel_left, h1]
    simp [h2, h3, Nat.add_sub_cancel_left]
  · simp only [h1, ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2, ite_true, moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      simp [h2.2, Nat.add_sub_of_le h2.1]
    · simp [h1, h2, moved tag d i w h]

theorem applyMoves_inj (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms) := by
  induction ms with
  | nil => intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves, List.foldl_cons] at h
    have h1 := ih hok.2 h
    have := congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1, move_invol p.1 p.2 b hok.1.1] at this

theorem applyMoves_runD {d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD d Y s ws) :
    RunD d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  have hneg : ∀ a, applyMoves ms (negD d a) = negD d (applyMoves ms a) := fun a => by
    simp only [negD, hand, hxor, h256, hd]
  have hand' : ∀ a b, applyMoves ms (andD d a b) = andD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [andD, hand, hd]
  have hor' : ∀ a b, applyMoves ms (orD d a b) = orD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [orD, hand, hor, hd]
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @one s a r save hne0 hned hnm _ ih =>
    have e1 : (negD d a :: kept save a r).map (applyMoves ms) =
        negD d (applyMoves ms a) :: kept save (applyMoves ms a) (r.map (applyMoves ms)) := by
      simp [kept_map, hneg]
    rw [e1] at ih
    refine Run.one save ?_ ?_ ?_ ih
    · intro e; rw [← hneg] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← hneg] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← hneg, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)
  | @two s a b r conj ka kb hne0 hned hnm _ ih =>
    have eop : applyMoves ms (if conj then andD d a b else orD d a b) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) := by
      cases conj <;> simp [hand', hor']
    have e1 : ((if conj then andD d a b else orD d a b) :: kept ka a (kept kb b r)).map (applyMoves ms) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two conj ka kb ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach d2 roots2 p bank →
      ∃ bank', NatReach d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail d1 b' (applyMoves ms v)) →
      Avail d2 b w → Avail d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha
      refine ⟨negD d1 (applyMoves ms a) :: b', Or.inl ⟨b', applyMoves ms a, rfl, hrb', ha'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨negD d1 (applyMoves ms a), List.mem_cons_self, by simp only [negD, hand, hxor, h256, hd]⟩
      · exact avail_cons _ _ (hbb v hv)
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha; have hc' := hav hbb hc
      refine ⟨binD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
        Or.inr ⟨b', applyMoves ms a, applyMoves ms c, op, rfl, hrb', ha', hc'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨binD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
          cases op <;> simp only [binD, andD, orD, hand, hor, hd, ite_true, ite_false, Bool.false_eq_true]⟩
      · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower d1 roots1 T1 L) : Lower d2 roots2 T2 L := by
  obtain ⟨hand, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)

-- lower_slice!
def pairOK (d T : Nat) (p : Nat × Nat) : Bool :=
  d.testBit p.1 && d.testBit p.2 && (T.testBit p.1 != T.testBit p.2)

def essOK (d T : Nat) (roots : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  pairOK d T p && roots.all (fun v => (v == a) || (v.testBit p.1 == v.testBit p.2))

theorem countP_ge_sublist (p : Nat → Bool) {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, a ∈ ys) (hall : ∀ a ∈ xs, p a = true) :
    xs.length ≤ ys.countP p := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
    have ham : a ∈ ys := hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a) := List.perm_cons_erase ham
    rw [hperm.countP_eq, List.countP_cons, hall a List.mem_cons_self]
    have ih' := ih hnd' (fun x hx => by
      have hne : x ≠ a := fun e => hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true, List.length_cons]
    omega

theorem lower_slice {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower dSub rootsSub TSub L) :
    Lower d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail dSub next TSub := avail_of_eq (by
    rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht
  have hL : L ≤ q := hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst, a ∈ ws := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok (a', r1, r2) hm
    simp only [Bool.and_eq_true, essOK, pairOK, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    obtain ⟨_, ⟨⟨hr1, hr2⟩, hdiff⟩, hiso⟩ := hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst, isConstB dSub a = true := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt := countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega

-- poolCut (compact 52-bit hint!) + covers + eval6 + bar!
def runChoices (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if ia < pool.length && (op == 2 || ib < pool.length) then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      let w := if op == 2 then negD d a else binD d (op == 1) a b
      runChoices d (pool ++ [w]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach d roots q bank →
      (∀ v ∈ pool, Avail d bank v) →
      runChoices d pool p bits = some result →
      ∃ bank', NatReach d roots (q + p) bank' ∧ ∀ v ∈ result, Avail d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨hia, hopb⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := if op == 2 then negD d a else binD d (op == 1) a b
      have ha : Avail d bank a := hsup a (getD_mem hia)
      have hr1 : NatReach d roots (q + 1) (w :: bank) := by
        by_cases h2 : op = 2
        · simp only [w, h2, beq_self_eq_true, ite_true]
          exact Or.inl ⟨bank, a, rfl, hr, ha⟩
        · have hib : ib < pool.length := hopb.resolve_left h2
          have hb : Avail d bank b := hsup b (getD_mem hib)
          simp only [w, h2, beq_iff_eq, ite_false]
          exact Or.inr ⟨bank, a, b, (op == 1), rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB dSub pool)

theorem checkCutEntry_sound {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry dSub rootsSub LSub s ws hint = true) :
    ¬ RunD d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail dSub rootsSub v := fun v hv => Or.inr ⟨v, hv, rfl⟩
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail dSub bank w := by
      intro w hw
      have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

-- covers, eval6, hw256, hk, bsr, bar, bar_all!
def coversP (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u, v⟩ hm
  have hp := List.all_eq_true.1 hpairs (u, v) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

-- Fast bitmask-decorated covers (150x faster than per-pair testBit!)
def maskP (m : Nat) : Nat := 2 ^ m - 1

def projBit (rs : List Nat) (w : Nat) : Nat :=
  rs.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0

theorem projBit_testBit (rs : List Nat) (w : Nat) (i : Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false := by
  induction rs generalizing i with
  | nil => simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one, decide_false, Bool.false_and, Bool.false_or,
        List.length_cons, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i), decide_true, Bool.true_and, Nat.add_sub_cancel,
        List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false := by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1, Bool.or_false]; exact ih i

theorem projBit_negD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (w : Nat) :
    projBit rs (negD dm w) = projBit rs w ^^^ maskP rs.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_xor, projBit_testBit, maskP, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    simp [hi, negD, hdr, hmr]
  · simp [hi]

theorem projBit_andD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (andD dm a b) = projBit rs a &&& projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_and, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, andD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem projBit_orD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (orD dm a b) = projBit rs a ||| projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_or, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, orD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def coversD (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  if dws.length == s + 1 then
    dws.foldl (fun acc d => acc ||| ((d.2.1 ^^^ mp) &&& d.2.2)) 0 == mp
  else
    dws.foldl (fun acc d => acc ||| (d.2.1 ^^^ d.2.2)) 0 == mp

theorem coversD_eq (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) :
    coversD (maskP pairs.length) s (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP pairs s ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  simp only [List.length_map]
  split
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
        Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
            Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true, r1s, r2s, List.getElem_map]
          exact hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Nat.testBit_two_pow_sub_one, decide_false, Bool.xor_false, Bool.and_false, not_false_eq_true, Bool.false_eq_true]
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s, bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true, r1s, r2s, List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Bool.xor_false, Bool.false_eq_true, not_false_eq_true]

theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x == f a) = false := beq_false_of_ne (fun e => h (hinj e))
      have hx : (x == a) = false := beq_false_of_ne h
      simp [hf, hx, ih]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, andD, Nat.testBit_and, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, orD, Nat.testBit_and, Nat.testBit_or, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih => rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]; omega

def scoreCheck (dm y s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let a := code &&& 255
  let b := (code >>> 8) &&& 255
  let c := (code >>> 16) &&& 255
  let d := (code >>> 24) &&& 255
  let e := (code >>> 32) &&& 255
  let f := (code >>> 40) &&& 255
  dm.testBit a && dm.testBit b && dm.testBit c && dm.testBit d && dm.testBit e && dm.testBit f &&
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)

theorem scoreCheck_no {dm y s ws} (h : RunD dm y s ws) (code : Nat) :
    scoreCheck dm y s ws code = false := by
  unfold scoreCheck
  by_cases hok : dm.testBit (code &&& 255) = true ∧ dm.testBit ((code >>> 8) &&& 255) = true ∧
      dm.testBit ((code >>> 16) &&& 255) = true ∧ dm.testBit ((code >>> 24) &&& 255) = true ∧
      dm.testBit ((code >>> 32) &&& 255) = true ∧ dm.testBit ((code >>> 40) &&& 255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hok
    simp only [ha, hb, hc, hd, he, hf, hl, beq_self_eq_true, Bool.true_and]
    by_contra hbad
    have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht := Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1, ht.1.1.1.1.1.1.2, ht.1.1.1.1.1.2, ht.1.1.1.1.2, ht.1.1.1.2, ht.1.1.2, ht.1.2⟩

def scr (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD dm y s zs) : scr dm y s pool zs = false := by
  unfold scr; rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
  intro x _; rw [scoreCheck_no h x]; simp

def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : negD dm a ≠ 0) (hd : negD dm a ≠ dm) (hnm : negD dm a ∉ (a :: rest))
    (h : RunD dm y s (negD dm a :: kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  have hnc : ws.contains (negD dm a) = false := by
    cases h : ws.contains (negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true => simp [kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then andD dm a b else orD dm a b) = false := by
    cases h : ws.contains (if conj then andD dm a b else orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then andD dm a b else orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then andD dm a b else orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then andD dm a b else orD dm a b) = (if conj then andD dm b a else orD dm b a) := by
      cases conj <;> simp [andD, orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then andD dm b a else orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {dm y t ws} (h : RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD dm y s ys → f ys = true) →
      nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two p h0 hd hnm h f hf

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat :=
  (T >>> (w * i)) &&& (if w == 32 then 4294967295 else if w == 52 then 4503599627370495 else if w == 256 then mask256 else 2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw256 (seed w : Nat) : Nat :=
  let x := (((w &&& 4294967295) ^^^ seed) * 2654435761 +
            (((w >>> 32) &&& 4294967295) ^^^ seed) * 2246822519 +
            (((w >>> 64) &&& 4294967295) ^^^ seed) * 3266489917 +
            (((w >>> 96) &&& 4294967295) ^^^ seed) * 668265263 +
            (((w >>> 128) &&& 4294967295) ^^^ seed) * 374761393 +
            (((w >>> 160) &&& 4294967295) ^^^ seed) * 1274126177 +
            (((w >>> 192) &&& 4294967295) ^^^ seed) * 2869860233 +
            (((w >>> 224) &&& 4294967295) ^^^ seed) * 1640531527) &&& 4294967295
  let y := ((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295
  ((y ^^^ (y >>> 13)) * 3266489917) &&& 4294967295

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  let i := idxH s h
  decide (i < N s) && (htAt s i == h) && zs.isPerm (S s i)

def nextD_decor (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
         let dw := (w, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
         (f (dw :: ra) || (slack ≥ 2 && f (dw :: da :: ra))))) ||
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := if conj then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                      else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hneg : ∀ a, (negD dm a, (dec a).2.1 ^^^ mp, (dec a).2.2 ^^^ mp) = dec (negD dm a))
    (hbin : ∀ (c : Bool) a b,
      (if c then (if c then andD dm a b else orD dm a b, (dec a).2.1 &&& (dec b).2.1, (dec a).2.2 &&& (dec b).2.2)
       else (if c then andD dm a b else orD dm a b, (dec a).2.1 ||| (dec b).2.1, (dec a).2.2 ||| (dec b).2.2)) =
      dec (if c then andD dm a b else orD dm a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor dm mp slack (ws.map dec) g = nextD dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hneg, hbin, List.map_cons]

theorem nextD_decor_eq {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor dm (maskP pairs.length) slack (ws.map dec) g =
      nextD dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro a
    simp only [dec, projBit_negD hd hr1, projBit_negD hd hr2, List.length_map]
  · intro c a b
    cases c <;> simp only [dec, ↓reduceIte, Bool.false_eq_true, projBit_andD hr1, projBit_andD hr2,
      projBit_orD hr1, projBit_orD hr2]

def colB (mp : Nat) (d : Bool) (p : Nat × Nat) : Nat :=
  if d then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def addC (x : Nat) (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (c.1 ||| x, c.2.1 ||| (c.1 &&& x), c.2.2 ||| (c.2.1 &&& x))

def cov3 (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) : Nat × Nat × Nat :=
  dws.foldl (fun c dw => addC (colB mp d dw.2) c) (0, 0, 0)

def takeOne (c : Nat × Nat × Nat) (x : Nat) : Nat := (c.1 ^^^ x) ||| c.2.1
def takeTwo (c : Nat × Nat × Nat) (x y : Nat) : Nat :=
  (c.1 ^^^ (x ||| y)) ||| (c.2.1 &&& (x ^^^ y)) ||| c.2.2

theorem cov3_bit (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) (i : Nat) :
    let k := dws.countP (fun dw => (colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k) := by
  have hgen : ∀ (xs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (k0 : Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k := k0 + xs.countP (fun dw => (colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k) := by
    intro xs
    induction xs with
    | nil => intro c k0 ⟨h1, h2, h3⟩; simp [h1, h2, h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1, h2, h3⟩
      simp only [List.foldl_cons, List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) := by
        simp only [addC, Nat.testBit_or, Nat.testBit_and, h1, h2, h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb, Nat.le_add_left]
      have ih' := ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using ih'
  simpa only [cov3, Nat.zero_testBit, Nat.zero_add] using hgen dws (0, 0, 0) 0 (by simp)

theorem cov3_perm (mp : Nat) (d : Bool) {xs ys : List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys := by
  have heq : ∀ i, (cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i := by
    intro i
    obtain ⟨a1, a2, a3⟩ := cov3_bit mp d xs i
    obtain ⟨b1, b2, b3⟩ := cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i => (heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.2)

theorem takeOne_eq (mp : Nat) (d : Bool) (a : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, _⟩ := cov3_bit mp d (a :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeOne, Nat.testBit_or, Nat.testBit_xor, h1, h2, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, decide_true, Bool.xor_false, Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 1 ≤ k + 3 by omega,
      decide_true, Bool.xor_true, Bool.or_true, Bool.or_false]

theorem takeTwo_eq (mp : Nat) (d : Bool) (a b : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, h3⟩ := cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeTwo, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h1, h2, h3, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega, show 2 ≤ k + 3 + 1 + 1 by omega, show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true, Bool.xor_true, Bool.xor_false, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false])

theorem cov3_coversD (mp s : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    let d := (dw :: rest).length == s + 1
    ((cov3 mp d rest).1 ||| colB mp d dw.2 == mp) = coversD mp s (dw :: rest) := by
  intro d
  have e : ∀ b : Bool, ((cov3 mp b rest).1 ||| colB mp b dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp b x.2) 0 := by
    intro b; apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp b rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp b dw.2).testBit i)) =
        rest.any (fun x => (colB mp b x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  have hf : ∀ b : Bool, (cov3 mp b rest).1 ||| colB mp b dw.2 =
      (dw :: rest).foldl (fun acc x => acc ||| (if b then (x.2.1 ^^^ mp) &&& x.2.2 else x.2.1 ^^^ x.2.2)) 0 := by
    intro b; simpa only [colB] using e b
  unfold coversD
  dsimp only [d]
  cases (dw :: rest).length == s + 1
  · simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg (· == mp) (hf false)
  · simpa only [↓reduceIte] using congrArg (· == mp) (hf true)

def nextD_cov (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let len := dws.length
  let covF := cov3 mp false dws
  let covT := cov3 mp true dws
  let du0 := len == s + 1
  let du1 := len + 1 == s + 1
  let db0 := len - 1 == s + 1
  let db1 := len == s + 1
  let db2 := len + 1 == s + 1
  dws.any fun da =>
    let a := da.1
    (slack ≥ 1 &&
      (let pneg := (da.2.1 ^^^ mp, da.2.2 ^^^ mp)
       let uok0 := (takeOne (if du0 then covT else covF) (colB mp du0 da.2) ||| colB mp du0 pneg) == mp
       let uok1 := slack ≥ 2 && (((if du1 then covT.1 else covF.1) ||| colB mp du1 pneg) == mp)
       (uok0 || uok1) &&
       (let w := negD dm a
        w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
          let dw := (w, pneg)
          let ra := dws.erase da
          ((uok0 && f (dw :: ra)) || (uok1 && f (dw :: da :: ra)))))) ||
    (dws.erase da).any fun db =>
      let b := db.1
      a ≤ b &&
        [false, true].any fun conj =>
          let pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                    else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
          let ok0 := (takeTwo (if db0 then covT else covF) (colB mp db0 da.2) (colB mp db0 db.2) ||| colB mp db0 pz) == mp
          let ok1a := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 db.2) ||| colB mp db1 pz) == mp)
          let ok1b := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 da.2) ||| colB mp db1 pz) == mp)
          let ok2 := slack ≥ 2 && (((if db2 then covT.1 else covF.1) ||| colB mp db2 pz) == mp)
          (ok0 || ok1a || ok1b || ok2) &&
          (let w := if conj then andD dm a b else orD dm a b
           w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
             let dw := (w, pz)
             let r := (dws.erase da).erase db
             ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) || (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r))))

theorem nextD_cov_eq (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov dm mp s slack dws g =
      nextD_decor dm mp slack dws (fun dzs => coversD mp s dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      refine ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra
        rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 :
          (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra)
        rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hu0, hf0⟩ | ⟨⟨hsl2, hu1⟩, hf1⟩
      · left; exact ⟨hcov0 ▸ hu0, hf0⟩
      · right; exact ⟨hsl2, hcov1 ▸ hu1, hf1⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw]
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r
      rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r)
      rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r)
      rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r)
      rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
      · left; left; exact ⟨hcov0' ▸ hu0, hf0⟩
      · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a' ▸ hu1a, hf1a⟩⟩
      · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b' ▸ hu1b, hf1b⟩⟩
      · right; exact ⟨hsl2, hcov2' ▸ hu2, hf2⟩
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra; rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra); rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hc0, hg0⟩ | ⟨hsl2, hc1, hg1⟩
      · have hu0 : ((takeOne _ _ ||| _) == mp) = true := hcov0.symm ▸ hc0
        exact ⟨hsl, Or.inl hu0, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl ⟨hu0, hg0⟩⟩
      · have hu1 : ((_ ||| _) == mp) = true := hcov1.symm ▸ hc1
        exact ⟨hsl, Or.inr ⟨hsl2, hu1⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, hu1⟩, hg1⟩⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw] at hfx
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r; rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r); rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r); rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r); rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
      · have u0 : ((takeTwo _ _ _ ||| _) == mp) = true := hcov0'.symm ▸ hc0
        exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
      · have u1a : ((takeOne _ _ ||| _) == mp) = true := hcov1a'.symm ▸ hc1a
        exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
      · have u1b : ((takeOne _ _ ||| _) == mp) = true := hcov1b'.symm ▸ hc1b
        exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
      · have u2 : ((_ ||| _) == mp) = true := hcov2'.symm ▸ hc2'
        exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem bar_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [bar, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runD {dm Y u} (seed : Nat) (orig : List Nat) (h0 : RunD dm Y u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD dm Y u best →
      RunD dm Y u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

-- Bridge: HasCircuitSize 8 fG s -> Lower mask256 xs256 (enc256 fG) lb -> lb <= s!
def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD mask256 (w.getD i 0) acc) mask256
  | .or  => g.inputs.foldr (fun i acc => orD mask256 (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => mask256 | i :: _ => negD mask256 (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : mask256.testBit r = true := by simp [mask256_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem execN_reach (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), NatReach mask256 roots p bank →
      (∀ v ∈ w, Avail mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ NatReach mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail mask256 bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    -- Use gvN_step directly on roots=roots:
    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [binD, andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [binD, orD]; cases mask256.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · refine ⟨p + 1, negD mask256 (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def xs256 : List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def pt8 (r : Nat) : Fin 8 → Bool := fun i => r.testBit i.val

theorem xs256_bits : ∀ r : Fin 256, xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val) := by
  decide +kernel

theorem lower_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hlow : Lower mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ xs256, Avail mask256 xs256 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates xs256 hfan 0 xs256 xs256 rfl hsup0
  have hout : (execN C.gates xs256).getD C.output 0 &&& mask256 = T &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates xs256 r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r) := hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hav_out : Avail mask256 bank ((execN C.gates xs256).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := hlow p bank hr (avail_of_eq hout hav_out)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def dom_7 : Nat := 0xff
def goal_7 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def roots_7 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xecececece8e8e8e8ecececece8e8e8e8ecececece8e8e8e8ecececece8e8e8e8
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xeaeaeae8eaeaeae8eaeaeae8eaeaeae8eaeaeae8eaeaeae8eaeaeae8eaeaeae8
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xffe8ffe8ffe8ffe8eae8eae8eae8eae8ffe8ffe8ffe8ffe8eae8eae8eae8eae8
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffff88ff88eecceeccaa88aa88ffffffffff88ff88eecceeccaa88aa88
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xffffffffe8e8e8e8ecececece8e8e8e8ffffffffe8e8e8e8ecececece8e8e8e8
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xffffffffe8e8e8e8ffffffffe8e8e8e8ecececece8e8e8e8ecececece8e8e8e8
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffff8888ffffffffffff8888eeeeccccaaaa8888eeeeccccaaaa8888
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xeeeeeeeceaeaeae8eeeeeeeceaeaeae8eeeeeeeceaeaeae8eeeeeeeceaeaeae8
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xffeaffe8ffeaffe8eaeaeae8eaeaeae8ffeaffe8ffeaffe8eaeaeae8eaeaeae8
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xffffffffffe8ffe8eeeceeeceae8eae8ffffffffffe8ffe8eeeceeeceae8eae8
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xffffffffeaeae8e8eeeeececeaeae8e8ffffffffeaeae8e8eeeeececeaeae8e8
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffaaff88eeeeeeccaaaaaa88ffffffffffaaff88eeeeeeccaaaaaa88
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffff88ffffff88ffffaa88ffffaa88ffaaff88ffaaff88aaaaaa88aaaaaa88
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xffffffffe8e8e8e8ffffffffe8e8e8e8ffffffffe8e8e8e8ecececece8e8e8e8
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xffffffffffa0ffa0ffffffffaaa0aaa0ffffffffffa0ffa0aaa0aaa0aaa0aaa0
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffff00ffffffffffffaa00ffffffffffaaff00aaaaaa00aaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xffffeae8ffffeae8ffffeae8ffffeae8eaeaeae8eaeaeae8eaeaeae8eaeaeae8
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xffffffffeae8eae8ffffffffeae8eae8eeeceeeceae8eae8eeeceeeceae8eae8
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffaa88ffffffffffffaa88eeeeeeccaaaaaa88eeeeeeccaaaaaa88
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xffffffa0ffffffa0ffffaaa0ffffaaa0ffaaffa0ffaaffa0aaaaaaa0aaaaaaa0
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffff88ff88ffffffffaa88aa88ffffffffff88ff88eecceeccaa88aa88
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xffffffffffc0ffc0ffffffffc0c0c0c0ffffffffffc0ffc0ccccccccc0c0c0c0
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffff8888ffffffffffff8888ffffffffaaaa8888eeeeccccaaaa8888
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xffffffffffffc0c0ffffffffffffc0c0ffffffffc0c0c0c0ccccccccc0c0c0c0
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffff00ffffffffffff0000ffffffffff00ff00cccccccc00000000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xffffffffffeaffe8eeeeeeeceaeaeae8ffffffffffeaffe8eeeeeeeceaeaeae8
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xffffffe8ffffffe8ffffeae8ffffeae8ffeaffe8ffeaffe8eaeaeae8eaeaeae8
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xffffffffffe8ffe8ffffffffeae8eae8ffffffffffe8ffe8eeeceeeceae8eae8
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffff88ffffffffffffaa88ffffffffffaaff88eeeeeeccaaaaaa88
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xffffffffffffffa0ffffffffffffaaa0ffffffffffaaffa0aaaaaaa0aaaaaaa0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xffffffffffffffc0ffffffffffffc0c0ffffffffffc0ffc0ccccccccc0c0c0c0
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xffffffffffffeae8ffffffffffffeae8eeeeeeeceaeaeae8eeeeeeeceaeaeae8
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xffffffffffffe8e8ffffffffffffe8e8ffffffffeaeae8e8eeeeececeaeae8e8
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xffffffffffffffe8ffffffffffffeae8ffffffffffeaffe8eeeeeeeceaeaeae8
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_7
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (2, 6), (4, 5), (4, 6)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 4]
def r2sG : List Nat := [3, 5, 3, 6, 5, 6]
def mpG : Nat := 0x3f
def pool6G : List Nat := [2203385726211]
def xsM : List Nat := roots_7.map (· &&& dom_7)
def goalM : Nat := goal_7 &&& dom_7
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xd4bda944
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000000000000000000000000000000000000000000000000000cc00000000000000000000000000000000000000000000000000000000000000aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x30000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000003
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3a000000000000000000000000000000000000000000000000000000000000002d0000000000000000000000000000000000000000000000000000000000000017
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 3 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_7 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_7 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_7 == dom_7) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_7 goalM u ys) : RunD dom_7 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_7 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_7 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_7 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_7 roots_7 goal_7 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_7 goal_7 := by
    have h0 : isConstB dom_7 goal_7 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_7

theorem low_7 : Lower dom_7 roots_7 goal_7 4 := S_7.noCircuit

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00, 1, 9)] (by decide +kernel) (by decide +kernel) low_7

def isoMv_23 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_iso isoMv_23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_39 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_39 : Lower dom_39 roots_39 goal_39 5 :=
  lower_iso isoMv_39 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

theorem low_31 : Lower dom_31 roots_31 goal_31 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff00, 1, 9)] (by decide +kernel) (by decide +kernel) low_23

theorem low_47 : Lower dom_47 roots_47 goal_47 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff00, 1, 9)] (by decide +kernel) (by decide +kernel) low_39

namespace S_79
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 6), (4, 5), (4, 6), (8, 9), (8, 72), (10, 11), (10, 14), (10, 74), (12, 13), (12, 14), (12, 76), (64, 72), (65, 67), (65, 69), (65, 73), (66, 67), (66, 70), (66, 74), (68, 69), (68, 70), (68, 76)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 12, 12, 12, 64, 65, 65, 65, 66, 66, 66, 68, 68, 68]
def r2sG : List Nat := [3, 5, 9, 3, 6, 5, 6, 9, 72, 11, 14, 74, 13, 14, 76, 72, 67, 69, 73, 67, 70, 74, 69, 70, 76]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [72848081552643, 71512317494025, 71519963776517, 1142663021827, 71520940983561]
def xsM : List Nat := roots_79.map (· &&& dom_79)
def goalM : Nat := goal_79 &&& dom_79
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x8a462a2888207c9313efc088
  | 6, 0 => 0x8d990af8
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000000000003333000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff00000000000000ff0000000000000000000000000000000000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000cccc000000000000cccc00000000000000000000000000000000000000000000ffff000000000000aaaa00000000000000000000000000000000000000000000aaaa000000000000aaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x118f5635aac6885
  | 6, 0, 0 => 0x46855
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1c7f1e70000000000000000000000000000000000000000000000000000000001f8fff80000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000000001c070600000000000000000000000000000000000000000000000000000000000380e180000000000000000000000000000000000000000000000000000000001ff80070000000000000000000000000000000000000000000000000000000000070007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x146d1a60000000000000000000000000000000000000000000000000000000001b0ed500000000000000000000000000000000000000000000000000000000001ffc900000000000000000000000000000000000000000000000000000000000124ff840000000000000000000000000000000000000000000000000000000001d274720000000000000000000000000000000000000000000000000000000000b92e590000000000000000000000000000000000000000000000000000000001ffdbaf00000000000000000000000000000000000000000000000000000000004f12af
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 8 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 1
  | 5 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x39f9f2c5
  | 5, 0 => 0xa313c3b38d990af85fd304c147f2637a
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x1000000000000100000000000000000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 1 => checkCutEntry dom_15 roots_15 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_79 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_79 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_79 == dom_79) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_79 goalM u ys) : RunD dom_79 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_79 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_79 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_79 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_79 roots_79 goal_79 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_79 goal_79 := by
    have h0 : isConstB dom_79 goal_79 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_79

theorem low_79 : Lower dom_79 roots_79 goal_79 7 := S_79.noCircuit

namespace S_107
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (2, 3), (2, 34), (8, 9), (8, 72), (10, 11), (10, 42), (10, 74), (32, 34), (32, 96), (33, 35), (33, 41), (33, 97), (40, 41), (40, 42), (40, 104), (64, 72), (64, 96), (65, 67), (65, 73), (65, 97), (66, 67), (66, 74), (66, 98)]
def r1sG : List Nat := [1, 1, 2, 2, 8, 8, 10, 10, 10, 32, 32, 33, 33, 33, 40, 40, 40, 64, 64, 65, 65, 65, 66, 66, 66]
def r2sG : List Nat := [3, 9, 3, 34, 9, 72, 11, 42, 74, 34, 96, 35, 41, 97, 41, 42, 104, 72, 96, 67, 73, 97, 67, 74, 98]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [36327506708739, 71511765420360, 36327930200866, 36327945405193, 71610162225760]
def xsM : List Nat := roots_107.map (· &&& dom_107)
def goalM : Nat := goal_107 &&& dom_107
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xd9cde658717669b4
  | 6, 0 => 0xd9cde658
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f0f000000000000000000000000000000000000000000000f0000000f0000000f0000000f000000000000000000000000000000000000000c0c00000c0c00000c0c00000c0c0000000000000000000000000000000000000a0a00000a0a00000a0a00000a0a000000000000000000000000000000000000000000000f0f0000000000000f0f0000000000000000000000000000000000000f0f00000f0f0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x2c682c6885
  | 6, 0, 0 => 0x58d05
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1fe00000000000000000000000000000000000000000000000000000000000001c1f00000000000000000000000000000000000000000000000000000000001c001cc00000000000000000000000000000000000000000000000000000000003838030000000000000000000000000000000000000000000000000000000001fe01ff0000000000000000000000000000000000000000000000000000000001fe0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x125fe88000000000000000000000000000000000000000000000000000000000093d1f20000000000000000000000000000000000000000000000000000000001c88bcd00000000000000000000000000000000000000000000000000000000007878570000000000000000000000000000000000000000000000000000000000da01770000000000000000000000000000000000000000000000000000000001ff2520
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_107 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_107 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_107 == dom_107) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_107 goalM u ys) : RunD dom_107 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_107 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_107 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_107 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_107 roots_107 goal_107 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_107 goal_107 := by
    have h0 : isConstB dom_107 goal_107 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_107

theorem low_107 : Lower dom_107 roots_107 goal_107 7 := S_107.noCircuit

def isoMv_55 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55 : Lower dom_55 roots_55 goal_55 6 :=
  lower_iso isoMv_55 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_103 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_103 : Lower dom_103 roots_103 goal_103 7 :=
  lower_iso isoMv_103 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_79

def isoMv_151 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_151 : Lower dom_151 roots_151 goal_151 7 :=
  lower_iso isoMv_151 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_79

def isoMv_167 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_167 : Lower dom_167 roots_167 goal_167 7 :=
  lower_iso isoMv_167 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_79

def isoMv_179 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_179 : Lower dom_179 roots_179 goal_179 7 :=
  lower_iso isoMv_179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_107

theorem low_63 : Lower dom_63 roots_63 goal_63 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff00ff00ff00, 1, 9)] (by decide +kernel) (by decide +kernel) low_55

theorem low_95 : Lower dom_95 roots_95 goal_95 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff000000000000ffff0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_79

namespace S_111
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 6), (2, 34), (4, 5), (4, 6), (8, 9), (8, 72), (10, 11), (10, 14), (10, 42), (10, 74), (12, 13), (12, 14), (12, 76), (32, 34), (32, 96), (33, 35), (33, 37), (33, 41), (33, 97), (36, 37), (36, 38), (36, 100), (40, 41), (40, 42), (40, 104), (44, 45), (44, 46), (44, 108), (64, 72), (64, 96), (65, 67), (65, 69), (65, 73), (65, 97), (66, 67), (66, 70), (66, 74), (66, 98), (68, 69), (68, 70), (68, 76), (68, 100)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 12, 12, 12, 32, 32, 33, 33, 33, 33, 36, 36, 36, 40, 40, 40, 44, 44, 44, 64, 64, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 68]
def r2sG : List Nat := [3, 5, 9, 3, 6, 34, 5, 6, 9, 72, 11, 14, 42, 74, 13, 14, 76, 34, 96, 35, 37, 41, 97, 37, 38, 100, 41, 42, 104, 45, 46, 108, 72, 96, 67, 69, 73, 97, 67, 70, 74, 98, 69, 70, 76, 100]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := [36327930200866, 36474007848201, 72848081552643, 36473030641157, 36327945405193]
def xsM : List Nat := roots_111.map (· &&& dom_111)
def goalM : Nat := goal_111 &&& dom_111
def NN : Nat → Nat
  | 5 => 1
  | 6 => 6
  | 7 => 6
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x8d4fb1d2
  | 6, 0 => 0xdffc7207d558effcd28dd89cbfe2ffbc625ddfb944fa0ee9
  | 7, 0 => 0xb0028674a54a46d9a3f1d6578d034d1357a7aa6b204bc7c7
  | 8, 0 => 0x8166842f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa0000aaaa0000aaaa0000aaaa000000000000000000000000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000000008888000088880000888800008888000000000000000000000000000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ff000000ff000000ff000000ff00000000000000000000000000000000000000f8f80000f8f80000f8f80000f8f8000000000000000000000000000000000000eeee0000eeee0000eeee0000eeee000000000000000000000000000000000000ffff0000ffff0000000000000000
  | 0, 1 => 0xffff0000ffff0000aaaa0000aaaa00000000000000000000000000000000000033330000333300003333000033330000000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000005555000055550000555500005555000000000000000000000000000000000000ffff0000ffff0000888800008888000000000000000000000000000000000000ff880000ff880000ff880000ff88000000000000000000000000000000000000cccc0000cccc0000cccc0000cccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x432105
  | 6, 0, 0 => 0x436bd064328706c4368b643687a649687064361506
  | 7, 0, 0 => 0x4368b06436187070c436876436875074368e70743687d07
  | 8, 0, 0 => 0x4368706
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 24
  | 6 => 28
  | 7 => 32
  | 8 => 28
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3c0078000700000000000000000000000000000000000000000000000000003c00e381c0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffe000000000000000000000000000000000000000000000000000000000000fc01ff0000000000000000000000000000000000000000000000000000003c00e381c0c0000000000000000000000000000000000000000000000000000003fc00783c3f00000000000000000000000000000000000000000000000000003fff00000000
  | 0, 1 => 0x3fff0078000700000000000000000000000000000000000000000000000000003c3fffffc3c700000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000003fc3ff87fff800000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000000000fc01ff00000000000000000000000000000000000000000000000000000003c000003c38
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x47c24f8454f00000000000000000000000000000000000000000000000000003c88e391c8d2000000000000000000000000000000000000000000000000000000440008040900000000000000000000000000000000000000000000000000002222fffe102000000000000000000000000000000000000000000000000000001111fc21ff0400000000000000000000000000000000000000000000000000003ccce399ccdb00000000000000000000000000000000000000000000000000000ffc6dfafdff00000000000000000000000000000000000000000000000000003fff92452200
  | 0, 1 => 0x3fffb6fd674f0000000000000000000000000000000000000000000000000000343bb6f54346000000000000000000000000000000000000000000000000000000006dbaddff00000000000000000000000000000000000000000000000000003b83db07bab000000000000000000000000000000000000000000000000000003fff924d260900000000000000000000000000000000000000000000000000001155fc29ff0d00000000000000000000000000000000000000000000000000000bc4490abcb9
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 15 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 15 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 15 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 15 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 6 => 9
  | 7 => 21
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0xc03ef3ce8166842f5c8c93235b2ea9d54f1df9b849331d913d226d743bb6c6f51343da00
  | 7, 0 => 0xe50ac2afc224757bacb924e59ce3352698d72b3f825c72ab8166842f7ef30aa0796ac1ab6f70099964cd9134552177dd459ad36636d61ca92e54f1832c92a79027bad6fd1c7fdeee1a971b4c0ff5fcaa0bb7c113
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x200000000000020000000006100000000000210000000000121000000000002102000000001210200000000000010000000000000
  | 7, 0 => 0x200000000000020000000000002000000000000300000000000010000000000003000000000000200000000000000000000000002000000000000000000000000030000000000002000000000000200000000000000000000000001000000000000000000000000000000000000003000000000000200000000000020000000000003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_103 roots_103 7 s ws hint
  | 1 => checkCutEntry dom_47 roots_47 6 s ws hint
  | 2 => checkCutEntry dom_107 roots_107 7 s ws hint
  | 3 => checkCutEntry dom_79 roots_79 7 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_111 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_103 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_107 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_79 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_111 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_111 == dom_111) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_111 goalM u ys) : RunD dom_111 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_111 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 6 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_111 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_111 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_111 roots_111 goal_111 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_111 goal_111 := by
    have h0 : isConstB dom_111 goal_111 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_111

theorem low_111 : Lower dom_111 roots_111 goal_111 9 := S_111.noCircuit

theorem low_119 : Lower dom_119 roots_119 goal_119 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff000000ff000000ff0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_103

theorem low_123 : Lower dom_123 roots_123 goal_123 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f00000f0f00000f0f0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_107

namespace S_219
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (1, 17), (2, 3), (8, 9), (8, 72), (10, 11), (10, 74), (16, 17), (16, 144), (18, 19), (18, 146), (24, 25), (24, 88), (24, 152), (26, 27), (26, 90), (26, 154), (64, 72), (65, 67), (65, 73), (65, 81), (66, 67), (66, 74), (80, 81), (80, 88), (80, 208), (82, 83), (82, 90), (82, 210), (128, 144), (129, 131), (129, 137), (129, 145), (130, 131), (130, 146), (136, 137), (136, 152), (136, 200), (138, 139), (138, 154), (138, 202), (192, 200), (192, 208), (193, 195), (193, 201), (193, 209), (194, 195), (194, 202), (194, 210)]
def r1sG : List Nat := [1, 1, 1, 2, 8, 8, 10, 10, 16, 16, 18, 18, 24, 24, 24, 26, 26, 26, 64, 65, 65, 65, 66, 66, 80, 80, 80, 82, 82, 82, 128, 129, 129, 129, 130, 130, 136, 136, 136, 138, 138, 138, 192, 192, 193, 193, 193, 194, 194, 194]
def r2sG : List Nat := [3, 9, 17, 3, 9, 72, 11, 74, 17, 144, 19, 146, 25, 88, 152, 27, 90, 154, 72, 67, 73, 81, 67, 74, 81, 88, 208, 83, 90, 210, 144, 131, 137, 145, 131, 146, 137, 152, 200, 139, 154, 202, 200, 208, 195, 201, 209, 195, 202, 210]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := [212801709146889, 212561195696913, 212318793765129]
def xsM : List Nat := roots_219.map (· &&& dom_219)
def goalM : Nat := goal_219 &&& dom_219
def NN : Nat → Nat
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0x8e86f0dd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x2c6886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3f03ff00000000000000000000000000000000000000000000000000000003f00003f0f00000000000000000000000000000000000000000000000000003838c38c38cc800000000000000000000000000000000000000000000000000007003803800070000000000000000000000000000000000000000000000000003fc003ffc00000000000000000000000000000000000000000000000000000003ffffc0000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2492a7f23ff04000000000000000000000000000000000000000000000000000127f11297f0f20000000000000000000000000000000000000000000000000003938cb8cb8cc90000000000000000000000000000000000000000000000000000f0978978955f0000000000000000000000000000000000000000000000000003fe403ffd20a00000000000000000000000000000000000000000000000000003ffffe4024a00
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_219 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_219 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_219 == dom_219) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_219 goalM u ys) : RunD dom_219 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_219 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_219 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_219 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_219 roots_219 goal_219 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_219 goal_219 := by
    have h0 : isConstB dom_219 goal_219 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_219

theorem low_219 : Lower dom_219 roots_219 goal_219 7 := S_219.noCircuit

theorem low_231 : Lower dom_231 roots_231 goal_231 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000000000000000000000ff000000ff0000000000000000, 32, 96)] (by decide +kernel) (by decide +kernel) low_167

namespace S_237
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (4, 5), (8, 9), (8, 72), (12, 13), (12, 76), (32, 96), (32, 160), (33, 37), (33, 41), (33, 97), (33, 161), (36, 37), (36, 100), (36, 164), (40, 41), (40, 104), (40, 168), (44, 45), (44, 108), (44, 172), (64, 72), (64, 96), (65, 69), (65, 73), (65, 97), (68, 69), (68, 76), (68, 100), (128, 160), (129, 133), (129, 137), (129, 161), (132, 133), (132, 164), (136, 137), (136, 168), (136, 200), (140, 141), (140, 172), (140, 204), (192, 200), (192, 224), (193, 197), (193, 201), (193, 225), (196, 197), (196, 204), (196, 228)]
def r1sG : List Nat := [1, 1, 4, 8, 8, 12, 12, 32, 32, 33, 33, 33, 33, 36, 36, 36, 40, 40, 40, 44, 44, 44, 64, 64, 65, 65, 65, 68, 68, 68, 128, 129, 129, 129, 132, 132, 136, 136, 136, 140, 140, 140, 192, 192, 193, 193, 193, 196, 196, 196]
def r2sG : List Nat := [5, 9, 5, 9, 72, 13, 76, 96, 160, 37, 41, 97, 161, 37, 100, 164, 41, 104, 168, 45, 108, 172, 72, 96, 69, 73, 97, 69, 76, 100, 160, 133, 137, 161, 133, 164, 137, 168, 200, 141, 172, 204, 200, 224, 197, 201, 225, 197, 204, 228]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := [212398015776009, 212397082036320]
def xsM : List Nat := roots_237.map (· &&& dom_237)
def goalM : Nat := goal_237 &&& dom_237
def NN : Nat → Nat
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xd2e18b09
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000000000003333000000000000333300000000000033330000000000003300000033000000330000003300000033000000330000003300000033000000303000003030000030300000303000003030000030300000303000003030000022220000222200002222000022220000222200002222000022220000222200003333000033330000000000000000000033330000333300000000000000000000333300003333000033330000333300000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x2c6886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3fff80000000000000000000000000000000000000000000000000000003f0003f00780000000000000000000000000000000000000000000000000003838c3838e0640000000000000000000000000000000000000000000000000000700387001e030000000000000000000000000000000000000000000000000003fc003fc000000000000000000000000000000000000000000000000000000003ffffc0000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2492a64bfff80000000000000000000000000000000000000000000000000000127f1127f047a0000000000000000000000000000000000000000000000000003938cb938e2650000000000000000000000000000000000000000000000000000f0978f093e2f0000000000000000000000000000000000000000000000000003fe403fd248d00000000000000000000000000000000000000000000000000003ffffc0249100
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_237 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_237 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_237 == dom_237) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_237 goalM u ys) : RunD dom_237 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_237 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_237 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_237 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_237 roots_237 goal_237 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_237 goal_237 := by
    have h0 : isConstB dom_237 goal_237 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_237

theorem low_237 : Lower dom_237 roots_237 goal_237 7 := S_237.noCircuit

namespace S_249
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (8, 9), (8, 72), (16, 17), (16, 144), (24, 25), (24, 88), (24, 152), (32, 96), (32, 160), (33, 41), (33, 49), (33, 97), (33, 161), (40, 41), (40, 104), (40, 168), (48, 49), (48, 112), (48, 176), (56, 57), (56, 120), (56, 184), (64, 72), (64, 96), (65, 73), (65, 81), (65, 97), (80, 81), (80, 88), (80, 112), (80, 208), (128, 144), (128, 160), (129, 137), (129, 145), (129, 161), (136, 137), (136, 152), (136, 168), (136, 200), (192, 200), (192, 208), (192, 224), (193, 201), (193, 209), (193, 225)]
def r1sG : List Nat := [1, 1, 8, 8, 16, 16, 24, 24, 24, 32, 32, 33, 33, 33, 33, 40, 40, 40, 48, 48, 48, 56, 56, 56, 64, 64, 65, 65, 65, 80, 80, 80, 80, 128, 128, 129, 129, 129, 136, 136, 136, 136, 192, 192, 192, 193, 193, 193]
def r2sG : List Nat := [9, 17, 9, 72, 17, 144, 25, 88, 152, 96, 160, 41, 49, 97, 161, 41, 104, 168, 49, 112, 176, 57, 120, 184, 72, 96, 73, 81, 97, 81, 88, 112, 208, 144, 160, 137, 145, 161, 137, 152, 168, 200, 200, 208, 224, 201, 209, 225]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := [27218554654985, 212446826467728, 212448554535008]
def xsM : List Nat := roots_249.map (· &&& dom_249)
def goalM : Nat := goal_249 &&& dom_249
def NN : Nat → Nat
  | 6 => 3
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0x509643112c13f8e415eaaab4
  | 7, 0 => 0x50964311
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x303030303030303000000000000000003030303030303030202020202020202020202020202020202020202020202020202020202020202030303030000000003030303000000000303030300000000030303030000000003030000030300000303000003030000030300000303000003030000030300000300030003000300030003000300030003000300030003000300030003000300010101010101010101010101010101010101010101010101010101010101010103030303030303030000000000000000030303030303030300000000000000000303030303030303030303030303030300000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x2c7886f63c1ac6886
  | 7, 0, 0 => 0x2c7886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 22
  | 7 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3fe00ffffff0000000000000000000000000000000000000000000000000000e0381c0078030000000000000000000000000000000000000000000000000000000000fffe0000000000000000000000000000000000000000000000000000000001e0fc01f0000000000000000000000000000000000000000000000000000003c000e381cc00000000000000000000000000000000000000000000000000001fc7e3ff87fc0000000000000000000000000000000000000000000000000000fc01ff0000000000000000000000000000000000000000000000000000000000fffe00000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1fe00b6dd770000000000000000000000000000000000000000000000000000e0783c24f8570000000000000000000000000000000000000000000000000000912492fffe0000000000000000000000000000000000000000000000000000004893e8fc11f2000000000000000000000000000000000000000000000000000027c845e389cd00000000000000000000000000000000000000000000000000001f87c3db07a80000000000000000000000000000000000000000000000000000fe01ff4922880000000000000000000000000000000000000000000000000000ffff00924520
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 8 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_249 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_249 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_249 == dom_249) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_249 goalM u ys) : RunD dom_249 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_249 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_249 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_249 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_249 roots_249 goal_249 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_249 goal_249 := by
    have h0 : isConstB dom_249 goal_249 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_249

theorem low_249 : Lower dom_249 roots_249 goal_249 8 := S_249.noCircuit

def isoMv_159 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_159 : Lower dom_159 roots_159 goal_159 8 :=
  lower_iso isoMv_159 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_95

def isoMv_175 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_175 : Lower dom_175 roots_175 goal_175 8 :=
  lower_iso isoMv_175 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_119

def isoMv_187 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_187 : Lower dom_187 roots_187 goal_187 8 :=
  lower_iso isoMv_187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_123

def isoMv_221 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_221 : Lower dom_221 roots_221 goal_221 7 :=
  lower_iso isoMv_221 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_219

def isoMv_235 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem low_235 : Lower dom_235 roots_235 goal_235 8 :=
  lower_iso isoMv_235 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_123

def isoMv_238 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem low_238 : Lower dom_238 roots_238 goal_238 7 :=
  lower_iso isoMv_238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_219

def isoMv_243 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem low_243 : Lower dom_243 roots_243 goal_243 8 :=
  lower_iso isoMv_243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_123

def isoMv_246 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem low_246 : Lower dom_246 roots_246 goal_246 7 :=
  lower_iso isoMv_246 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_219

def isoMv_250 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem low_250 : Lower dom_250 roots_250 goal_250 7 :=
  lower_iso isoMv_250 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_219

theorem low_127 : Lower dom_127 roots_127 goal_127 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff0000ffff0000ffff0000ffff0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_111

namespace S_223
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 6), (4, 5), (4, 6), (8, 9), (8, 72), (10, 11), (10, 14), (10, 74), (12, 13), (12, 14), (12, 76), (16, 17), (16, 144), (18, 19), (18, 22), (18, 146), (20, 21), (20, 22), (20, 148), (24, 25), (24, 88), (24, 152), (26, 27), (26, 30), (26, 90), (26, 154), (28, 29), (28, 30), (28, 92), (28, 156), (64, 72), (65, 67), (65, 69), (65, 73), (65, 81), (66, 67), (66, 70), (66, 74), (68, 69), (68, 70), (68, 76), (80, 81), (80, 88), (80, 208), (82, 83), (82, 86), (82, 90), (82, 210), (84, 85), (84, 86), (84, 92), (84, 212), (128, 144), (129, 131), (129, 133), (129, 137), (129, 145), (130, 131), (130, 134), (130, 146), (132, 133), (132, 134), (132, 148), (136, 137), (136, 152), (136, 200), (138, 139), (138, 142), (138, 154), (138, 202), (140, 141), (140, 142), (140, 156), (140, 204), (192, 200), (192, 208), (193, 195), (193, 197), (193, 201), (193, 209), (194, 195), (194, 198), (194, 202), (194, 210), (196, 197), (196, 198), (196, 204), (196, 212)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 12, 12, 12, 16, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 26, 26, 26, 26, 28, 28, 28, 28, 64, 65, 65, 65, 65, 66, 66, 66, 68, 68, 68, 80, 80, 80, 82, 82, 82, 82, 84, 84, 84, 84, 128, 129, 129, 129, 129, 130, 130, 130, 132, 132, 132, 136, 136, 136, 138, 138, 138, 138, 140, 140, 140, 140, 192, 192, 193, 193, 193, 193, 194, 194, 194, 194, 196, 196, 196, 196]
def r2sG : List Nat := [3, 5, 9, 17, 3, 6, 5, 6, 9, 72, 11, 14, 74, 13, 14, 76, 17, 144, 19, 22, 146, 21, 22, 148, 25, 88, 152, 27, 30, 90, 154, 29, 30, 92, 156, 72, 67, 69, 73, 81, 67, 70, 74, 69, 70, 76, 81, 88, 208, 83, 86, 90, 210, 85, 86, 92, 212, 144, 131, 133, 137, 145, 131, 134, 146, 133, 134, 148, 137, 152, 200, 139, 142, 154, 202, 141, 142, 156, 204, 200, 208, 195, 197, 201, 209, 195, 198, 202, 210, 197, 198, 204, 212]
def mpG : Nat := 0x1fffffffffffffffffffffff
def pool6G : List Nat := [212810332636425, 30901233058566, 212569819186449, 212801709146889, 142432054674691, 212327417254153, 212809355429381]
def xsM : List Nat := roots_223.map (· &&& dom_223)
def goalM : Nat := goal_223 &&& dom_223
def NN : Nat → Nat
  | 7 => 6
  | 8 => 6
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 7, 0 => 0xc6753600a704dbfc985ec8625c19f25e5642a6d30b57bd35
  | 8, 0 => 0xfb41992cb7477579a3a25e36a246353c52e0290d1902419d
  | 9, 0 => 0x159fc3d7
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555555500000000555555550000000055555555000000005555555500000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000ffffffff000000000000000000000000ffffffff0000000000000000
  | 0, 1 => 0xfcfcfcfc00000000fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc00000000fafafafa00000000fafafafa00000000fafafafa00000000fafafafa00000000ffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaa0000000000000000000000000000000000000000555555550000000055555555000000003333333300000000333333330000000033333333000000003333333300000000ffffffff00000000ffffffff0000000000000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x6584c3276587a09765842b07652a10976584370765432107
  | 8, 0, 0 => 0x65842709865e84209806582a09765d842098065843207065847097
  | 9, 0, 0 => 0x65842097
  | _, _, _ => 0
def stateW : Nat → Nat
  | 7 => 32
  | 8 => 36
  | 9 => 32
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1fe1ffffc3ffff0ffffffff000000000000000000000000000000000000000000000000001ffc007ffff0000000000000000000000000000000000000000000000007ff000000007ff00ff00000000000000000000000000000000000000000001e00781c01e0700781c1c3000000000000000000000000000000000000000001ffffffffe0000f00000000f0000000000000000000000000000000000000000001e00003c0000f00000000f000000000000000000000000000000000000000001ff87f1fe1fc7f87f1f1f3f00000000000000000000000000000000000000001fff800001fffff800000000
  | 0, 1 => 0x1fe07f8fc1fe3f07f8fcfcf000000000000000000000000000000000000000001e1e780e3de038f780e0e0cf00000000000000000000000000000000000000001fff80003dfffff80000000f00000000000000000000000000000000000000000000000001ffff0ffffffff000000000000000000000000000000000000000001e1ff87e3fe1f8ff87e3e3cf00000000000000000000000000000000000000001ffffffffe0000000000000000000000000000000000000000000000000000001e00780e01e0380780e0e0c0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1dc1f76d83ddb60f76dadaa000000000000000000000000000000000000000001111222923ffc087ffff000800000000000000000000000000000000000000000888fff01088a44fff00ff04000000000000000000000000000000000000000005e21785c45e1711785c5cb100000000000000000000000000000000000000001fffffffff3349f4cdb7255f0000000000000000000000000000000000000000023e08927c2249f08925255f000000000000000000000000000000000000000001bb86f1761bc5d86f17171d00000000000000000000000000000000000000001fffc44001fffffa22009200
  | 0, 1 => 0x1fe67f8fcdfe3f37f8fcfcf300000000000000000000000000000000000000001e7e799efde67bf799ededff00000000000000000000000000000000000000001fffccd27dfffffaab25b75f00000000000000000000000000000000000000000000000000ccb60b3248daa000000000000000000000000000000000000000001a1de87a3ba1e8ee87a3a34e00000000000000000000000000000000000000001fffffffff1100044492000000000000000000000000000000000000000000001e44790e89e43a2790e8e8e2
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 15 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 15 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 15 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 15 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 6 => 3
  | 7 => 20
  | 8 => 25
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0x915736bf4095019606b71a26
  | 7, 0 => 0xea2cd636dcc372c3d960f4fdbe990cf079fa47095b5d638d49392989490828a74562580a3f6e7e57301507912ba294ad2929f61d1a0a6490159fc3d712b380ea115525b0059096e7049a63a203549c60
  | 8, 0 => 0xe31753adcbf17c04c3f2c155c3b3faaebb368f2ab9e97082b772a8e7b3c80e63a1261f088cbccda48beba96d7697c9436da88b044c5ba33b3c9055bd35bf89ba329f36ec31aea96830cfbbe424b88c68249d95442420a854159fc3d71280f24d022e1921
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x610000000000111000000000002100
  | 7, 0 => 0x15103000000000210300000000000030000000002100000000000210300000000000000000000006100000000001110200000000000010000000015104000000000000200000000000010000000000005000000000000200000000000040000000000002000000000a103000000000210400000000061030000000000000
  | 8, 0 => 0x1000000000000000000000000020000000000000000000000000000000000000030000000000000000000000000400000000000040000000000000000000000000300000000000030000000000004000000000000400000000000050000000000001000000000000300000000000030000000000005000000000000000000000000040000000000004000000000000400000000000030000000000004
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_151 roots_151 7 s ws hint
  | 1 => checkCutEntry dom_221 roots_221 7 s ws hint
  | 2 => checkCutEntry dom_79 roots_79 7 s ws hint
  | 3 => checkCutEntry dom_95 roots_95 8 s ws hint
  | 4 => checkCutEntry dom_159 roots_159 8 s ws hint
  | 5 => checkCutEntry dom_219 roots_219 7 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_223 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_151 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_221 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_79 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_95 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_159 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_219 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_223 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_223 == dom_223) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_223 goalM u ys) : RunD dom_223 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_223 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 6 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 6 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_223 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_223 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_223 roots_223 goal_223 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_223 goal_223 := by
    have h0 : isConstB dom_223 goal_223 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_223

theorem low_223 : Lower dom_223 roots_223 goal_223 10 := S_223.noCircuit

namespace S_239
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 6), (2, 34), (4, 5), (4, 6), (8, 9), (8, 72), (10, 11), (10, 14), (10, 42), (10, 74), (12, 13), (12, 14), (12, 76), (32, 34), (32, 96), (32, 160), (33, 35), (33, 37), (33, 41), (33, 97), (33, 161), (36, 37), (36, 38), (36, 100), (36, 164), (40, 41), (40, 42), (40, 104), (40, 168), (44, 45), (44, 46), (44, 108), (44, 172), (64, 72), (64, 96), (65, 67), (65, 69), (65, 73), (65, 97), (66, 67), (66, 70), (66, 74), (66, 98), (68, 69), (68, 70), (68, 76), (68, 100), (128, 160), (129, 131), (129, 133), (129, 137), (129, 161), (130, 131), (130, 134), (130, 162), (132, 133), (132, 134), (132, 164), (136, 137), (136, 168), (136, 200), (138, 139), (138, 142), (138, 170), (138, 202), (140, 141), (140, 142), (140, 172), (140, 204), (192, 200), (192, 224), (193, 195), (193, 197), (193, 201), (193, 225), (194, 195), (194, 198), (194, 202), (194, 226), (196, 197), (196, 198), (196, 204), (196, 228)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 12, 12, 12, 32, 32, 32, 33, 33, 33, 33, 33, 36, 36, 36, 36, 40, 40, 40, 40, 44, 44, 44, 44, 64, 64, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 68, 128, 129, 129, 129, 129, 130, 130, 130, 132, 132, 132, 136, 136, 136, 138, 138, 138, 138, 140, 140, 140, 140, 192, 192, 193, 193, 193, 193, 194, 194, 194, 194, 196, 196, 196, 196]
def r2sG : List Nat := [3, 5, 9, 3, 6, 34, 5, 6, 9, 72, 11, 14, 42, 74, 13, 14, 76, 34, 96, 160, 35, 37, 41, 97, 161, 37, 38, 100, 164, 41, 42, 104, 168, 45, 46, 108, 172, 72, 96, 67, 69, 73, 97, 67, 70, 74, 98, 69, 70, 76, 100, 160, 131, 133, 137, 161, 131, 134, 162, 133, 134, 164, 137, 168, 200, 139, 142, 170, 202, 141, 142, 172, 204, 200, 224, 195, 197, 201, 225, 195, 198, 202, 226, 197, 198, 204, 228]
def mpG : Nat := 0x7fffffffffffffffffffff
def pool6G : List Nat := [212398015776009, 151923942491682, 216100222862086, 215695616919648, 36330101310217, 36475186348805, 214137473205507, 212395282663752, 216336462906117, 36879833498402, 36475186546181, 36327571981571, 142430446100995, 11187341591302, 151922137170694, 213497472680710, 212397042704992, 212799188763907, 36476163753225, 212398016038153, 44812653429513, 212800807175683, 36879837692706, 212799190075651]
def xsM : List Nat := roots_239.map (· &&& dom_239)
def goalM : Nat := goal_239 &&& dom_239
def NN : Nat → Nat
  | 6 => 15
  | 7 => 131
  | 8 => 205
  | 9 => 25
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xd9b7456cc405af58c131507abc17f3e1b85b27e7b072072ba37659d89e9e1f839e9802cc7ffe0b3c7ef8a9da72df548b58c270531795619216892923
  | 7, 0 => 0x622bcd2c62011eee6126ac4760abd7ec608a7ef25b4a8e825b22893c56e65ca6562107875501507b4c60840c4b63f8cd4b599ea24b3bd53548119a2d47ff80f845ada6e7454e262344b1f8ce40e50949401c826c3e6ce7793d959dfa3d47d8393c2545df3c1a70493abf49ad3a08b59d396c884837b8da5734bfad7d332ccc1e30d636e130a5e7ac2dc200d72b2ac2ce2afa323727cff72f278244ad2678e78d2611e487250c832524fb603b2463014824406d8220a2212b1eaa538f1e7b1ebe1e2b447b1c3007421c256fbe1b805db319c7129f16a2f10a0fd5d6420e1c8b2e0d805dd90d7733f70b3a1e5009951ef70740a1af01ccac8601307f3101014a60
  | 7, 1 => 0xfdea9786fc79bd79fbdd9024faf10833f7f50af4f17e75afecb777eeec1b4a99ea86b481e4c4880de18b0988e15bd4b7e070c328dda8f488dc381a7bd00a273bcc76fa6ecc75d4f0c0cb4d7fc02f202abb259b30b601e0f4b32f51b7aeb97c5bacdc758fab671dbba969d671a9365a4ea63f9b69a1a1b2f3a08e1f1b9e8e42979db9981a9a9513f89836b6d998033ab694d3a46f94c8c75191dbd552913fa7fd8ded495d8c8c2f688bf002138bbc85f08b257abd87ed6ebd85f48ecf85b045e98395a7b9832961777f7af34c7e0453507a5370fa77eb2048774ef2f373c408e16e47d3b46e03d77e6daba65f6c4a8c6a6c171047693a0d1c671f2b2863b92de6
  | 7, 2 => 0xff72148dfef022f1fed6499e
  | 8, 0 => 0x45f91c1a4467437244594c96433929e242aaddfd42195fc541f0068f41ee9f9240d44d943ece78d73c701bb83bf9ac133a6e461439d218bf38e0243338aec525365e5ee235cf856934107b35334fc67f326d52183177be65316ef7273131acfb30da7a9830c59447302966f22e7114a229e9aac8277d45ac2762c6562624c52525cd36f42546e1ef2531099f245322682437cb1e236612972289134f2255f0ec223195a221cc3df6209535de1f0264241e8cd5d91a2ca31615563d0e150141d414eaae6d14802ebf123d3c5d113bbfba10fe760a1083f149054dbd9f04b7c144043412a10404ddd002f149f8025c0a6501d9c1a1012f6eed0051fda10005e05e
  | 8, 1 => 0x8ef395838e7fc54f8d41dd0a8b31b2fe8a42f2a288913c4a87f50ef5876fae0285de96dd84aa280783fb383083915b1d81e2596781dd4ab17e93321f7d66189a7cfbf6037c8fa5477a52866378d9198d774aa65774ab77457318afa971a4601770cda00170af39cf6f1d7ba56bfe66746a9d7cf96a4cd16a6954faae6900efd46864c27f684f994c67fb87706570cb126504b25e64688509638e12626381efd5628e2add6139747b5fff1a8e5e77a0895cdf0cbc5a5d3f11593d1c5d57a530ae5768b696574bed1d56c5bc7c5369701b52494d6751dbec1b4eb2b7a04da33b504bfca47d4a7900484a0c2c8e48bcd7ec48b1139a47bee8aa47b58c3e4618cd85
  | 8, 2 => 0xf33e2795ef1ede09e90d2133e6bf3d86e4d337a5e4a5a98ce4508366e42e0410e3e06f4ce3745698e2d82943df555a6fd614d4e8d222842ed2123dfad1cfa89dd1893db9d14c75dfcf48c42bcd8d0043c72ef110c625212cc48ef809c39e3cbac332b39ac069ed58bf932d42bedc1214be992dcbba1b400ab44ea506b3e15929b32d61c6b0d32d84ae752cf4adce83d6ace0b8dcac5a2067a7bcc700a7b15100a71523aba5ece9e6a5e37e2ea56ee353a41d3e41a223fc659dccadab9d92ff709d3d99019cfc7a139cddc8bf9ca16bac994de22c96dcc6619697e7739689a768963330f494c47ab594433b6d943bc3bb915cf58190f0dccd9054af788fa39a33
  | 8, 3 => 0xfee12394fe3e0b77fd7efbecfbb369a5fb6b9a3dfb03af12fa31f68bf9792ab2f83cf065f4a90b6ff48d74e6f3f6698ff34de82f
  | 9, 0 => 0xf036095ce5dbbcb3c88c8747c605a2d5aa18b71ba48b62809fa4ff1c935842e88d4686128af8a2658819d42b87adbb7787118e227a4e39c76b6855ef676c1879511a1dbb4a264ec54135def23cd5ac2f3b162b40332cfa6228349d0f1752148807bb54b4
  | 10, 0 => 0x8a152192
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xe8e80000e8e80000e8e80000e8e80000e8e80000e8e80000e8e80000e8e80000ffff0000ffff0000ffff0000ffff000000000000000000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000ffff000000000000ffff000000000000ffff000000000000cccc000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00003333000033330000333300003333000033330000333300003333000033330000ffff0000ffff00000000000000000000ffff0000ffff0000000000000000
  | 0, 1 => 0x111100001111000011110000111100001111000011110000111100001111000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000f0f00000ffff0000f0f00000cccc0000c0c00000cccc0000c0c00000f8f80000f8f80000f8f80000f8f80000f8f80000f8f80000f8f80000f8f80000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee
  | 0, 2 => 0xffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000cccc00008888000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00009999000099990000999900009999000099990000999900009999000099990000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaa0000cccc000088880000cccc00008888
  | 0, 3 => 0xffff0000ffff00008888000088880000ffff0000ffff00008888000088880000ffff0000ffff0000aaaa0000aaaa0000ffff0000ffff00008888000088880000000000000000000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc0000000000000000000000000000000000007777000077770000777700007777000000000000000000000000000000000000333300003333000033330000333300000707000007070000070700000707000007070000070700000707000007070000555500005555000055550000555500005555000055550000555500005555
  | 0, 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc0000ffff0000ffff0000ffff0000ffff00000000000055550000000000005555000000000000777700000000000077770000000000007777000000000000777700008888000088880000888800008888000088880000888800008888000088880000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff0000ffff0000000000000f0f0000000000000f0f0000ffff0000f0f00000ffff0000f0f00000ffff0000f0f00000ffff0000f0f00000333300003333000033330000333300003333000033330000000000000000
  | 0, 5 => 0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc0000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000ffff000088880000888800008888000088880000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ff000000ff000000ff550000ff550000ff000000ff000000ff550000ff550000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000088880000888800000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e
  | 0, 6 => 0x77000000770000007700000077000000770000007700000077000000770000000000000000000000000000000000000000000000000000333300003333000000000000333300000000000033330000000000003333000000000000333300000000000000000000555500005555000000000000000000005555000055550000ffff0000ffff0000ffff0000ffff000044440000444400004444000044440000ffff0000ffff00000000000000000000ffff0000ffff00003333000033330000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000ffff000088880000ffff000088880000ffff000088880000ffff00008888
  | 0, 7 => 0xffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ff880000ff880000ff880000ff880000ff880000ff880000ff880000ff880000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000ffff0000ffff0000ffff0000ffff000000000000333300000000000033330000ffff0000ffff0000ffff0000ffff0000eeee0000eeee0000eeee0000eeee0000aaaa0000aaaa0000aaaa0000aaaa000088880000888800008888000088880000f1f10000f1f10000f1f10000f1f10000f1f10000f1f10000f1f10000f1f1
  | 0, 8 => 0xffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa00000303000003030000030300000303000003030000030300000303000003030000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f00000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000ffff0000cccc0000ffff0000ffff0000ffff0000ffff0000fcfc0000fcfc0000fcfc0000fcfc0000ffff0000fcfc0000ffff0000fcfc0000ffff0000fcfc0000ffff0000fcfc0000ffff0000ffff0000fafa0000fafa0000ffff0000ffff0000fafa0000fafa0000000000000000000077770000777700000000000000000000777700007777
  | 0, 9 => 0xffff0000ffcc0000ffff0000ffcc0000ffff0000ffcc0000ffff0000ffcc0000ffff0000ffff0000fcfc0000fcfc0000ffff0000ffff0000fcfc0000fcfc0000fff00000fff00000fff00000fff00000fff00000fff00000fff00000fff00000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa00002222000022220000222200002222000022220000222200002222000022220000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000ffff0000ffff0000f0f00000f0f00000ffff0000ffff0000f0f00000f0f00000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa
  | 0, 10 => 0xf0f00000f0f000000000000000000000f0f00000f0f000044440000444400004444000044440000444400004444000044440000444400000505000005050000050500000505000005050000050500000505000005050000fffa0000fffa0000fffa0000fffa0000fffa0000fffa0000fffa0000fffa00000000000000000000333300003333000000000000000000003333000033330000fffc0000fffc0000fffc0000fffc0000fffc0000fffc0000fffc0000fffc0000ffff0000fff00000ffff0000fff00000ffff0000fff00000ffff0000fff00000ffff0000ffff0000ffff0000ffff0000ffcc0000ffcc0000ffcc0000ffcc
  | 0, 11 => 0xffff0000eeee0000ffff0000eeee0000ffff0000eeee0000ffff0000eeee0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000ffff0000ffff0000eeee0000eeee0000ffff0000ffff0000eeee0000eeee0000ffff0000fafa0000ffff0000fafa0000ffff0000fafa0000ffff0000fafa0000ffff0000ffff0000ffff0000cccc0000ffff0000ffff0000ffff0000cccc0000ffff0000ffff0000ffff0000f0f00000ffff0000ffff0000ffff0000f0f000000033000000330000003300000033000000330000003300000033000000330000005500000055000000550000005500000055000000550000005500000055
  | 0, 12 => 0xfefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000000000005555000000000000555500000000000055550000000000005555
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x485106400660a1098330018485084cb826122c416001982930608a806121421400198284260c9026222428b1019868508401006121458f0019828b103800661a1420c040184851620500612144070019828406080806
  | 7, 0, 0 => 0x14213047c7067002428b0820006700149822a3850070074485084cc007001421c266070070024284384c11e700744852608a8070014e13045470070044284384c10e700242842660d00700242842608d8070024218025800670014213240870a700242930468a8070044485084c11a70044485164c1067
  | 7, 0, 1 => 0x2428426093007008c485084cc0a70044485384c11570024284264010070010e130458700700142133038500700242932408a8a70014213049400670024284483c0067001420848380067008c4852608a8a700242842609100700846850870100700242840404020700242130468b007002459304580067
  | 7, 0, 2 => 0xb8485084c10a7002428848540067004448508212067001421304b4700700242844e4c90270024293047ca867008c485089c982758ac284104c0068002550426080067002429304640067002428426094807002429c2660a807004448508709987002429304a0006700142272608700700242842648c0a7
  | 7, 0, 3 => 0x2420848580067004429304547067002429304b4a80700242844e4cc0070044485084c12d70024213047cb067002428426619807002421c2660b00700242842609900700242a72608a80700242886290006700c02842608500700344850808d0070024e130454b007002429330545007001422f260c1007
  | 7, 0, 4 => 0x344850870c007008c485080808a7004c1152c380067002421304b4b00700142020238500700344853808a80700446890a10e027002421304dc006700149982a380067007448508080807004428426607067001421c0404700700158930438006700242842609b00700242843809a80700242842609a0a7
  | 7, 0, 5 => 0x242842609d80700242820254500700242843860080700242b1266000670024284744dc80700344843808b00700c0293045400670045805084c106700444852660a867002429c0404a8070044485087010170044485624c106700109982c38006700355850870100700242b8260800670024284240808a7
  | 7, 0, 6 => 0x42ac2842608500800142180238006700141012a380067004428404047067002428b260850070025f042608500700242844e08080700c0213045800670014227260c100700249982a580067002421c0404b00700258930458006700242843004500700004851620006600242bd782000670034485089c1007
  | 7, 0, 7 => 0x241012a5800670025f130454006700444be084c10670074485084c902700242842608f8a70024284260949f700242980254006700444850860086700242b1040400670024284260a006700142130468700700145930438006700444850404a86700101012c38006700f8213043800675625f8508200068
  | 7, 0, 8 => 0x242842630100700ac485084c90a7002428410905007
  | 8, 0, 0 => 0x242af2608a800d0015890a10e13040200003a24284260803801216184384c10080084485084cc000d00000508709821c01c0090a11d1c260804002284485084c10680000485084c11a00e000090a2c9820019c0090af5e1304003400121421304d000680108485084c1000d0004858210982001a000012101012c003380121422f26481068
  | 8, 0, 1 => 0x344852608a800d000485089ce13040200111a242842608340012142120404006800242bd08201000d0004857a10e130402002b12142130428040012162842608500800844842608b000d0011890a10101001a00090a11793300034008824284384c10080000284260870a00e00284260808e001a0021561421304003400121421304d40068
  | 8, 0, 2 => 0x242bc0870982010006ab0a10982001a00090a1041c260804001214227260850085625f85084c1000d2006890a10998001a00090af4213042804001216484384c10080024284272010a010000090a709822a01c0002224284384c13807e14213043800680000485084c90214e02385084c10e001a0000462428426085380121421305180068
  | 8, 0, 3 => 0x242ce084c1000d00048578109821402002c12142133000340058266842608006800344842608b000d00048508209821402004c1214213040034001214202032c00680000485084c11f0ce000090a4c1151401c000121421c266003ac12142082608006900242930404a800d0008890a10982021a00090a1098294003400582429304540068
  | 8, 0, 4 => 0x485089c98200e004842608096001a00090a1098230280400131c2842660006800266c7084c1000d0004d00a10e13040200097e149822a003400002421c2608b007002668508080800d0000090a109981401c04f121421304003400121421c2608c00800b1585084c1000d0004c70a4c115001a0000121420848003380121421330040068
  | 8, 0, 5 => 0x455890a109820d000284104c10e001a00301214213040034000b2421304380068000029304547000ce000110a109821c19c000121421304b403804224284040400680144485084c1000d000485084c1241402002b1214208260034001a242845e0800680025f05084c1000d0004bf0a10998001a00099afc213040034000af421304380068
  | 8, 0, 6 => 0x1421304607000d0004d40a10982001a00001a242843808038013342bc2608006800444857a109820d0015890a10998001a00090a1178202003400121421c2648100800242c9084c9020d000005084cc0e0019c023121421c260804001214213054c00680015e0426087000d0004d20a10982001a00090a109821e003400562429304540068
  | 8, 0, 7 => 0x485087010100e00485084cc56001a00090a10982aa00340042242c926080068004448578109820d000485104c115001a00111214208260834000a109824838006800ac4842608b000d00001112149822a19c00d1214202020034001215e8426600068000021304587000ce004857810413001a00090a2c2130400340042242bd26080068
  | 8, 0, 8 => 0x242930460a800d0000090a101011401c0090a10e1304e4040022242842608c06800266850870982010016090a10101001a00090a109823e0034001215e04266000680024284260ab800d0004bd084c116001a000060142130400338012142082660006800242c9084cc000d0000090a4cc150019c000222428426603380121443126080068
  | 8, 0, 9 => 0x25fc7084c1000d0010890a10e130402005a1214213040034000024213305800670025f8508080800d000485084c159001a000978109822c0034001214982485400680044485084c1240d0004c70a10101001a0005084c9021c00340012104130458006800b04bf084c1000d0000092608a960019c0090a10982b0003400562428426480068
  | 8, 0, 10 => 0x5626685084c1000d2006890a10e13040200231214213300034009a142130438006800ac48508080800d0004852648115001a0009084c1242c003400462429304540068000028404047000ce0048508bce13040200090b2422f260834004224284260850080024284ba4c1000d0004842608c16001a005c121421304003400b62428426080068
  | 8, 0, 11 => 0x263850870982010000090a10c010019c0090af0202020034001214208040400680024284260af000d000485089d7930402002e1214213040034005824284384c100800242c908080800d0000090a080950019c0002224284040433801a242842608500800242bd08080800d00108d0a10982001a00090a10e1304680400121421324600068
  | 8, 0, 12 => 0x25f042608006700242e2084c1000d0011890a11793041a0009c214213040034001214202300400680025f8508201000d0004bf0a10e13040200099a1421330003400121421305800068001422f26087000d002f890a10982001a00090a1098202280400422668526080068
  | 9, 0, 0 => 0x1214208260800681216484260800680024293045400670044485084c10671215e842608006856242842608006800142130438006712fc28426080068131c284260800680024284260850071214213040400685824284260800680024284384c10071a2428426080068121422f26080068422428426080068
  | 9, 0, 1 => 0x1334284260800680024284040400671214213240800684624284260800681214213049000680024213045800671214213046000680024284266000671215e0426080068
  | 10, 0, 0 => 0x2428426080067
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 46
  | 7 => 60
  | 8 => 67
  | 9 => 60
  | 10 => 53
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 7 0) :: stateWires n (ids >>> 7)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7ffffffff80000000000000000000000000000000000000000000000000000000001ffc000001fe001ff000000000000000000000000000000000000000000007801e03807801e1e01c0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000780000f0078001f00007000000000000000000000000000000000000000000787fe1f8ff87ffffffc3c70000000000000000000000000000000000000000007ffe000007ffe000000000
  | 0, 1 => 0x7807e1f80f807ffe0fc3c00000000000000000000000000000000000000000007fffffffffffe00001ffff00000000000000000000000000000000000000000007801e0700781ffffe3c380000000000000000000000000000000000000000007801e038000000000000000000000000000000000000000000000000000000007801e03807801e1e01c0c00000000000000000000000000000000000000000007fffffffffffe0000000000000000000000000000000000000000000000000000000000000001ffffe000000000000000000000000000000000000000000000007f81e07f07f8001f03c3f
  | 0, 2 => 0x7ffe0000f7ffe0000000000000000000000000000000000000000000000000007ffe003fffffe01ffe00ff00000000000000000000000000000000000000000007fe1fc7f87fe1e1fe3f3f0000000000000000000000000000000000000000007807e1f80f807ffe0fc3c000000000000000000000000000000000000000000007801e0700780000003c380000000000000000000000000000000000000000007ffe0000f7ffe001f000070000000000000000000000000000000000000000000001fffff8001fffffffff00000000000000000000000000000000000000000000780000f0000000000000
  | 0, 3 => 0x7ffe000007ffe0000000000000000000000000000000000000000000000000007ffe0000f7ffe0000000000000000000000000000000000000000000000000000000000000001fffffffff0000000000000000000000000000000000000000007ffffffff8780000003c380000000000000000000000000000000000000000000000000007ffffffffffff000000000000000000000000000000000000000000000000000787ffffffc3c700000000000000000000000000000000000000000007fe1fc7f87fe1e1fe3f3f0000000000000000000000000000000000000000007f87ffff0ff87ffe0ffff8
  | 0, 4 => 0x7fffffffffffe000003c380000000000000000000000000000000000000000007ffffffffff8600001fff80000000000000000000000000000000000000000007fffffffffffe00001ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007ffe000007fffffffe00000000000000000000000000000000000000000000007ffffffff87fe000003f3f0000000000000000000000000000000000000000007801e03807801fffffc0c0000000000000000000000000000000000000000000787fe1f8ff87e000000000
  | 0, 5 => 0x7ffe1e0707ffe000003c380000000000000000000000000000000000000000007ffe0000f7fffffffe00070000000000000000000000000000000000000000007ffffffff80000000000000000000000000000000000000000000000000000000001ffc000001fffffff0000000000000000000000000000000000000000000000780000f0079ffffe00070000000000000000000000000000000000000000000001ffff08001ffe0ffff80000000000000000000000000000000000000000007fffffffffffe00000000000000000000000000000000000000000000000000007f81e07f07f8001f03c3f
  | 0, 6 => 0x7ffe003fffffe01ffe00ff0000000000000000000000000000000000000000000000000000001fffffc3c7000000000000000000000000000000000000000000787fe1f8ff87e00001c3c70000000000000000000000000000000000000000000001ffff08001ffe0ffff80000000000000000000000000000000000000000007ffffffff8780000003c380000000000000000000000000000000000000000007ffe000007ffffffffc3c700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffe0000
  | 0, 7 => 0x781ffc700781fe001ff380000000000000000000000000000000000000000000001ffc000001fe001ff000000000000000000000000000000000000000000007f81fe3f07f81e1e01fcf80000000000000000000000000000000000000000007879e038f7879e1ff1c0c70000000000000000000000000000000000000000007fffffffff87e00001c3c70000000000000000000000000000000000000000007ffffffff87f8001f03c3f00000000000000000000000000000000000000000000780000f00000000000000000000000000000000000000000000000000000007807e1f80f807ffe0fc3c0
  | 0, 8 => 0x79ffc0f0079fe1f1ff07000000000000000000000000000000000000000000007e01c0f807e1e1fe03070000000000000000000000000000000000000000007ffffffffffffe1e01c0c00000000000000000000000000000000000000000007ffffffff8781ffffe3c380000000000000000000000000000000000000000007ffffffffff81e1e01fcf80000000000000000000000000000000000000000007f81fe3f07f81ffffffcf80000000000000000000000000000000000000000007fffe038f7fffe1ff1c0c70000000000000000000000000000000000000000000001fffff8001fffffffff
  | 0, 9 => 0x781ffc700781fffffff380000000000000000000000000000000000000000007ffffe3f07fffe1e01fcf80000000000000000000000000000000000000000007801fff807801ffe01ffc00000000000000000000000000000000000000000000079ffc0f0079fffffff0700000000000000000000000000000000000000000000780000f0078001f0000700000000000000000000000000000000000000000007fe0007f87fe001fe003f0000000000000000000000000000000000000000007fffe03807fffe1e01c0c00000000000000000000000000000000000000000007fffffffffffe001f00007
  | 0, 10 => 0x1fc7f80001e1fe3f3f00000000000000000000000000000000000000000007801e0700780000003c3800000000000000000000000000000000000000000007861fc7087861e00e3f380000000000000000000000000000000000000000007879fff8f7879ffff1ffc70000000000000000000000000000000000000000000001e1f8f8001fffffc3c70000000000000000000000000000000000000000007f81ffff07f81ffe01fff80000000000000000000000000000000000000000007801fff807801fffffffc00000000000000000000000000000000000000000007ffffffff8781fe001ff38
  | 0, 11 => 0x7f81e07f07f9ffffe3c3f00000000000000000000000000000000000000000007fe1fc7f87fe000003f3f0000000000000000000000000000000000000000007ffe1e07f7ffe001f03c3f0000000000000000000000000000000000000000007879e038f7879fffffc0c70000000000000000000000000000000000000000007ffe1e0707fffffffe3c380000000000000000000000000000000000000000007fffe03807ffffffffc0c0000000000000000000000000000000000000000000787e0038ff87e01ffe00c70000000000000000000000000000000000000000007f86003f0ff8601e0e00f8
  | 0, 12 => 0x7ff9fe3ff7ff9e1ff1fcff00000000000000000000000000000000000000000007f9ffc7f07f9fe1f1ff3f0000000000000000000000000000000000000000007f87ffff0ff8600001fff8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1998661b3199860630ccdb0000000000000000000000000000000000000000007ffffffff80011110800000000000000000000000000000000000000000000002223ffc042223fe041ff040000000000000000000000000000000000000000007911e43a27911e1e21c8d2000000000000000000000000000000000000000000444488a48c445ddd9e102000000000000000000000000000000000000000000008f82249f08f8223f0454f0000000000000000000000000000000000000000006877a1e8ee877bbbed43460000000000000000000000000000000000000000007fff110007ffe888852200
  | 0, 1 => 0x600781a00e0079980d02000000000000000000000000000000000000000000003bbb775b73bba00001efdf00000000000000000000000000000000000000000057ccdeb79d7cdffffebcb90000000000000000000000000000000000000000007d55ecbea95015551a98b00000000000000000000000000000000000000000007999e63b37999e1e31ccdb0000000000000000000000000000000000000000007ffffffffffff9998d2200000000000000000000000000000000000000000000444488a48c445ffffe10200000000000000000000000000000000000000000001ff87e5ff1ff8667f2fdff
  | 0, 2 => 0x7fffbbedfffffddd9f36290000000000000000000000000000000000000000005ddc003fbdddc01fbe00fb00000000000000000000000000000000000000000006ee1bc5d86ee1e1de372d000000000000000000000000000000000000000000608f83a11e08f9981d060900000000000000000000000000000000000000000017885e171178844412bcb90000000000000000000000000000000000000000007fff3349f7ffeaabf5674f0000000000000000000000000000000000000000000000eefff80017777addff0000000000000000000000000000000000000000004cfcaaedf84895551a1429
  | 0, 3 => 0x7fff130117ffe8889526090000000000000000000000000000000000000000007fff3349f7ffe889952609000000000000000000000000000000000000000000000000000000066672ddff0000000000000000000000000000000000000000007ffffffff97895551abcb90000000000000000000000000000000000000000000000000007f76eeee7fbf60000000000000000000000000000000000000000000000000006876aaae54346000000000000000000000000000000000000000000066619c4c86661e1ce33240000000000000000000000000000000000000000007707ddb60f707ddc0fbab0
  | 0, 4 => 0x7ffffffffffffddd9fbeb90000000000000000000000000000000000000000007ffffffffb30311109aa900000000000000000000000000000000000000000003b33755a63b3200001ebd600000000000000000000000000000000000000000000880201100880001004090000000000000000000000000000000000000000007fff99a48fffffffff32200000000000000000000000000000000000000000007ffffffff82ab11108270d0000000000000000000000000000000000000000007d55ecbeafd55fffffd8f20000000000000000000000000000000000000000006877a1e8ee8779998d0200
  | 0, 5 => 0x7fff5f1717ffeccc97beb90000000000000000000000000000000000000000007fffbbedffffffffff776f0000000000000000000000000000000000000000007ffffffff80891111804090000000000000000000000000000000000000000006667ffe4ce667fffffff240000000000000000000000000000000000000000004cfcaaedfccfdffffe556f0000000000000000000000000000000000000000002223fff64a223ff44bffb40000000000000000000000000000000000000000007ffffffffffff9999d260900000000000000000000000000000000000000000006e81a45d06e8061d2352d
  | 0, 6 => 0x5d54003eadd5401fae00f2000000000000000000000000000000000000000000000000000000022260414600000000000000000000000000000000000000000028332148628320000143460000000000000000000000000000000000000000000000ccb6080015540a98b00000000000000000000000000000000000000000007ffffffff97015550ab8b00000000000000000000000000000000000000000007fff110007ffeaaae563460000000000000000000000000000000000000000001910641a2191060620c8d200000000000000000000000000000000000000000044cc8aa59c4cdffffe1429
  | 0, 7 => 0x37abffd7537abfe453ffbd00000000000000000000000000000000000000000022abffc1522abfe051ff0d0000000000000000000000000000000000000000007f99fe3f37f99e5e33fcfb00000000000000000000000000000000000000000079f9e67bf79f9e3ff1cddf0000000000000000000000000000000000000000007ffffffffa8331110943460000000000000000000000000000000000000000007ffffffff9ff9777fafdff00000000000000000000000000000000000000000008f82249f00880011004090000000000000000000000000000000000000000007917e5ba2f917f9e2dcad2
  | 0, 8 => 0x2afbffc9f2afbfe3f1ff4f000000000000000000000000000000000000000000006601c0c80661a1cc03040000000000000000000000000000000000000000007fffffffffffff9fadead20000000000000000000000000000000000000000007ffffffffd7cdffffebcb90000000000000000000000000000000000000000007ffffffffff99f5f3bfcfb0000000000000000000000000000000000000000007fddfebfbffddffffffcfb0000000000000000000000000000000000000000007ffff77bf7fffebff5efdf0000000000000000000000000000000000000000000000ecfee80017776ad9f6
  | 0, 9 => 0x77effff7df7effffffffbd0000000000000000000000000000000000000000007fffff3f37fffedeb7fefb0000000000000000000000000000000000000000007b33fffa67b33ffe61ffd60000000000000000000000000000000000000000006effffedfeefffffffff6f00000000000000000000000000000000000000000008702048e0870223e0414600000000000000000000000000000000000000000004cc0005984cc0019e00290000000000000000000000000000000000000000007ffff53a27fffe9ea5ead20000000000000000000000000000000000000000007ffffffffffffbbbfd674f
  | 0, 10 => 0xac5d80001615a152d00000000000000000000000000000000000000000017005c160170044402b8b000000000000000000000000000000000000000000006061984086061c00e32200000000000000000000000000000000000000000007bfbfffbf7bfbffff1ffdf0000000000000000000000000000000000000000000000a0e8e80013336841460000000000000000000000000000000000000000007fbbffff77fbbffe73ffff0000000000000000000000000000000000000000007f77fffeeff77ffffffff60000000000000000000000000000000000000000007ffffffffb7abff55bffbd
  | 0, 11 => 0x5ffcfefffdffdffffefdff00000000000000000000000000000000000000000002aa1341502aa00000270d0000000000000000000000000000000000000000007fff7f5ff7ffeeeff7ffff0000000000000000000000000000000000000000007dfdeeffffdfdfffffddff0000000000000000000000000000000000000000007fffdfb79fffffffffbeb90000000000000000000000000000000000000000007ffffdbeaffffffffffaf200000000000000000000000000000000000000000048540028ac85401bac0042000000000000000000000000000000000000000000550400360d50401c0e00b0
  | 0, 12 => 0x7ff9fe7ff7ff9e7ff3fdff0000000000000000000000000000000000000000003ffbffdff3ffbfe7f3ffff000000000000000000000000000000000000000000330355120330200001aa90
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 99 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 99 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 99 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 99 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 7 0) :: stateWiresD n (ids >>> 7)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 7 0) :: stateWiresS n (ids >>> 7)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 1
  | 6 => 36
  | 7 => 401
  | 8 => 580
  | 9 => 35
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x217baaf7
  | 6, 0 => 0xfa91a59ff7313a29eee71e2eee4af0d9e68ff63ae2297aeed67ef37dce318af7bf4ec913be21d38bb2aa5e0ab1321d3db073b633a58795cca1a1b2f3a1773e72a0ef756695ccb701953089ac9196e3ed8898e56e885b4b688545f2ce8500c1e17bae112c78f6595272425f4e700389bb63eb85373ec3945434acf4b90eae5f840de4c40e0bc4c53703b5970801e81a03
  | 7, 0 => 0x27ff421927da7a4b27946d4725ccf19d25887f8e251c564b23e8cf4d23e27c4023e17799225f7703223859582223d37c21c349ae212e7d0e1ec0878b1eab1e6d1e36c6481d9b4d591bbccb111b8942691b6ab0011a1194f118e45530183a393b1783dbd517646c2416c8d27916a6b67e16675638163aa2ce155d007e110c10d210a239dd10a0f9e110950fae10499b590f39a8ed0e670d800e19d47e0d47ff260d3f83ea0be9e6bb0b1178270a28e69808badc4b089f5261082444ea07f99f6f0672e00606277bf405ece50f05d7e2150544d4da04b9bd3d04ab8401045b8ee30404ddd003e948b903e00b9603bb7e2d020f9ac9019d47b60091adcb00864c88
  | 7, 1 => 0x4ed83c2f4eb27bad4e8fde1d4e51ffbf4d79e91f4c6bc0764bb391454a9fa7e04a176eea498777c848fc927c484873c54778f6e647756cd84756da7046d4260545e0d6c045aea9b2445febb6442a724b435096934346c5fb41d907444135def240d44d943f3d1e0c3e13b91a3ddcf0573d5b143d3ce3fadd3c813a1d3bcae5673bac52ff3b1025aa3a231bb139e9b85e390316c737d7f23037aabd3837a653c237a60f22377ba1fd35d7102d357b4441349fc3e534898904332cfa6232f9557a326414f4325be2c03213a663315346923122f42030d6b2ac30c97e8e306a7d632f75c4b52e09fe742cb37d4b2c199a122c0e1b9c2bedec352b4634b82affe18e
  | 7, 2 => 0x808d783f8049e0727edec5f77ea484417e0b317d7d521a1f7b11580779eacc4d78a4786c7823071f7593988b75551758749f5901741ca3bc726aefd671def7847133b9ef705fa5567047eeeb6d0660166cd133b86c950ebc6bec691f6b2434af69aa76fe692d65a3676c1879661248756522faf264f2cb4464ef41366486cd9d61a2e36860504c5c601da8035ffaadc25fcb78f15eb6601e5b61ef245b3e56165aa7beb55944b9c5593159d65924709058f923755889fa08586cc4a757f3b44a57a97d4a5768d28a5768b69654ec025e5465232653eab7e653bfabac5296752051e3a61951df945251593123513149454ffce9df4fd4f9bc4fb767b34f1b3a5e
  | 7, 3 => 0xab3f979faacaf066aa7dbfd6a9d523d0a9298ca8a8cab4eba88f93c5a84a91cea7f8fc64a7eefbe7a78c24e8a6432577a5f831bfa5c54951a5b20a5aa5ab3fada48b6280a3dcaaeea2587387a18b7069a093c52ba04c8b2e9f3444929f2068f59dc3b4d09d865cc39c9ae8b59c0af1939be81c839b2ef46199f8e6a398341d1c9735f53b96c3a22e96a99deb9679a66895d41a13954d77e994433b6d935842e8928ae09b92580b8792192d5f9091be63907404068f846cf08f6dffc68e7ada058a15219289d4fa1188da000c88a0b95b87ea6ab387adbb7787118e2285a4c1ac8570675c84f791718454795d84386c67822ab5038200a1fb80e73e0180e60dc7
  | 7, 4 => 0xd23c7c27d1e85dddd15f0275d147c379d142d9fcd0ab9624d0a562cad03edfc1cff29251cfb4df8dcf1f7129ce645582cda607f2cd93fd8dcd5a6541cd03b04ecc5c938ecc3d0dc0cb197fddca6cfee1c74ef82ec73c09fcc65bd165c5b47b04c4db860ac427e99cc4233cb3c42058e2c40a581cc350fc2ec1f91f3dc1a5487cc15d65c0c1335132c0aa1441c092864fbff658fabfa414e0bf54ad83bf2cafa2bd2e11b7bc818e40bac28e02b936af88b878b542b7dc87edb7910244b772bb01b61bd896b505a73eb4cd6981b3f89d59b38a3cf6b2e3a258b1fad929af258a0dae5b7119ae0696c4adee6f27ad1cb6a0ad175eafac9ea59babd05845aba7ea5b
  | 7, 5 => 0xf6110747f56e0ed3f45efb83f45b8f93f3fa0ecaf3946326f32aebbbf2b62921f21f82bef14e8449f0ed3922f0cd650ef061dce1f059c173f0472e9bf009d68eefc5af8cefa9b136ef9558edef943344ef2e0c98eeda7eb3eed6548eee256a82edb26e2cec3d1119ec0961a7eb903f4fead6b9e6ea4e5b59e9f9156ae9ec2664e7a5f78ae70ba1b0e66f745be666619ce5dbbcb3e5db8168e522d9f7e3254e0ddff1426ddfe5b7dedf498a89df140f03decfccc7dde70398ddae1bc7dd702d58dd6670d3dcf24aeadc55f197db05cde5d8e65998d87cd1d1d8595307d8087a03d6e7e549d63fac90d5565c4bd4a7106bd48aa7cfd40ca691d3698792d2cd5a3d
  | 7, 6 => 0xfee12394fe74b840fd4e6a31fd33ede8fd19b2effd1054dafcc35ee7fc97c093fc0c6452fbf91b30fbbfcf5bfb7b2813f8f9280af89ba26ff86a23c1f7e468bef7cefd85
  | 8, 0 => 0x1b620f191aae64481a1c32cf19e01af919b4348619a9f7a51967cfa518f3f9fd18b71f1b186d22271836cfa61829ce09181af1c618196416178f95851754003b174fdd2e16e0c2a716b7d2e6165bc83615c87767144e8118141f654a1362d1f9113a172910ce739b108b623e0fda57d80faceb7d0f540db70f15ef520c3d620b0be810370bcc6cfe0b7f311c0ae0ef7f0adc43f40aac4a4a0a8a258e09f38f5709df6c8c0973a5fe09552a07094e6daf086099f3083adb1b07c0da6507474582071c1d33071370820617599d05df523c058b93f6055761f70557489f0553ee99054031150399c2aa02894ba8023c0fc6019597e20174c16301470c250021e58d
  | 8, 1 => 0x34698f4f3431a74434221eb4338a9499333e18c73307cfd932625b423248b3f031fb12bd31c8557631a3528031728edf3148f93e3143730e3015a6132fa9df852f6123b42e2d346d2e276bd92d26852d2ccadd292c8f4bfb2b0b5c3a2a7eea622a70ed602a677c212a3a34bc299e07672944bf422934a43228d0850d289179b527aafaea274e74f226f5190e2625121f26207faf2598eb9d254ef80524fcbe4824c6dd1e2495f1912465fac12461a68c246018dc2408735923999b3d2373a15c22fe87ac22f755dc22ddf09521ba4c8c210d540d1f1da09d1f1418711ee4b91d1e8885c71e34d6591e24312c1e0b539c1ddf7afe1d5cf2471cb250b41c5e9791
  | 8, 2 => 0x4f4f552e4eb724b54eaffd514e168a4b4d8755204d7123924c2918df4b0042e04a7c8a564929a52348bf4cd64850b02448160fcd47ec9de847e0d42047503e79474e39884722bb554717dbc546afd52f4691d86644f46dae44e15ff2446785d24353286242ecdcb942ae4aba41d7ec6a410f4eb54089519b406cf747404456723ff9d07a3f55bb6f3f3a918b3e324b823e13b91a3dacb0a53d65400a3cd5ac2f3cae0af93ba3b2173b42ad103b24647c3b0784c23b054dbe3a1b7fbf3a0d753d3997ddc538bcfe61389bc3223894cb14382838a63820d10c381297d0374da3d236a25bd2362d75d735e4bc2d35d1710c3594c62435933874354a43d234cf9862
  | 8, 3 => 0x6ba394ca6b905ea96b35338c6a436ac1695671026823e6ea680b71c1678a610d65e64bc4654db196652302f0650aa8fb649c8fb363d4cecc6394cb606338a17762da0ba3620f803761366e4160d7e31d6054b7425f0220365e74b7545e4fe6c95e11d3e45e02aae75dba8dd05d75a41d5c791a775c35e4cf5c3362785c1922135c01d0825bac1fe05b9609f45b6e26035b5d86e95b03e0e95a44543059ffb90c58ff96da588159205880edfc57e2f4c75744cd06566e0cf0559aa56a558c6c2e558be6d054efb97b547a8078540248725397255953308feb52e1dcc1521ecdce513da990513b2274509db5a85057491150270d28501affc04feb82834fe14f3a
  | 8, 4 => 0x81ebad4081145b1880b275d5807272698053a3247fca74897fad44a77f7c1f1d7f48e9237e5376e27dc580577db7498d7d4e35eb7d3bb70c7d2953027d2660357cd3ef2e7c89e0177c50f8467c2f091f7b82966f7b78a9887b69bd637aedd35f7a64f51c7a18282179c9f9d879b9bd38797892d9791ceacd789dcdab7879b9da780f052577e6d3ac77a2ec71779f5fc87777266e7706bf1c76e5205776e392a77638fdc775ea8b5475820177746c98c373fe65cf73e7cb0b73d71d4173ac67a6739e61b27302345d72ff04f572698dd9718f128870df58a670cd8a617004b0d46f7f563d6f3f52d16e6470dd6e3405186d34f01a6cdc62566bfd41c06bb6e71e
  | 8, 5 => 0xa38717a1a35ed95ca35c99bca34e6080a34aa852a2901519a258ce20a187cf10a145cffa9fa4ff1c9f18d8ec9eaf7bba9d83bcab9d5724899c693efa9bcd11a59afa29949a4fd0f49a0de81599d1b35399334efa983081fd980b5e6597a6945f96eaff9d955e78e6950da8969480937a9477ae2a93f5e56191ebd30b910caf9e910764b9907c08bb8f9a30168ec019608d392a008bcb0aa58b83eb1d8b63c8e78adf1ff78a3808438a15219289fdfe5389818e18897007c88901b2a688ca48b4886835f8885464eb875d213586e50d2d85ed00d185b26e10853ca3f9851640bb85093e1b8406911083c6f68e83c6ecd9839525a38391a7eb834d73e28200a9f9
  | 8, 6 => 0xc3020f65c2f9ec6ac2f01dfbc2683f8cc202d008c1c2cc9cc1406e03bf815753bd862625bd5d2ed6bd2b53cebae01b5dbac427f9ba998e77ba2c1ee8b9f3331fb9cbfd67b9aa0908b974df7eb95ccd26b946e603b8ea1ef7b881b841b832b798b7ab5e0bb770158cb6b22594b6695fe0b5fad3cfb50a32b7b4c4c71db4662ca9b446d0f6b3b9e80cb3739594b35bd871b3441b39b3378973afb7c79fae854a4dae727626ae2239ecae1983bfacd8b740aba12478ab53e896aac017d8a918bd4aa8da3294a8c4134ba8197075a813c66ba7ce0063a7593c5ba756c6bca61a9f24a5a4e919a5771532a5560924a48fc18ea44d20c7a41cd653a3db0ffca3be9c3f
  | 8, 7 => 0xe02b3a56dfe0428fdfb544fcdfa66de6df9306addf210f18ded1e0a4dcd52801dc81781edc5c19e3dc4dd1c2dc1a3e45dbf38193dbdfb8a1dbd4aff6dba3f20eda6dc1e6d8745a96d81224e9d7d82d41d7ab670ad739b238d71c3ef1d6fe4d37d66e00b8d5d0edadd58cab71d578af8bd50eb174d4a3e242d3bdfd83d3af2994d366e607d33006f8d23db4e6d1cc62eed19f09c9d1182a88cff68b8bcf5d3d48cf36d2c1cf0d59e2ce72d1e8cdd14503cb4f1a5fca7919b3c9cb53b7c9b1bdf9c9457904c8a33524c81be11fc7ad063bc67d56cac671be37c588f3d7c50adea5c4d114a3c4c435b2c43fbb64c434d056c400369cc3d20ce2c38c4b50c351042c
  | 8, 8 => 0xff18be7efea99868fe3c77d4fe3b27cafcba52dbfbd687fcfb7a259ffb6ac16efb08ee9ffad1be56fa974036fa3e45c8f9992018f989972df8dddeeaf8757c1df7b085aef74b68eff73bb380f7125d3df6ab24f1f5b2441ef48d7139f45ce546f3f0cc92f36bdcd3f3549f3df2ef6246f2c942fcf2a50877f24521dcf236e8a0f13ef850f10fd9eef0fb2472ef9d2b69ee244c46edcea341ed3275ececd711a6ead4fa5ae97307cbe7c03ef3e776a78ae6914ae2e6848ca9e6280471e6184957e5ed84ffe5b25879e5ac8184e5124b9be5036c03e4cc4190e43c3d4ce41ee207e38484f2e302c835e26b9fb0e24d1df9e0e2a30ce07be3c3e069f259e05f6047
  | 8, 9 => 0xff9b5403ff85b838ff77baf5ff387c56
  | 9, 0 => 0xfe7db90ff65832addcd52801dadbc0b1d260d0b8c5f3b16bae2cf4369ed0a5158a15219280badcfd802ce6727a0a528c7605c7cd7346bec1678a690b663c34e765fc317b57f34ceb52beaf2c5252e89e4a54040347f8011e41bd218a3e0b18323d6cb3d93b24647c2ca19ad7280051b81db1f7b81b1e85361b1cf78619bb66560a1fb0a302894ba8023c0fc6
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x35051200
  | 6, 0 => 0x60000000002102000000000a102000004540620300000000000020000000051100000000000e10200000000021000000000011102000000000a100000000000000500000000021020000000000002000000000a1020000000012102000412644030300000000000020000000000001000000000e1000000000006102000004540220300000000121000000000000003000000291520300000460552040000000000000000000000610200000000000010004126440303000004140e20300000000061000000000000002
  | 6, 1 => 0x414022030000000011102000004140a2030000005905203
  | 7, 0 => 0x20000046440203000000001210400000000000080000000016103000000280e20300000000000050000000000005000000000e10200000000000080000000000002000000000000600000000021070000001909203000000000000500000000000010000000000003000000000e1010000004515207000000011510100000000000030000000000002000000000000000000000000020000000000005000000000e102000000000610700000000000050000000000002000000011510100000000551040000046440203
  | 7, 1 => 0x10000000000009000000000e101000000001210100000000000080000000000008000000000e10000000000061000000000000004000000000a102000000000610200000000000030000000012102000000000000500000019012030000000000002000000000a1010000005812203000000000a10400000000121040000001812203000000080e203000000000000800000000000020000000000001000000000e107000000005510400000019052030000000012104000000000000500000000000070000000000001
  | 7, 2 => 0x2806203000000580620300000000551070000000000002000000000e100000000000000b00000100412030000000006101000000000a107000000000000200000000000070000000000004000000000000200000000000020000000000003000000000000200000000000080000000000001000000000210100000000061010000000000000000000000a104000006544020300000019152070000001812203000000000210200000000121000000000000007000000000e101000000000000100000000000080000000000003
  | 7, 3 => 0x8000000000210100000000061020000000000003000000000a10400000000000050000000012101000000005110000000000000050000005802203000000000000200000000000030000000012101000000000210400000018022030000000000002000000000000b00000029152030000000000000000000000a1000000000002107000000000a101000000000000000000000000030000000000005000000000e1020000000006103000000580a203000000000000800000000000020000000002104000000000a104
  | 7, 4 => 0x500000000000020000000000003000000000610300000000000080000000000003000000180220300000000061070000000000008000000000a100000000000000300000000021040000000000008000000180e203000000000000400000000021040000000000002000000000000800000000551030000000000008000000005510400000000000030000000002101000000000000800000000000050000000000001000004540220300000000551070000000000007000000000210000000028062030000005806203
  | 7, 5 => 0x61020000005802203000000000e100000000005510100000000000000000000000005000000000000400000000061040000000000005000000000000600000000000010000000000006000000580a20300000000000080000000000003000000005110000000000511000000000000002000002644020300000000000080000000000005000000180e203000000000000200000364402030000000000001000000000a10100000018122030000000000002000000000a102000000000a10100000000021000000000012102
  | 7, 6 => 0x8000000000000400000000000020000000000001000000000000700000000061070000000000005000000080e20300000000000080000000000001000000280e20300000000000090000000055101000000290d2030000000105103000000000000200000000000030000000000002000000000000800000000000020000000006104000000281220300000058062030000000000001000000000e1070000000055101000000000210400000464402030000000016103000000000e10200000000000070000002802203
  | 7, 7 => 0x30000000002100000000000610100000059092030000000000001000000000000500000000551070000000000007000000000000800000000000000000000000004000000000610100000000000040000000000002000000000a1070000006915207000000080e203000004540620300000000061000000000115101000000000000200000000000010000000000005000000000a100000000080e2030000000000005000000000000800000058062030000000000002000004340220300000000061040000000000002
  | 7, 8 => 0x30000000000006000000000000700000029012030000005901203000000181220300000000000080000000000003000000000000100000000000050000000000002000000000e101000000290520300000059052030000000000007000000000610000000424022030000000000000000000000000200000100412030000000000008000000000e101000000391520700000000111020000000115103000000000000b000000000000500000000000080000065440203000000000000200000000000060000000006104
  | 7, 9 => 0x29152070000000055101000000000210000000028122030000000000008000000581220300000000000010000000000000000000000000600000000021020000000000005000000000000500000000000050000000000005000003451520700000000000010000000000003000004040220300000000000050000000000001000004240e20300000000551040000000000003000000000a1000000000000006000000000000800000414022030000000055104000000000a102000000000610200000000000070000000000005
  | 7, 10 => 0x4000000000a1020000000012102000000000000000000018122030000000000002000000000210100000000551070000000115101000000180a20300000058062030000001802203000000000210100000009152070000000000000000004040e2030000000000007000000081220300000000551040000000000007000000000000200000000000080000000000004000000000000a00000000000030000000006102000004140e20300000000061010000000000001000000000000200000028062030000005806203
  | 7, 11 => 0x4000000000000100000000021020000000000003000002644020300000000551010000000006103000000000210200000000000030000000000003000000580a2030000000000008000000000a1020000000000008000000180e20300000000000080000000012102000000005110000000000000040000000000009000000000000200000000000050000036440203000000480e203000000190d2030000000000006000000000000100000018022030000016515207000000000000200000000121010000000000008
  | 7, 12 => 0x50000000000005000000000610000000028022030000000000003000000000a107000000180e2030000005802203000000000210200000000000010000000002107000000001210400000000551040000000000008000000000000900000000000050000000055101
  | 8, 0 => 0x210300000000021070000000002101000000000000200000000000030000000000007000000000000200000000061010000000000004000000011510700000000c110300000000000010000000115103000000000000000000000021030000000055103000000001210100000000000030000000000007000000000000800000000000020000000000002000000000e107000000000000100000000000020000000000002000000000e103000000000a103000000010910300000000000040000000000000000000000a107
  | 8, 1 => 0x12103000000001610300000000000020000000000004000000000000400000000000040000000000005000000000e103000000000a1030000000000002000000000a1030000000105103000000001610300000000121010000000012103000000000a103000000000e10300000001151010000000016103000000004010300000000000070000000000004000000000210300000000021010000000000001000000000e103000000000610400000000000080000000000001000000000000200000000000040000000109103
  | 8, 2 => 0xe1000000000000005000000000210300000000000020000000000004000000000a107000000000e10100000000121070000000000002000000000a101000000010d1030000000002103000000000210100000000000050000000000004000000000000800000000021030000000002104000000000000500000000061030000000006103000000000000800000000121040000000000005000000000000700000000000010000000000004000000000000500000000000040000000000002000000000a1010000000055107
  | 8, 3 => 0x1000000000e1030000000002103000000000000100000000000040000000000000000000000000200000001151030000000000003000000000000000000000000010000000000001000000001210700000000021070000000012104000000000e10700000000000070000000115107000000000610100000000000020000000006103000000000a101000000010d103000000010910300000000000040000000115107000000000a10300000000161030000000055107000000000000700000000000010000000000003
  | 8, 4 => 0x16103000000000a1040000000000004000000000000400000000061030000000002101000000000210300000000061030000000000000000000000a103000000000000200000000121030000000016103000000000a10400000000c110300000000000070000000000008000000000a10200000000061040000000000005000000000e1030000000012102000000000000000000001151070000000006103000000000000200000000021030000000000004000000000e103000000000a10100000000121030000000015103
  | 8, 5 => 0x12107000000000000100000000151030000000000000000000000000400000000000070000000115103000000000210400000000000010000000012101000000000000200000000551040000000000003000000000a1000000000000001000000005510700000000021030000000000000000000000e103000000000210400000000000070000000012101000000001210300000000021020000000012103000000010d1030000000000007000000000000500000000c5103000000000000800000000000080000000016103
  | 8, 6 => 0x210400000000000000000000002107000000000000700000001011030000000000001000000000610300000000000070000000105103000000000e1030000000000008000000000e10400000000551010000000000001000000000e1020000000000007000000000a103000000001610300000000000010000000000005000000000210000000000000080000000000003000000000610300000000000050000000002101000000000e107000000000a10400000000000000000000000001000000000a1070000000000004
  | 8, 7 => 0x700000000951030000000085103000000000000700000000851030000000000008000000000000200000000061010000000115101000000000a10300000000161030000000000007000000000a102000000000a103000000001210200000000061030000000000008000000000210300000000000050000000000005000000000000200000000000010000000006107000000001210300000000061010000000081103000000000000700000000c91030000000041103000000000e1040000000000001
  | 8, 8 => 0x951030000000000001000000000a1030000000000004000000000210700000000161030000000006103000000000610100000000000050000000105103000000000610300000000000080000000109103000000000000400000000000050000000000000000000000a10200000000121020000000000004000000000e1030000000006107000000000a107000000000210300000000000050000000000005000000000210300000000000010000000000007000000000e104000000000000300000000000070000000000004
  | 8, 9 => 0x61020000000000003000000000e102000000000e10300000000000080000000000001000000000000400000000000050000000002102000000000a103000000000a107000000001610300000000000040000000081103000000001210700000000000040000000006103000000000210700000000000000000000055103000000000000100000000551010000000000007000000004110300000000000010000000000007000000000000100000000151030000000006103000000000000000000000000050000000000008
  | 8, 10 => 0x7000000000e1020000000002103000000000000100000000061010000000000002000000000e101000000000000700000000000010000000000004000000000000300000000021030000000115101000000000210700000000000040000000000004000000000610300000000401030000000000000000000000000100000000551040000000000001000000000000800000000000040000000000000000000011510300000000000070000000006107000000005510300000000000050000000002103000000000e103
  | 8, 11 => 0x30000000000001000000000000200000000000000000000012103000000000000000000000000020000000000000000000000000100000000021030000000105103000000000000800000000061040000000000000000000000a103000000001610300000001011030000000000005000000004010300000000061030000000006104000000000000200000000000070000000012103000000000610200000000000080000000006103000000000e1030000000105103000000000000400000000000030000000000005
  | 8, 12 => 0x50000000006103000000000e1030000000000005000000000a1030000000055101000000000e101000000000610400000000000030000000000002000000000610700000000000030000000055107000000005510100000000511070000000006103000000000000300000000c5103000000000000700000000021030000000000007000000010d1030000000000000000000000610000000000000040000000000008000000000000700000000000070000000101103000000000000300000000000040000000006101
  | 8, 13 => 0x40000000000003000000001610300000000000070000000006102000000000610300000001151010000000000009000000000000700000000c51030000000000002000000000000300000000000000000000000004000000001210400000000000040000000000008000000011510700000000000070000000115101000000000e10300000000000060000000015103000000001210300000000000040000000002101000000000000300000000c11030000000115103000000001210400000000000040000000000007
  | 8, 14 => 0x200000000000070000000115101000000000000800000000000030000000055107000000000e1010000000012101000000000210300000000061070000000000004000000000000500000000000040000000000001000000000000500000000000020000000000001000000000a101000000000000400000000000080000000000009000000000000200000000000040000000000001000000000000100000000000010000000000004000000005510100000000000070000000000008000000000a1030000000006103
  | 8, 15 => 0xc9103000000000e10700000000000050000000000003000000000e10100000001151070000000000001000000001610300000000061030000000000004000000000000700000000000080000000006107000000000000100000000121030000000002101000000000a104000000000a103000000010110300000000161030000000101103000000000000300000000000050000000000004000000000000700000000061030000000000001000000000000100000000000010000000115107000000010d1030000000012103
  | 8, 16 => 0x500000000551010000000000002000000000000a000000000000600000000000010000000000000000000000a101000000005510400000000000020000000000003000000000e10100000000851030000000055104000000000000500000000021040000000000008000000000e107000000000000200000000000020000000000007000000000000600000000000020000000002103000000000000100000000000000000000000002000000000000300000000000030000000000000000000000e1030000000000005
  | 8, 17 => 0x1151010000000000005000000000000800000000000010000000000008000000005510400000000161030000000055107000000001210300000000551010000000006103000000000210200000000000080000000081103000000000000400000000121030000000109103000000000e104000000004110300000000121030000000000000000000000000100000000000040000000095103000000000a1030000000051100000000001610300000000c91030000000000002000000000000200000000000020000000000000
  | 8, 18 => 0x2103000000001210700000000000070000000012101
  | 9, 0 => 0x30000000000001000000000000300000000000010000000000003000000000000300000000000030000000000007000000000000300000000000020000000000007000000000000300000000000020000000000003000000000000300000000000040000000000007000000000000000000000000010000000000004000000000000300000000000040000000000002000000000000300000000000070000000000003000000000000300000000000010000000000003000000000000100000000000070000000000001
  | 9, 1 => 0x300000000000030000000000004
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_167 roots_167 7 s ws hint
  | 1 => checkCutEntry dom_235 roots_235 8 s ws hint
  | 2 => checkCutEntry dom_79 roots_79 7 s ws hint
  | 3 => checkCutEntry dom_111 roots_111 9 s ws hint
  | 4 => checkCutEntry dom_175 roots_175 8 s ws hint
  | 5 => checkCutEntry dom_238 roots_238 7 s ws hint
  | 6 => checkCutEntry dom_47 roots_47 6 s ws hint
  | 7 => checkCutEntry dom_231 roots_231 8 s ws hint
  | 8 => checkCutEntry dom_237 roots_237 7 s ws hint
  | 9 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 10 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 11 => checkCutEntry dom_107 roots_107 7 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_239 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_167 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_235 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_79 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_111 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_175 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_238 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_231 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_237 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_107 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_239 goalM u ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_239 goalM u ys) : RunD dom_239 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_239 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_80 : ∀ i, 80 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 112 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_112 : ∀ i, 112 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 131 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 131 → Z 7 i = true := (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 (range_split z7_112 z7_128))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 80 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_80 : ∀ i, 80 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_96 : ∀ i, 96 ≤ i → i < 112 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_112 : ∀ i, 112 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 144 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_144 : ∀ i, 144 ≤ i → i < 160 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_160 : ∀ i, 160 ≤ i → i < 176 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_176 : ∀ i, 176 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 205 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 13 192 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 205 → Z 8 i = true := (range_split (range_split (range_split z8_0 (range_split z8_16 z8_32)) (range_split z8_48 (range_split z8_64 z8_80))) (range_split (range_split z8_96 (range_split z8_112 z8_128)) (range_split (range_split z8_144 z8_160) (range_split z8_176 z8_192))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 25 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 9 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 25 → Z 9 i = true := (range_split z9_0 z9_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_239 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_239 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_239 roots_239 goal_239 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_239 goal_239 := by
    have h0 : isConstB dom_239 goal_239 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_239

theorem low_239 : Lower dom_239 roots_239 goal_239 11 := S_239.noCircuit

namespace S_251
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (1, 17), (2, 3), (2, 34), (8, 9), (8, 72), (10, 11), (10, 42), (10, 74), (16, 17), (16, 144), (18, 19), (18, 50), (18, 146), (24, 25), (24, 88), (24, 152), (26, 27), (26, 58), (26, 90), (26, 154), (32, 34), (32, 96), (32, 160), (33, 35), (33, 41), (33, 49), (33, 97), (33, 161), (40, 41), (40, 42), (40, 104), (40, 168), (48, 49), (48, 50), (48, 112), (48, 176), (56, 57), (56, 58), (56, 120), (56, 184), (64, 72), (64, 96), (65, 67), (65, 73), (65, 81), (65, 97), (66, 67), (66, 74), (66, 98), (80, 81), (80, 88), (80, 112), (80, 208), (82, 83), (82, 90), (82, 114), (82, 210), (128, 144), (128, 160), (129, 131), (129, 137), (129, 145), (129, 161), (130, 131), (130, 146), (130, 162), (136, 137), (136, 152), (136, 168), (136, 200), (138, 139), (138, 154), (138, 170), (138, 202), (192, 200), (192, 208), (192, 224), (193, 195), (193, 201), (193, 209), (193, 225), (194, 195), (194, 202), (194, 210), (194, 226)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 8, 8, 10, 10, 10, 16, 16, 18, 18, 18, 24, 24, 24, 26, 26, 26, 26, 32, 32, 32, 33, 33, 33, 33, 33, 40, 40, 40, 40, 48, 48, 48, 48, 56, 56, 56, 56, 64, 64, 65, 65, 65, 65, 66, 66, 66, 80, 80, 80, 80, 82, 82, 82, 82, 128, 128, 129, 129, 129, 129, 130, 130, 130, 136, 136, 136, 136, 138, 138, 138, 138, 192, 192, 192, 193, 193, 193, 193, 194, 194, 194, 194]
def r2sG : List Nat := [3, 9, 17, 3, 34, 9, 72, 11, 42, 74, 17, 144, 19, 50, 146, 25, 88, 152, 27, 58, 90, 154, 34, 96, 160, 35, 41, 49, 97, 161, 41, 42, 104, 168, 49, 50, 112, 176, 57, 58, 120, 184, 72, 96, 67, 73, 81, 97, 67, 74, 98, 81, 88, 112, 208, 83, 90, 114, 210, 144, 160, 131, 137, 145, 161, 131, 146, 162, 137, 152, 168, 200, 139, 154, 170, 202, 200, 208, 224, 195, 201, 209, 225, 195, 202, 210, 226]
def mpG : Nat := 0x7fffffffffffffffffffff
def pool6G : List Nat := [90400912581216, 212801709146889, 151844837921168, 36396494620931, 212446822271304, 151973568455328, 36879833498402, 212319738005777, 90272182634824, 212318356113667, 27218588336905, 212561195696913, 90272178987080, 44810774381321, 36637013313795, 61687568794402, 90402797406304]
def xsM : List Nat := roots_251.map (· &&& dom_251)
def goalM : Nat := goal_251 &&& dom_251
def NN : Nat → Nat
  | 6 => 1
  | 7 => 22
  | 8 => 74
  | 9 => 13
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xd39de3d8
  | 7, 0 => 0xcaa6261ac580ba51b1b717f1ae75421ba39078a99826a1e8808a3da2806fbacf648d3f6d532c42c250db1fa15095f69f2c6da4b42957b8fe212c65481d41bd261827ff7f1685ddd31429098611d4b30c0ba3ce4405798e32
  | 8, 0 => 0x7897cba074ed92b37298896e727073ad6ae962c265baf2cc6505d3a36298100c61fe3d3661248a0b5eed28e65cc0ca525c39174c5abae6885a87e15e55ffc2f54f9576aa49e8c36d47edbbba44c5a17d4438608b441dddb841d4c76e40079e133d1c50f23a999fe03515bc193438dbb132a5d3fe329e9db02f7242be2ef8e1e32e9562562ce8057c2c6da4b429c0915526d09ab52620016c2402de8d22a8cbfd229b4bcf2248234e20100ea01fccfa551861c164185ec64117a5487917070fa9168b717315ea8d3a14ea9ec21452928910781c850e3b64f30d47299a0c7fd89b0ac51d5c09e651b90982ee770718563c02dd57a9029d4126020879c5010464d7
  | 8, 1 => 0xe7662f9dd0f21376c4218318bc3914fa8f69ae738e54490388ebfca982c100267b871e3579adbcd3
  | 9, 0 => 0xabbcdebda0c6db679f0c202877154aca5e3c72f838fd11d437a0f94831fd7fed2ef8e1e32534092c229b4bcf1775dbf10fce2101
  | 10, 0 => 0xabbcdebd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0a0a0a0a050505050a0a0a0a050505050a0a0a0a050505050a0a0a0a050505050f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
  | 0, 1 => 0xf000f000f000f000f050f050f050f050f000f000f000f000f050f050f050f0500000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f030303030303030303030303030303030303030303030303030303030303030300000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000a0a0a0a0f0f0f0f0f0f0f0f000000000a0a0a0a0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000c0c0c0c080808080c0c0c0c080808080c0c0c0c080808080c0c0c0c08080808
  | 0, 2 => 0x30303030202020203030303020202020303030302020202030303030202020200000000050505050000000005050505000000000505050500000000050505050a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a00000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050505050505050505050505050505050505050505050505050f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a
  | 0, 3 => 0xf0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f0a0a0a0a000000000f0f0f0f0f0f0f0f0a0a0a0a000000000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e00000000000f000f00000000000f000f00000000000f000f00000000000f000f0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0c0c0c0c0d0d0d0d0c0c0c0c0d0d0d0d0c0c0c0c0d0d0d0d0c0c0c0c0d0d0d0d0e0e0e0e0c0c0c0c0e0e0e0e0c0c0c0c0e0e0e0e0c0c0c0c0e0e0e0e0c0c0c0c
  | 0, 4 => 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000
  | 0, 5 => 0xf0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c00000000000000000303030303030303000000000000000003030303030303030f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00
  | 0, 6 => 0x30303030000000003030303000000000303030300000000030303030f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f
  | 0, 7 => 0xf0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x1440c20406
  | 7, 0, 0 => 0x11144215040700510355604070050d318b040700e2441cd300701424511334170051081cb04070051034cb04070031c630b040701110354c04070142450d318174911440d0040800914f0c7040700e1441cd2c070091cd18c04070051031cb28070091481c60407
  | 7, 0, 1 => 0x1114454d0407009144647040701114460304070091441d704070090d318c040700511334b0407
  | 8, 0, 0 => 0x124451031c102112451031e0040900024511334101c02459831c604080252440c730102002450e41c604080098c51221c102002458441cd04080091441cd80102007c91440c7040801e2450c718102002451031dd04080142451031cb06005091447031c180091440c76c1020015a1031cb0408
  | 8, 0, 1 => 0x98ee1031c1020052d2451031c180001440d32c101c01440c72ec040802b2451031c10200a8914488704080058440c72c1020000e2451034c070112451031c102001440c72e004080112451034c102000142450c718170051220c72c102002451031e904084491611031c102402681670c70408
  | 8, 0, 2 => 0x2451cd18101c01447031cb04080091431d51810200a051031cb04080112451081c102002451031d60408009144907341020025a1031cc040801e245107341020024510341304080122451034c102004898c40c704080091441cd2c10200bc91440c70408009b851034c102000051031cb0407
  | 8, 0, 3 => 0x9491440e41c102405091440c74c180352451031c10200d091440c704080005051031cb05c01671031cb04080091440c7cc102002451180c704080252458431c102000143891440c7700044510354101c02451031f20408009c451031c102004491431c604080091440c7c010200a911440c70408
  | 8, 0, 4 => 0x9e451031c10200245e040c704080091447034c102001440c74cb04080091440c7dc102004491441cd040800911c0c73010200949a050c704080091441d53410200d891440c70408
  | 9, 0, 0 => 0x91440c704072458440c704082451031e00408a891440c704082631440c704082451031d304084891440c7040826e1440c704080051031cb040700e2451031c074491440c704080091441cd04072451031d50408
  | 10, 0, 0 => 0x91440c70407
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 40
  | 7 => 52
  | 8 => 58
  | 9 => 52
  | 10 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 6 0) :: stateWires n (ids >>> 6)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x78001e000f0003e0000070000000000000000000000000000000000000000007ff00ffffffc3c3fc07c1f00000000000000000000000000000000000000000000000007f803fc003ffc00000000000000000000000000000000000000000000000ff0000003c3c03f83e0000000000000000000000000000000000000000000780f0e07870000003c7398000000000000000000000000000000000000000000787ffe1fff0c003e3ffff80000000000000000000000000000000000000000007ff00007fffc00000000000000000000000000000000000000000000000000007ffffff800000000000000
  | 0, 1 => 0xffe180003ffc1fffff8000000000000000000000000000000000000000000000ffff80003ffffffffff00000000000000000000000000000000000000000007f0f1f878ffffffc38c670000000000000000000000000000000000000000007ffffff807fc03ffc003ff0000000000000000000000000000000000000000007ffffffffffc00003fffff0000000000000000000000000000000000000000007ff001e7fffc0000000007000000000000000000000000000000000000000000000000000003ffffc000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0x78001e000f3ffffc00007000000000000000000000000000000000000000000787ffe1fff0c00003ffff8000000000000000000000000000000000000000000000000000000003e00000000000000000000000000000000000000000000000000000007ffffffffffffff000000000000000000000000000000000000000000787ffe1fff0fffc1fffff800000000000000000000000000000000000000000000000007f803fffffffc00000000000000000000000000000000000000000000078001e000f3ffffc000070000000000000000000000000000000000000000007ff001e7fffc003e000007
  | 0, 3 => 0x780f0e07ff03ffffffff980000000000000000000000000000000000000000007ffffff80003ffffc000000000000000000000000000000000000000000000007ff00007fffc003e0000000000000000000000000000000000000000000000007f8f0fe787f0003e3c739f0000000000000000000000000000000000000000007ff00ffffffc0000007c1f000000000000000000000000000000000000000000780ffe078703c3c03ff3f8000000000000000000000000000000000000000000787ffe1fff0c00003ffff8000000000000000000000000000000000000000000780f0e078700003e3c7398
  | 0, 4 => 0x78ff1e000f3c3fe3f83e70000000000000000000000000000000000000000007fffffff870000003c7398000000000000000000000000000000000000000000000ff0000003ffffff83e00000000000000000000000000000000000000000007ffffff800f0003e000007000000000000000000000000000000000000000000780f0e07ff03fc003fff980000000000000000000000000000000000000000007fff0e07fffc00003c73980000000000000000000000000000000000000000007ffffff80003c3c03f83e00000000000000000000000000000000000000000007ffffffffffc0000000000
  | 0, 5 => 0xff007f803ffffffffe0000000000000000000000000000000000000000000078001e7f8f3fc3e3ffc070000000000000000000000000000000000000000007ff00007ffffffffc00000000000000000000000000000000000000000000000078001e000f000000000070000000000000000000000000000000000000000007ffffff800f3ffffc00007000000000000000000000000000000000000000000780f0e078703fffffc73980000000000000000000000000000000000000000000000f1f80003ffffc38c67000000000000000000000000000000000000000000000ff007f803ffc03fffe0
  | 0, 6 => 0x7f0f1f878fc0000038c670000000000000000000000000000000000000000007f8f0fe787f3fffffc739f0000000000000000000000000000000000000000007fffffff8703fffffc73980000000000000000000000000000000000000000007fffffffffffffffc0000000000000000000000000000000000000000000000000000007fffc3c3fc07c1f00000000000000000000000000000000000000000000000007fffc00003fffff0000000000000000000000000000000000000000007ff001e7fffffc3e3ffc070000000000000000000000000000000000000000007ff00ff807fc003fc0001f
  | 0, 7 => 0x780ffe07ff03ffc03ffff80000000000000000000000000000000000000000007fffffff8703c3c03ff3f8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf8113e089f0447e0494af0000000000000000000000000000000000000000006ee00fbeedd83c3bc07c1d0000000000000000000000000000000000000000002222248ff843fc083ffc04000000000000000000000000000000000000000000111ff0411227c3c43f83e2000000000000000000000000000000000000000000788f0e27871088827c7399000000000000000000000000000000000000000000343aa50d5284447e334a400000000000000000000000000000000000000000007ff88007fffd11109102400000000000000000000000000000000000000000007ffffffc40022221224800
  | 0, 1 => 0x111ffc591227ebc57febf200000000000000000000000000000000000000000000077ff80002eeef6efdbf0000000000000000000000000000000000000000000770f1d878ef777d838c660000000000000000000000000000000000000000005ddddb7007bc03f7c003fb0000000000000000000000000000000000000000003bbbb6eddb74000037deef0000000000000000000000000000000000000000007ff992e7fffd11109596ef00000000000000000000000000000000000000000044444912248bffffc8211000000000000000000000000000000000000000000048850a22851088824c3199
  | 0, 2 => 0x74051d028eb777d808426000000000000000000000000000000000000000000303aa40d52040000334a40000000000000000000000000000000000000000000040001000080447e00000000000000000000000000000000000000000000000000000003bffddddeddb7ff000000000000000000000000000000000000000000707eec1f760fbb81fb6b5000000000000000000000000000000000000000000066666d9ffccbfffffffd140000000000000000000000000000000000000000004fc55bf2adfbffffccb5bf0000000000000000000000000000000000000000007ff993e7fffd557e9596ef
  | 0, 3 => 0x7eef6fbfffdbffffffff9d0000000000000000000000000000000000000000007ffffffe648bffffea69100000000000000000000000000000000000000000007ff88107fffd557e9102400000000000000000000000000000000000000000007f8f1fe78ff0ccfe7cf7bf0000000000000000000000000000000000000000002aa006acc9500000005c0d000000000000000000000000000000000000000000799ffe679737cbc67ff3fb00000000000000000000000000000000000000000078bfae2fd71488827f7bd90000000000000000000000000000000000000000007c8f0f278790ccfe7c7399
  | 0, 4 => 0x1f9ff3e19bf7c7fe3f97ef0000000000000000000000000000000000000000007fffffffc712aaa37e7b99000000000000000000000000000000000000000000555ff95336afffffffa3f20000000000000000000000000000000000000000007ffffffcc9f2667f26dcaf0000000000000000000000000000000000000000007aaf2eafff53fc8a7fff9d0000000000000000000000000000000000000000007fff8e27fffd9992fd73d90000000000000000000000000000000000000000007ffffffd5227e3e53fcbe20000000000000000000000000000000000000000007fffffffffff3331b34a40
  | 0, 5 => 0x777ffddffeeffffffffff60000000000000000000000000000000000000000002fa337eff9f3fc7e3ffcaf0000000000000000000000000000000000000000007ffcc917ffffffffd923500000000000000000000000000000000000000000000b8112e0897000000494af0000000000000000000000000000000000000000007ffffffeedfbffffeefdbf0000000000000000000000000000000000000000007ccf4f37a79bfffffc7399000000000000000000000000000000000000000000000071d80002666d028c26000000000000000000000000000000000000000000333ff4cffa67ffcc3fffe6
  | 0, 6 => 0x330b0c858640000038c660000000000000000000000000000000000000000007fcf5ff7affbfffffcf7bf0000000000000000000000000000000000000000007fffffffe79bfffffe7b990000000000000000000000000000000000000000007ffffffffffffffffb6b5000000000000000000000000000000000000000000000000002add81c1ac0341d000000000000000000000000000000000000000000000000019b7400001596ef0000000000000000000000000000000000000000007ffbb7effffffd7ebffeef0000000000000000000000000000000000000000004cc00b3005980033c00019
  | 0, 7 => 0x7bbffeefff77ffce7fffff0000000000000000000000000000000000000000007fffffffd737ebe77ffbfb
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 58 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 58 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 58 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 58 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 6 0) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 6 0) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 7 => 80
  | 8 => 169
  | 9 => 10
  | _ => 0
def CH : Nat → Nat → Nat
  | 7, 0 => 0x554c30b151ac782850f9beb84e7330254ddc9bda4a1fe17f46d53f603c61b4443b06eea93abcb6b03a0d9fae361f2bce35c907e6355a3b8f35089653344ff604338e86eb31ecda64316182b32ef8e1e32d9f13922d289f242c8b97f72adaf8d72902d6d9282801ad27fe3f3825c27c992534092c24e1569c249b3fbc2446a69f236fedb722a8cbfd20d412371fb4e7c21f92e0471e8cf12b1d10b9ad1be358d31a69d4721a1063541775dbf11635bc5015a5993214ea9ec20e95e5060ca4b5a80c605e1a0b9fb8f10b7aed7609db7d0d09cb511509933a4b08c851c908b1b6c007e631cd0736ac8206776f8c059ae8e704f3bfa202db01710102271700be6a9f
  | 7, 1 => 0xe22f8175cd59f379b3db02c4aec27c93abbcdebda2d7fa0298b6661e94b31f346cc9b1ff6ae962c269a959986032c2395fb5504a5eed28e65c315d6057cee2ed
  | 8, 0 => 0x25fb2ae62534092c244235b624378bd1240d42b223e3ccf122d0565022748ef021e3a8a2218442ca21588fc220cb7f51206099a51f9bf6dc1f94e1eb1f58bf121e33c0661ced19771ca474d91a72b31a1a3e05d61a1937aa19d3c87b18834a971775dbf11724f2cf15eb80ee1580c55c155a44f91527f8041488b9d21413413212f5882d12996aaa120c4b1911f4720b11d0f0941113ba540fce21010e9ce8ad0e8634880e5fc1200decbdf30d55a8140d53d49d0d42e3d20cb485df0904816807f48e0e07b81c5807a95b44070ade8d06d88aa0067351d205ea3f99047fa15e0436969a032ebc070307a47a014e35ae011199ec00e0967300debb720003b50b
  | 8, 1 => 0x5942efba5894f5b858780f4e54e5b66d541799b25258a47651d404d04fcd67474f48c7a14f2375a14dd157524dcef1194d29f87a4abd33144a996c994a6a4db54a2b39944a2997fd49607c8f485d1c3348220590479ffc6546535fb04594174f45729dbc44395c2a426781bb41f75a3840b6df5e3f6c1d093f2a79463f23f8f43ed4df3e3e744a683b4b354b3b00c8c63aaba1993a78f5ad38fd11d438bff81c3870841837a37dae37a0f9483619c41a353e43773518407f343b601732d6aa2e32b306483265bd7b31fd7fed30da16412ff91b7f2fadc76c2df2fb7a2d75e5ef2cd318532cb656382c7746962c08c3c9291d426429171f5628690b4027a43413
  | 8, 2 => 0xeeb8992ce1547176cd59f379cb856583c981ea96c5537962be11a1aabaac4930b615952fabbcdebda35c7ae2a0c6db679f0c20289e704b7c9e4bf7549a2cf3d794e361e98a5a99e383bea56e77b1674877154aca76991cad752dccd373917a277285a33771887ab76eefb65a6d01e5fb6bcfb7ab689cabf764800bfd5fe307975f76dfe55f2404135e3c72f85dc8ed625d53a3e55d0b0ee45bce2ce95b895f725b3db033
  | 9, 0 => 0x77b167485dc8ed6254e5b66d5258a47651d404d041f75a3837a37dae23e3ccf11ca474d9070ade8d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 7, 0 => 0x2102000000000210600000000000060000000006102000000000a1070000000006102000000000210100000000000040000000006105000000000a1020000000000002000000000000800000000061050000000002102000000000000500000000000020000000000003000000000a1020000000000008000000000e10600000000000080000000000002000000000a100000000000000400000000000010000000000006000000000e1010000000000004000000000e104000000001210400000000000010000000000002
  | 7, 1 => 0x30000000000003000000000000300000000061000000000000002000000001610000000000021020000000006100000000000000300000000000080000000000001000000000610200000000000010000000000004000000000000300000000000070000000002104000000000e105000000000000000000000000030000000000004000000000e1050000000012107000000000000200000000121060000000012105000000000000000000000000060000000000006000000000000000000000000000000000006106
  | 7, 2 => 0x20000000000002000000000610400000000000020000000000002000000000e1010000000016106000000000000800000000021070000000012100000000000e10200000000000030000000002106000000000000800000000161000000000002102
  | 8, 0 => 0x2101000000000a1020000000000000000000000e1000000000000007000000000000300000000000080000000000006000000000000200000000000040000000000005000000000e101000000000000000000000000080000000006101000000000000300000000000060000000000002000000000000100000000000020000000016106000000000a10100000000000010000000002102000000000a1010000000000001000000000a10600000000161020000000016101000000000000100000000000020000000000000
  | 8, 1 => 0x200000000000060000000000006000000000e10100000000000060000000000004000000000210200000000161020000000000006000000000000200000000021040000000000002000000000a1070000000000001000000000000400000000000070000000115104000000000e1060000000000002000000001210100000000000070000000002102000000000000600000000000060000000000002000000000e10000000000000060000000000001000000000000300000000000080000000000002000000000a102
  | 8, 2 => 0x12102000000000a101000000000000800000000000070000000000007000000000000600000000000080000000000008000000000000200000000000040000000000004000000000000400000000000080000000002104000000000000400000000000020000000000008000000000000200000000000040000000006101000000000000600000000000000000000000005000000000000300000000000070000000006101000000000000000000000000030000000000006000000000000700000000000030000000016106
  | 8, 3 => 0x2102000000001610200000000000040000000000000000000000000200000000000040000000000002000000000210400000000021020000000016104000000000000400000000021020000000002100000000000000500000000000010000000000006000000000000800000000061040000000000002000000000e10100000000000040000000000008000000000000200000000000080000000000001000000000e101000000000000400000000000010000000000004000000000210100000000061020000000000006
  | 8, 4 => 0x20000000006104000000000000100000000000060000000002101000000000000600000000000050000000000006000000000000400000000000020000000000006000000000000200000000000060000000000002000000000000500000000000000000000012104000000001210600000000000030000000000000000000000000000000000000010000000000002000000000000300000000000010000000000002000000000000400000000000070000000000002000000000000200000000000080000000002105
  | 8, 5 => 0x800000000000020000000000002000000000000100000000061050000000000005000000000610400000000000080000000000002
  | 9, 0 => 0x6000000000000500000000000000000000000004000000000000200000000000010000000000004000000000000400000000000020000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_123 roots_123 8 s ws hint
  | 1 => checkCutEntry dom_243 roots_243 8 s ws hint
  | 2 => checkCutEntry dom_249 roots_249 8 s ws hint
  | 3 => checkCutEntry dom_219 roots_219 7 s ws hint
  | 4 => checkCutEntry dom_235 roots_235 8 s ws hint
  | 5 => checkCutEntry dom_107 roots_107 7 s ws hint
  | 6 => checkCutEntry dom_187 roots_187 8 s ws hint
  | 7 => checkCutEntry dom_179 roots_179 7 s ws hint
  | 8 => checkCutEntry dom_250 roots_250 7 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_251 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_123 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_243 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_249 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_219 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_235 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_107 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_187 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_179 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_250 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_251 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_251 == dom_251) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_251 goalM u ys) : RunD dom_251 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_251 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 22 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 16 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 22 → Z 7 i = true := (range_split z7_0 z7_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 74 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 64 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 74 → Z 8 i = true := (range_split (range_split z8_0 z8_16) (range_split z8_32 (range_split z8_48 z8_64)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 13 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 13 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_251 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_251 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_251 roots_251 goal_251 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_251 goal_251 := by
    have h0 : isConstB dom_251 goal_251 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_251

theorem low_251 : Lower dom_251 roots_251 goal_251 11 := S_251.noCircuit

theorem low_253 : Lower dom_253 roots_253 goal_253 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030303030303030303030303030303030303030303030303030303030303030, 1, 5)] (by decide +kernel) (by decide +kernel) low_249

theorem low_254 : Lower dom_254 roots_254 goal_254 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5050505050505050505050505050505050505050505050505050505050505050, 2, 6)] (by decide +kernel) (by decide +kernel) low_250

def isoMv_191 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_191 : Lower dom_191 roots_191 goal_191 10 :=
  lower_iso isoMv_191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_127

def isoMv_247 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_247 : Lower dom_247 roots_247 goal_247 11 :=
  lower_iso isoMv_247 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_239

namespace S_255
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 6), (2, 34), (4, 5), (4, 6), (8, 9), (8, 72), (10, 11), (10, 14), (10, 42), (10, 74), (12, 13), (12, 14), (12, 76), (16, 17), (16, 144), (18, 19), (18, 22), (18, 50), (18, 146), (20, 21), (20, 22), (20, 148), (24, 25), (24, 88), (24, 152), (26, 27), (26, 30), (26, 58), (26, 90), (26, 154), (28, 29), (28, 30), (28, 92), (28, 156), (32, 34), (32, 96), (32, 160), (33, 35), (33, 37), (33, 41), (33, 49), (33, 97), (33, 161), (36, 37), (36, 38), (36, 100), (36, 164), (40, 41), (40, 42), (40, 104), (40, 168), (44, 45), (44, 46), (44, 108), (44, 172), (48, 49), (48, 50), (48, 112), (48, 176), (52, 53), (52, 54), (52, 116), (52, 180), (56, 57), (56, 58), (56, 120), (56, 184), (60, 61), (60, 62), (60, 124), (60, 188), (64, 72), (64, 96), (65, 67), (65, 69), (65, 73), (65, 81), (65, 97), (66, 67), (66, 70), (66, 74), (66, 98), (68, 69), (68, 70), (68, 76), (68, 100), (80, 81), (80, 88), (80, 112), (80, 208), (82, 83), (82, 86), (82, 90), (82, 114), (82, 210), (84, 85), (84, 86), (84, 92), (84, 116), (84, 212), (128, 144), (128, 160), (129, 131), (129, 133), (129, 137), (129, 145), (129, 161), (130, 131), (130, 134), (130, 146), (130, 162), (132, 133), (132, 134), (132, 148), (132, 164), (136, 137), (136, 152), (136, 168), (136, 200), (138, 139), (138, 142), (138, 154), (138, 170), (138, 202), (140, 141), (140, 142), (140, 156), (140, 172), (140, 204), (192, 200), (192, 208), (192, 224), (193, 195), (193, 197), (193, 201), (193, 209), (193, 225), (194, 195), (194, 198), (194, 202), (194, 210), (194, 226), (196, 197), (196, 198), (196, 204), (196, 212), (196, 228)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 12, 12, 12, 16, 16, 18, 18, 18, 18, 20, 20, 20, 24, 24, 24, 26, 26, 26, 26, 26, 28, 28, 28, 28, 32, 32, 32, 33, 33, 33, 33, 33, 33, 36, 36, 36, 36, 40, 40, 40, 40, 44, 44, 44, 44, 48, 48, 48, 48, 52, 52, 52, 52, 56, 56, 56, 56, 60, 60, 60, 60, 64, 64, 65, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 68, 80, 80, 80, 80, 82, 82, 82, 82, 82, 84, 84, 84, 84, 84, 128, 128, 129, 129, 129, 129, 129, 130, 130, 130, 130, 132, 132, 132, 132, 136, 136, 136, 136, 138, 138, 138, 138, 138, 140, 140, 140, 140, 140, 192, 192, 192, 193, 193, 193, 193, 193, 194, 194, 194, 194, 194, 196, 196, 196, 196, 196]
def r2sG : List Nat := [3, 5, 9, 17, 3, 6, 34, 5, 6, 9, 72, 11, 14, 42, 74, 13, 14, 76, 17, 144, 19, 22, 50, 146, 21, 22, 148, 25, 88, 152, 27, 30, 58, 90, 154, 29, 30, 92, 156, 34, 96, 160, 35, 37, 41, 49, 97, 161, 37, 38, 100, 164, 41, 42, 104, 168, 45, 46, 108, 172, 49, 50, 112, 176, 53, 54, 116, 180, 57, 58, 120, 184, 61, 62, 124, 188, 72, 96, 67, 69, 73, 81, 97, 67, 70, 74, 98, 69, 70, 76, 100, 81, 88, 112, 208, 83, 86, 90, 114, 210, 85, 86, 92, 116, 212, 144, 160, 131, 133, 137, 145, 161, 131, 134, 146, 162, 133, 134, 148, 164, 137, 152, 168, 200, 139, 142, 154, 170, 202, 141, 142, 156, 172, 204, 200, 208, 224, 195, 197, 201, 209, 225, 195, 198, 202, 210, 226, 197, 198, 204, 212, 228]
def mpG : Nat := 0xffffffffffffffffffffffffffffffffffffff
def pool6G : List Nat := [28845556237574, 212561195696913, 92479792177224, 212809355232005, 151844837921170, 28846415939106, 212318793892617, 28845554336518, 36542018553381, 214137473205507, 90418211522888, 151990748324512, 92473884214022, 212318827120131, 212319738135313, 212464856204553, 212567897539333, 90420889846534, 212801709146889]
def xsM : List Nat := roots_255.map (· &&& dom_255)
def goalM : Nat := goal_255 &&& dom_255
def NN : Nat → Nat
  | 7 => 13
  | 8 => 115
  | 9 => 318
  | 10 => 136
  | 11 => 14
  | 12 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 7, 0 => 0xdcc8d68cc3905142c0f47acbac64f1ac938010e3864b3dcc7a41705f49dd8b7f4924f7843874a02720331eea0ba395cb096ba6fc
  | 8, 0 => 0x633b5788619e0dcb5f1aeddc5dc028565bcd1d2759622230578887b956de8559502f1ccc500e6f6d4cafc0584c6a9e434bd80ba64ad2638347fed96d47ca1c0a44e69de644d299114385869c437b50753fc051193e1ec3453d4a168e3cdf2f5d3a412aa637f3a136373897d232ecaa8a3261655d3235b98f2f4ee9462f0fde582f005c2b2b50987f2af208302abfc3b62aa4b33425272c87235a593e2258e96e21708257211902aa1f8fdb761d60c7441cba0fa01bc00e181a8055391a70d30c18f86bbe18c200eb15b3246f0fbcd8de0c9fcb660c0698690a833c2f0a42618f0a1b291409ce4bf708d13e2506d8feb506ac18500582859902ab147901b376cb
  | 8, 1 => 0xf55cd682ee6e05ceed9420a1e7dc6457e2b78a45e1554c3ddda08b3edd874ab8dab97cded8b4fd17d468e31fd2576278d1bfc4e0cfd9240acb3b97a0bd303bc1b270b34fb208bdcab2005381ab4768dea740cb0fa649d7f89fa909d59e18f74c959dbca39580091692b141f09187c25890adb93d8fc000e28e8d8d658c9ccf198ba9bd2e8a928a218551c5c57e394d657b192511783216b177cae0a7762d96ea760e32a3760301027330792670c23ca66cdd5dba6ad318c267be4acc6741fda866899bf264920a706370b6de
  | 9, 0 => 0x2478e74823679e112334052022f2e518223e1e79217172861fbcb0251f5f3f3e1f5724ec1f0ae9011e8665a31e852b931e081caa1d8739141d713e411d68cf931c79e5421b48e6421af4a3ba1ad816471a3b841e1a2b85cc19f8bc3d19be7535199c883a188d6e2e1885a24b1871e0bb185dbef016e1b72516418a4613e437c211134c2710c1f64610413f2d0ffea6ca0fbf44100f0a44c40e6c9ffa0e5a20400e45b7ad0dea9b510dcc85710d97e6650d2fa1800ccc70920bb1361e0b1d9e490b1a164109d67adc095edd6208e1b88008d1f19a083307e106b95d23050c52c6048345d103da5c840306d76602683aac023d521101ff282501ace892007f6d23
  | 9, 1 => 0x47fca8f247d169654576cc1644bb23a84448b0d043e2d0fc43111acb42f3767f41ce1db641a7c2bc4047f085400bec833ffa2efa3f387b2f3e9cf9823e56df9c3e1c92ca3e16fc733d96a67f3cccc0b23cb59b5b3c6b71a93c5464bd3bb929ef3a54d0043a1f7f2f3a0cd7b739be2b25381572dc37f727303753e96d37208d7e36cc50b63639319335d6e9ea353bbebb353baf1c3521499034e3c25e33a3bc753373790632fb3e3d32f66a1d32ecaa8a32c347ba302b9a892ffa837f2ef483892e63ed602e2c11592e22cd582cccbe2b2cb975492b5173882b2f78bd2a5ee97d2a27cd05299ca82a28e97914275249df267a5c6a2621450b253dcbf424ee5d75
  | 9, 2 => 0x7378e21272116f967115712e70cd1dda7056400c6f8323e06da54d9b6cc146726c01a83f6be8e35269fdf2a869d63ecd6991813067cbaaca66e4d72665bb2dc86470ddb8642889d863a2425b6281dde261ab44ff60d1bfff60b067ec5fa1b76d5f9f86f25f30c66b5f067aa75ece0a685e6198f05dab7d255d91f8f45d01c8c25c8c32115c2da1c25ba912a15a11e36c57a0a3ea57595a33568bc2155662c619565f1efb56374bdb550a218d5475933e53c477785332ea6552b5db7c52554e0752389aa0518466195176572d4fff2c594fd1da434e2b8e694c74e4224c4236e04bac6c9e4ada52474a83990049d20fd149c8b1f8487c35ff483d418348030225
  | 9, 3 => 0xb3b7f7ecb34e010faf929fe2ae7d03ffad648b38ab9e1877ab272f2da98ffff8a91c0cd1a7a9a8f4a73e9a94a62fa34ba57adcaca54b6a8aa526a1f1a3777bcea2c38c00a234a2f8a1fdd638a1d42c70a1c323d6a005568e9fe79cee9fafe9d09f3676c39e18f74c9d7bb4379cfb33689be54f849a4af46c997e487997c5358497b26e1d9638e1ba94a1b2859476f11a93a4e44b92d9a75d9257d006905d1d17902668218fdc89998e6859338ce5defd8bbb35bf8ae9ea85877f29358727e7c6863645ea85bb6b4d852b4e2383e2d61a830540b2828835d5816e117d816ab65e7b2fc408793a72ff7860ff59782c5a917718cb92760e32a37490161b74113d3a
  | 9, 4 => 0xfd331b18fc773132f7ca514df78ba30bf12676bdef0372ebee6bd553eb84c6f3e85e11d8e6280f58e61c824fe1b91cd7e0fb1d46df5856d4de2a75e8ddb79d43dd73a9b9dd6c9ceddcb7bfd3dbc9bc74da8e8fb8d785718ad3939391d34f03e2d299e363cf791d49cf462913ceac63f4ccd1890fccce5942ccae4db5cc0ccfd3cae6a08cc9832d20c94f7157c86a6cd6c7bc90abc70afd69c65d10f0c3ecdb82c2f5e86bc2dde439c2bfa41fc2ae133fc1939dcfc0d364b2c0097ee5bfb6b84cbefc3d24be0a5a44bc80f60bbbc6eb23bb1df0beb80704edb71811d1b6f704dfb63a1537b62c8967b5a37c72b4f3a401b4d2885ab3fad3a8
  | 10, 0 => 0x5911f2865852b485570a9e96546f9eb24f98bafd4bd0f8374ba159b34ad821cc463cc3013fe015933fa8398c3f9ef58b3e48e65e3ba0758137f4f6b5366a85a83309688e32ed9ab9308711342eed66742cc50e752c9baba52c6b54832b18b06d2af1c8202a099661295a98eb26b0ba9f269e32ef260639f9258dc8f3246f0ac42326f4d520a23acc20866cf71cd1ca161b3a9ae11aef2c501a5de0b31a347de319e434891954df27192341a51835855617bdaff216ee55a21437b37e13f952d71236b6d81147cc87113ed4d3108f11730fc28aff0eaf434b0df359650dda90c50dc9f6950b864cda08a562e70831c878080a64f005e1336c05ce5794050f2672
  | 10, 1 => 0xe04f2293dceadde0dcdc97a3dcb58f58dc7e6c68dc62c8bfdacb998ad7ca0131d4b31560d30fc602d24f8ce5d185a718d0f542f5cd6bf77cccbc076bc2dbb3bec132ddf8bee0b36bbdf02597b9f9b146b9a743dbb8bac2c7b7abcb7eb6f704dfb62a58ecb4bbb5b4b33f4c09b1eb79fab13ecac5ac6b78d2aafa70aca3d3f83999884dbb92e6de9191ec017e903474228f1a3d508d0073578894f3c58390e7997ea559727d7dd0727b0da9637a2a826e79384284751e6a8e744cb45d73cb3e3f72e35c4e722c901f7082a2da6e085a446d79279c6807ea486719e36d64af1298643203af6167341b5f9f86f25e0857bd5b787c0b5ab3f8cb5978d125591cc996
  | 10, 2 => 0xffe7fd86fe5ba9bcf9da3a0bf51687b9f43181fdef45f3d6ec02c2dce62f3d93
  | 11, 0 => 0xee31b78bd457dbf1c7a6811fa36829b18ab46ab7711baf256f847ff05c5449ff49711ee83709f1260df128ea09059ac302c140aa0297ddda
  | 12, 0 => 0x1f6d511d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f91111111111111111111111111111111111111111111111111111111111111111ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | 0, 1 => 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffaaaaaaaacccccccc88888888ffffffffaaaaaaaacccccccc88888888ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa0000000000000000ffffffffffffffff0000000000000000fffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f09999999999999999999999999999999999999999999999999999999999999999
  | 0, 2 => 0xffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffccffccff88ff88ffccffccff88ff88ffccffccff88ff88ffccffccff88ff88f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f100000000000000000000000000000000fffffffffffffffffffffffffffffffffcfcfcfcf8f8f8f8fcfcfcfcf8f8f8f8fcfcfcfcf8f8f8f8fcfcfcfcf8f8f8f8
  | 0, 3 => 0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888880000000000000000ffffffff555555550000000000000000ffffffff55555555aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc8888888888888888cccccccccccccccc88888888888888885555555555555555555555555555555555555555555555555555555555555555
  | 0, 4 => 0xff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ffffffffff88ff880000000000000000ffffffffff88ff880000000000000000ffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee3333333333333333333333333333333333333333333333333333333333333333ffffffff55555555ffffffff5555555500000000000000000000000000000000ff00ff00ff00ff00ff11ff11ff11ff11ff00ff00ff00ff00ff11ff11ff11ff11ffffccccffff8888ffffccccffff8888ffffccccffff8888ffffccccffff8888ffffffffffffffffffffffffffffffffcccccccc88888888cccccccc88888888
  | 0, 5 => 0x7777777777777777000000000000000077777777777777770000000000000000555555555555555500000000000000007777777777777777ffffffff88888888ffffffff88888888ffffffff88888888ffffffff88888888ffffffff00000000ffffffff00000000ffffffff00000000cccccccc00000000cccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ffffffff555555550000000000000000ffffffff555555550000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffff0000ffff0000ffff0000ffff0000ffff5555ffff5555ffff5555ffff5555
  | 0, 6 => 0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc888888880000000000000000333333333333333300000000000000003333333333333333ff00ff00ff00ff00ff00ff00ff55ff55ff00ff00ff00ff00ff00ff00ff55ff55ffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa8888888888888888ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffff8888888888888888ffffffff00000000ffffffff00000000ffffffff00000000ffffffff33333333
  | 0, 7 => 0x770077007700770077007700770077007700770077007700770077007700770000000000000000000000000000000077777777777777777777777777777777ffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000ffffffffffffffff8888888888888888ffffffffffffffff88888888888888880000000055555555000000005555555500000000555555550000000055555555aaaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaaaa88888888888888880000000000000000555555555555555500000000000000005555555555555555
  | 0, 8 => 0xffffffffffffffffcccccccc88888888ffffffffffffffffcccccccc88888888ff00ff00ff00ff00ff55ff55ff55ff55ff00ff00ff00ff00ff55ff55ff55ff55ffffffffffffffffffffffffaaaaaaaaffffffffffffffffcccccccc88888888f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd4444444444444444444444444444444444444444444444444444444444444444f0f0f0f0f1f1f1f1f0f0f0f0f1f1f1f1f0f0f0f0f1f1f1f1f0f0f0f0f1f1f1f1ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff55ff55ff55ff55
  | 0, 9 => 0xffffffff00000000ffffffff55555555ffffffff00000000ffffffff55555555ffffffffaaaaaaaaffffffff88888888ffffffffaaaaaaaaffffffff88888888ffffffffffffffffffffffffffffffffffff8888ffff8888ffff8888ffff8888cccccccccccccccccccccccccccccccc8888888888888888888888888888888855555555555555554444444444444444555555555555555544444444444444440000000000000000000000000000000033333333333333333333333333333333000000007777777700000000777777770000000077777777000000007777777700000000ffffffff00000000ffffffff00000000ffffffff00000000cccccccc
  | 0, 10 => 0xffffffffffffffffffffffffffffffff00000000555555550000000055555555ffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffffffffffffffffff88888888888888888888888888888888ffffffffffffffffccccccccccccccccaaaaaaaaaaaaaaaa8888888888888888ffffffff55555555ffffffff55555555ffffffff55555555ffffffff55555555ffffffff00000000ffffffff33333333ffffffff00000000ffffffff33333333ccccccccccccccccccccccccccccccccddddddddddddddddddddddddddddddddcccccccc44444444cccccccc44444444cccccccc44444444cccccccc44444444
  | 0, 11 => 0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa2222222222222222222222222222222222222222222222222222222222222222ffffffffffffffffffff8888ffff8888ffffffffffffffffffff8888ffff8888ffffffffffffffff0000000000000000ffffffffffffffff3333333333333333ffffffffffffffffffffffff00000000ffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000003333333333333333
  | 0, 12 => 0xffffffffffff8888ffffffffffff8888ffffffffffff8888ffffffffffff8888ffffffffffffffffffffffff88888888ffffffffffffffffffffffff88888888ffffffffffffffffffffffffffffffff55555555555555555555555555555555ffffffffffffffffffffffffffffffff00000000000000005555555555555555ffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffff88888888ffffffff88888888cccccccccccccccccccccccccccccccc44444444444444444444444444444444ffffffffffffffffffffffffffffffffaaaaaaaa88888888aaaaaaaa88888888
  | 0, 13 => 0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffff4444444444444444ffffffffffffffff44444444444444443333333322222222333333332222222233333333222222223333333322222222ffffffffffffffff2222222222222222ffffffffffffffff2222222222222222ffffffffffffffffffffffffffffffffffffffffffffffffccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffff8888888888888888ffffffff11111111ffffffff11111111ffffffff11111111ffffffff111111110000000000000000000000000000000055555555555555555555555555555555
  | 0, 14 => 0x3333333333333333222222222222222233333333333333332222222222222222ccccccccddddddddccccccccddddddddccccccccddddddddccccccccdddddddd0000000011111111000000001111111100000000111111110000000011111111ffffffffffffffffffffffffffffffff22222222222222222222222222222222000000000000000011111111111111110000000000000000111111111111111155555555555555555555555555555555555555555555555500000000000000003333333333333333333333333333333322222222222222222222222222222222cccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000
  | 0, 15 => 0xffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffffffffffffffffffffffffffffffffffffffffffccccccccffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaa0000000033333333000000003333333300000000333333330000000033333333ffffffff22222222ffffffff22222222ffffffff22222222ffffffff22222222ffffffffffffffff1111111111111111ffffffffffffffff1111111111111111ffffffffffffffffffffffffeeeeeeeeffffffffffffffffffffffffeeeeeeeeffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000
  | 1, 0 => 0x555555555555555533333333333333333333333333333333333333333333333300000000000000000000000000000000000000005555555500000000000000000000000055555555ffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccceeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbffffffff44444444ffffffff44444444ffffffff44444444ffffffff444444440000000000000000000000003333333300000000000000000000000033333333
  | 1, 1 => 0x55555555555555555555555555555555444444444444444444444444444444445555555544444444555555554444444455555555444444445555555544444444
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x60504100201007060504030e010070a0605040f0200705040f020701007060504120801007110a0605040f0e70a060504100e0070a05040f0e070070605040308010070d0504090c0b0070a0605040908007050409080701007060504030201007
  | 8, 0, 0 => 0x6052709161b260080605040f250e01008062104091618010080d14050409201b018060504091b240123806052209161b010080a06210409161b0081106050410161b018060504091620180180a06050409161f1e80504091d0207010081c06050409161b008060504091a191800814061704090e010080a14050409161500814060513090e01008
  | 8, 0, 1 => 0xa061704090e1b0080a050409182407008050409161b31070080d0504092b180100830050409161b01008050409161b2f0700811060504091a1b19806050409161b2e0080a2d0504091618008050409162c18010080a0d0504092b1b0080a060504091d020080605040918242a0080605040f0e2901008280409161b07010081704090e1b0701008
  | 8, 0, 2 => 0x6050409162f18008050412161b070100806050409163938008370605040f0e010080605040916361f018110a2d050409161b8060504091b19350080006050409080100706053409161b01008060504091b0801008330605040f0e010080a2d050409161b0081106210409161b018060504091b32240180605040f0e02010080a06280409161b008
  | 8, 0, 3 => 0x509161b3f070100805040f0e1b07010080a06050409161b3e80d140504093d1f018060504090b243c0080a06050412161b0080605040916383c00811061704090e1b018050409163b180700805040916153a01008140605040f0e010080d050409361b0100814060504100e01008060504120e1d01008110a0504091b24078060504090b3924008
  | 8, 0, 4 => 0x6050444161b01008000a0605040f0e0070a060504090e2b0080a060509161b3f0080a0605040f0e1b00806050412161b01008170409161807010080a0605040916182380504094342070100811050409161b3b0780a170409161b07008110a060504091824806050441161b010080005040f0e07010070605041216180100806054009161b01008
  | 8, 0, 5 => 0x50409160b3907008110a06170409161b80a0504090e1d0700811060509161b3f0181106050409161b3b8050409161b4801008110605040916471b811170409161b07018061704091b0201008060504121d0201008060546091b2401008060504090e08010081106050409163b1880605040916451b0080a0617040916180080a060504094342008
  | 8, 0, 6 => 0x605040f0e0b01008110a060504090e1d8060504121b2401008000605040f020100705040916184901008060504092b02010080605040f1b0201008060504090802010080a050409161b490080a0605040f161800806050412182401008110a050409161807805040f1618070100811061704091618018061704090e1f010080a05040f161b07008
  | 8, 0, 7 => 0x1c060504091618008110a0605040f161b806050410161801008
  | 9, 0, 0 => 0x110605040f161b01837060504091618290194e06050409161b010090a060504093d161800906170409160b1b010091106050409162b1b0190504091618240701009112d06050409161b019142d050409161b010090a0d060504093d1b0090d050409161b3a01009064d170409161b01009060504091a0b1b24009060504093d1f1b4c01906050409161b4b010093706050409161b4a019
  | 9, 0, 1 => 0x1106050409161b3901906050409182402010091106050409161b3a01906050409161b54010090a5306050409161b0090d060504093d18010090a050409161b1d070095206050409161b010090a14060504090e160090605040951161b01009060504091650180100906050412161b02010090605040916361b010094f06050409161b0100906050409251b2401009001106052709161b018
  | 9, 0, 2 => 0x1106050409161b3b0190a060504091618240091106050409161b15019065b170409161b0100937060504093d1b2401906170409161f1b0100906050409161b5a010090a37060504091b24009050409161d18070100959060504091a161800906050409161b580100906050409161b570100906050409561b4c0100906050409161b3b290090a0d060504091b2400906050409160b1b55019
  | 9, 0, 3 => 0x6054609161b0100811050409161b24070190a0504090e161b070090a14060504091b24009060504091b2402010090d06050409182401009060504091618610100906050409161b60010090014050409161501008060504091a1824010095f060504091b240100914060504093d161f0190a1406050409161f0095e06050409160b1b0095d060504091618010091106050409161b5c019
  | 9, 0, 4 => 0x504090e161807010090a06050409161d180091406050409182401009050409160b180701009140605040916650100906050409161b64010090d140504093d1b010096306050409161b2901933060504091b2401009622d050409161b010090d140504090e16010090d14050409160b010090006050409161f1e018115306050409161801906050409161f1b550193706050409182401009
  | 9, 0, 5 => 0x504096b161b070100906050409161b6a3b0095906050409161f1b2996906050409161b010091159060504091a161b9060504091b1d0201009140605040956160100906050409161b65680190504093d161f1b070196706170409161b010090a050409161f1b07009000a2d050409161b0082d59050409161b0100905040916651807010096606050409161b3b0091406050409160b29009
  | 9, 0, 6 => 0x2d050409161801008060504093d161f1e0190d140504091b2401009000a0504091b240700806170409161b29010090605040916186e01009060504091f1b242901911060504091a1b240195e06050409161801009115d06050409161b01900060504091d0201008060504096b160b1b009060504091b246d01009110a06050409161b2491406050409245c0100906050409161b6c01009
  | 9, 0, 7 => 0x50409182407010081406050409161b3b00963060504091b24010090a06050409166518009060504090e0b1d01009050409160b1b07290090504091b182407010090a060504090e1618009060504091b382401009050409161b65070100906280409161b680100906050409161801700090605040943182401009140605040916471b0093706050409161b3b009060504096f1b2401009
  | 9, 0, 8 => 0x6050409161801720090d060504096b1b0100906050409431b24010090605040f160b1b0100906050409560e1d010090d060504093d1f1b0190006050409161f013c80504091b245c070100900061704090e1b01008110a06050409161b1d9060504090e161e0100905040956161b070100914060504090e2b0100906050409161b710100906050409161b3b2f0090a060504093d161f1b9
  | 9, 0, 9 => 0xa0605040918240080006050409161b31008060504090e163a0100906050409160b3a010090a060504091b1824009050409161b4a0701009060504096b1618010090006050409161b2f0085d060504091a161b0090a06050409161b65009060504091b2474010090605040956161e0100906050409161b7301009060504093d161f180190a06050409161f180090504091618420701009
  | 9, 0, 10 => 0x3706170409161b0100906050409161b682901906050409160b18290097906050409161b0100900050409161b3b070080a060504091b245c0090504091618072901009110a060504090e161b9060504090e161801009060504091b1e240100978060504091618010090a06050409161b4c0090a0605040956161b009060504091b2477010090605040976161b0100906050409161b7501009
  | 9, 0, 11 => 0x59060504091b24290090d060504091b4a010090504093d1b2407010091406050409160201009060504091b243a010093706050409161b550191406170409161b01009060504091a161b320190605040918245c010090a06050409161b4a00906050409164c18010091406051309161b01009060504095616180100953050409161b3a010090a0605040916184200906050409161b7a01009
  | 9, 0, 12 => 0x5306050409182401009050409161b020701009060504091b24013c0090605040f161b290100953060504090e16010090504091a161807010095306050409160b010090006050409163b180080504096b162c1b0100900110a060504091b2480a06050409161b42009060504090e1d29010090605040916184a010090006050412161b0100806054609160b1b010097b06050409161b01009
  | 9, 0, 13 => 0x53060504091b240100914060504090e240100914060504090b240100900060509161b3f0100833060504090e1d01009000605040f0e1b010080605040916187c0100914060504091638010097e06050409161b0100900060504091618012387d06050409161b010091406050409166f01009060504090e1d0201009060504091a1b7c0100900170409161b07010080a06050409161b7c009
  | 9, 0, 14 => 0x6050409160b1f1b2990a3306050409161b0090006050409434201008050409166f1b07010095f06050409161801009140605040943160100937060504090e1d010092d050409160b1b01009110504091a161b07019001106050409161b3b8060504097f161b010090a370605040916180095906170409161b010090a06050409161b020090a0d06050409161800900000605040f0e01007
  | 9, 0, 15 => 0x605040983161b010090605040916821b0100906050409161b3e0100914050409161b7c010093306050409161801009370605040f161b010090504090e1b2407010090504090b1b24070100914060504090e1d01009810605040916180100900061704091618010080a140605040916180090605040916180201009050409161b38070100906050409161b80010090504094316180701009
  | 9, 1, 0 => 0xa0504091618070080a060504090e1b2400906050409431b02010090504090e1b1d07010096606050409161b010090a8406050409161b0090a050409161b18070090a060504094316180095e060504091b240100906050409161b020100906050409161f1b4a019110a0d06050409161b90a0d14050409161b00905040943161b0701009140605040f161b010091406050410161b01009
  | 9, 1, 1 => 0x6050409651824010091406050409165c01009060504090e1824010090a0605040943161b009060504090b182401009060504091b240186009060504120e161b0100906050409161b8501009050409161b550701009001106170409161b018000504090e1d0701008110a1406050409161b906050409161b6a01009050409161b1e070100906050409166f18010090d14050409161801009
  | 9, 1, 2 => 0x60504091b65240100933060504092b1b010090504091b24072901009060504091618880100900110a050409161b07878060504091b240100906050409161b3101009000a060504090e1d0082d050409161b2901009060504096b1b24010090a060504090e1b1d0090a060504091f1b2400906050409161b87010090005040f161b070100859060504096b161b00906050409161b6d01009
  | 9, 1, 3 => 0x60504091824290100900110a0605040916188060504093d161b68019110a06050409161b1890d140504092b1b0100900050409161b4901008000605040f16180100806050409162b18010092d06050409161801009060504091618890100906050409165518010091106050409161b38019050409161b5c07010097b060504091b2401009
  | 10, 0, 0 => 0x6050409161b5c010090006050409161b3b010091406050409161b1d0100a33060504090e161b0100a0006050409161b150100900060504091b2429010090000110a06050409161b8060504096b1a161b0100a00115906050409161b019060504093d161b1e0100a060504090e161b020100a005906050409161b290093706050409161b1d0100a0006050409161b3901009000504093d161b07010090006050409161b3a01009
  | 10, 0, 1 => 0x6050409166f0b1b0100a060504093d161b180100a000d060504093d1b0100937060504090e161b0100a3706050409160b1b0100a005306050409161801009000a060504093d161b00959060504093d161b0100a0006050409161b013c0090d060504090e161b0100a00001106050409161801800050409161b2407010090d06050409160b1b0100a060504090e1a161b0100a001106050409161b180190006050409161b6801009
  | 10, 0, 2 => 0x6050409161b18240100a000d060504091b240100900060504091a1b2401009005d06050409161b01009000a06050409161b240095906050409161b240100a005306050409161b0100900050409161b1d07010090014060504090e16010090059060504091a161b009001406050409160b01009060504091a161f1b0100a06050409160b1b380100a14060504090e161b0100a00060504093d1618010091406050409160b1b0100a
  | 10, 0, 3 => 0x5f060504091a161b0100a1406050409161b290100a06050409166f1b290100a000a060504090e161b00900002d050409161b01008005e06050409161b010090d06050409161b290100a0006050409161d180100906050409251a161b0100a000504090e161b0701009000a06050409161b1d0090014060504091b240100900050409160b1b07010096306050409161f1b0100a0006050409161824010090037060504091b2401009
  | 10, 0, 4 => 0x6050409161b650100900050409161b072901009007806050409161b0100900000a060504091b240080d060504091a161b0100a00060504096b161b01009330d06050409161b0100a00060504093d161f1b019000a06050409161f1b00900060504091665180100900060504090e1618010090006050409160b18010095f0d06050409161b0100a060504090e161b180100a00000504091b24070100806050409160b1b180100a
  | 10, 0, 5 => 0x6050409160b1b240100a000006050409161b3b008000605040916182901009060504091a161b350100a631406050409161b0100a06050409161b18290100a0006050409161b4a0100900060504091618420100906050409161b18420100a00060504091b245c01009000605040956161b0100914060504091a161b0100a0000060504091824010080006050409160b1b2900900060504091b182401009331406050409161b0100a
  | 10, 0, 6 => 0x60504090e160b1b0100a003306050409161b010091406050409161b180100a1406050409161b3a0100a003706050409161801009000006170409161b01008000a1406050409161b0090006050409161b0201009000d060504091618010093706050409161b180100a005f06050409161b010091406050409162b1b0100a0d06050409161b180100a06050409160b1b1d0100a000a0d06050409161b0090006050409161b7c01009
  | 10, 0, 7 => 0x6050409161b1d290100a06050409161f1b4c0100a060504091a3d161b0100a0000050409161807010080605040956161f1b0100a00060504090e1b240100900060504090b1b240100900050409161b1807010090006050409431618010090006050409166f1b01009000d14050409161b0100900000a050409161b0700806050409160b1f1b0100a06050409161b24290100a06050409560e161b0100a001406050409161801009
  | 10, 0, 8 => 0x605040f161b010081406050409161b240100a002d06050409161b01009060504090e161b290100a0000060504090e1d0100800060504090e1b1d01009060504096b161b290100a000605040943161b01009
  | 11, 0, 0 => 0x50409161b07010081406050409161b010090d06050409161b0100906050409161b290100900060504091b2401008060504090e161b0100906050409160b1b0100906050409161b1d0100906050409161b2401009060504093d161b01009000605040916180100806050409161b1801009000a06050409161b0085906050409161b01009
  | 12, 0, 0 => 0x6050409161b01008
  | _, _, _ => 0
def stateW : Nat → Nat
  | 7 => 60
  | 8 => 68
  | 9 => 76
  | 10 => 84
  | 11 => 76
  | 12 => 68
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 8 0) :: stateWires n (ids >>> 8)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfffffffffffffffffff0000000007fffffffff000000000000000000000000000000000000000000000fffffffff800000000000000000000000000000000000000000000001fff8000ffff000007ffffc00000000000000000000000000000000003fff00000000000ff00ff0007ff803fe0000000000000000000000000000f801fe0ff007f07f803fffffff03f83f0f878000000000000000000000000000f801fe0ff007f07f803fffffff03f83f0f878000000000000000000000000000ffffc0000001fffffff000000000000000000000000000000000000000000000fffffffffffe00000000000000000000000000
  | 0, 1 => 0xf8003e00f001f007800f0f0f0f0078070381800000000000000000000000000007fe01f00ff80f807fc0000000fc07c0f0787f0000000000000000000000000007c001f00f000f80780fffffffff87c0f0787000000000000000000000000000003e00000000000007c000000000000000000000000000000000000000000000ffffc00000f9fffffff0000000fc000000000f0000000000000000000000000000003ffffffe0000000fffffffffffffffffff00000000000000000000000000f8003e00f001f007800f0f0f0f00780703818000000000000000000000000000f801fe0ff007f07f803fffffff03f83f0f8780
  | 0, 2 => 0x1fff8000ffff000007ffffc00000000000000000000000000000007c001f00f000f8078000000000007c0f078700000000000000000000000000000000000000000000000000000fc000000000000000000000000000000000000003e000000f8000007cfffffffff800000000f0000000000000000000000000000003fff00000000000ff00ff0007ff803fe0000000000000000000000000000f801fe0ff007f07f803fffffff03f83f0f878000000000000000000000000000000000000001ffffffffffffffffffffffffff00000000000000000000000000f8003e00f001f007800f0f0f0f007807038180
  | 0, 3 => 0xfffffffffffe000007c0000000fc000000000f00000000000000000000000000003e000000f80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffff060000000ffffffffffffffffff000000000000000000000000000003e000000f8000007c0000000fc000000000f00000000000000000000000000ffffc1f00f01fffffff00000000007c0f078700000000000000000000000000007c0000000000f80780000000000000000000000000000000000000000000000ffc1ffffff07fffff83fffffff03fffffffff0
  | 0, 4 => 0x3fff00000000000ff00ff0007ff803fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffc1f00ff9fffffff0000000fc07c0f0787f00000000000000000000000000f83ffe0ff0fff07f87fffffffffff83f0f878f00000000000000000000000000ffc1ffffff06000000000000000000000000000000000000000000000000000000003ffff0060000000fffffff03ffff0fff8000000000000000000000000000000000000001fff8000ffff000007ffffc000000000000000000000000000000fffffffffffe00000000000000000000000000
  | 0, 5 => 0x3ffffffe0000000fffffffffffffffffff0000000000000000000000000000003fffff060000000fffffffffffffffffff000000000000000000000000000000000000000000000fffffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffc1c0000001fffff83000000000000000000000000000000000000000000000fffffffffffffffffff000000000000000000000000000000000000000000000000000000001fffff83fffffff03fffffffff0
  | 0, 6 => 0xfffffffffffe0000000fffffffff800000000000000000000000000000000000003e000000f8000000000000000000000000000000000000000000000000000000003e0ff0fe0000000ffffffffff83f0f878f0000000000000000000000000000003fffff060000000ff00ff0007ffffffff00000000000000000000000000007fe01f00ff80f807fcfffffffff87c0f0787f00000000000000000000000000fffffffffffe000007c000000000000000000000000000000000000000000000ffffc00000f9fffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffff83f0f878f
  | 0, 7 => 0xffffc000fffffffffff00ff00fff8007fc01ff00000000000000000000000000000000000001ffffffffffffffffffffffffff00000000000000000000000000fffffffffffe0f8078000000000007c0f0787000000000000000000000000000003e000000f8000007c000000000000000000000000000000000000000000000ffffc0000001fffffff000000000000000000000000000000000000000000000ffc1ffffff07fffff830000000007ffffffff000000000000000000000000000003e00000000000007c00000000000000000000000000000000000000000000000003fffff060000000fffffff03fffffffff0
  | 0, 8 => 0xffffc0000001fffffff00000000000000000000000000000000000000000000000003fffff060000000fffffff03fffffffff000000000000000000000000000ffffc00000f9fffffff000000000000000000000000000000000000000000000f8003e00f001f07f803fffffff03f83f0f878000000000000000000000000000ffc1ffffff07fffff83fffffff03fffffffff00000000000000000000000000007c001f00f000f8078000000000007c0f0787000000000000000000000000000f801fe0ff007f07f803f0f0f0f00783f0f87800000000000000000000000000000003fff00000000000fffffff03fffffffff0
  | 0, 9 => 0x3fffff060000000ffffffffffffffffff000000000000000000000000000003e00000000000007cfffffffff800000000000000000000000000000000000fffffffffffffff8000ffff000007ffffc00000000000000000000000000000007c001f00f000000000000000000000000000000000000000000000000000000ffc1c1f00f01fffff8300000000007c0f0787000000000000000000000000000000000000001f07f87fffffffffff83f0f878f00000000000000000000000000fffffffffffffffffff0000000007fffffffff00000000000000000000000000fffffffffffffffffff00000000007c0f07870
  | 0, 10 => 0xfffffffffffffffff830000000007ffffffff000000000000000000000000000fffffffffffe0f807fc0000000fc07c0f0787f00000000000000000000000000fffffffffffe0000000000000000000000000000000000000000000000000000ffffc1f00f00000007c000000000000000000000000000000000000000000000ffc1ffffff07fffff83ffffffffffffffffff00000000000000000000000000000003e0ff0fe0000000ffffffffff83f0f878f0000000000000000000000000007c001f00f01fffff83fffffff03fffffffff00000000000000000000000000007c001f00f000f8078000000000007c0f07870
  | 0, 11 => 0xffffc1f00f01ffffffffffffffff87c0f07870000000000000000000000000000000000000000000000fffffffffffffffffff00000000000000000000000000ffffc00000f9ffffffffffffffff800000000f00000000000000000000000000003e000000f8000007c0000000fc000000000f00000000000000000000000000ffffc0000001fffffffffff000007ffffc000000000000000000000000000000ffffc0000001fffffffffffffffff83f0f878f00000000000000000000000000ffffc0000001ffffffffffffffff8000000000000000000000000000000000000000000000000000000ffffffffff83f0f878f
  | 0, 12 => 0x1fff8000ffffffffffffffc000000000000000000000000000000ffffc0000001ffffffffffffffff800000000000000000000000000000000000fffffffffffffffff83fffffff03fffffffff000000000000000000000000000fffffffffffe0000000fffffff03fffffffff000000000000000000000000000fffffffffffe000007cfffffffff800000000f00000000000000000000000000fffffffffffe0000000fffffffff80000000000000000000000000000000000007c001f00f000f8078000000000007c0f0787000000000000000000000000000fffffffffffe00000000000000fc0000000000
  | 0, 13 => 0xfffffffffffffffffff0000000fc000000000f00000000000000000000000000ffffc1f00f01fffffff00000000007c0f0787000000000000000000000000000003e000000f8000007cfffffffff800000000f00000000000000000000000000ffffc00000f9fffffff0000000fc000000000f00000000000000000000000000fffffffffffffffffff00000000007c0f0787000000000000000000000000000fffffffffffffffffff000000000000000000000000000000000000000000000f801fe0ff007f07f803ffffffffff83f0f878000000000000000000000000000000000000001fffff83fffffff03fffffffff0
  | 0, 14 => 0xf83fc00000f9f07f87f0000000fc000000000f00000000000000000000000000ffc1ffffff07fffff830000000007ffffffff000000000000000000000000000f801fe0ff007f07f803000000000783f0f878000000000000000000000000000fffffffffffe000007c0000000fc000000000f0000000000000000000000000000003e0ff0060000000fffffff03f83f0f878000000000000000000000000000ffc1ffffff07fffff83000000000000000000000000000000000000000000000f83ffe0ff0fe000007c0000000fc000000000f0000000000000000000000000007c001f00f000f807800000000000000000000
  | 0, 15 => 0xfffffffffffffffffff0000000fc07c0f0787f00000000000000000000000000ffffffffffffffffffffffffffff87c0f0787000000000000000000000000000ffffffffffffffffffffffffffff800000000f00000000000000000000000000f83ffe0ff0fff07f87f000000000783f0f878f00000000000000000000000000003e000000f8000007cfffffffff800000000f00000000000000000000000000fffffe0ff007ffffffffffffff03f83f0f878000000000000000000000000000ffffc1f00ff9ffffffffffffffff87c0f0787f00000000000000000000000000ffffffffffffffffffffffffffff8000000000
  | 1, 0 => 0xfffffff03fffffffff000000000000000000000000000f83ffe0ff0fff07f87f00000000000000000000000000000000000000000000000003fffff0600000000000000007ffffffff000000000000000000000000000fffffffffffe0f80780fffffffff87c0f078700000000000000000000000000007fe01f00ff80f807fc00000000007c0f0787000000000000000000000000000003e000000f9f07f87fffffffffff83f0f878f0000000000000000000000000007c001f00f000f80780fffffffff87c0f078700000000000000000000000000000003e0ff0fe0000000000000000783f0f878f
  | 1, 1 => 0xffc1ffffff060f8078000000000007c0f078700000000000000000000000000007c001f00f000f80780fffffff0387c0f07870
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7bdeef7b777b7bdbbbd0000000007effbfdfbf000000000000000000000000008421108488848424442fffffffff810040204000000000000000000000000000421088424443fff8020ffff000207ffffc00080000000000000000000000000021087fff00204212211ff00ff0107ff803fe0400000000000000000000000000f8c7fe3ef31ff1f798ffcfcfcf0f78f73b9db300000000000000000000000000e001f80ec007c076003ccccccc0360340a040000000000000000000000000000ffffe1080001fffffff444444441221002440000000000000000000000000000ffffffffffff08400008888888824424880000
  | 0, 1 => 0xf8c63e30f319f18798cf0f0f0f0c78c73399b3000000000000000000000000001ffe07f13ff83f89ffc3333333fc9fcbf5fbff0000000000000000000000000097e315f4af8cafa57c6fffffffff97c2f17971000000000000000000000000008c7f0090090894accfe666666645814050285100000000000000000000000000ffffe31911f9fffffff5555555fd2a5916ce9f0000000000000000000000000000001ef7fffe0000000bbbbbbbbeddeffdbbff00000000000000000000000000f8843e20f211f107908f0f0f0f0878872391a200000000000000000000000000e043f81ec10fc0f6087ccccccc0760741a0c11
  | 0, 2 => 0x42528852454bfff80a4ffff000247ffffc08190000000000000000000000000017c205f02f082f8178422222220497c2f179710000000000000000000000000000620010018800800c41111111fc0040100811000000000000000000000000008c7f129599fc94accfefffffffff894954aadf00000000000000000000000000254a7fff09284692695ff22ff214fff853fe5500000000000000000000000000f885fe2ef217f17790bfcfcfcf0b78b72b95a200000000000000000000000000000000000000f7bffff77777777dbbdb77ffff00000000000000000000000000fcc63eb0fb19f587d8cf2f2f2f0cf9c773b9f3
  | 0, 3 => 0xffffffffffff18c88fc9999999fe4c6d9c8a9f00000000000000000000000000087e021111f80080084000000084004010081100000000000000000000000000004200100108008008400000000400401008110000000000000000000000000000001ce6ee860000000bbbbbbbbed5a6e9316000000000000000000000000000087e021111f810888fc1111111fc0849148a9f00000000000000000000000000ffffe5f82f09fffffff666666645b7d2f37d710000000000000000000000000017c2011001082f81784000000004024010481100000000000000000000000000f781fdeeee07ef77703eeeeeee03f7b6eb7560
  | 0, 4 => 0x214a7fff01284292295ff00ff0147ff813fe1500000000000000000000000000a56b61080000c6b66d7444444441221002440000000000000000000000000000ffffe7f93ff9fffffff7777777fdbfdbf7ffff00000000000000000000000000e83dfa0fd0f7d07e87bdddddddfb683d0e868e00000000000000000000000000f7a1fdeeee87084000088888888244248800000000000000000000000000000021087fffc0264212211ff88ff8127ffc0bfe0400000000000000000000000000465288d24d4bfff84a4ffff22224fffffc285900000000000000000000000000ffffffffffff0cc0484aaaaaaa86c564d82851
  | 0, 5 => 0x1ee7fef60000000bbbbbbbbaddafedb3ee0000000000000000000000000000001ce6ee060000000bbbbbbb3addafedb3ee0000000000000000000000000084631094898c84a44c6fffffffff8140502851000000000000000000000000008421108488848424442eeeeeeec78100402040000000000000000000000000000442009009080480484222222204814050285100000000000000000000000000f7a1e1080001ef77743444444441221002440000000000000000000000000000fffffffffffffffffffcccccccc366348a440000000000000000000000000000421088424443ffff723ffff66621ffffff7568
  | 0, 6 => 0xffffffffffff8c64442fffffffffc524c82040000000000000000000000000008c7f129599fc0480484aaaaaaa8681405028510000000000000000000000000000001a07d0f600000009999999ba482d0c828e0000000000000000000000000021087fff66224212211ff00ff0107ffeabff24000000000000000000000000009fff17f5bffcbfadffefffffffff9fcbf5fbff00000000000000000000000000ffffffffffff18c88fc8888888c6446498081100000000000000000000000000ffffe31911f9fffffff4444444c52250124c11000000000000000000000000008421108488848424442fffffffff890944a2ce
  | 0, 7 => 0xdeb58000fed7bd6dd6a00ff00feb8007ec01ea00000000000000000000000000000000000000f73ff7b777777779bb9b67f7ee00000000000000000000000000ffffffffffff2fc1784aaaaaaa86d7e6f9797100000000000000000000000000087e021111f810888fc0000000c0000000000000000000000000000000000000ffffe1180109fffffff4444444452250124c11000000000000000000000000007380ed6a66036b5330100000000076b6ab552000000000000000000000000000087e0010010810888fc00000004400401008110000000000000000000000000000001ce6ee060000000aaaaaaa02d5a6e93160
  | 0, 8 => 0xffffe1980909fffffff666666645a350526c510000000000000000000000000021087fffee264212211ffaaffa12fffeebff6400000000000000000000000000fffff39d99fdfffffffeeeeeeec7a350526c5100000000000000000000000000f8843e20f211f13790bf4f4f4f0978972395a200000000000000000000000000f7c3fdfeef0feff7787eeeeeee07f7f6fb7d7100000000000000000000000000178005e02e002f017002222222009782e1716000000000000000000000000000f884fe2af213f157909f0f0f0f0878b72b95a20000000000000000000000000021087fff00204212211ff22ff210fffa63ff64
  | 0, 9 => 0x84211ce6ee868424442fffffffffd5a6e93160000000000000000000000000008c7f1094898c94accfefffffffff814050285100000000000000000000000000fffffffffffffff80a4ffff888a67ffffc08190000000000000000000000000017c205f02f080880084000000004044090081100000000000000000000000000f781e5e82e01ef77703666666601b792e3756000000000000000000000000000000000000000d03e87b555555579281906868e000000000000000000000000007b9cef6b76737b5bb390000000007ebfafd7ae000000000000000000000000007bdeef7b777b7bdbbbd00000000076f6bb5d31
  | 0, 10 => 0xffffffffffff6b5330188888888276b6ab552000000000000000000000000000ffffffffffff3fc9ffcbbbbbbbfedfeffdfbff00000000000000000000000000ffffffffffff08c0084888888886446498081100000000000000000000000000ffffe5f82f0918c88fc000000044044090081100000000000000000000000000f7a1fdeeee87ef77743ffffffffff7b6eb75600000000000000000000000000084211a87d8f68424442fffffffffc92d4ca2ce0000000000000000000000000017c205f02f08efb7787666666605b7d2f37d7100000000000000000000000000178005e02e002f017002222222049782e17160
  | 0, 11 => 0xfffff5fcaf8dffffffffffffffffb7d2f37d7100000000000000000000000000000000000000000000033333333c99cb75bbff00000000000000000000000000fffff39d99fdffffffffffffffffab5956eedf00000000000000000000000000083c020110f010088781111111f8080904828e00000000000000000000000000ffffe95a454bfffffffffff444657ffffe4c1900000000000000000000000000ffffe1080001fffffff5555555792a1906c68e00000000000000000000000000fffff18c8885ffffffffffffffffa310426440000000000000000000000000000000000000000000000111111138080904828e
  | 0, 12 => 0xc67398d6cdcffffc4e6ffffffffffffffc285900000000000000000000000000fffff19c898dffffffffffffffffa350526c5100000000000000000000000000ffffffffffffef77703eeeeeee83f7b6eb756000000000000000000000000000ffffffffffff0840000aaaaaaa82d5a6e9316000000000000000000000000000ffffffffffff9ceccfefffffffffcd6ddcaadf00000000000000000000000000ffffffffffff8ce44c6fffffffffc564d828510000000000000000000000000017c205f02f082f017002222222009782e1716000000000000000000000000000ffffffffffff08c00c49999999fe4464980811
  | 0, 13 => 0xfffffffffffffffffffdddddddff6e7d9ece9f00000000000000000000000000ffffe5e82e01fffffff666666641b792e3756000000000000000000000000000883d120590f4902c87adddddddfb080904828e00000000000000000000000000ffffe30910f1fffffff5555555f92a1906c68e00000000000000000000000000fffffffffffffffffffeeeeeeec7f7f6fb7d7100000000000000000000000000fffffffffffffffffffcccccccc766749a4c1100000000000000000000000000e421f88ec887c476443fffffffffe1344a244000000000000000000000000000000000000000e737703666666601b392637560
  | 0, 14 => 0xe83de20910f1d07e87b5555555f9281906868e0000000000000000000000000077c2edfa6f0b6fd3785222222204f7f6fb7d71000000000000000000000000006000e80a4003405200100000000060340a040000000000000000000000000000ffffffffffff18488789999999fa4c2d8c828e0000000000000000000000000000001806c0060000000888888802402408000000000000000000000000000000f781fdeeee07ef77703ccccccc0366348a440000000000000000000000000000e83dfa0fd0f710488789999999fa482d0c828e0000000000000000000000000017c205f02f082f817840000000000600804000
  | 0, 15 => 0xffffffffffffffffffffffffffffffffffffff00000000000000000000000000fffffffffffffffffffffffffffff7f6fb7d7100000000000000000000000000ffffffffffffffffffffffffffffef7ddeeedf00000000000000000000000000681cea0b5073505a839000000000683d0e868e000000000000000000000000008c3d128598f4942cc7afffffffff890944a2ce00000000000000000000000000fffff90ec007fffffffccccccc4362340a440000000000000000000000000000fffff7fdbffdffffffffffffffffbfdbf7ffff00000000000000000000000000ffffffffffffffffffffffffffffe734ca6440
  | 1, 0 => 0x222222200918261316000000000000000000000000000e83dfa0fd0f7d07e87bcccccccc360340a04000000000000000000000000000000000c626602000000000000000054a6a9112000000000000000000000000000ffffffffffffafe57c6fffffffffd7e6f97971000000000000000000000000001ffe07f13ff83f89ffc2222222c497c2f1797100000000000000000000000000087e021111f8d0be8ff5555555fd2859168e9f0000000000000000000000000097a115e4ae84af25742fffffffff9782e171600000000000000000000000000000000a0350720000000000000000482d0c828e
  | 1, 1 => 0xf781fdeeee072f41700aaaaaaa02d7a6e9716000000000000000000000000000978115e4ae04af25702eeeeeee039782e17160
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 138 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 138 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 138 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 138 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 8 0) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 8 0) :: stateWiresS n (ids >>> 8)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 7 => 25
  | 8 => 460
  | 9 => 1987
  | 10 => 807
  | 11 => 35
  | _ => 0
def CH : Nat → Nat → Nat
  | 7, 0 => 0xfcae6e95d7462cb7bcb4c7f3b529bcaaa632bb22a519e6fd97c535848d8742c88bd4bd698128daef7569058d677da47663a371265e2aaabd5dbbf1895a2d61c64e5d1c034913f240459dd8a735ddc85b289a8443214e3f3c17cd0076162a616e13b3df04
  | 8, 0 => 0x166384991628220315cf52aa158f7702157fec9c157c649415419603152f5e61150cd8a01501c66314593fa1133259c612fcbf151285b42e12372597120ab8ff115d7a3e1127696310cb1b00107adce3103a2c71100f47ba0f558d940e590b2c0e5583240e3a43660df359650ddce76a0dc763e80d4acc9e0cd104d30cc17e670c63c5f40baa939b0b4107050b27bcb20adbfcaa0abc35a909af8a3f096010e608fc714d0881c649082716e6081c99a007dc1ce207ccd6d507b502f807b0db6a0755cbee073f93fd0739876c07363a240672252a05a96e44058407ae04bffe9d0459c0d7044b6bba0396382202cce6e802cb908d02c14c3c029f079b02388676
  | 8, 1 => 0x2aa69a9a2a9b6e0929fe55f928e2f48028ce24b427fe9327278d491b27689af126f5ab83267a5c6a2671283e2633530725f2958c254c5195254650232435059b23c04aaf237fa5682355285e22b7bb4122964b262252fc8b2223643221cc69d6211ee964211196d720ff3aea209a667d20717e4320255b261f8927e11f6f8d2a1f6d511d1f5724ec1ec446db1e2b24ff1d97fa561d8bfa6c1d126fee1c6fe8491c3c69ae1c11a6ae1bf4f0711bcf1d1c1bc5c3431ba57e741b9751471b46359a1b394a901b2e81531a8b0c281a8784201a4863851a456b6b1a1d0e5a19995efb194c898e192341a5186963031849b7d4182c01d6181b60e81750d55b16f2450c
  | 8, 2 => 0x44e6950944e3e3f344cf178444c19c2843a3ec7142e193f5427f8c2e418abedb417e9f0e406d88b53fb6af5b3f68f4b93f392d423f2efe893e1c92ca3daf45ac3d68cc8c3cc6890a3c3768cf3c2f59a83c01318f3b9eb7eb3b4075b83ae5fea03ad9dd0a3a36c7db3a30446b3a0cd7b73a03c73c39f7059639f37d8e39e695e639d5d942399f2f44389afbd838540c3237ed70e8372190ef3714d63f368ba199366f75df364eb6ce360001b6358ec409350107623422fbd0341c8b0833ff16493323e1cc32bc966a31f1fb9231a1f90d30d2d5ed30d1494f2fc8d3af2f4a4f912f33f51c2f1422892cf8dd862cf5557e2c3974102b50a9772b2ea00a2b27263c
  | 8, 3 => 0x5e3126495e21a5125e06409b5cc279825c435a155c2da1c25baeb87d5ba5f3c75a6ff4bd5a4a8c8559b2eeed5978d12559761e28592ae95d591abb0e58dd9a96582c66e657e90a8957e0fb1c56807d5a556b062d55677e2555024d2054cd8fbd53f87dd853e26d2f53d5801e53afa68352d80a6e52d53ed55289d8ce523d04f7523ad47c516a0fc65163ce1e51248dad50d3cdbb4fcffed74f98bafd4f3ade694f1ce9bd4ea97c884e8306ad4dd4b2124da3b1a44da1d2af4d9e4aa74d84eb524d5612a74d557edf4d3251294ab1798f4aa12ce34a8b5f7649b1029c4965c135489d561147fc6fa547fb787c47f6714a46fa7949459d5f1a455ac84145167e26
  | 8, 4 => 0x793ff77c7938428477b80ffb76d9723976a668fa76222e9b75dfbedb74c1be7f7493cea274394cef73dd9b2f72dd282c7296ade771ede41270fec43e70d2e3346f678f9e6f52cb8e6f4801236f2ef3426efa4fc86ea2c2446e8741416e4b44256e39827d6e0fdfc36e085a446dadb5b86d7bcbd56d1584066cf08e386c3799506bcb2aab6aa845786a38419769fd67cc695aada868d090da67e656c367e1975a67936ef4675fba7d674e0038662a2cc765be6f2364a063476447767163ca678863b6fcaf639abba3635b86d4633aad0f62a1055462312f0c61e59bc661ab44ff61a6043260d7d0f15f3c17875f2866185f2133c15f04329a5edf8ec35ea0f007
  | 8, 5 => 0xa40ab944a37094d4a2b5d759a2ac4b5da270cc49a2389870a158b1cc9e33c4249e0418659ddc44779dc27cb79d34c0109cc374959b8ee60e98b10c629851c86c97a1b239977a13ba975ec9a4965b665c94dea2b5940394be93fd4ac49354a9e892e6de9192d5d81890bd4c458ff618308ff3d8038e03ca4c8df8f3dc8df582a78da90f518bd013d18b50c41b8a9e3e8689d2c334898696b989748f468804521287a5c8228752e05385d0495f84feba5284aca1598445c4fb831cd53082fac8e782c90b9c81b3433f816ab65e815d7f2a810fa71b8093253e7ee0a5207e5683497dba8bb57cd6dd827bba7f537b6565267b37c58e7a9777de79d9492479c6283f
  | 8, 6 => 0xdacb347bda167bf1d92e03bdd8d8de61d7cd04f0d6c2efd2d4d6bf5ed4647217d3bb8e70d185a718d0a5aefccead5366ce054f7dccf25e99cc88d239cbe25611cb957823ca717c99ca283429c5e24193c5287f10c4c77d0ec3852457c2d4f4b9c1a9dfb3c1925951c136dd55c047363fbee4a8e3becdc382bd81ee16bb9583adbadfd497ba96f736b98f1633b8c4735cb8bac2c7b861f9b8b8001df3b73b55a1b6b04e5db6672017b66119f7b5174dffb4511a8fb2576504b25205d6b040ba61aed5f4c0adc33babad86652babb374bcab64ef11ab3737d7ab3131b7aa53e12da963ac64a943d778a93400a5a65d244ba632a72ca58fbabea54edfd1a485c9e0
  | 8, 7 => 0xffe7fd86fef73d86f43181fdf185004ceb5cb926eb2314f6e88e6684e62898d9e5379699e2bb064fdcb58f58dbbe4f89
  | 9, 0 => 0x42293cb0407366b03be1d5603ba503303b4188b03b3362e03a2a56f03945c14034027a7033f76d6032a5efd0329ee68032829e4030932660302539c030032f902fec78202f84cff02f591d402e2027c02cac33d02c140aa0297ddda027d2aa4026b1ddf02647efb024242e3022b6cec020d737d01ec857e01cecd6701be398601bb2c4a01b2012701aca8ac01853c1f017cb78101679d3f0166ce43016533e9014e09fc013ffaf7012e4d1a01017fef00e9bf5a00e898d400e5df1400df811200d4256700d3d46400cc627100ba8ea500b401d100aeefe1009ebde6008cbec50079639a006c458200542966005308ca0046e59c00208da9001d1dfa00134cab
  | 9, 1 => 0x989a32c09857a0b09800247097c7a3f0978938b0912318609059ac308fbe68508d7d9a508c07af308ba40f908ae9bf708ad4f0408a9cb60089ecb9208680c5608554f0708341137080e5af40805c2b107ee4ad607c5076207b9b8fd079b4c9e07787420075baf5c0759c0b7074d9128073bc7cc072311c4071e1d3e071a953606ad3c6806a2828906959b8106912e77064ba7b0061657ee05f8240105f16c3905e1336c05c4741105a1437f059cc516058af995056d2c76052eec16051dccdc0519858d0510cde604e19af904e0b1cc04ce463904c0a81104bd200904b9dd8b04aec3da04ae1ead049b4e20049460f60493befd047ae151045a1bd60427f1f3
  | 9, 2 => 0xd105e8f0d0abdb10cf9e91b0cb29a690cae88780cad06da0c7df23c0c7ac0070c70f2710c4eeb550c4326760c4111bb0c19a79a0c12aedd0c0f26d50bf02cb10becc40d0bded8210bd417490bce22060bc01dcc0b999c320b9729cf0b96e4de0b935cd60b6552470b62700a0b48a6370b4334eb0b427b4f0b316bde0b312aa00b0df76c0aff0c430af07f990ada90fe0ad963150ad946790a92444f0a88746d0a7d39c30a6920cf0a671dda0a64ee330a5d5e470a5b60720a4131b40a3ebf630a3c8ee80a39faae0a368ecb0a219e4c0a16d39c0a1297480a0f7d480a0f46d40a079cd009e1673b09bb601b09b5e5c209b00b4609a48f63099b436309972153
  | 9, 3 => 0x1218fdce1218cbc712076b3a11f58bcd11da504e11d05b7f11ccd37711c4df2611b77b7211a9c986116ab7731147cc87113a6c89112444ce11171d4f110b554b1100704f10fcd1c610edeeca10dc65ed10c1ef3d109e0da110836166107365b910662b6b1053d76110323a5810197f020fe29ee00fe1ecfa0fc3a73d0fc28aff0f8159a70f6d17a00f6c48f70f67daed0f4bf0330f40c5c40f3441fc0f264bbb0f1b11d30f10da4c0eec68ee0ed875a00e6bc4b20e6ae1990e635bf90e5ae6310e572cb60e4671110e3110bf0e0b6f530df128ea0de7c6c70db228970daf435f0d9b061f0d7a80d40d6b43680d64b5af0d4e6eee0d3ceb900d17f8cc0d16b4bf
  | 9, 4 => 0x1773206117730eb6176d946c1766f80f1764326b172ff67c16c7320216c7120f1653815c164967cc163c9a28163ac5e81618fd611610aba7160a793e1604554b15eb5fa7159b6b07158b48b21583738b157b66f715756c6915671478154f5a8a153f658815302c7c14f73d7214f0687814ec9eef14b82f4914aab5ba14a12fbd145e4435143d746f1437b37e142fa36a1428e86d13db00c113cd31fa13cac27b13abf14c139db282138612321368adb11363e13313556fba12f9164a12f79f1612d3b82312ce8b3c12b988ac12af018112994ff51296924a129536b11278a444127698ae12654ef71253345a1244f88312415601123883d51236b6d81230af42
  | 9, 5 => 0x1c1e85861be6627d1bbc0f8a1bb8b71b1bb349a61b9613ab1b8b8a2c1b3f0f831b3cc5871b3a0ffb1b20b7961b17d6cb1aef2c501acdb9501ac16df01abc1fc11aba55c71aa707c21a9b980d1a955ea51a7899801a6fa04a1a6c68bf1a6b96c51a692aca1a642a3c1a3891e31a33f1581a04b48519e79f2e19e15c06199ac9d91954cbeb194e5a93193b57931917af0718edaeb418e4ba8c18ccfb0718b4a9d118a18783189b2ba81894e6f818949def187772c21866b959184da675184cfa2a18469cff1844c2f5183585561834ebe4182f4dae182dd68618284083181640e91813cadc180cfdd117dcc72317b09785178825971787d61e17849d8f1782de4b
  | 9, 6 => 0x210cf99920f4416120edbe7920ac7451206c5e44204c7b2420308ec62022e5f5200c0d751ffac9661fede8c81fd9d2ad1fd82f561fd66ad21fb773541fad8fbd1f93daab1f8008b81f73b5e21f71eb001f715db61f6d511d1f634d6c1f55c6211f48ada41f2b6b921ef6a6f91eeb15441edbd98c1ecabc191ebbb46b1eb913c31e8c86c21e885a111e84d2091e7837521e6b0cb81e675ed41e3f94651e32a7761e30136d1e2ec29c1e2af86f1e1d830d1e1b1f2a1df864281dd59fa01dccc5121dc938351da77cd91d7b5aaf1d69605e1d5456261d53e60f1d3e25161cee12e31cd054471cb884b11cb7ce731ca6bd4b1c8d89b11c6a54c91c5eae881c2bd765
  | 9, 7 => 0x273ef7d1270afb49270770e5270700b826f08b8426d481a226c5148a26c1e8e826bbfd6a268776c1266cadc7266c90ab26509fd6263f01ce262e33082627b74825f1291225c843a725c52bc025983816258ff96e2581e672257a3f482573cc14256bb7b5254a6af42546e76b2545bdda253473a725164d4424f7cdbe24e3608024db72c424bc937924af03ec249648f8246ea5b5245cebdd24495d39242cd5a42414a2cc240c5d502401dc6123fbd21623e4caad23b34dca2344fdf9231e359d2317c8e022eba3d522e07fc522d9a27122cc8d9222c0cd9322b7be5e22a049e6224b060421c7109d219cd5eb218ece432177c70521556e982151e69021422388
  | 9, 8 => 0x2cf9da4c2cf133692cc50e752cbb582d2cb8f6342c902de82c7383012c6b54832c4096882c0e5cb42bfb06822bc799db2bc08ca22bb885b22b89d9562b86b68e2b7df7992b601b022b56563d2b52ce352b4746242b0817962aff0f9f2afda9992aca03862ac9b6ef2aaff0f82a85ae612a63d2cc2a6069852a5de0142a42a8292a268f392a04a4c82a03e45929ef535929ebcb5129ceeea729c5e00729c5050829b1141729ad23b929a58bd72997891b296f7ca52958ef56292c332a28d50f5f28ccfd8e28a39abe286e0d56286cc06328693cbf284774fc283e390f283285a12801c49c27f175d927cfca0627bc385a27889f69276341422743034827408817
  | 9, 9 => 0x322cf33b320469e23202823431f1d12831eda67631de1b3731c6dc9931c0a843319553523138d8583121aac3311dc675310e96a03105501430dde45830d0be9030bfe1ae30bbd81c30a9fd7630763a6130743947306adebc3042d2c5302280b23001ce432ff658cb2fd3e3fc2f7043162f68cb162f67de0d2f5d426f2f50f70f2f41922c2f40cb062f3495922f2bba562f24e7c42f186b272f1422892f1157a72f08229f2eed66742ee588912ed07e592ec73ebc2eb4c1a52ead7a412e9ba36e2e8c5a5d2e82b7e92e74e6392e4c7c7a2e2d6b192de810ef2dde3f772dcc66ff2da7ff982d8bcd862d7d37d32d79e0dc2d2f71d92d2c59062d23b1c12d06fbe1
  | 9, 10 => 0x36d85e3f36cde06c36b69ece36addfd9369247af369003423671f1d736528091363516a9362d91d93624ecbe3622b0a53612f2bb3612712b360bfb5d35e9988135ddb4f235d24cad35c1f6f0359ab467357b3bf5354c7cb835452ada3542e4ea35404634352c981c3508c4973505dee934fbe76334cd8a0034ca02b034b54dee3482825b345ca7f8345a1c16343e0afd34214fa4340fa0e433fce5ce33f085c633d7542133a51b30339842af338f9f68337c0e07337552fd335a4538334965e6332f3c4b3321184c331e1eb932f9a4be32be4bbb32b887a932952add32932982328f3a0a327b631d3264103b3258c1543255008b325446c4324339fc32316537
  | 9, 11 => 0x3daa83753d9bff673d98fca23d75b0203d540d043d17fbe13d0bb3013cf9eac73ce7d6993ce5a7103cd27e703ccef6683c8ac2213c873a193c61719b3c3bebe93bf691a83bd1f4973bb828b43b91c2933b8a1a7a3b62bb923b26410b3b2398053b200e933b04e1ca3af05aa93a8d2aaf3a818f0e3a7c99e63a57007f3a380adf3a27876439cb8bae39c864113999c216393104a338fcd6cc38b9850e38ad2013388a7599387b2d8f387453cc3871d3b6384675d238445499384273bc3836e4213806806537f4f6b537ccc80937af7b3a37a3df7b3781245e376ebdbf3756b591372b40b8371d90e73714604937126b2a370bc93a3709f12636f6677b36f2d9f4
  | 9, 12 => 0x44efcd2644d35fb344d070d14459d8f84432c9e044145efb440b623d43e1178b43da663f43a43c0c431e18b242e5718242c48d4c42c1f71942a31ed64299e670428bb2a94272b7e242682e4f425bf01e4238004f4232fbfa422e3b8a4215fceb41f3a90f41e1247e41d575d941befaf841a21ea3419c9e63418ff3c04189636b41855da641680036415c474a41500c2f413be39d413a8b13410dcf2340fba66340c2e3ba40bb9ea8406c5b224039d6c5402bcfa33fefccf23fedf4df3fa80c013f6df33d3f4709483f332c2c3f13b9a43f0995673f05b3be3ee5b7d43ead956c3ea7482c3ea1af033e6b099c3e582dc43e558ae33dec8b5f3dda90893db58e1d
  | 9, 13 => 0x4c0dca7d4bacf52b4b89761b4b83d9644b8263134b81952e4b5bd9d54b5a534f4b1f8c614b1aa7804ac08d084a9d0af14a9a1a324a9077af4a8e845c4a57f0e64a3e81494a31cae649e0e1fd49d1a2b749d0346549c3b1f749a6005e49711ee849627b594957d870492bfd8948fff20548bc9da248bc8d08489a1012484c612f4834a44f4817bed9480e6fe24804972b47f0ab5847ad75af47937ce1478955fb47765a224739197b4715f182470aec3c4705078b46fd772646f8120946f48796467d2f954653ccc5464d3ed646462ae3463a7eb84607578745fb097445eda46745d6444945a835a3456c8a9e456487d44559aea2454c997b45246a3e4503ae2d
  | 9, 14 => 0x527a3fc9526e0ab9525c9ab7523ad47c522e4b895216574351badbc151ad17d551a68c1b519b7e1151965b8e514b20b050f4f77e50dd37d450bf5b8650ab26bc5074263a502a501b5029bd9f502151e550148e7e5007471f4ff040284fdcdde24fcf593a4fa2d4dc4f98bafd4f8fc5674f5f26f94f3cd6284f10a5004f0975ee4f0702424ed191694ea23ffc4e75a4504e751d874e4e09804e443b134e4229484e28cc9d4e0bf5e74df896324de3f33d4dcdfc4f4dab81db4d8bd85e4d7d59c24d62e43a4d4f46554d4e30ad4d41cddb4d1ae01e4d16e77e4d110cbe4cfda2ad4ceee3384cc189ae4cb94bab4cb0a4c84c9021054c8329074c26072f4c1a1e90
  | 9, 15 => 0x594b245f592d37b659299de2592147af591d4a1c59104327590fb28958f0bb2858eda54658c8b3b2587651705870a0aa57dea48657acc1d0578bbcb7578b9800576bf1f75766805c5751eae8574a7e5156b24b5356a9e85056a7e7755692a6595681e9b55653867a564b3fb7564032d15629d536560c85e555fbbff155f095a055a8e73f5599608a55807fac554cacf15535006555001ca554efd43c54ec6f5754d5f81f54ad560c54963da1546ddd8054244c8154093de153fc527753eee01553dc793f53d6926753bf5e2753b223ad539adb5553790280536fd14253648c8f5323ef72531626d752fac74152e848be52e7b6e352dbd2c752c133a952835e72
  | 9, 16 => 0x615f961a615aa11d6141786360f3f2c960eda24260d50e5260ba8a69609911f0605dd85d605965dd60527cfa604b514c602ad9ef5fef153f5fc2a6a65f9a59555f6e82575f677d605f4b19515f35c53f5f0585f65ec469d55eb7b37d5e989b835e94d94c5e851b625e79cae05e6e2e755e179f235e0a88385da9c2805d91819a5d52d8195d23533c5d15ae0a5d0c02495d059e4e5ce8bcbd5ce62c175cde896e5cce65ef5cadc4395ca5186f5c84e5e55c62bfce5c5449ff5bfabe6c5bcc3fc15ba833495b96ab515b879b285b2ebfce5b1a84a75af3bd295ac53af55a711fdc5a6cbe685a45fdfd59f410f359d2283c59a58c9059a324a75972997d595ff9f0
  | 9, 17 => 0x6840717c6807ea4867d4f5e267cdcd4f67ab0f7167a4bf37679081236784833f67773ca4677602d967405ca467355b0666ddbc6966dd6c0966b783686672dea8665c772e65e1cbcf65a133ae657da0bb6567a702655e95626549668465468d34653b865a6535a93b6523f933652153a564f52ab364e41b1764c31f8c64a4179d649f5742648fe230646d93c264670c2e64490142643cf2d26417491e63d1763a63c4327063b4c2d363a2869d63a088ea637b9e506370a989635b5c00630d4dde62dfc41c62d3c43262d2ac3062bf814a629be55562936c9162406dcb62279fae6221c3c16207d52161e46f1b61c65ae661a06311617d90ee6167341b6164bc3f
  | 9, 18 => 0x6ff80cdb6fe337cf6fd3a36c6f96f46e6f8eca996f847ff06f841ae16f8149d66f3d6aa06f3b73b26f0c4edc6efc47876ee6f1836ec34b496e8b44406e6214ab6e358f806e03ac726d8b78c26d84e9a46d8044476d3767796d2c18266d13289c6d12d3846cfded226c8f7e5a6c7c0f4a6c6fe55c6c343a1e6bf634f46bf6097b6bc8fa306b7b398c6b7770e96b5da7166b2f17206ad70d8b6acb433d6ac74c926ac1cf9d6abb1c2c6aa7452e6aa743e96aa6d80e6a988cba6a765dae6a4be7b86a4afdf36a1d236e699faf6c699e6631698fa5c469709ff769678c9969460163691ac9026912047d69087e3368dbfe6168d1faca688e4be4684ee746684808c0
  | 9, 19 => 0x7828cbbb7802055b780087bb77261d347725f1bb76b1b7e476a148fb767fd6d776756fe6764bd8107637993376222e9b7612130075d8da1175cac08975c990a875964aa2753ff10b753af1f474c7b8f774af459b7480dc21744cb45d74386673742360dc741d2d877404431073f7576e73dcee3c73bac65273af872c7375b534733e034d7304de2272e35c4e72da1cd572a7ba1d72997d6272985ea77276945772536cc67224c758721ec13871e8b10d71e82e6d71d4798a71bba829716f0671715ec2d37145aef57142472f713c281f7136a074711baf2570eefc3670e2028370cfb6a770cdef5770cdd9e170b468dd70a48e4b707ecce5705bb6f6700bd10a
  | 9, 20 => 0x7f0584b07edb85217ed5e09c7e9aaf317e91ac397e71bb997e3ff94e7e3e7e3d7e38b64f7e0271df7db8d0f27da057087d9f2c967d80d9d97d7dd0727d59b3bf7d3bc2097d1816ad7d06b2f67cf0b1cc7c7f28377c5a86ea7c2b4a537c11eac37be4062d7bdacc207bc726267b7a1adb7b67a4a87b640ceb7b4c4cc97b1608597b0f287e7b0da9637b09a4997b038bac7af387457ae134a37ab64eb07aa4f92f7a323a977a2f83937a2cca047a1a497079cb0f7979bed71a79aeb7ee79a556b579a4ec7c799c88c8795ac0e07953595d792ee0617920e76a78f56ec778ede30278b02c87789da4e5786b2a237869ebc37861048d78357c1d7833e341782dd562
  | 9, 21 => 0x8789669e875870c58743f49e872830008712e71386f9d09886f93ee186f70e6686da156986bad62a8699f65b867031ec863de6b285b0f0db85a8195085a13d2e859cb86e84eebf5a84d20b6684cceddb84a38c76849881bc846dc9f9845ec8a1845662c88429c12584267d8d84255707840b70ff83be0c1183bad3ce8390e7998383a3cf831acd5f82ccbf3d8268336d825926608215e7f08203b27781fab16f81bce13981bb6b6481b29c9c816016fb815be733811f0779811bd4b08116983280d2624c8087b4d580815f23807c55c5807677fb80661f75805f3e168050a9c980508349801eea77801c41d680054e927f9c307a7f8934c37f3b47f47f2ccede
  | 9, 22 => 0x903aac798ff298fd8fb77e3a8fb1e94d8f885dc38f55fb0b8f40bb358f2a121b8f28e2e38efcdbff8e96754b8e3902778da519d98d9d3d248d8e4b768d7ef3a78d62a9cb8d445b038d2d0dd38d123d478cecc9798ce18d598cc5053c8cb78bad8ca52ec78c8971c58c7fb3df8c40239e8c37f7908c13a0118bd1ee6d8bc087168baa88758b961fde8b77f0608b49d2848b401fe88b084c208ac722528ab7de1b8ab46ab78ab18bb68a8144258a7898f28a10059689ef31d889cb188e89bc4ea2897e2d8e897cafee89772d0788f78c1c88bd2e7f889b6fc088936580886baa49886b915d883f104b883b1765882c50c0880d184c87fbff0a879a3f1c878e8104
  | 9, 23 => 0x992d96969921f0559918013b98d0f49298cf088698b94a4498768b7398623c649859557898474f8497fa8db797f4ed7c97e773ed97d5170797c4494797446ce496c88a5e96c75dfb96933b96965fca07964225bb963f7d69963639c696180db8960b3b3296057b9e95fe996095f70a92956aba0c953665ff9510e842950d0fcc94de272494d9740f944ecc3d9434c1eb93c70c8093bdb2da938ddd68936ef88b934ea4809339b99d93379ee092e70cd292e6de9192cfe59292c9629c929a619e928bcf4e925ec894924e8a7f92448b90922ec1d691cc729891bdb26e91a79fcc91a01a2c9193eae9915d868990ac63da90a173e2908b2d21908012a3905ccd53
  | 9, 24 => 0xa30be592a286e23ba2530c6da23f448fa1db081aa1a52638a17a5ca8a16f65a9a158b1cca1471905a0f1f616a0d7e499a0d397f5a0d159d8a051747ca04cf883a040d082a01038ea9fc90e4d9f7b002b9f751c0f9f4458f19f415ad39f1e6dbb9f0e07e09f07674e9ea15ed29e9a4da19e923de19e3efcf49e2651c09dcd48679d87153b9d78f1589d62911a9d5b747c9d3bcc2b9d1248119cda8cff9c6d66cd9c6ab1ff9c3f530a9c3ea96c9bd0cd3c9bcb61e59ba3778c9b6a94b99b46a9ce9b2b0b909b25d36c9ae2e6749adf5e6c9aabbf8e9aa91df19a9810a99a8c7a029a73b44f9a4e97f69a19764199adcc9399a23992999ffd799977841b9944f1f9
  | 9, 25 => 0xae55e0baae422bd7ae3bcdd2ae32fb51ae31c2b1ae172e2fadafe126ad9261afad7a0636ad305928ad061492acbc19b2aca918aaaca5455dac697debac65bf28ac20ad48abeefc23abe058f1abb1f123ab7ff875ab382806ab10c9b5aafd43f7aaef5326aa9c0ffdaa6270fda9f29bf1a9c377b7a97bc001a9732ee7a9354d95a8f418eaa8c9e64fa883a59ea8428216a8212d88a7b016b4a7548b58a72f1199a72188e0a697877aa668cda4a63a03aba632a72ca604485da60443f1a5f99ad3a5f004b6a5be2c0ba58f1c96a5314f23a52860afa52670efa50f9bc2a4b5e1d0a468bc1ea435096ca3f2358ca3e93284a36829b1a3633dbaa33c556da32fef94
  | 9, 26 => 0xba4beb61ba2c13a3b9f91abcb9a97456b961aaf1b8d7729ab8ac95bbb850fbd8b835fcd2b82aa2e0b7f2c6d9b7e982d8b7ddfd77b799662bb72d43f9b70be2f1b6e1d963b6d0465eb69373abb6900371b68ecd7bb663b58fb61f3b66b614a5f0b5d77f17b5d10117b59735d6b560e2f7b51888f4b4f3f1d4b4780759b4217b74b41aa28bb3ce2b82b3c4fea7b39e45e3b3912239b38493f3b37121a6b353450fb33f4c09b2f684dbb2c2f9e7b2920a2fb20626b7b203fcefb183b314b0ef4f3db0bf1aafb09a96feb0856fecb04caa2bb03f8402afe6c807afe45a19af802cabaf5b7895af1c0321af0b1556af033d6eaefc551baeb512f5ae8a1e66ae56b532
  | 9, 27 => 0xc7482070c6ba2989c6701a07c653ee4bc6317ca3c5f42f8cc5bdba9fc55df08dc556b6d6c53fd164c4d95c96c426f483c41b8584c3cfc9cec322af19c310fe52c30a928bc2c19225c28d83a2c282d2cac25764adc246539ac211ed22c1e83c9ec1bfe247c1874c6bc1812730c13278e9c092fadec090cb37c04f2ee8c0487134c02494ccbfed5a77bf5754f5bf3f63debf04e7fcbef4e6e7bee4a8e3bee0b36bbe9c2e3dbe51af40be1f8917bdff256abd95980dbd858111bcef1170bceaac5cbcdd46c4bcd64bf4bccf2e50bc3f9fd3bc31350abc183830bbde9930bb896f3bbadfd497bacf4916bab175c8bab028d8baa64093ba9dd256ba98acbaba88ee4d
  | 9, 28 => 0xd5e52673d5ad445ad52c9314d51bee24d4b501d1d4b31560d4ac2e66d457dbf1d3db84e7d3d38ce0d3be9a24d3440552d3199c15d312b66ed30fc602d287763ed2723795d1c35e72d115b8b2d0e78e4ed07e8c0ecfc0a03fcf986df3cf56dcc3cf11c040cefe1649cef3806bceb4ae16ce9e6aebce5dcc08cd6b4365cd6185a8cd5fb4abcd5c5136cd4fea0dccefca87ccba2bffcc5cdb62cc228640cc14d4edcb12d273cad03b14cacc1c0aca34d03cca262607c9b22505c998a3fac9705bd9c8fa98f3c89ea079c891d241c88e99dfc88957aec871f580c8406c60c82e3963c80d2f04c7e9b3d5c7e3484ac7e2ce2ec7dd422ac7a6811fc79054eec76f8813
  | 9, 29 => 0xe62f3d93e537989ce4ce39abe3a2d85de37eb0b2e2c5618fe27a2013e26d849ee1dae9cee1c9f324e1bd4622e1b0c2e1e19656a2e17d4ba0e16e6fe5e0527795e0526c3de0257af0dfd4827fdf8921a9df72a9ffdf64999cdecab5eade86f16dde6bf2bade62f296dddf7841ddc9cba3ddacd067dd39fe00dcf8bc2cdcd6a9ebdcd2d5badc7c90fcdc41d699dc2d795bdb65f9b0db4b1041db28add7dafff02edadae0f0dac85633d9b1c168d99fef4fd969aadfd8c448a3d8b83ec8d86debf6d7ea143fd7ca0131d746f3abd7300035d7125be9d6f62ee6d6bbf997d69a0ae4d6956a09d66b10d5d652e50ad643a541d61406bdd60dafc6d604e836d5edf1a8
  | 9, 30 => 0xfd2f88f8fd00ef26fcb659c5fc9f3d29fc91a772fbdb74e6fbcba1c5fb729a49fb40b071fb2fbaf1faf8a01afa8479a1f9db587af9da3a0bf9b62e8ef94af911f8c98be8f818cf20f7d1eafff6ef7194f5cbd753f5c85dbff5038de9f4be14e5f392fe3ff3461b57f23e2800f182cfd1f0fba840f0679ee3f0421153f0308079effb4252efc81fefef7e215beee8c520eed80133ee31b78bed8d9675ed5d018aec9741aaec520c66ec1f66c2eba6fbfbeb7c10bceb4e860deb42e63aeb3f9d32eb2de99bead596edeaadda30ea771d6ce9b392bee980472ce952c027e93522f9e8cd3027e8a89af7e88e6684e83e7b59e7bd1094e7b1d543e779b105e6312a04
  | 9, 31 => 0xfe4662ccfe0ac8d7fdd9d9ff
  | 10, 0 => 0xb0f8a110ae548740aaf04040a95275e0a7be0d60a70e7430a21265c09fc6a6f09f3d85a09ca758a09b3451b09059ac308ba29fc087d84c6086fc085086b99c708653b3a07c2a8a107a296a4076d005d07447ff3073adc15072f7abd06a43b6d065be3c30653a07705e96d7b05d894fd05bbd60f051d073404d8ecb6048d7a010445bdb2043db1e8043a303c0435c23203fd143b03e0a4a703ba503303ad423e03a77e12035e4a09031afb1102fef80402f1640d027ded340265e50602392aad0226f07c02249e55020fc7dd01f7e10701df342d01de45d40175eaae015a34d800f681fc00f59e2700d047e800cd1f2c00b401d1008d6f200030574f00168d7c
  | 10, 1 => 0x1718ed4916d2917916bf462d168d98f916039e2915f7098415deabd9156b84ce1557266d153a4589153a38d9152f5e61152816f81523c09a14db66f614bf707e14bb9f0914a6169b14a4521714855a99147cb3cb13f9352713dd187013bf793813be6b1613899bb01368adb1135a6e071355963f12f8dfb412c64b6d129a177c125cd2811217f33111e70352117e367a11568fa511363b3110f7188410780a901061c3cf103832730fe707450fac6dab0f9ba0950f567b570ee869f90ee0db5b0ebf07290e40cb210ddabd460dc88bdb0dbf4c220d7c98e10d6912ed0d34a09e0ce1b2210c8b84200c55bd630c3714eb0c2c5a930c266a3c0c13100b0b5d058c
  | 10, 2 => 0x25abcb9d25a510a0257f4bfb24fddff82489320a242b29b42401c6e423f9a19b239d68f3239526012294ce2e226a16fd226190d2218ef5022180f509216511af215e152d2152e946213fcf702134b25d211f58c120549dd3203a6f8d2038db43202b3b03202428cc1fd5fedb1fbbba111f6d511d1f2e50ca1f1a6b841f18e0541f172e521f0e13741ecc1ac61e120a131dfa1a6f1d95cfcd1d5b00541d49e9221cbf5d1e1c9c76dd1c8a1f9f1c6e0f2d1c38bdcb1c1ad27d1be116661bd575081bbd59e71bb2b6fe1bab808e1b92fbcf1b176b961aea70b41a8e59b91a13a51f19becf6c191774d118c9b95b18a0568b18509b3d183fc2bf181eaabc1785a5a3
  | 10, 3 => 0x34c8be9434973052347fa364347118e1345ca7f83433e691334218b3328162fe3206e34931154e43305801bf300e28c12fa059c42f748c5b2f5b11f42f4560682ed49e4b2ed07e592e324fdb2dedbea82de67cfc2ddad6bb2d6f5e032d3919932d2f71d92d123bde2cd849912cba36572c942f132c8dfd6d2c3d5aaa2be0526f2b8486132b74955c2b51363e2b33c6542b22edd62b16f20c2ad0f41e2ac364e52ab77fc62a9a0e4e2a93d73a2a6f83cd2a49233a2a10c62229c9cea829c2c53229a06bd828ef36e928433a4227e5d58027a26f462786a171272437a7270770e526f4d51d26c0438726bb8dbb2698f7ec2681ab2a26509fd6262d646c25e85f98
  | 10, 4 => 0x4429518a440f51b543f0410743d4e98743cab10643809215436df95b434304cc43311a7542f726aa42c4851c423c09e141befaf841a2f5e3418f70f340ac669b40a7e2893ffb2b7a3ff10e6c3eb83e1b3e92c34e3e63fc453e5f8a973e45dd163e3c88d63dee33fb3d8a84e73cd27e703ccef6683c843fc93c48e4fb3c3a84a33c2c192b3c01d6943bdf13a93ba2b76c3b87a8ad3b4b16da3b21b40a3af9ea6f3aeba4d839f0797839ea358939e8e89639e564f23940cfdc3919be643902a5d43851e57237e8d5fa37ccc80936f05fcc36e69ca436c132ed36b334df3681db293680940a36498ec73590caff355dde03353f3278353dde9934fbfbf034f9b6e8
  | 10, 5 => 0x51777101510e899c50ea1b70507bb2185076ec8a4f6a5c2e4f56b8bc4f472bec4f1e44a24f10e77c4f04d1c74e4e73614e46416b4e1528934ddd99ce4da3a1f54d5dc16d4ceee3384ca2693e4c7aa9154c0d283b4c0952e24bb433124b4a0daa4b47f9304b47b3e14a90657d4a8c0a0e4a2948464a26b7064a1943a049d38ae349b30c5449b0c9fb49711ee8493ad02e490bc0b948eec71748e908eb48da9b1e484a089f4832c701482a080c48240210480c2b754803551147df270747c02d8147abe9ab47a9ba0c47a6603a478f1aee475ece1f4710830446bf0d1d467aff1a45ec93a545cb193645a4d75645790e01455db02f449d407f4434afdc442b78d5
  | 10, 6 => 0x5f7f90c55f7997995f7123b75f29895f5f0800915edf0c6d5e9af0095e8d34f15e6b0b6b5e5f10435e3573de5e2cccfb5e28cbd35e04d1245d2d0cea5d03c0d45cf920f65ca68c2d5c9bb4945c7ba5f45c734ed15c0353e85bcc34025b55f4d95b0f5cf85b0a5e2d5afd5b105ae113515adc1f9c5a898b515a87e635599c1c515993e70c597c3607590366ce58d44c24589cd7dd589219b55873da3058215cb0578070215769cc9a5715ac8256d811d85648e6ca5617170f55a6c5a9552aa0605520643f5519e69c54f45bf0549d4e4f5497a50553f89d07539f63d2539e41ad53059ba152d86f7d52b80bd0520f0b0151adb57151a7f7d6518814b65185889f
  | 10, 7 => 0x751cb11d74ecd1bc74ba6346740b1b1f73fb37ac73b4375c735c9c107292a823725cc2b07247a60670e3a59370b1ed72709399287079ace66f93c7566f4f3cd76efc69f36e2140a26dd423396d4a18276d38973b6cf840046c68f12a6be8e69b6b85f3636b4e506f6b21b4c36a7fc7796a6980b868bb0619682e7386680df36b6809087467cb9cd46739410767047c116702dc8a667c44d8662fe6f6662d90d965e8c6b865e14d5165a27eef65a074b464e0b4c264a73dbc649c530564860c44645cb1de6431caf36404275863ee69c763b6fcaf6329400862e00ead62d7323b629de205625dce1d62189b1161a6784e615acbb3610dbef160ca8eb160873c69
  | 10, 8 => 0x8aefaf068a84c7c58a7290db8a2c54ba89a9fd958997340288a2456788a219ee886ed936872427d6871272d586f70e6686bcc9d386bc193e865817ca863bb63786105b7b85b48ea6858cf8a184faf7b9848f16128481065584564508842916878423e250835cd7fd82309110820b803f81502810812bf49081131ca1810af2cc80786fba80678af7800f6992800df6e280076c737f7fd4a57e0ba68d7d9473bc7d4522637d0fed307cf761bf7c910bf37bc726267baba93f7b7a1adb7b48801c7b0bcdf77af11e827ab02bde79fb72f979e7a72879deac207918fca97833ab9b77ddbb40772c78bc76e3cf3576a02166763f47bf760c0a6375e9bbf5752f2e1b
  | 10, 9 => 0xa07904329fdca7dc9fc6ddd29ec3d5799ec083369e68f1ac9ddf0d1d9dcb17ec9d8f3ec09d67f2dc9be6ffd99b52044d9b1f7cf09adb4fab9a1797f39a02e86399f20fe599e7d27c98f3869298df89c598c01cd19873369998243d2397f85d3c97c218cc97494587971d656196e68cd396d63bf096c659e3968d0dee9685fd7496771fec966ae78d961fb4a995daf0d495a2a5c095a17f3a950d0fcc9496f5929448e770940e9b71930ccf1592d68aa5929b2fac9292c06592127aa791dacbbc90e76a9590715ed18fb883a88ef306b98ebfc95d8eaaa5258e943ee08e2154738d8e12f68ce3ccdb8cc874fc8c92308c8c7fb3df8ba857fa8b9671a38b85d0aa
  | 10, 10 => 0xbfaf7b9dbcfc20a8baf7e834ba3325aeb9ffcdd1b8a2acf2b7fbbb01b7d71c03b67b0bbab62ebde9b5655ab7b5479787b525c203b3315e27b2fe20cbb2ee362eb2eb8ddcb2cf17fbb2bfd2f3b22f5802b203a9ffb1bcf8b5b09828cdb0196973ae8425fcae823a3eae53b03fae4df8cbae02a807adbaebb8ad4d8455ad1f9fbface6bcecac23bc83aaf3ac4ea97115afa9682218a9639c20a9513f3aa87d2e6ba86a8457a861f62ea83b74e2a7e6a220a77332c5a6d1e434a54fb619a4eb20bea34b92d2a3375846a323c7ffa31c425fa310131ca2e013b4a21d9c15a2075554a1e6560da1d2cb2aa16a5350a133a66da0e79d00a0d2aa0ca0d28e00a0bce368
  | 10, 11 => 0xe0d304f6e0076644de6bf2badcd0a53fdc5283fedc4c6347dbb0f86fdb46d3d0da0b790fd9bc9493d9895737d94b0dead8ebb046d8c448a3d7e51718d724cd8bd65584c9d582ed4ad55a2f7bd544bd58d49ed74cd3cfc5f4d378533ad3519150d3420ecad25603bed2464fe1d20cf36ad1c49967d1a0bcffd0710f1acfcbd0cbcfc78739cd03d762cbf154cfcbc81394cbaf4de1caf6230fcaddd324ca539acdca151a1dc9b22505c95ef3dac9158e5ec8a96c2cc85e0196c79b6399c753a74ac7482070c7284df8c71e6b22c690f677c4975aefc3802522c37538ecc2ee1933c2770464c25c9249c204fe34c1d71cd5c1bbac35bfe2b8f9bfdbce70bfb7f605
  | 10, 12 => 0xfd429d9bfd00ef26fcb6d154fb7069cefaec9f07f9f0e01ef948c896f8f5d938f684dba7f47d7b6ef45d3a6ff3be6c5cf3461b57f3195c29f2f4b074f1ce9470f1aa4eeaf1a1a323eed2de35ee29fee7eda9a18eed3baf00ec447e66ec2e3901ea2194a1e9d3a63de9663c72e8cd7a53e88a656ce7cf0d3de65b7e51e64355a2e62539e1e5297af8e4c02d85e495c448e48edea1e47bd28ee1fab441
  | 11, 0 => 0xee4ccd72bfcfd872bec9ac88b84e0c67b24eb633b1430605af47401fa974856fa93e40ffa8428216a1ed87049d24802d9873369997b7de6a7947c50775d8da116080f9fa5e6b0b6b5c0c8db057f7274d4675df1b40d73a273e0a25a03d00ae463575c9ce3152270e2901cdd6244273a01f6d511d1ee53b201da2926f1737fe420cec92010af82e250ac4f0c9
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 7, 0 => 0xa110041304000000000e1020004007841300984400784140000041274403050000000000007000400784130027419104404030004047441300984400784140098440078414010000000000008000a110041304000a1100413061041a274404030004105840300000000000210200040754413000001210440300104162744040300019104403030484127440403294407644140329440078414010000000016102
  | 8, 0 => 0xa000000000000b00021654123030004127440300000127644030000006174193030011d15415301000000001a1070000000816206000000000000200218474023000002237440301000000600620500000374022050000000000006000000001610700000000161070004010412300000206541930300012274403010000001816204000000541a2040000076440205000000000210700000000000050000000000009000000000000200000018152040000065419204000020480630300000104402050001537440301
  | 8, 1 => 0x2151001a30000000000000060001210416300001211001a3030004127440300000001044020000012068163010000000000003002001541530100000000000040001637440300000005744020600000374022050000000002107000005640220400219070063030000000945205000227544030300041274403040004127440304000005740220500040104163010000047402206000003744020500000274402050000047440204000120681630000000000000010001907959303002191001530100000374402050002227440300
  | 8, 2 => 0x401040000000806205000000000000a000000000210700000068022060000005806206000127544030300200164193030000000000004000000000000400040104163000001627440301001211041a30000000000000070000000002107000000000000d0000076440205000000000210700000000021070005d170023000004127440303000000700620400000764402040000076440204000020481a30000000000000080000000819206000401041a300000027641530100016008063030021570059303
  | 8, 3 => 0x4127440303001d90084030000219154193030000000000004000412744030600000000000010002247440301000000000000e00002274403010000000040106000000581a205000150081230100000564022050000000000003000000001210700000764402040000005802204000000694520600000000000020000075404204000000001a1070000617415300000000000000a00041274403010000010402204000000000000400041008123000004127440304000020481a301000000000000300002374403000001a04806303
  | 8, 4 => 0x16107000001641620400000000000000000204816300000401041a3010004127440303000195641530300022764403030000000012107000000001610c00041274403030000210416300000020681630100019564123030004127440301000060581a303000412744030500041274403040000056415204000000181a206000a10784130300000164162040000006019205001c471501300000000001a107000000000000700000374402050000027440205000000000000a000007544020400000008152040000005802206
  | 8, 5 => 0x816206000000000000a000001640220400000104402010001a27440301000120541a30100000008062050000006806205000000000210c0000065406204000000081a206000000000e10200219700553000001a00806303000000000000a0001510440301000412744030100000058062040001a37440300001d5008403030000016402204000006540220400040104123000020016419303000000000e1070000010041205000000000000a00000000021070002056415301000000001210700000000121070000005806204
  | 8, 6 => 0x2117002300000000000000400000000000060000047440204000000640620500040104163000002247440300000190480630300000058022040000010041205000000001610700000000000050000006816205000413744030300041274403030012105406301000127644030300000374042040000076440205000000000000a002184740230300022164193030000010041204000152744030100000064162040004127440301000000194520500000018022040001227440300000000001210700019474403030000000806204
  | 8, 7 => 0x2000000000210700000574402050005d170023030000000012107000000000000a000001040620400000064162060000015415204000000001210700000000021070001604806300000000081a20600041274403040000010041204002151001a3030000000000002000000000000800101701053010000076440206000003744020400000274402040001206816300002001541530000000000121020019500819303000000180220400000058592040000001016204000400784130000041274403030004106816300
  | 8, 8 => 0x68162040000000002104000000000210700000000000040000007815201000205641530000000058062050000000000005000000181620500000764402060002247440300000005041a2050000001815204000000000000600019164063030000606416303000000000000000000000000050000000000000000000000000a000020541a3010004127440301002191001630300000000000080005c154153010000010041204000000000000600000000021020001515412301002001641930100000008592040000076002204
  | 8, 9 => 0x40001600806300000412744030300000104402000011d00840301000000000210600121064163030000206816300000000000000400040764413030000005595204000000001a1070004007841301000001044020000000574402050000000016107000001001620400000000000080000006559204000000000000800019008063030000006802204000000194120600000000000050020116412303000000000000c000060581a30000000000181050000000000004001d90084030300000760022040021447402303
  | 8, 10 => 0x12107000407544130000000104402000000000000008000000000000a0000000016107000123744030300041274403060000000806205000000180220500201154123000002065419301000000000000b000e1078193010004127440301000000000000e00061064163030021970055303000000000000a000000000000a0011d00819303000000181a2060001500855301000400784130000040104123030000071002204002014140630000000008192060004127440301000001000220400055414153010000000002107
  | 8, 11 => 0x185920400000000121070000056406205000020481a30300000474022060000000016107002184740230000000000161070001637440303000000000000800006104123000001a04806301000a107815300000550541a301000000001a10700000274402040010170105300000002740420400000000000040000000941206000215640630100000100412050000037440206001211001a301002151001a300000000000000700000064402030004137440300000000000000a0000010016205001c100859303000000641a205
  | 8, 12 => 0x7000001004120600019764403030000016406204000223744030000000654062040000000016107000000000000700000000000050011d008403000000000859204000160480630000000064162050004007841300000061041630000041274403010000000000004000001000220500000000021070000001802204000206541930300121100163000000005859204000610641630000000000021070000047440204000023744030300000068162040000000000007001c1008553000000000002107000000000610c
  | 8, 13 => 0x104062040000000000004000000000000400041274403010000010440200000412744030600016008063000004127440305000001041620400002048163000001956406303000227544030000000000000070000000012107000001044020000000008162040000000002107000001001a20500115654193030001a374403030000007841200000000081a2050000037440206000000000210600000000161070000016406204000000100520400002048063000000000000007000412744030100041008063000000015415204
  | 8, 14 => 0x6840200001c5009013000004010416300000060681630000000000021070000000816205000000000210400000000121070004047441300002194055930300002048163000004010412300
  | 9, 0 => 0x21070000000006104000000000000400000474402010000010402200000006541920100000164062030000000141105000001001620300000001591040000000016105000000000000600000058062030000040406203000001741920300000078592000000000006104000000001a107000001541a201000000000000a000007644020000000058062000000000141106000000000000400000174022030000076440205000000000000700000000000000000006806201000000700620000000000191050000010416201
  | 9, 1 => 0x5910500000154062000000004802201000000480620000000000061040000000819203000000000000c000000000210500000000000060000000806201000004744120000000008162030000000002105000000080620000000000000050000000000004000000000000a000000481a203000000640620300000071592010000000040106000000581a20000000454022000000000002106000000001610400000058062000000000819205000000541a2000000000806204000000080620600000078412030000000806200
  | 9, 2 => 0x10412201000000081a2000000007995203000000081620600000764402060000010440203000000000000c00000754022010000000040105000007644020300000474402010000000840203000000481a20300000000000040000000006104000000001910400000000000040000000059104000000785520000000764402010000000159105000003744020300000274402030000000145106000000481a201000000081a205000000000000600000001411060000000016104000000081a2010000075440200000004041a200
  | 9, 3 => 0x10455200000000004110400000374402030000027440203000000001910400000008062000000000806200000001541a201000000000210600000078192010000075441200000001641220100000164162050000065412203000000000000a000000000000a0000070059203000000480620100000104402000000000000000000000001510400000000000090000047419203000000081920000000000000060000006806203000000680620000000008162000000000000001000001741520000000374402060000027440206
  | 9, 4 => 0x80620000000000551040000004806200000000001610400000405052010000065419203000001041a20300000070062040000000000004000000000000700000064122030000000819200000004744020300000000161070000000806206000000001a1050000000002105000001044020000000564022000000000002106000004540220300000078152010000004816201000000001a10500000058062030000000006106000000781920300000475592010000004806201000000081a20600000514022060000065419201
  | 9, 5 => 0x81a2030000000006106000001044020000000048022000000000141105000001044020100000008402030000005406201000007650520100000154122000000005806203000000795920100000008062030000037440203000002744020300000105052000000075440204000000080620000000000551040000000000007000000580620300000764152010000005806201000000001210700000000121070000004806201000004141a201000000481a2030000010402201000000001810500000754402000000000059104
  | 9, 6 => 0x48062010000010519200000000481a200000000680620300000465592030000015415200000001041620300000474402050000000006104000000781520100000068062040000000816201000000000000700000058062000000000006104000000000000f0000005406201000001741920300000068062000000040416201000000080620000000058062010000000002104000000000210600000000021040000076440203000000681620100000058062030000005806203000001740220100000374402050000046416203
  | 9, 7 => 0x806200000000000000b0000000016105000001740220300000000000080000037440203000002744020300000104402010000000000007000001540620100000765052000000000040105000000001610c00000414152010000000055104000000000610900000000161060000076505201000000081a2000000000000006000000000000a0000075440200000000581a206000000000000000000414162030000000812201000000640620100000000000050000000141105000000081620400000000021040000000040104
  | 9, 8 => 0x50000004806203000000081a200000000080620400000564022010000000006105000007640220000000070062060000005806201000000680620000000000551040000000006106000000015910600000054062010000010412200000000781520100000000161060000065406203000004741920100000008162030000004816201000000000000900000374402000000000000007000001001a2050000065419200000000000000a00000100122000000000141105000000000000300000000000070000000000008
  | 9, 9 => 0x21050000000806203000007540220100000474192000000000000007000000000610500000454062010000000806201000000001610500000105012010000000000006000000000610900000000000040000017419200000000000210400000000000000000015406204000001044020300000000021070000005412200000000000000700000001411050000075440203000000000610400000048022010000017559200000004744020100000764022010000010406201000000000610600000048062000000046415201
  | 9, 10 => 0x580220500000000000040000000901201000000080620100000064122010000041416201000000081520300000174152000000010501200000000081a20100000000000040000000806203000000001210700000068062030000000816201000000000000700000464022030000010440200000000480620000000764022030000000006104000000000610c00000000000070000000000001000004041a2010000047440204000004740220000000058062040000000000007000000581a20300000000000070000000006105
  | 9, 11 => 0x7905200000000014510500000754402040000000000005000000580220600000414022030000015406201000000001610500000104162010000010440201000000081a20600000174022000000047402200000000481a20300000048062030000007855201000000000000700000000000040000016406200000000000000d000000001610600000474402050000000000005000000000000a00000000000010000010402203000007644020500000000000040000047440201000001700220400000000061060000000806200
  | 9, 12 => 0x81a203000003744020400000274402040000047440200000001541520000000474402000000005806201000000000610400000000000030000000812200000001041a20000000000000050000065412203000000081a203000004041520100000404152010000004802201000007644020000000274402010000076402204000000000210700000404152030000016416201000007544020100000474022010000000041104000007544020000000155052010000076415201000000000210c00000000021050000076402203
  | 9, 13 => 0x56415203000000000000500000000021050000010406200000000481a2010000000000008000000004010600000000161070000000000006000001700220000000000401060000000000007000000581a203000000001a105000000680620000000564152010000000015104000000580620000000164192030000046559203000000000000700000000000000000000159105000000001610400000000000070000000002106000000641620300000105012030000000806201000000001210700000068062040000017402201
  | 9, 14 => 0x1755920100000754402000000006406201000000000210c000000000000400000000000070000005406201000000004010300000414022010000076440203000000000000700000068162000000004806201000000000000400000414162000000000006104000000005510400000078552010000000806204000000000000500000175952030000075440200000000081a2030000017419200000001001a20300000078592030000000016105000000000000a0000015406203000003744020300000274402030000000816200
  | 9, 15 => 0x1651920000000000411040000000000007000001550520000000274402010000010016200000004541a20300000464162000000006416206000000000000300000104022010000076402201000000000210600000154062000000005412201000000000000a000000640620300000754402030000000000003000000000000a000000001a1060000076440205000000080620100000000151040000051406205000000081a2030000045406201000000541a2010000000000006000000001810600000000000040000000816201
  | 9, 16 => 0x8192030000000002104000000015910600000000000070000000000007000000081620100000000000060000047440200000000000000300000079012000000045402201000000000000100000008062010000000000000000001001a2030000000006104000000580620300000454062030000016402201000001640220500000654022030000004806200000000000000400000000401040000000002107000001041a201000001044020100000068062000000010416200000000001a10600000754402000000000000000
  | 9, 17 => 0x1001220300000654122030000005806200000001044020100000574402050000006816204000007005920100000474022000000000000000000001540220000000165192000000075440200000004641620100000001451060000075505200000000681620100000464162000000004816200000000000210700000000021070000047595203000000081a2030000004806201000004041620100000274402030000007819203000000080620000000000021040000046406203000000001a10400000564152010000006806200
  | 9, 18 => 0x784120000000008062010000017002201000000081a200000000001a105000000000000400000000000070000000806203000000001a1060000000015104000000000000400000000061050000006806200000000004010400000404192030000006416204000000005510400000100162060000041402200000004740220100000764402010000000040101000007544020400000164122010000076402203000000014510600000064162010000040415203000000481a200000000000000700000000000050000000016107
  | 9, 19 => 0x75440203000000084020000000754022010000046402200000000481a2010000000002105000000000210500000474402040000000006106000000000000700000754402030000010416205000000540620300000374402000000006806204000001044020500000000021060000075402203000000000000a000004041920300000754412010000000016105000000081a2060000076440201000000081520100000404162000000057402205000005640620100000465592030000006806200000000581a2030000005806203
  | 9, 20 => 0x104402060000000006104000007640220100000048162000000006806203000000000000500000008062030000004806203000000000000700000048062000000040406203000001044020000000104162030000006806201000000001610700000754402000000010440206000000081620500000000191060000010440203000000081620000000104022000000000000004000000000210600000008062040000010412200000004744020100000008162010000047415201000000000000100000754402030000075440204
  | 9, 21 => 0x170022030000045402203000000081a2010000046402200000004740220300000008122000000037440200000000000000500000048062030000000901201000000680620000000000061050000000002105000000000000c0000040416200000004041a20100000068062030000017419203000000000000a0000056406200000000541a20300000000021060000010440201000000081520000000764402000000006806203000000000000b00000000000070000006816201000000000000400000008062010000000041106
  | 9, 22 => 0x3000000081920400000374402010000007841200000000000000a00000000061050000000000007000000081920100000754402010000010440200000000580620100000274402010000000040106000004141a203000000700620300000000021070000000000003000000080620000000000000060000005412201000000000000a00000000411060000000000005000000000000500000705052000000010440205000000000000a000001041a2030000000000006000001641220000000008062010000016412203
  | 9, 23 => 0x5000000001a1050000007901201000000005910400000164062000000047440200000000000610400000000411040000005806200000001041220100000274402000000000040100000003744020500000274402050000000002104000000000000700000504062060000000159104000000000610400000170022050000006806201000000001510400000009012000000057440205000000000000700000764402010000047440201000000081a20300000078152000000000000000000000001a1050000000002106
  | 9, 24 => 0x154152010000000000007000000000210500000000000050000000901200000000000000000000000061060000027440201000004141a201000004559520100000000021040000040505201000000081a2010000000040100000000000000a0000015412201000000480220000000001591040000006406203000000004010600000654062010000000006104000002744020600000764022000000000041106000000000610500000700552010000016412201000001700220300000000061040000065402203000000000000b
  | 9, 25 => 0x300000754402010000004806201000000000000600000104062000000000000007000000080620400000100122000000040415200000000080620100000754402010000010440201000000005910500000374402010000027440200000001541520100000374402000000000806205000000541220300000164162010000075402203000004641620000000754402000000000041104000000000210500000000161070000000000004000000581a2000000075440201000000000610600000474402040000010016203
  | 9, 26 => 0x580620000000008062000000000000003000000001a1070000075402201000000000000a0000000006105000000000000a000007650120300000564062010000004802201000001041620000000000000050000000019105000000480620000000000061050000006816201000004541a20100000764402030000000806201000000001510400000000000040000000002106000000081520100000000000010000005806205000000001610400000064122030000006416200000000580620100000165052000000005806205
  | 9, 27 => 0x174152010000046559201000001740220600000000151040000016416203000000000000a00000000591050000076415200000000081620000000000000090000007006201000001044020500000405052000000037440200000000001510400000079052000000000000008000000000000c0000010440200000007544020100000048162000000047440206000000785920100000058062000000000006106000006541920000000000000040000000019105000001541a200000000000000600000000000050000070105201
  | 9, 28 => 0x6816201000000781520000000404162000000006416204000000001a1050000000006106000000001610600000008402060000004802200000001044020000000404152000000045595203000000004010400000754402030000016402201000000000000400000464022000000010402200000004741920300000000061060000000000004000003744020000000000021070000017402200000000081a200000000081a201000000084020300000654022030000000000004000000781920100000000000070000010406204
  | 9, 29 => 0x47419200000000715920100000764152000000010402200000001700220300000100192030000015415203000000081a2010000000006105000003744020000000000000070000000000001000000481620100000104022050000004806201000000680620300000000000070000000002105000007640220000000000151040000000812200000005640620000000079952030000000006104000000581a2050000000000003000000000000700000105012000000000000007000000481620000000474402010000000000006
  | 9, 30 => 0x61050000000002105000000001610500000764152010000000000000000000480220000000154122010000070105203000000004010600000104062000000000019105000004744020300000564022050000000000007000001700220000000008062050000046559201000000015910500000048022000000047440204000000000000700000474022010000000000005000000080620000000705052000000005406200000000000000700000048162000000016416201000004041a201000000001a1050000000815201
  | 9, 31 => 0x21050000047440203000000000000a000000019510400000374402000000016505201000000001a104000000480620100000068062050000005412200000000014510500000100162000000000006105000000001a105000000000610500000414062000000047440200000000480620000000079052030000000005104000001640220300000170022000000000040105000000000610400000000000070000027440205000000000000400000070062000000005406204000000000000500000474402050000047440203
  | 9, 32 => 0x75440201000000000000b000001640620300000000161040000000000006000000580620400000404152010000070455200000000795920000000764402000000010402201000000000000700000000021060000000040104000000014110500000000061060000000016105000004740220000000058062000000017415203000000000000500000174022030000007006200000001641920300000008122000000000040106000000641620300000009012000000000819204000000481a20300000000061040000005806201
  | 9, 33 => 0x48162000000000000005000001541520300000000000070000000000000000000000000100000000021070000000016104000000000000400000474192010000006806201000000001610400000374402030000000000005000001741520100000000000080000000000005000001540220100000000000070000004802203000001040620000000764402040000007859200000000790520300000000061040000000002104000001740220000000104402040000016402201000000001a10500000000551040000000000006
  | 9, 34 => 0x48062010000000806201000004540220100000048162030000056415204000004040620000000000591050000000000008000000481a201000000000000b0000010012201000000084020000000105012010000000002104000000481620000000048062030000000000007000000001a10600000700552030000000000007000000541a20100000155152010000005406200000000081520300000474412000000076440203000004041520100000754402000000037440205000004744020300000764022000000000000003
  | 9, 35 => 0xa0000000059105000004141620000000068162000000000000007000000000000a00000104402000000015412200000004741520100000374402010000000000007000000000000700000104192030000000002104000000080620000000064122030000000000008000000481620000000474402000000000000000000000080620500000654192030000000000004000000641520300000008122000000016416203000000081920300000000000070000047402201000001641220300000008062050000000816200
  | 9, 36 => 0x21040000000002104000004140620100000048062030000000000007000000481a20000000164062060000000002105000000004010500000754402000000010406203000003744020100000000000070000000000004000001541520000000000401010000000816204000000001a1050000000000007000000700620300000008162000000076440201000001001a203000004050520000000764402030000000000007000004141620000000000121070000017402200000000000000600000008162000000000000007
  | 9, 37 => 0x5412201000007644020000000000161070000004802203000000081a205000000541a200000000000000400000048062000000004816203000001050120000000000000040000000816200000000001810500000374402010000004802200000000640620100000000401040000000002106000001041a2050000004816203000000580620100000104402040000047440201000007544020000000474022000000010016204000000480220000000104402000000000000003000007005920000000164162040000005806200
  | 9, 38 => 0x404192010000041402200000007640220000000009412050000000816200000000001910400000000061040000016406203000000000000400000474402000000000000004000001044020000000048162000000005412201000000784120300000001591040000027440200000000000000b00000001591060000017019203000000000210600000104162000000041402203000000481620300000174192030000000000007000000000000300000008162010000000000002000000080620100000000000040000000000003
  | 9, 39 => 0x404062010000017402200000000000000a000001640220400000008062000000010440203000004744020100000000021060000000059105000006541220300000048062000000000002106000000000000500000000000050000000000004000001050120300000048022000000000002105000000680620600000000000070000015402201000000000000b000000080620000000414022000000076440201000000541a201000007644020100000000000060000000006104000000000000000000064122010000017419200
  | 9, 40 => 0x41106000000000000800000000021070000010406206000000000210700000000000040000000000006000000000000a000000580620300000000000000000000816204000000081620000000000161040000076415201000007050520300000374402000000000000007000000000000a000001041a2010000005806201000000000000a0000040416203000002744020400000008062010000027440204000004741520100000104122010000007901201000000001610600000000000040000000840204
  | 9, 41 => 0x64062050000015415201000000541a20300000000000050000076440203000000004010500000104062000000075440201000001044020100000104402000000000059104000000090120300000000401000000000055104000000700620000000079012000000000016104000000480220000000104402040000040559200000000000000a000001541520400000079952010000004802203000000481a2030000075419203000000481620000000000401060000000002105000000001610700000008162010000000816200
  | 9, 42 => 0x81a2010000000816200000000080620300000274402030000000812201000000680620500000000551040000015415201000000481620100000000000010000000012107000000000610400000104402010000000816200000004541a2010000056402204000000000210700000164152010000004806201000004559520000000064062030000075440200000000000000a00000000000030000000019106000000001a104000000019510400000705052030000016505203000000004110500000000000010000007901203
  | 9, 43 => 0x37440200000000001810600000154022000000006406200000001044020300000564062000000006816204000000480220000000454062030000000000007000000000000400000000161040000006816200000000000000300000000000000000000816200000000000000600000000021040000000041106000000000000a00000164022030000070455201000000001a106000000080620100000070062010000010412200000000081620300000009012030000010440200000000004110500000000000060000000002107
  | 9, 44 => 0x6816200000000000000a000000000000200000000591050000000145106000007541920100000058062000000010412203000000480620000000754402000000007006200000000000000a00000078412000000027440201000000000000500000154122000000000000000000000000000a00000070062030000004802201000002744020400000000021070000000000007000000000210400000000000060000006416201000000000000000000064122010000070105200000000000000600000374402000000010012201
  | 9, 45 => 0x1610c000000000000700000008152010000000055104000005041a20500000068162000000000806200000004050520000000104402040000000816203000005744020600000764402010000000041104000004141a20300000104402010000000000007000000681620100000008162030000006806201000001044020000000048022010000000000006000000001a106000000481620000000058062040000000059104000004744020000000000000070000057440205000000000000400000654192030000004806201
  | 9, 46 => 0x7000000700620000000000591060000000055104000000000610600000068162010000010440203000000081920100000000021050000047402200000007650520300000374402000000000000007000000000210400000274402030000000000004000000000000300000754402010000000000007000000481a200000000715920000000000000050000000040100000000081620000000000021040000000815201000001541a20100000474402010000000816203000000081620300000048062000000015415201
  | 9, 47 => 0x700000000061050000056412200000000000000300000000061050000010416200000000580620600000175952010000041406203000000480220100000068162010000000002106000000480220000000008062040000006816200000000000000c0000006816204000000001610c00000001451050000000012107000000001610700000000161040000007819201000000580620500000700592000000007855201000004040620100000008062000000000004104000000541a20000000058062010000000000007
  | 9, 48 => 0x8162010000000002104000000004110600000155152010000000000004000000000000a000000000000a000000000000000000000000070000027440201000000000000400000001411060000000019106000000081a203000000000000a0000027440205000000001610400000000000050000037440204000002744020400000071592000000000000004000000580620300000048062010000000812201000004041a20300000764402060000047440203000000481a200000000001610500000000021090000000000008
  | 9, 49 => 0x48162010000065412201000000000000a0000047415201000000000000400000404152000000000816203000000000210400000000000060000000000007000000000000d0000041406201000004041a2030000016412200000000014510600000000000070000000806201000001001a2010000006816200000000680620300000000000030000027440203000000000000400000000000070000075440203000000481a20100000000161070000000000006000000001210700000000000060000037440203000000581a200
  | 9, 50 => 0x191040000004816201000004540220100000000000040000000000007000001041220000000000411060000017415203000000081220100000701052000000045406201000003744020000000000000070000010402200000005744020500000000000060000005802205000000000000700000000401010000016406201000000000000a00000078552030000005806200000004740220000000104402010000037440201000001541a20000000104022000000056406200000001001220000000105012000000010406201
  | 9, 51 => 0x6816200000000541a20100000048022010000000000004000000581a2000000000000000000001044020000000075592010000007841201000000001210700000068062060000056415203000000000000700000000000090000005806204000000541a20100000000000030000006806200000004540220300000048162000000000806201000004140620000000000161050000047440200000000001610700000008162040000076402206000000581a2030000000812201000001540220000000474402000000000806200
  | 9, 52 => 0x81a204000001041520000000000161040000000000001000004540620300000564122000000046406200000000480620000000000551040000000816203000000000000500000000000040000005406200000000081a200000007544020400000058062050000000016106000000000000d0000037440200000001040620000000008062000000070505200000000580620500000000161040000000000007000000580620100000000000070000000816201000000781920000000464062000000000006105000000000000a
  | 9, 53 => 0x80620100000000021040000000000007000000001a106000000081a2000000056402200000007050520000000000000040000000806206000001041220000000100162000000040406200000000000000300000008062040000004802203000000000000000000048022000000000000004000000541220000000000000090000006406204000000001910500000000021070000000041104000000080620500000164162000000010440204000001641620000000000161040000000002104000000000000a0000000000008
  | 9, 54 => 0x8162000000047440206000007644120000000000000050000004816200000000000210400000000000070000000041104000005641520100000000021070000000006105000004040620000000174022040000010406201000000680620100000000000070000004816201000000000000400000000000070000010416200000000480620000000008162040000000000006000001650520000000000000070000000000000000000080620000000374402030000000000007000006540620300000174022000000000019105
  | 9, 55 => 0x21040000000019104000000000000400000000000020000000159106000000000000a00000054122000000071501200000005141a2050000000002104000000000210600000104162040000007959200000000481a201000000084020000000104402000000016519203000000481620300000464162030000010412200000000000210400000654022010000000000005000001050120000000000161070000007006200000000000000b00000000411040000016412203000001640220000000000000020000000002104
  | 9, 56 => 0x6104000000001510400000474402000000000002107000001041620000000000000070000076505203000001740220000000001451050000000002105000000000000700000048022000000046406200000000680620000000000401040000000000008000000004010400000000401040000000000008000004541a203000000081620100000079052000000005802205000000680620100000048022010000000016104000004744020000000058062000000000000004000004140220000000000000080000010402200
  | 9, 57 => 0x300000155152010000065419203000000581a204000000081a201000001740220000000000000070000040416200000000481a2030000000002104000000000000400000564022000000000002104000000080620000000000191050000000000007000000000000b000000480620000000001951040000056406205000000000210600000000000070000041416200000001040220400000000000040000010406200000000004110400000000000000000000000007000001044020000000000121070000076440203
  | 9, 58 => 0x6816200000000641620000000000000050000004802201000000000000b00000165052030000047440200000000001a107000001640620100000414022000000076402200000004744020100000474402000000000000004000000581a2060000000040104000001040220000000048022000000000040100000000480620000000104162000000000195104000000000000400000000161070000040406200000000001a1050000000815200000000001a1050000000145105000000001a10500000000411040000000000007
  | 9, 59 => 0xa000000681620100000155152030000000002104000007050520000000001411050000047440203000000000000a0000000006104000000000210700000104122000000010440200000000000000500000000191050000047440200000001755920000000164022030000000816204000007644020000000104402010000047440200000007644020100000000000040000000040104000000000000700000078192040000000006104000000000000a0000004816203000007641520100000000191060000000000004
  | 9, 60 => 0x4744020000000414062000000000000000000000000000800000000021070000004806200000000000210400000068062050000000806200000000680620500000048062000000000000007000000000000400000048062000000007841200000002744020100000764022000000076440201000000000210400000564122000000000002104000000000000a000000480620000000000401050000047559200000000000000d00000000021040000000006104000001044020000000105592000000000901200000000081a201
  | 9, 61 => 0x1591040000000040104000000000000d00000000161050000007901200000001700220000000000000070000006816200000000784120000000000021040000000000007000000000000a00000048062000000000040104000000004110400000068162010000000002107000000000000a00000000000070000000806200000000001210700000070062000000047559200000000004010400000000021040000000006104000000080620400000008062000000041406200000000000000400000008062000000000002104
  | 9, 62 => 0xa00000105012000000056406204
  | 10, 0 => 0x1451050000000059106000000001210000000000061030000000041103000000001510000000000061040000000119101000000019510300000000191030000000019101000000000610000000000411000000000159103000000001510300000000161010000000000007000000004110600000001151010000000040101000000000000500000000021030000000059101000000001510000000000161040000000041100000000000210000000000000040000000000007000000001910600000001051010000000012103
  | 10, 1 => 0x401010000000019101000000001910000000001191000000000015104000000000000600000000000060000000041100000000001a10600000001591060000000019104000000000210000000001051010000000002101000000000000700000000061000000000015100000000015910500000001011000000000115103000000000000500000000021040000000000003000000014510600000000191010000000055101000000005910000000000591000000000002100000000000000500000000000060000000000007
  | 10, 2 => 0x4010100000000000090000000000006000000004110000000001591050000000059100000000014110500000000411030000000041103000000000210600000000151000000000000006000000001210300000000411030000000016103000000001510300000001151030000000040101000000000210300000001591010000000015103000000001a1030000000002101000000000610300000001011010000000040101000000001610300000001191010000000115103000000000210400000000411040000000105101
  | 10, 3 => 0x40103000000000000600000000411010000000159104000000000000a000000001a10100000000151030000000101101000000000000500000000121010000000019100000000000000300000000151010000000002106000000019510000000001191010000000006101000000001610300000000000050000000006100000000011510300000001051030000000006101000000001910300000000000050000000006104000000000610600000000021030000000141106000000004110000000000021030000000002103
  | 10, 4 => 0x400000000021000000000059103000000014510500000000000030000000006103000000000610000000000000070000000041101000000010110300000000061000000000159104000000000000c00000000191030000000019100000000001910400000000061060000000159100000000000000500000000000030000000000006000000000210300000000061000000000015101000000001910000000000191000000000016100000000011510000000000061000000000006100000000001a1000000000002103
  | 10, 5 => 0x61040000000159101000000005510300000001191000000000059100000000001610300000001151030000000002100000000000610000000000061000000000059105000000001a10000000000591010000000159105000000010510000000000021060000000016104000000004110100000000000040000000000004000000015910000000000161010000000019103000000010110000000001151010000000019103000000000210300000000151010000000000000000000000000400000000551000000000019103
  | 10, 6 => 0x21010000000115103000000004010100000000401000000000040100000000000610000000000161050000000141105000000000000100000000411000000000006101000000000210300000000151030000000006103000000001610100000001191030000000115101000000000610300000000061010000000105103000000000210400000000000040000000041101000000000000700000000000050000000040101000000001210100000000021010000000019101000000000210600000000061030000000195103
  | 10, 7 => 0x61010000000101103000000000000700000000000060000000006104000000001a1030000000195100000000004110400000001051010000000019101000000000610100000000021010000000055101000000001a103000000000210300000000121010000000059100000000000000700000001011000000000105100000000000000700000000000050000000159101000000015910000000000161060000000000003000000015910500000001051000000000000006000000000210400000001591040000000041103
  | 10, 8 => 0x4000000005910300000000191030000000041101000000001610100000001151010000000015104000000000610100000000151010000000059101000000000000500000000000030000000141105000000010510000000000021000000000115100000000004110100000000000060000000006100000000001910100000000000070000000055100000000005910100000000401000000000159103000000010510100000000551030000000059104000000015910000000000061050000000002101
  | 10, 9 => 0x400000000000060000000000009000000001610100000001591000000000000000000000011910000000000000050000000059103000000005510000000001591030000000000006000000001a106000000019510300000000021010000000000004000000001a100000000004110000000001051000000000101101000000005510000000000151000000000195104000000005510400000000000060000000002100000000005510000000000000070000000000007000000001a10300000001951000000000000007
  | 10, 10 => 0x700000000151000000000006100000000000000500000001591010000000059103000000000610100000001191000000000115103000000001a10100000001191000000000159101000000001210000000000021060000000040105000000005510300000000401010000000101101000000000610400000000000050000000006100000000001510000000000000000000000002101000000000000a0000000101100000000000210500000000061030000000105100000000001610500000000411000000000040105
  | 10, 11 => 0x10510000000000411030000000012100000000000000400000000551040000000002100000000019510300000000551010000000000006000000005510000000000021010000000159100000000000610300000000551040000000000004000000011910300000000000040000000002106000000010110000000000000050000000000008000000001a1030000000000006000000001910100000000411000000000019104000000000210500000001011030000000000001000000010510300000000021010000000040100
  | 10, 12 => 0x6100000000010510000000000000050000000000007000000000000c000000001210100000000591030000000055103000000010510000000000000010000000055100000000010110300000000591060000000055101000000005910400000001191010000000006101000000005510000000001191000000000059101000000000610100000000000040000000159101000000001910300000000061030000000000005000000000000000000001011000000000105101000000001a10100000000000070000000059105
  | 10, 13 => 0x11910000000000061000000000002105000000000000c0000000000001000000000000000000000411000000000000007000000001a1000000000101101000000004010300000001951030000000101100000000011910300000000000040000000015100000000011910000000000411050000000016100000000000000a000000004110100000000551030000000040101000000000610300000000000050000000019100000000011910000000000401030000000015101000000004010400000001051030000000055100
  | 10, 14 => 0x10510000000000021000000000101103000000000610100000001051030000000012100000000000610000000001011000000000040103000000010510300000000551000000000000005000000000610000000000411000000000055103000000005510300000000021050000000101100000000011910000000000000070000000000000000000001a1010000000002100000000011510300000000000040000000145105000000000000400000000000050000000041106000000000000700000000551000000000105100
  | 10, 15 => 0x401000000000000004000000010110000000001151000000000055101000000010110300000000000040000000101103000000004010000000001591000000000055101000000001210300000000411010000000006101000000005910100000000000040000000015101000000000000100000001591010000000105101000000010110000000001151010000000019105000000001210000000001191000000000101100000000000000400000001191030000000119103000000015910000000000591030000000006104
  | 10, 16 => 0x161000000000040100000000000210000000000000040000000012100000000000000600000000121000000000159100000000000000400000001191010000000000004000000000000400000000161040000000015103000000000000700000000551010000000016100000000004010400000000411030000000101101000000004010100000001191010000000015103000000000610000000001051010000000055101000000000000500000000191030000000006105000000000610100000001151010000000019105
  | 10, 17 => 0x1191030000000006101000000001910300000000061010000000000004000000004110100000000000040000000006100000000000610600000000411000000000012100000000000210400000000021000000000000005000000000000700000000021000000000006105000000000000000000000151000000000002100000000010110100000001051000000000000005000000000000c0000000016100000000004010100000000161010000000002104000000000210000000001191010000000012103000000001a105
  | 10, 18 => 0x4000000005910300000000061010000000016103000000010110300000000000070000000016100000000000610300000000551000000000002101000000000210000000000161000000000000004000000010510100000000021040000000159100000000000210300000000411040000000000005000000015910100000001151010000000012100000000001510400000000121030000000000005000000001610100000000161000000000000007000000000210000000000161040000000002103
  | 10, 19 => 0x1610300000000061050000000002100000000010110100000000161030000000012101000000000000b0000000002100000000000000400000000401010000000002103000000004010600000000000070000000002100000000000000700000001191000000000119100000000000000400000000401050000000002100000000005510000000000121000000000041101000000000210100000000021000000000059103000000001610000000000191000000000015100000000000210400000000151010000000105100
  | 10, 20 => 0xc0000000000005000000000000900000000000060000000002100000000001210000000000061040000000059100000000000000500000000021030000000115101000000001910100000000061000000000002100000000011910000000000191010000000006100000000010110000000000161000000000000004000000001510100000001591010000000016103000000001610300000000021000000000105100000000005910100000000151010000000006105000000011510300000000021030000000006100
  | 10, 21 => 0x101101000000000000100000000000000000000002101000000000000100000001191000000000000008000000000000400000001191010000000040100000000004110000000000021010000000105100000000014510500000001051010000000000007000000000000400000001151010000000040105000000004110100000000401000000000006101000000001510100000000411060000000101100000000001910600000000021000000000000004000000000000700000000411050000000002103000000001a103
  | 10, 22 => 0xa00000001151010000000006103000000000610100000000000010000000041100000000001a10000000000000000000000055103000000000610600000000151000000000000004000000001210300000000121000000000000007000000000610500000000021040000000006100000000010510100000000401040000000002101000000001a1000000000055104000000011910000000000061040000000002104000000015910400000001011000000000006100000000014110500000000000060000000012101
  | 10, 23 => 0x40000000000005000000000000700000000021000000000006103000000000000500000000121000000000006100000000004010000000000161050000000012101000000000610000000000000000000000000004000000000210000000000551030000000000006000000000000b0000000040104000000005910300000000401000000000101101000000000610100000001951030000000006100000000000000600000000061040000000059100000000000000400000000161000000000000004000000000000b
  | 10, 24 => 0x1011000000000002100000000000000d00000000021010000000041100000000000000700000000061040000000000004000000005910300000000000070000000016104000000004110000000000401000000000012101000000001510000000001051000000000040100000000004110400000000061000000000041100000000000610300000000151040000000015100000000004010100000000000040000000040100000000004010400000001591000000000000004000000000610000000001591010000000000006
  | 10, 25 => 0x159100000000000000700000000401000000000002100000000004110000000000411040000000002101
  | 11, 0 => 0x3000000000000000000000000000000000000001000000000000000000000000040000000000003000000000000000000000000040000000000000000000000000000000000000050000000000001000000000000600000000000050000000000001000000000000100000000000030000000000004000000000000100000000000000000000000003000000000000300000000000030000000000000000000000000100000000000040000000000000000000000000000000000000050000000000001
  | 11, 1 => 0x3
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_251 roots_251 11 s ws hint
  | 1 => checkCutEntry dom_247 roots_247 11 s ws hint
  | 2 => checkCutEntry dom_249 roots_249 8 s ws hint
  | 3 => checkCutEntry dom_239 roots_239 11 s ws hint
  | 4 => checkCutEntry dom_223 roots_223 10 s ws hint
  | 5 => checkCutEntry dom_191 roots_191 10 s ws hint
  | 6 => checkCutEntry dom_127 roots_127 10 s ws hint
  | 7 => checkCutEntry dom_253 roots_253 9 s ws hint
  | 8 => checkCutEntry dom_221 roots_221 7 s ws hint
  | 9 => checkCutEntry dom_159 roots_159 8 s ws hint
  | 10 => checkCutEntry dom_254 roots_254 8 s ws hint
  | 11 => checkCutEntry dom_63 roots_63 7 s ws hint
  | 12 => checkCutEntry dom_95 roots_95 8 s ws hint
  | 13 => checkCutEntry dom_31 roots_31 6 s ws hint
  | 14 => checkCutEntry dom_246 roots_246 7 s ws hint
  | 15 => checkCutEntry dom_238 roots_238 7 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_255 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_251 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_247 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_249 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_239 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_223 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_191 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_127 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_253 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_221 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_159 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_254 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_63 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_95 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_246 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_238 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_255 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_255 == dom_255) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_255 goalM u ys) : RunD dom_255 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_255 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 13 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 80 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_80 : ∀ i, 80 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_96 : ∀ i, 96 ≤ i → i < 112 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_112 : ∀ i, 112 ≤ i → i < 115 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 112 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 115 → Z 8 i = true := (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 32 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_32 : ∀ i, 32 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_48 : ∀ i, 48 ≤ i → i < 64 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_64 : ∀ i, 64 ≤ i → i < 80 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_80 : ∀ i, 80 ≤ i → i < 96 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_96 : ∀ i, 96 ≤ i → i < 112 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_112 : ∀ i, 112 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_128 : ∀ i, 128 ≤ i → i < 144 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_144 : ∀ i, 144 ≤ i → i < 160 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_160 : ∀ i, 160 ≤ i → i < 176 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_176 : ∀ i, 176 ≤ i → i < 192 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_192 : ∀ i, 192 ≤ i → i < 208 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_208 : ∀ i, 208 ≤ i → i < 224 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_224 : ∀ i, 224 ≤ i → i < 240 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_240 : ∀ i, 240 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_256 : ∀ i, 256 ≤ i → i < 272 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_272 : ∀ i, 272 ≤ i → i < 288 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_288 : ∀ i, 288 ≤ i → i < 304 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_304 : ∀ i, 304 ≤ i → i < 318 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 14 304 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 318 → Z 9 i = true := (range_split (range_split (range_split (range_split z9_0 z9_16) (range_split z9_32 (range_split z9_48 z9_64))) (range_split (range_split z9_80 z9_96) (range_split z9_112 (range_split z9_128 z9_144)))) (range_split (range_split (range_split z9_160 z9_176) (range_split z9_192 (range_split z9_208 z9_224))) (range_split (range_split z9_240 z9_256) (range_split z9_272 (range_split z9_288 z9_304)))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_0 : ∀ i, 0 ≤ i → i < 16 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_16 : ∀ i, 16 ≤ i → i < 32 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_32 : ∀ i, 32 ≤ i → i < 48 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_48 : ∀ i, 48 ≤ i → i < 64 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_64 : ∀ i, 64 ≤ i → i < 80 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_80 : ∀ i, 80 ≤ i → i < 96 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_96 : ∀ i, 96 ≤ i → i < 112 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_112 : ∀ i, 112 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_128 : ∀ i, 128 ≤ i → i < 136 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 136 → Z 10 i = true := (range_split (range_split (range_split z10_0 z10_16) (range_split z10_32 z10_48)) (range_split (range_split z10_64 z10_80) (range_split z10_96 (range_split z10_112 z10_128))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11 : ∀ i, 0 ≤ i → i < 14 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 14 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 12) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
  · exact fun i hi => z11 i (Nat.zero_le i) hi
  · exact fun i hi => z12 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_255 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 7 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 12) (h : RunD dom_255 goalM s xsM) : False := by
  have hmin : 7 ≤ s := by
    have hl := run_len h; change 8 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_255 roots_255 goal_255 13 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_255 goal_255 := by
    have h0 : isConstB dom_255 goal_255 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_255

theorem low_255 : Lower dom_255 roots_255 goal_255 13 := S_255.noCircuit

abbrev fMain : (Fin 8 → Bool) → Bool := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)
theorem hTMain : ∀ r : Fin 256, goal_255.testBit r.val = fMain (pt8 r.val) := by decide +kernel
theorem mainThm : ∀ t : ℕ, HasCircuitSize 8 fMain t → 13 ≤ t := lower_to_circuit fMain goal_255 13 hTMain low_255
end PEqualNP.Outside.L_meta_10652_aux.Base_aux

theorem PEqualNP.Outside.L_meta_10652_aux.Base : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)) t → 13 ≤ t := PEqualNP.Outside.L_meta_10652_aux.Base_aux.mainThm


namespace PEqualNP.Outside.L_meta_10652_aux
open PEqualNP.MetaComplexity

def extended (x : Fin 9 → Bool) : Bool := (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 5 && x 8)

theorem inherited (s : ℕ) (h : HasCircuitSize 9 extended s) : 14 ≤ s := by
  have dep : ∃ x : Fin 9 → Bool,
      extended (Function.update x 4 (!x 4)) ≠ extended x :=
    ⟨fun i => decide (i = 8), by decide +kernel⟩
  have nc : ∃ x y : Fin 9 → Bool,
      extended (Function.update x 4 false) ≠ extended (Function.update y 4 false) :=
    ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 5), by decide +kernel⟩
  obtain ⟨t, saved, pin⟩ := Deletion.one_gate_at 8 extended 4 false s dep nc h
  let labels : Fin 9 → Fin 8 := ![5, 2, 3, 4, 0, 1, 6, 7, 0]
  have smaller := Deletion.relabel_size labels _ t pin
  have eq : (fun x : Fin 8 → Bool => extended (Function.update (x ∘ labels) 4 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)) := by
    funext x
    simp [extended, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  have := Base t smaller
  omega

end PEqualNP.Outside.L_meta_10652_aux

theorem PEqualNP.Outside.L_meta_10652 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 5 && x 8)) t → 14 ≤ t :=
  PEqualNP.Outside.L_meta_10652_aux.inherited
