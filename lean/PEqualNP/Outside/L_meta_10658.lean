import Mathlib
import PEqualNP.Defs

-- The certified eight-input lower bound is from merged L_meta_8517.
-- The pin and relabel lemmas are from the Bow section of merged L_meta_8451.
-- The nine-input reduction and vertex map are by steveDOTdigital.
namespace PEqualNP.Outside.L_meta_10658_aux.Deletion
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
end PEqualNP.Outside.L_meta_10658_aux.Deletion


namespace PEqualNP.Outside.L_meta_10658_aux.Base_aux

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

def dom_25 : Nat := 0x3030303
def goal_25 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_25 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xffaaaa88ffaaaa88ffaaaa88ffaaaa88ffaaaa88ffaaaa88ffaaaa88ffaaaa88
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xecececece8e8e8e8ecececece8e8e8e8ecececece8e8e8e8ecececece8e8e8e8
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffaaaa00ffffffffffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xffe8ffe8ffe8ffe8eae8eae8eae8eae8ffe8ffe8ffe8ffe8eae8eae8eae8eae8
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xffaaffa0ffaaffa0ffaaaaa0ffaaaaa0ffaaffa0ffaaffa0ffaaaaa0ffaaaaa0
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xffffffffe8e8e8e8ffffffffe8e8e8e8ecececece8e8e8e8ecececece8e8e8e8
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xffffffffffffffffe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xffeeeeecffeaeae8ffeeeeecffeaeae8ffeeeeecffeaeae8ffeeeeecffeaeae8
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xffecffecffe8ffe8eeeceeeceae8eae8ffecffecffe8ffe8eeeceeeceae8eae8
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffaaaa88ffffffffffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xffffffffffaaaaa0ffffffffffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffaa88aa88ffccffccff88ff88eecceeccaa88aa88
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xffffffffffffffffffffffffaaa0aaa0ffa0ffa0ffa0ffa0aaa0aaa0aaa0aaa0
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xffeaffe8ffeaffe8ffeaeae8ffeaeae8ffeaffe8ffeaffe8ffeaeae8ffeaeae8
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xffffffffeae8eae8ffffffffeae8eae8eeeceeeceae8eae8eeeceeeceae8eae8
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xffffffffeaeae8e8ffffffffeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xffffffffffffffffeae8eae8eae8eae8ffe8ffe8ffe8ffe8eae8eae8eae8eae8
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xffffffffffffffffeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xffffffffffffffffffaaaaa0ffaaaaa0ffaaffa0ffaaffa0ffaaaaa0ffaaaaa0
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xffffffffffffffffffffffffe8e8e8e8ecececece8e8e8e8ecececece8e8e8e8
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xffffffffffffffffffffffffc0c0c0c0ffccffccffc0ffc0ccccccccc0c0c0c0
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffaaaa00ffaaff00ffaaff00ffaaaa00ffaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffff000000ffccffccff00ff00ffccccccff000000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xffeeffecffeaffe8ffeeeeecffeaeae8ffeeffecffeaffe8ffeeeeecffeaeae8
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xffffffffffeaeae8ffffffffffeaeae8ffeeeeecffeaeae8ffeeeeecffeaeae8
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xffffffffffffffffffffffffeae8eae8ffecffecffe8ffe8eeeceeeceae8eae8
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xffffffffffffffffffffffffeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xffffffffffffffffffffffffffc0c0c0ffccffccffc0ffc0ffccccccffc0c0c0
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xffffffffffffffffffeaeae8ffeaeae8ffeaffe8ffeaffe8ffeaeae8ffeaeae8
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffaaaa88ffeeffccffaaff88ffeeeeccffaaaa88
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xffffffffffffffffffffffffffaaaaa0ffaaffa0ffaaffa0ffaaaaa0ffaaaaa0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xffffffffffffffffffffffffffeaeae8ffeeffecffeaffe8ffeeeeecffeaeae8
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

def isoMv_25 : List (Nat × Nat) := [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_25 : Lower dom_25 roots_25 goal_25 4 :=
  lower_iso isoMv_25 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00, 1, 9)] (by decide +kernel) (by decide +kernel) low_7

def isoMv_23 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_iso isoMv_23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_27 : List (Nat × Nat) := [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_27 : Lower dom_27 roots_27 goal_27 5 :=
  lower_iso isoMv_27 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_29 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem low_29 : Lower dom_29 roots_29 goal_29 5 :=
  lower_iso isoMv_29 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_39 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_39 : Lower dom_39 roots_39 goal_39 5 :=
  lower_iso isoMv_39 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 6), (4, 5), (4, 6), (8, 9), (8, 24), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (16, 17), (16, 24), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 12, 12, 12, 16, 16, 18, 18, 18, 20, 20, 20]
def r2sG : List Nat := [3, 5, 9, 17, 3, 6, 5, 6, 9, 24, 11, 14, 26, 13, 14, 28, 17, 24, 19, 22, 26, 21, 22, 28]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [1142663021827, 1185613874449, 1142764864265, 1151219401477, 1142797960707, 1177156977923]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 5 => 3
  | 6 => 6
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x4f6731102515df9714e17f6b
  | 6, 0 => 0xb762f0af599be9b21f16380d14e17f6b09e2bbbd090d6eb4
  | 7, 0 => 0x1f16380d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaa000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc0000000000000000000000000000000000000000000000000000000055555555
  | 0, 1 => 0xffaaffaa00000000000000000000000000000000000000000000000000000000fff0fff0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x431065417655432105
  | 6, 0, 0 => 0x432170604317650432175043210549321764832176
  | 7, 0, 0 => 0x432175
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 24
  | 6 => 28
  | 7 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf00000000000000000000000000000000000000000000000000000000001f1f3f0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000e0e0c000000000000000000000000000000000000000000000000000000000001c1c300000000000000000000000000000000000000000000000000000000000fffff0
  | 0, 1 => 0xff0f0000000000000000000000000000000000000000000000000000000000e0ffc0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x25255f000000000000000000000000000000000000000000000000000000000017171d00000000000000000000000000000000000000000000000000000000006d00fb0000000000000000000000000000000000000000000000000000000000ff9208000000000000000000000000000000000000000000000000000000000092ff040000000000000000000000000000000000000000000000000000000000e8e8e200000000000000000000000000000000000000000000000000000000005c5cb10000000000000000000000000000000000000000000000000000000000dadaa0
  | 0, 1 => 0xb7ff5f0000000000000000000000000000000000000000000000000000000000faffe6
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 10 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 10 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 10 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 10 then wireAt i else 0
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
  | 5 => 6
  | 6 => 5
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x7f95d5887f482aa1599be9b2472e25f720f514d61f16380d
  | 6, 0 => 0xc3e14ac6974979bd564c9356202fbf561e29e5df
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x100000000000020000000000000000000000000200000000000030000000000002
  | 6, 0 => 0x20000000000004000000000000000000000000020000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 1 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 2 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 3 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 4 => checkCutEntry dom_25 roots_25 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31 == dom_31) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31 goalM u ys) : RunD dom_31 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
private theorem z6 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 0 = true)
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
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_31 goal_31 := by
    have h0 : isConstB dom_31 goal_31 = false := by decide +kernel
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

end S_31

theorem low_31 : Lower dom_31 roots_31 goal_31 8 := S_31.noCircuit

theorem low_47 : Lower dom_47 roots_47 goal_47 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff00, 1, 9)] (by decide +kernel) (by decide +kernel) low_39

namespace S_59
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (1, 17), (2, 3), (2, 34), (8, 9), (8, 24), (10, 11), (10, 26), (10, 42), (16, 17), (16, 24), (18, 19), (18, 26), (18, 50), (32, 34), (33, 35), (33, 41), (33, 49), (40, 41), (40, 42), (40, 56), (48, 49), (48, 50), (48, 56)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 8, 8, 10, 10, 10, 16, 16, 18, 18, 18, 32, 33, 33, 33, 40, 40, 40, 48, 48, 48]
def r2sG : List Nat := [3, 9, 17, 3, 34, 9, 24, 11, 26, 42, 17, 24, 19, 26, 50, 34, 35, 41, 49, 41, 42, 56, 49, 50, 56]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [44123005915401, 1143135085059, 36361362473745, 36362000666883]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xcf7e460ebc079af29113e543
  | 6, 0 => 0xf0260ba
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5050505050505050000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a000000000000000000000000000000000000000000000000000f000f000f000f
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x11d5d73a8ac6885
  | 6, 0, 0 => 0x47515
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
  | 0, 0 => 0x1f8fff80000000000000000000000000000000000000000000000000000000001ff800700000000000000000000000000000000000000000000000000000000003803e00000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001c07c00000000000000000000000000000000000000000000000000000000000000739800000000000000000000000000000000000000000000000000000000000700070000000000000000000000000000000000000000000000000000000001c7fc1f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1b0eb500000000000000000000000000000000000000000000000000000000001ffd6bf00000000000000000000000000000000000000000000000000000000013a2be20000000000000000000000000000000000000000000000000000000001ffc2100000000000000000000000000000000000000000000000000000000001e47d44000000000000000000000000000000000000000000000000000000000091f39900000000000000000000000000000000000000000000000000000000004f14af0000000000000000000000000000000000000000000000000000000000c5d41d
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
  | 4, 0 => 0x5c3ca4e9
  | 5, 0 => 0x8c1e741e6ecbae435bafac8c0f0260ba
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
  | 0 => checkCutEntry dom_25 roots_25 4 s ws hint
  | 1 => checkCutEntry dom_27 roots_27 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_59 == dom_59) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_59 goalM u ys) : RunD dom_59 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_59 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_59 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_59 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59 roots_59 goal_59 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_59 goal_59 := by
    have h0 : isConstB dom_59 goal_59 = false := by decide +kernel
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

end S_59

theorem low_59 : Lower dom_59 roots_59 goal_59 7 := S_59.noCircuit

theorem low_185 : Lower dom_185 roots_185 goal_185 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30303030000000000000000000000000303030300000000, 128, 160), (0x30303030303030300000000000000000000000000000000, 32, 160)] (by decide +kernel) (by decide +kernel) low_25

def isoMv_55 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55 : Lower dom_55 roots_55 goal_55 6 :=
  lower_iso isoMv_55 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_79 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_79 : Lower dom_79 roots_79 goal_79 7 :=
  lower_iso isoMv_79 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59

def isoMv_93 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem low_93 : Lower dom_93 roots_93 goal_93 6 :=
  lower_iso isoMv_93 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_167 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem low_167 : Lower dom_167 roots_167 goal_167 7 :=
  lower_iso isoMv_167 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59

def isoMv_199 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_199 : Lower dom_199 roots_199 goal_199 6 :=
  lower_iso isoMv_199 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_185

theorem low_63 : Lower dom_63 roots_63 goal_63 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffffffff00000000, 2, 34)] (by decide +kernel) (by decide +kernel) low_31

theorem low_111 : Lower dom_111 roots_111 goal_111 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff000000000000ffff00000000, 2, 34)] (by decide +kernel) (by decide +kernel) low_79

theorem low_187 : Lower dom_187 roots_187 goal_187 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f0f0f0f0f00000000000000000000000000000000, 32, 160)] (by decide +kernel) (by decide +kernel) low_59

theorem low_189 : Lower dom_189 roots_189 goal_189 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303030303030303000000000000000003030303030303030, 1, 5)] (by decide +kernel) (by decide +kernel) low_185

namespace S_235
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (2, 3), (2, 34), (8, 9), (8, 72), (10, 11), (10, 42), (10, 74), (32, 34), (32, 160), (33, 35), (33, 41), (33, 161), (40, 41), (40, 42), (40, 104), (40, 168), (64, 72), (64, 192), (65, 67), (65, 73), (65, 193), (66, 67), (66, 74), (66, 98), (66, 194), (96, 98), (96, 104), (96, 224), (97, 99), (97, 105), (97, 225), (128, 160), (128, 192), (129, 131), (129, 137), (129, 161), (129, 193), (130, 131), (130, 162), (130, 194), (136, 137), (136, 168), (136, 200), (138, 139), (138, 170), (138, 202)]
def r1sG : List Nat := [1, 1, 2, 2, 8, 8, 10, 10, 10, 32, 32, 33, 33, 33, 40, 40, 40, 40, 64, 64, 65, 65, 65, 66, 66, 66, 66, 96, 96, 96, 97, 97, 97, 128, 128, 129, 129, 129, 129, 130, 130, 130, 136, 136, 136, 138, 138, 138]
def r2sG : List Nat := [3, 9, 3, 34, 9, 72, 11, 42, 74, 34, 160, 35, 41, 161, 41, 42, 104, 168, 72, 192, 67, 73, 193, 67, 74, 98, 194, 98, 104, 224, 99, 105, 225, 160, 192, 131, 137, 161, 193, 131, 162, 194, 137, 168, 200, 139, 170, 202]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := [11412401424643, 152151393306952, 152150336348832]
def xsM : List Nat := roots_235.map (· &&& dom_235)
def goalM : Nat := goal_235 &&& dom_235
def NN : Nat → Nat
  | 6 => 3
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0x9a70f0b1467986fc286241c3
  | 7, 0 => 0x9a70f0b1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000000005050000050500000505000005050000050500000505000005050000050500000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000f0f00000f0f000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x3d8c86f6621ac6886
  | 7, 0, 0 => 0x3d8c86
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
  | 0, 0 => 0x1f803fe000000000000000000000000000000000000000000000000000000ff863f8fc7fc0000000000000000000000000000000000000000000000000000fc000003c1f00000000000000000000000000000000000000000000000000000e380078001cc00000000000000000000000000000000000000000000000000000079c07038030000000000000000000000000000000000000000000000000000fffe07fc01ff00000000000000000000000000000000000000000000000000000001fffc00000000000000000000000000000000000000000000000000000000fffe00000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x4923fa03fe880000000000000000000000000000000000000000000000000000db063f0f87a80000000000000000000000000000000000000000000000000000fc109127d1f20000000000000000000000000000000000000000000000000000e3884f908bcd000000000000000000000000000000000000000000000000000024f9c0f078570000000000000000000000000000000000000000000000000000b6dc05fc017700000000000000000000000000000000000000000000000000009245fffd01200000000000000000000000000000000000000000000000000000ffff244a2400
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_235 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_235 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xffffffff00000000ffffffff00000000, 96), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_235 == dom_235) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_235 goalM u ys) : RunD dom_235 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_235 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_235 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_235 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_235 roots_235 goal_235 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_235 goal_235 := by
    have h0 : isConstB dom_235 goal_235 = false := by decide +kernel
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

end S_235

theorem low_235 : Lower dom_235 roots_235 goal_235 8 := S_235.noCircuit

namespace S_237
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (4, 5), (8, 9), (8, 72), (12, 13), (12, 76), (32, 160), (33, 37), (33, 41), (33, 161), (36, 37), (36, 164), (40, 41), (40, 104), (40, 168), (44, 45), (44, 108), (44, 172), (64, 72), (64, 192), (65, 69), (65, 73), (65, 193), (68, 69), (68, 76), (68, 196), (96, 104), (96, 224), (97, 101), (97, 105), (97, 225), (100, 101), (100, 108), (100, 228), (128, 160), (128, 192), (129, 133), (129, 137), (129, 161), (129, 193), (132, 133), (132, 164), (132, 196), (136, 137), (136, 168), (136, 200), (140, 141), (140, 172), (140, 204)]
def r1sG : List Nat := [1, 1, 4, 8, 8, 12, 12, 32, 33, 33, 33, 36, 36, 40, 40, 40, 44, 44, 44, 64, 64, 65, 65, 65, 68, 68, 68, 96, 96, 97, 97, 97, 100, 100, 100, 128, 128, 129, 129, 129, 129, 132, 132, 132, 136, 136, 136, 140, 140, 140]
def r2sG : List Nat := [5, 9, 5, 9, 72, 13, 76, 160, 37, 41, 161, 37, 164, 41, 104, 168, 45, 108, 172, 72, 192, 69, 73, 193, 69, 76, 196, 104, 224, 101, 105, 225, 101, 108, 228, 160, 192, 133, 137, 161, 193, 133, 164, 196, 137, 168, 200, 141, 172, 204]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := [106843288896777, 154348988418240]
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
  | 0, 0 => 0x7f807ff800000000000000000000000000000000000000000000000000003f0000007e07800000000000000000000000000000000000000000000000000038e0707071864000000000000000000000000000000000000000000000000000001e0e0e0070300000000000000000000000000000000000000000000000000000007fff800000000000000000000000000000000000000000000000000000003fff800000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1248ff807ff800000000000000000000000000000000000000000000000000003f0424a4fe27a00000000000000000000000000000000000000000000000000038e2727271965000000000000000000000000000000000000000000000000000093e1e1e12f2f00000000000000000000000000000000000000000000000000024917fffa40500000000000000000000000000000000000000000000000000003fffc94949480
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

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
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

def isoMv_95 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_95 : Lower dom_95 roots_95 goal_95 9 :=
  lower_iso isoMv_95 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_63

def isoMv_175 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_175 : Lower dom_175 roots_175 goal_175 8 :=
  lower_iso isoMv_175 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_111

def isoMv_183 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_183 : Lower dom_183 roots_183 goal_183 8 :=
  lower_iso isoMv_183 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_111

def isoMv_207 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_207 : Lower dom_207 roots_207 goal_207 8 :=
  lower_iso isoMv_207 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_187

def isoMv_215 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_215 : Lower dom_215 roots_215 goal_215 7 :=
  lower_iso isoMv_215 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_189

def isoMv_221 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_221 : Lower dom_221 roots_221 goal_221 8 :=
  lower_iso isoMv_221 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_111

def isoMv_231 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem low_231 : Lower dom_231 roots_231 goal_231 8 :=
  lower_iso isoMv_231 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_187

def isoMv_238 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_238 : Lower dom_238 roots_238 goal_238 7 :=
  lower_iso isoMv_238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_237

def isoMv_249 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem low_249 : Lower dom_249 roots_249 goal_249 8 :=
  lower_iso isoMv_249 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_187

def isoMv_250 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_250 : Lower dom_250 roots_250 goal_250 7 :=
  lower_iso isoMv_250 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_237

theorem low_127 : Lower dom_127 roots_127 goal_127 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffffffff00000000ffffffff00000000, 2, 34)] (by decide +kernel) (by decide +kernel) low_95

namespace S_191
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 6), (2, 34), (4, 5), (4, 6), (8, 9), (8, 24), (10, 11), (10, 14), (10, 26), (10, 42), (12, 13), (12, 14), (12, 28), (16, 17), (16, 24), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (32, 34), (32, 160), (33, 35), (33, 37), (33, 41), (33, 49), (33, 161), (36, 37), (36, 38), (36, 164), (40, 41), (40, 42), (40, 56), (40, 168), (44, 45), (44, 46), (44, 60), (44, 172), (48, 49), (48, 50), (48, 56), (48, 176), (52, 53), (52, 54), (52, 60), (52, 180), (128, 160), (129, 131), (129, 133), (129, 137), (129, 145), (129, 161), (130, 131), (130, 134), (130, 162), (132, 133), (132, 134), (132, 164), (136, 137), (136, 152), (136, 168), (138, 139), (138, 142), (138, 154), (138, 170), (140, 141), (140, 142), (140, 156), (140, 172), (144, 145), (144, 152), (144, 176), (146, 147), (146, 150), (146, 154), (146, 178), (148, 149), (148, 150), (148, 156), (148, 180)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 12, 12, 12, 16, 16, 18, 18, 18, 18, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 36, 36, 36, 40, 40, 40, 40, 44, 44, 44, 44, 48, 48, 48, 48, 52, 52, 52, 52, 128, 129, 129, 129, 129, 129, 130, 130, 130, 132, 132, 132, 136, 136, 136, 138, 138, 138, 138, 140, 140, 140, 140, 144, 144, 144, 146, 146, 146, 146, 148, 148, 148, 148]
def r2sG : List Nat := [3, 5, 9, 17, 3, 6, 34, 5, 6, 9, 24, 11, 14, 26, 42, 13, 14, 28, 17, 24, 19, 22, 26, 50, 21, 22, 28, 34, 160, 35, 37, 41, 49, 161, 37, 38, 164, 41, 42, 56, 168, 45, 46, 60, 172, 49, 50, 56, 176, 53, 54, 60, 180, 160, 131, 133, 137, 145, 161, 131, 134, 162, 133, 134, 164, 137, 152, 168, 139, 142, 154, 170, 141, 142, 156, 172, 145, 152, 176, 147, 150, 154, 178, 149, 150, 156, 180]
def mpG : Nat := 0x7fffffffffffffffffffff
def pool6G : List Nat := [151923942491682, 57364137969944, 36913265771281, 142440611251717, 36329292858121, 142466548630787, 36507961787665, 36878763950882, 36473736529161, 36509671883525, 160752589931270, 142432054674691, 36475186546181, 44123073283337, 151958436447778]
def xsM : List Nat := roots_191.map (· &&& dom_191)
def goalM : Nat := goal_191 &&& dom_191
def NN : Nat → Nat
  | 6 => 7
  | 7 => 45
  | 8 => 79
  | 9 => 14
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xc4844849b6b565508ac569243de1c12021ec8a8e0dc3127306abf93f
  | 7, 0 => 0xde4ff9cfde3238d0dd0af760dc374ae7d766b567a5afdea88f384bf48d63181e897241da80a341187c81633c7bcbd22c77f7b40a76eb565974620e3771590fce712fa29471254c3f6402e77662def81c5dc2c1b45cea442a5cc25c2357fcb79a3fdd141a36fae83d335cea572fa850552fa20b0d2ee9b9d52de8c2982cc181282bedd4af2ae506c4251efcaa21627bdf1b1ace4317ebb7e5166e6f0d13286e5412cbe1c5112a606d0c737ef50b9b016b06ad74db
  | 8, 0 => 0xa7e20143a42d6741a2f474b3a21bf7299d9fa1479c55d79490437cab8e6c656d8c92eccb8b4906c984f5ebf87ca055a57016b9c36d2ecc906b58b1d75f4cd1c15b25db0d585a2153580e79af5692be8455f642e852de248251a531f450ccb46a4f57c8e44da0f7e54d968cb34b0694d548a900234771fe0f448ec46c3fff624e3f81d2533ef439ec3a30f05b369dc76e346ae6412cb50fa529eda57228abbf23251d34442444b6ba23717f6e2363ebcf2341e0b622cfcb34223caa5f2168fde621689a4220901cb81f572a2a1e7e97251de23ea41ae21bab19910a95142084d312d9a466126c3c3c105cf5370d7eafac0ca6322204a7002902adb7ae02404b10
  | 8, 1 => 0xfdea6e1dfa501f54f7b38f93f5267a4ee8c54d2dd469fef3cb9afe31cb2b91e3c7e6642fc63e0553c3231a9eb885a198b741a74db649c130abbd54f3
  | 9, 0 => 0xed13b4429bc471837f62a35a6f3c73d36b87d9d16a4ee743697669b968017e3363b04a24579def3b431c211c1d50b578105d44e20854cd9d
  | 10, 0 => 0xb46e26d2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfafafafafafafafa0000000000000000fafafafafafafafa0000000000000000eeeeececeeeeecec0000000000000000eeeeececeeeeecec0000000000000000ffffffff000000000000000000000000ffffffff000000000000000000000000ffffaaa0ffffaaa00000000000000000ffffaaa0ffffaaa00000000000000000ffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000000ffffffffffffffff00000000000000000000000000000000
  | 0, 1 => 0xffffaa88ffffaa880000000000000000ffffaa88ffffaa880000000000000000fafaf8f8fafaf8f80000000000000000fafaf8f8fafaf8f80000000000000000f8f8f8f8f8f8f8f80000000000000000f8f8f8f8f8f8f8f80000000000000000eeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeee000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00000000000000009999999999999999000000000000000099999999999999990000000000000000ffff0000ffff00000000000000000000ffff0000ffff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00
  | 0, 2 => 0xffff0055ffff00550000000000000000ffff0055ffff00550000000000000000ffffffffffffffff0000000000000000aaaaa0a0aaaaa0a000000000000000005555555555555555000000000000000055555555555555550000000000000000ffffffffffffffff0000000000000000cccccccccccccccc0000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa000000000000000033333333333333330000000000000000333333333333333300000000000000000000ffff0000ffff00000000000000000000ffff0000ffff0000000000000000111111111111111100000000000000001111111111111111
  | 0, 3 => 0xdddddddddddddddd0000000000000000dddddddddddddddd000000000000000044444444444444440000000000000000444444444444444400000000000000000000000000000000000000000000000033333333333333330000000000000000ffffffffffffffff000000000000000088888888888888880000000000000000ffffffff888888880000000000000000ffffffff888888880000000000000000aaaaa0a0aaaaa0a00000000000000000aaaaa0a0aaaaa0a00000000000000000faf8faf8faf8faf80000000000000000faf8faf8faf8faf80000000000000000ffff8888ffff88880000000000000000ffff8888ffff8888
  | 0, 4 => 0x77007700770077000000000000000000770077007700770000000000000000e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0e00000000000000000ffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaa0000000000000000aaaa8888aaaa88880000000000000000aaaa8888aaaa8888000000000000000088888888888888880000000000000000888888888888888800000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000eeeceeeceeeceeec0000000000000000eeeceeeceeeceeec0000000000000000ffffffffaa88aa880000000000000000ffffffffaa88aa88
  | 0, 5 => 0xffffffffffffffff0000000000000000aaaa8888aaaa88880000000000000000aa88aa88aa88aa880000000000000000aa88aa88aa88aa880000000000000000aaa0aaa0aaa0aaa00000000000000000aaa0aaa0aaa0aaa000000000000000000e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0e0000000000000000ffffffffaaa0aaa00000000000000000ffffffffaaa0aaa00000000000000000fcfcfcfcfcfcfcfc0000000000000000fcfcfcfcfcfcfcfc0000000000000000f1f1f1f1f1f1f1f10000000000000000f1f1f1f1f1f1f1f10000000000000000ffffffffffffffff00000000000000004444444444444444
  | 0, 6 => 0xfffafffafffafffa0000000000000000fffafffafffafffa0000000000000000f5f5f5f5f5f5f5f50000000000000000f5f5f5f5f5f5f5f500000000000000000000555500005555000000000000000000005555000055550000000000000000fffff0f0fffff0f00000000000000000fffff0f0fffff0f00000000000000000ff55ff55ff55ff550000000000000000ff55ff55ff55ff550000000000000000fefefefefefefefe0000000000000000fefefefefefefefe0000000000000000fff0fff0fff0fff00000000000000000fff0fff0fff0fff00000000000000000ffccffccffccffcc0000000000000000ffccffccffccffcc
  | 0, 7 => 0xffff5555ffff55550000000000000000ffff5555ffff55550000000000000000ffffffffffffffff0000000000000000eeeeeeeeeeeeeeee00000000000000002222222222222222000000000000000022222222222222220000000000000000ffffeeeeffffeeee0000000000000000ffffeeeeffffeeee000000000000000005050505050505050000000000000000050505050505050500000000000000000033003300330033000000000000000000330033003300330000000000000000fffffcfcfffffcfc0000000000000000fffffcfcfffffcfc0000000000000000000f000f000f000f0000000000000000000f000f000f000f
  | 0, 8 => 0xffffccccffffcccc0000000000000000ffffccccffffcccc0000000000000000ff88ff88ff88ff880000000000000000ff88ff88ff88ff880000000000000000ffffffffffffffff0000000000000000ffffccccffffcccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x289103480060a3c18202018289103860060a2468c16018289100850060a244070c01828406080806
  | 7, 0, 0 => 0xa244023e78038512080933a2dc289040499c16e6c482024c58070a2440d0254038510340932201c28f100809300e144880e04d0070a60402184c03851220c812601c298100809500e14b88040498070a24402024cb38512201142a49c288045491100e14402284c9117
  | 7, 0, 1 => 0xa244260254038512201012aa1c284100809300e14482024d38070a21301264403854a201014801c298040498b00e144882804aa270a200954444038512201232001c28828049a222e14488048498074024402024c03800a2440d18018289103461300e144822804a8b7
  | 7, 0, 2 => 0x1448804049af70a244020254eb8512201013855cd89100809500e14488043170070a2418202b403851220a924401c28910049ac00e14413248888070a2010c464403ab12201012601c28910a838c00e1448852049807
  | 8, 0, 0 => 0xa24402280499580a20101265488080014402280499170a258080404a8080a25888045009380a24382024c58080a25808045009380a24402024d70080a24101268c58080a244021804a8080a24402024d68080a24402185009380a2010c024c88080a24188044c90080a2442a043098080a244023e04a808
  | 8, 0, 1 => 0xa24436040498080a24402184c90080a24402025490080a244020254f0080a20101264888080a24402024da8080ad04880e0498080a25988040498080014488045009570014402025488070a24432040498080014488040499d70a25808043098080a258880404a8080014488040499c7006c48804049807
  | 8, 0, 2 => 0xae4488040498080014c08040498070a24402024dc0080014488045490070a24188024d10080a24402265490080014488045099270014402264888070a25888044c90080a25502024c58080a944880404a8080a25808044c90080a94488045009380a244023e0498080a25b88040498080a258b004049808
  | 8, 0, 3 => 0x14488025510070a2440126551008001448828049a270014401268888070a24402024de8080a25808024d10080a2440c024d10080b00488045009380afc4880404a8080a244027c5009380a244022649e8080af04880404980800144881a0498070a24402024dd8080a24402024dd0080a2440c4c049808
  | 8, 0, 4 => 0xa2442a0404a8080a244360404a8080a24407044c90080ad1288040498080a24402024c80080014488264910070014488043118070a244070404a8080a24402184d18080a24407045009380a24402028ca8080a2442a0e0498080a24407043008080b09288040498080a2608804049808
  | 9, 0, 0 => 0x14488024d10070014488044c90070a24402024c900800144880404a8070a24402024ca8080014488045009370014402024c88070a25888040498080a25808040498080a24402180498080a2442a040498080a24188040498080a24407040498080a24402024d1808
  | 10, 0, 0 => 0x1448804049807
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 46
  | 7 => 53
  | 8 => 60
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
  | 0, 0 => 0x780f01c7de1e1fe703818f0000000000000000000000000000000000000000000780f03800000000f07870000000000000000000000000000000000000000000000000001ffffff80000000000000000000000000000000000000000000000007ff000001fe00007fc0000000000000000000000000000000000000000000000000ffe07c01fe3e003fe0f000000000000000000000000000000000000000000780f01c01e1e1c070381800000000000000000000000000000000000000000000780f03800000000f078700000000000000000000000000000000000000000007fffffffe0000000000000
  | 0, 1 => 0x7ff000001fe00007fc0000000000000000000000000000000000000000000000780f01c01e1e1c07038180000000000000000000000000000000000000000000780f01c01e1e1c070381800000000000000000000000000000000000000000000780f03fc00003e0f0787f0000000000000000000000000000000000000000007ff001ffffe01ffffc01ff000000000000000000000000000000000000000000787f0fc03ffffc1f0f87800000000000000000000000000000000000000000007ff000001fe00007fc0000000000000000000000000000000000000000000000000ffe00001fe00003fe00
  | 0, 2 => 0x7ff001f83fe01c1ffc01f00000000000000000000000000000000000000000007fffffffe00000000000000000000000000000000000000000000000000000007ffffff83ffffc1ffffff00000000000000000000000000000000000000000007fffffffe0000000f0787000000000000000000000000000000000000000000000000007c00003e000000f000000000000000000000000000000000000000000787f0fc7ffffffff0f878f000000000000000000000000000000000000000000000fffffe01ffff803ffff000000000000000000000000000000000000000000787f0fc03ffffc1f0f8780
  | 0, 3 => 0x7ffffff83ffffc1ffffff00000000000000000000000000000000000000000000780f03800000000f07870000000000000000000000000000000000000000000000000001fffffff0f878f0000000000000000000000000000000000000000007fffffffe0000000000000000000000000000000000000000000000000000000000000001ffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000780f01c01e1e1c070381800000000000000000000000000000000000000000007ff000001fe00007fc0000
  | 0, 4 => 0x7ff001ffffe01ffffc01ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007ff00007dfe003e7fc000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007f0fe3fe1e1e3f8fc7e7f0000000000000000000000000000000000000000000780f03800000000f07870000000000000000000000000000000000000000000000000001ffffff8000000
  | 0, 5 => 0x7fffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000780f03fc00003e0f0787f000000000000000000000000000000000000000000000000001ffffff80000000000000000000000000000000000000000000000007f8ff1f81e1e1c07f3f9f0000000000000000000000000000000000000000000787f0fc03ffffc1f0f87800000000000000000000000000000000000000000007fffffffe0000000f07870
  | 0, 6 => 0x780fffc7de1fffe703ff8f0000000000000000000000000000000000000000007ffffff83ffffc1ffffff0000000000000000000000000000000000000000000000ffff8201ffc1803fff00000000000000000000000000000000000000000007fff01c01ffe1c07ff81800000000000000000000000000000000000000000007ffffff83ffffc1ffffff00000000000000000000000000000000000000000007f8ff1ffde1e1fe7f3f9ff000000000000000000000000000000000000000000780fffc01e1ffc0703ff80000000000000000000000000000000000000000000078ffe38001fe000f3fe70
  | 0, 7 => 0x7ffffff83ffffc1ffffff00000000000000000000000000000000000000000007fffffffe00003e0f0787f00000000000000000000000000000000000000000000000007c00003e000000f0000000000000000000000000000000000000000007ff0f03fdfe003e7fc787f00000000000000000000000000000000000000000007f0fe3821e1e018fc7e70000000000000000000000000000000000000000000787001c7ffe01fff0c018f0000000000000000000000000000000000000000007ffff1f81ffe1c07fff9f000000000000000000000000000000000000000000007f0003fe1e003f8fc007f
  | 0, 8 => 0x7ff0f0381fe00007fc7870000000000000000000000000000000000000000000000ffe00001fe00003fe000000000000000000000000000000000000000000007fffffffffe00007fc7870
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x799f33dfde3e3fe7379bbf0000000000000000000000000000000000000000001f93f0fac6664d6bf5f9fb000000000000000000000000000000000000000000444889243ffffff88040400000000000000000000000000000000000000000007ff556439feaa5c7feae8e0000000000000000000000000000000000000000002abffe4fcabfe7e55ffe9f000000000000000000000000000000000000000000790f21d09e1e1c472391a20000000000000000000000000000000000000000001782f0b84444482af179710000000000000000000000000000000000000000007ffffffff1111210000000
  | 0, 1 => 0x7ff5560b5feaa1a7feae1d000000000000000000000000000000000000000000799f31dade3e1d673799bb000000000000000000000000000000000000000000798f31d8de1e1c673399b30000000000000000000000000000000000000000001f93f2ffc6666febf5fbff0000000000000000000000000000000000000000005dd001fef7601f7bb401fb00000000000000000000000000000000000000000060ec1d08799990341a0c110000000000000000000000000000000000000000007ff444021fe88107fe2408000000000000000000000000000000000000000000222ffe01089fe0844bfe04
  | 0, 2 => 0x7ff445b23fe8991ffe25680000000000000000000000000000000000000000007ffffffff333175114808a000000000000000000000000000000000000000000776eedb03dddd81eeb75600000000000000000000000000000000000000000007ffffffff5555a3af179710000000000000000000000000000000000000000000891124fc22227e1148a9f000000000000000000000000000000000000000000687d0f47bbbbb7d50e868e000000000000000000000000000000000000000000000bbbfde0177ef801dbf7000000000000000000000000000000000000000000606c0d00399990140a0400
  | 0, 3 => 0x77eefdb87dddd83efb7d710000000000000000000000000000000000000000001702e0b00444480ae17160000000000000000000000000000000000000000000000000000aaaa5c50e868e0000000000000000000000000000000000000000007ffffffff111123010081100000000000000000000000000000000000000000044c8992c7ffffff8904851000000000000000000000000000000000000000000089100428222054114808a000000000000000000000000000000000000000000798f33d9de1e3ce7339bb70000000000000000000000000000000000000000007ff4540a5fe88127fe2c19
  | 0, 4 => 0x5d5001f6b7601f5ba401ea000000000000000000000000000000000000000000190320d086060c432191a20000000000000000000000000000000000000000007ff5564fdfeaa7e7feae9f0000000000000000000000000000000000000000000890100a42200121140819000000000000000000000000000000000000000000008010084000002010081100000000000000000000000000000000000000000006f0de2f61e1e3b8dc6e5d0000000000000000000000000000000000000000001f83f2f9c6466cebf1fbf700000000000000000000000000000000000000000044c99b2d7ffffff890ca55
  | 0, 5 => 0x7ffffffff331133114081900000000000000000000000000000000000000000000811209400220a0108a1500000000000000000000000000000000000000000008011241820224c1008a860000000000000000000000000000000000000000000690d22f406063a8d46a5d0000000000000000000000000000000000000000004c499b65bffffff980cac60000000000000000000000000000000000000000007f8ff1f8de5e5c6ff3f9f3000000000000000000000000000000000000000000796f2dd0bf9f9c572b95a20000000000000000000000000000000000000000007ffffffff5555a1ae17160
  | 0, 6 => 0x7bbfffdfdebfffe77fffbf0000000000000000000000000000000000000000007f6fedf0bfdfdc5febf5e2000000000000000000000000000000000000000000000aa9b0201558180151600000000000000000000000000000000000000000007fff65d29ffe9d47ffb5aa000000000000000000000000000000000000000000776fffb13ddff89eebff640000000000000000000000000000000000000000007f9ff3ffde7e7feff7fbff0000000000000000000000000000000000000000007b2fffd19e9ffcc76bffa600000000000000000000000000000000000000000037affeb94cdfe8aefbff75
  | 0, 7 => 0x7ffeedb23ffdd91fff75680000000000000000000000000000000000000000007ffffffff7777ffbf5fbff00000000000000000000000000000000000000000008110247822227c104828e0000000000000000000000000000000000000000007ff7f6ffdfeeefefffffff0000000000000000000000000000000000000000000660cc2021c1c018c8644000000000000000000000000000000000000000000048500146b320175104008a0000000000000000000000000000000000000000007ffff5fadffedd6ffffdfb00000000000000000000000000000000000000000004d0002e61600338940059
  | 0, 8 => 0x7ff6f4ba5fecc92fff7d7900000000000000000000000000000000000000000022affe09489fe0a45bfe150000000000000000000000000000000000000000007ffffffffffddb3fff7d79
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 67 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 67 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 67 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 67 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 6 => 14
  | 7 => 168
  | 8 => 336
  | 9 => 33
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0xf683cc19da4f01bed8edb4ddd59e0540d002e30fa24160d752893ebc47d30ed8463a55e1420d04be335cea573240846b19b2583102caa984
  | 7, 0 => 0x45c2973b4487f9fb445d121242ef410441caa2983fb06c043f9a6d6b3f8478f03ec1efe13bb57f18396981be3895d54532b94d47325295c5314c55952ec98d832d0aba582a95e1912a3d4ed629dc00f3291ce0a227c7e08026007db125f77a3423f2923720ea9d84203a73971f0505a71d53727a1cdb946d1cdb02271cb7d6051c02849d1c0265851bc0c16a1a48455d19e287eb1979ba8d18c1ff741708d12a16fb1c2e16e8a4a016674354150b53a213b94aef131ab85a1257d4ac1179b6c40f2d81680e3ae1c40d1ea32c0cbcb27b0caf98960b78e7660aba36800992f5100967774e08bf4897085c216c082f668807f28bc804408ba10431df1e03a157b9
  | 7, 1 => 0x95231b5d916e0919915ce2298dff13dd8d04c1d78c705d9c8a4abf648963d8a4874391228679b3a2858dea61852de654817bbea280ecbc6d7be524507bb8cbba787cb291779b7858774fc0707738217b76ba30a576ab19dc755953ed7344f6b871fdc9c97189b656711f0e74710ff7ab70ccace97016b9c36f86f8b26f3c73d36ebbd86f6ddc191a6d7719966a87b0176a4ee743697669b9689b1dad6840f6e9672cd1cb63ad911d5fcf9a5f5f1ca3fe5c5f9c595c09793f5b518b335ae237cf5a0e8b56595699e4585a2153576d04745744c1ef5710329f51aa50fe4f9297724f30ce0a4e508c674dc46da94a231c2c496ac3f0492f09c9488a6335470c1fa6
  | 7, 2 => 0xfe0de3e1f9ad0855f96ec1c5f8d3d96df78efcd0f693243cf338b73cf14decbaee4b2aaced13b442e2ead830e08727bfdcfc90d6d749be57d5327475d3ee7a2ad349e0b7ceee7d5ccd250aa5cd080e79c84d6051c3cbc964c3aa18cfc2d26c69c1c32cfcc05d24ddc009e487bee2a317b47b5556b46e26d2b04e5277aca0cdf2a3d7be20a3735409a1c9d2a69bc471839b08bd5e97341333964a6eb9957acabe
  | 8, 0 => 0x245095a22297b84421a3be43213fde2921100e5620f5ed01207f9f572012a6a41eadb4ef1d09c11a1cb8aa111c089c121be488711b4273011ad3c5081ab9953d1a71d1b11a3ac2601a2d6e6819775b5c19774dcd18c4a28518b88d0b188348f917787ed916af5f521605628315fd2e591584452114a80e6113add4d5139baee21289e04912763f071256bda41252890111b3040a11969d40117d8ebc112f058c10c7fa9210a849961049605f0f5c099b0e15acc70de293160dc8f4ba0c8c7ee70be26c8b0bb784a20ba6e0530b06744a0a42991c08f43e88082dd289072e2d4106f4dffb061c627105f1650d0509627604a776eb0323a0590258a0c3005642dc
  | 8, 1 => 0x498088fd4902d252476f849246f9cf6146aad0ca46a3ffa04613b7f84540b97d4521ca3d44007c8943d88f53433f96e042c8c508414b5d5340fa5b0d4068846d40532ced4023ac923fd3bab13f7aaf633f42e5bf3ee8b1393eda86b13eaa33003e10258b3e058c6c3d89c22c3ca5d9e53b3279d13af598fe39a3085d38e428e6386a6a3b376f3d60354363cb35095a9b34b9e8e734820a5933347ac9331e095131a6407530a294a7309f17953091e4ed2f6e386a2d44b7932d1700e42c955da12c7e6ed62bb508172bae84252b8e80ba2adc8a8d2acbdad32aafaebf2a726bcd2a40528f29ccd5d9285fbc8728572b0327d58c41274accb4270bae6825e37991
  | 8, 2 => 0x7f62a35a7d8d87837caa29307bcf7a6d7bc1ae8c798b1142796e58f07933e540789a0f737623512a755beedf754fa4b175244dee73fb408271c8b72d7036c15e6f5e43d46ead17be6e96280a6b87d9d16b3230b06a285b7969c489c4698c67dd6924453668804de06726160166fa41b6636738716345a7b462f5a114627e5da36235fedf607426005ee84e275d2a92575d19e29d5cc30cff5a89a63c59ccb54359591a8357f8de4f57b086ef569c57575603626f559c19ac548dbc9a545f346753a5fd5853931069526b7741510589d35103ad504ed062874ec582bc4d7fdf4a4d079d074cc2770d4c17fd434bce23ee4b8494344a95b5e94a7958cc4a744ead
  | 8, 3 => 0xaa95e886aa6a8e1caa403004a9f05084a9d090a2a979b65ba8f81318a8aa7439a6a496fba4fac655a44e56fda42a466aa3bce7a9a3baba00a34bc520a2e46a1fa2a2a6eca1ce46bca1ac4b9ea0a70ba39e6fa8559e56dfc69d4d167b9c7949d59c562df99ba01aed9aed62169a92791f99188fdc9768a16995ffd58695da10d395a4ec8f9553de7f954fbf48952757fc94cc6f05946281099172ef519029c9708fe1d6ca8f54cf2b8e7bb1468e679ed78c2d3cc88b1cfe198ad3f49189b9acfa8987cf91897a124788a194bd8867d15187ec88d48763baba8711a3ec862f718985e1183383cf9486837eab358342e3828191dec38115d12980c589658079d536
  | 8, 4 => 0xe837384de55d3c05e1b37391e056fdb6dfcb040fdfc219d4dd4b3a2cdc65c632dc572d5edbc7be25db7c21b8db461ae2d9246a60d87878b5d7c28ccad77d29d6d6784e34d5684658d53271e9d5090f61d39951d6d0e318add00a3e83cb7c65c5c9ce5fb5c8de2ba9c8ccbf31c8bd9c84c828189dc7755fc6c71a76cfc4f18499c3fd608ec3bb671fc3ad780fc201bf4cc1a3a1c7c11170cac003f809bf8df863be358e0ebc81736fbc1d0958baef9c87b80830cab46e26d2b3cf0006b2d2b076b29e5fcbb124aa66affec624afc2df07af3fc075af393008aee17376aebe1d32ae79d516ae69255cadccd0acad033d9aacd1e5ebac5f3690ab1bf802aaffe974
  | 8, 5 => 0xff5f685afac2cf04f9df0a24f9ad0855f8fce18df5d54274f554bce1f443e7f3f1798249f026df25efab184eef8835e8ed996e7aeb6d6496eab837dee9389a23
  | 9, 0 => 0xf900b305f4717374f3efd031ef220383eddc2738e0d1cdece01f1515dfc42c1ed39951d6ba5600edb46e26d29fbb593b9e8acd828a726c7c83dbe5ff75d447a675c397ec72766a926b152c9065b152565fa384b05caa31d858cd61e157843c0056af41bb51141f8a3ff482033221031c0dfe72300a85b57c0a233798072e2d41064323c9
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x8062030000000000004000000000000000041264403020004125440303000001500220300000000000000000002802203000000380620300000028122030000000000001000000000000400000038022030004126440302
  | 7, 0 => 0xe100000000080e20200000000000000000000000000000000000000400000000000050000000000005000000000000400000000000010000000000008000000080e203000000000a103000000000000300000000021050000026440202000000000e10300000000021030000000000001000000000000400000254402030000000000001000000000210300000000061020000000000001000000001210300000000000010000000000000000000000000700000000c91030000000000004000000380620200000000c5103
  | 7, 1 => 0x55108000000080a2030000002812202000000380620300000000000020000000000001000000000a103000002644020200000028122030000000006103000000000000100000000000010000000101103000000280620200000000021080000000002107000000000000100000000061030000000000005000000005110700000000000040000046440202000000080620200000000000010000000002108000000000000500000048062020000000055108000000000a107000000180e2020000000055100000000000a105
  | 7, 2 => 0x2000001044020200000000000030000000000008000000000000200000008122020000000002107000001044020300000000000000000000051107000000000000000000000021000000000055105000000000000a000000000610700000000000040000000000004000000000e10000000000000010000000000001000000000610200000000000060000000000000000005644020200000000021030000000006100000000000e103000000080a2020000000012103000000080e20200000038062020000000000007
  | 7, 3 => 0x6107000000001210300000000551000000000000000000000000a103000000000000000000000000040000000000005000000000000100000000000060000000000000000000000000900000000000010000000000006000000000a103000000000610300000001051030000000000003000000080a2020000000006108000003644020200000028062020000000041103000000000000400000000000090000002812202000003544020300000028062030000000006108000000000000100000000000010000000806202
  | 7, 4 => 0x610300000028062020000000000001000000000a1000000000002100000000000000100000000000010000000000001000000000000400000000000030000000806202000000000a10300000000000010000000002100000005644020200000000061000000000002103000000000000100000000061030000000040103000000080620200000000000020000000081103000000000a10700000028062020000000000004000000000a10800000008062020000010440202000000000210300000000021000000000006103
  | 7, 5 => 0x21030000000006102000000000000100000008062020000000041103000000000610300000008062030000000000006
  | 8, 0 => 0x85102000000000000000000000000020000000002102000000000e105000000000610500000000021020000000000008000000000e1020000000000001000000004010300000000021020000000000005000000000000800000000021020000000012102000000000210300000000121020000000006103000000000000200000000c9102000000000a108000000000210300000000121020000000000003000000001210300000000c5102000000010510300000000c910300000000c5102000000000a10200000000c5103
  | 8, 1 => 0x610300000000851020000000006102000000000000000000000000040000000055105000000000210200000000000080000000000008000000000000700000000411030000000006103000000000000000000000021020000000000002000000001210200000000021000000000002103000000000a103000000000a1020000000006105000000000a1030000000000007000000000e10200000000021020000000000007000000000000800000000551050000000055100000000000e103000000000e1080000000002102
  | 8, 2 => 0x610300000000c91020000000000001000000010110200000000000000000000000003000000000a10800000000c5102000000000a10700000000021030000000000003000000000210200000001011030000000002108000000000a102000000000a103000000000000500000000000030000000041103000000000e10000000000121030000000012102000000000000500000000000040000000000005000000000e108000000000000100000000551080000000000008000000000610300000000411020000000002105
  | 8, 3 => 0x50000000000000000000001210200000000061000000000000000000000000a102000000000000300000000021000000000000003000000000610200000000000070000000000003000000000a10300000000000070000000000004000000000000800000000551000000000006102000000000a105000000000e1000000000000002000000000a10200000000061020000000002102000000000000800000000061020000000000002000000000e1050000000000001000000000210200000000000070000000012102
  | 8, 4 => 0x101102000000000000200000000811030000000006103000000000610200000000000000000000002105000000000610800000000021020000000000008000000001210200000000000040000000000001000000005510500000000021020000000000003000000001210200000000121020000000006105000000000210800000000c9103000000000610200000000000080000000000000000000000610200000000000080000000055108000000000000000000000000050000000002105000000000e1030000000000008
  | 8, 5 => 0x61020000000006108000000000610000000000000010000000000000000000000000000000000000080000000000000000000000a103000000000000100000000000030000000000001000000000210300000000000070000000006100000000000000300000000121030000000000001000000000000000000000021020000000006102000000000a1000000000000001000000000000500000000000080000000000008000000000000800000000000000000000000006000000000000000000001051030000000085103
  | 8, 6 => 0x551000000000000000000000000a1020000000012103000000000e1000000000000003000000000a102000000000a1020000000000008000000000a10200000001091020000000002100000000000000800000000021080000000000000000000000a10300000000000030000000055100000000000e100000000000a102000000000000000000000c9103000000000610500000000551080000000006102000000000610200000000000020000000000003000000000000700000000c110300000000551000000000000001
  | 8, 7 => 0x401020000000081102000000000e1050000000002102000000000000300000000121020000000012103000000000210000000000000050000000040103000000000000000000000121020000000055100000000000a1050000000000003000000000e10000000000000000000000000006000000000610300000000000000000000000000000000000a1020000000000007000000000000200000000021030000000002102000000000210300000000021000000000000002000000000000300000000000030000000012102
  | 8, 8 => 0x100000000851030000000000001000000000000000000000000020000000002102000000000000300000000121030000000000001000000000a10200000000000000000000006100000000000000400000000000020000000002107000000000610200000000811020000000006103000000000000400000000000070000000002102000000000000100000000511070000000002103000000000a103000000000a1020000000000005000000008110300000000000000000000040102000000000a1080000000101102
  | 8, 9 => 0x3000000008510200000000000000000000006107000000008110200000000851030000000006102000000000000300000000000010000000006102000000000000000000000061030000000012102000000000000a000000004010200000000000010000000006102000000004110200000000061000000000002103000000000a10200000000000050000000000007000000000610200000000000030000000006103000000000210200000000000050000000006102000000000610300000000061000000000002103
  | 8, 10 => 0x7000000000210300000000411020000000006102000000000000400000000000030000000006102000000004110300000000061030000000000001000000000000100000000021000000000006102000000000210300000000000000000000000003
  | 9, 0 => 0x20000000000003000000000000200000000000000000000000002000000000000300000000000000000000000000000000000000300000000000020000000000005000000000000200000000000000000000000002000000000000300000000000020000000000008000000000000500000000000020000000000000000000000000200000000000020000000000002000000000000200000000000030000000000003000000000000500000000000020000000000003000000000000300000000000050000000000002
  | 9, 1 => 0x7
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 10 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_187 roots_187 8 s ws hint
  | 1 => checkCutEntry dom_189 roots_189 7 s ws hint
  | 2 => checkCutEntry dom_63 roots_63 9 s ws hint
  | 3 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 4 => checkCutEntry dom_185 roots_185 6 s ws hint
  | 5 => checkCutEntry dom_175 roots_175 8 s ws hint
  | 6 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 7 => checkCutEntry dom_167 roots_167 7 s ws hint
  | 8 => checkCutEntry dom_183 roots_183 8 s ws hint
  | 9 => checkCutEntry dom_59 roots_59 7 s ws hint
  | 10 => checkCutEntry dom_25 roots_25 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_191 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_187 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_189 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_63 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_185 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_175 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_167 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_183 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_191 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_191 == dom_191) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_191 goalM u ys) : RunD dom_191 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_191 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 32 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := (range_split z7_0 (range_split z7_16 z7_32))
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
private theorem z8_64 : ∀ i, 64 ≤ i → i < 79 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 15 64 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 79 → Z 8 i = true := (range_split (range_split z8_0 z8_16) (range_split z8_32 (range_split z8_48 z8_64)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 14 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 14 0 = true)
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
  scr dom_191 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_191 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_191 roots_191 goal_191 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_191 goal_191 := by
    have h0 : isConstB dom_191 goal_191 = false := by decide +kernel
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

end S_191

theorem low_191 : Lower dom_191 roots_191 goal_191 11 := S_191.noCircuit

namespace S_239
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 6), (2, 34), (4, 5), (4, 6), (8, 9), (8, 72), (10, 11), (10, 14), (10, 42), (10, 74), (12, 13), (12, 14), (12, 76), (32, 34), (32, 160), (33, 35), (33, 37), (33, 41), (33, 161), (36, 37), (36, 38), (36, 164), (40, 41), (40, 42), (40, 104), (40, 168), (44, 45), (44, 46), (44, 108), (44, 172), (64, 72), (64, 192), (65, 67), (65, 69), (65, 73), (65, 193), (66, 67), (66, 70), (66, 74), (66, 98), (66, 194), (68, 69), (68, 70), (68, 76), (68, 196), (96, 98), (96, 104), (96, 224), (97, 99), (97, 101), (97, 105), (97, 225), (100, 101), (100, 102), (100, 108), (100, 228), (128, 160), (128, 192), (129, 131), (129, 133), (129, 137), (129, 161), (129, 193), (130, 131), (130, 134), (130, 162), (130, 194), (132, 133), (132, 134), (132, 164), (132, 196), (136, 137), (136, 168), (136, 200), (138, 139), (138, 142), (138, 170), (138, 202), (140, 141), (140, 142), (140, 172), (140, 204)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 12, 12, 12, 32, 32, 33, 33, 33, 33, 36, 36, 36, 40, 40, 40, 40, 44, 44, 44, 44, 64, 64, 65, 65, 65, 65, 66, 66, 66, 66, 66, 68, 68, 68, 68, 96, 96, 96, 97, 97, 97, 97, 100, 100, 100, 100, 128, 128, 129, 129, 129, 129, 129, 130, 130, 130, 130, 132, 132, 132, 132, 136, 136, 136, 138, 138, 138, 138, 140, 140, 140, 140]
def r2sG : List Nat := [3, 5, 9, 3, 6, 34, 5, 6, 9, 72, 11, 14, 42, 74, 13, 14, 76, 34, 160, 35, 37, 41, 161, 37, 38, 164, 41, 42, 104, 168, 45, 46, 108, 172, 72, 192, 67, 69, 73, 193, 67, 70, 74, 98, 194, 69, 70, 76, 196, 98, 104, 224, 99, 101, 105, 225, 101, 102, 108, 228, 160, 192, 131, 133, 137, 161, 193, 131, 134, 162, 194, 133, 134, 164, 196, 137, 168, 200, 139, 142, 170, 202, 141, 142, 172, 204]
def mpG : Nat := 0x3fffffffffffffffffffff
def pool6G : List Nat := [106843288896777, 151923942491682, 152149965162688, 72071867074053, 72986057377027, 152150328607497, 142432054674691, 152151391208226, 151923210912518, 110368882295557, 36475178124805, 36327571981571, 72847680735491, 152149957084675, 152150898705923, 44398759642377]
def xsM : List Nat := roots_239.map (· &&& dom_239)
def goalM : Nat := goal_239 &&& dom_239
def NN : Nat → Nat
  | 6 => 6
  | 7 => 42
  | 8 => 116
  | 9 => 18
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xd9b7456cb072072b7ffe0b3c7ef8a9da179561920de4c40e
  | 7, 0 => 0xf0ed3922ef1ede09ecb777eee070c328aeb97c5bab671dbba1a1b2f3a08e1f1b98033ab691dbd5528bbc85f08b257abd85f48ecf7f7af34c6e47d3b46c950ebc6c1710476b2434af608a7ef25b61ef244fb767b34f1b3a5e4c60840c454e262344b1f8ce40e509493e6ce7793c2545df3c1a704937b8da572678e78d2611e487250c83251e7b1ebe1e2b447b1c3007421a1194f10e670d800b3a1e5009951ef701014a6000864c88
  | 8, 0 => 0x6864c27f684f994c6504b25e6394cb606381efd5628e2add5fff1a8e5dd015405cdf0cbc5c35e4cf5a5d3f115a44543057a530ae574bed1d558be6d05369701b52494d67521ecdce4eb2b7a048b1139a47b58c3e4618cd8545f91c1a44594c9641f0068f41ee9f9240d44d943a6e461438e0243338aec52535cf856934cf98623177be652e7114a229d2b5cd277d45ac2624c52525cd36f42531099f245322682437cb1e223195a221cc3df6209535de1a2ca31618f3f9fd165bc8361595f65f15563d0e150141d414eaae6d10fe760a10ce739b0be8103709552a0707c0da6504b7c1440404ddd002f149f8025c0a6501d9c1a1012f6eed0051fda10005e05e
  | 8, 1 => 0xfe3e0b77f48d74e6f45ce546f3549f3df34de82fef1ede09e2d82943e069f259d3a08b2fcf48c42bb3b9e80cae752cf4adce83d6ac5a2067a8c4134ba7b151009ca16bac97d31a4d9689a76894433b6d943bc3bb935842e890f0dccd8fa39a338e3650658af8a2658a42f2a288913c4a885464eb87f50ef5876fae0284aa2807839525a383915b1d81f4175981e259677e93321f7e5376e279b9bd3878d9198d774aa65774ab77457318afa972698dd970cda0016ff389f46f3f52d16bfe66746b35338c6a9d7cf96a4cd16a6954faae
  | 9, 0 => 0xaa18b71b935842e88af8a2658a1521928819d42b87adbb7787118e2280badcfd7a4e39c7676c187965fc317b57f34ceb511a1dbb3cd5ac2f3b162b4028349d0f1752148807bb54b4
  | 10, 0 => 0x8a152192
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xe8e80000e8e80000e8e80000e8e80000e8e80000e8e80000e8e80000e8e80000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000f8f80000f8f80000f8f80000f8f80000f8f80000f8f80000f8f80000f8f80000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000ffff0000ffff00000000000000000000ffff0000ffff0000000000000000
  | 0, 1 => 0xffff000088880000ffff000088880000ffff000088880000ffff000088880000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00000707000007070000070700000707000007070000070700000707000007070000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000009999000099990000999900009999000099990000999900009999000099990000111100001111000011110000111100001111000011110000111100001111000000000000ffff000000000000ffff000000000000ffff000000000000ffff
  | 0, 2 => 0x8888000088880000888800008888000088880000888800008888000088880000ffff0000ffff00008888000088880000ffff0000ffff000088880000888800000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000000000000000000000000000000777700007777000077770000777700005555000055550000555500005555000055550000555500005555000055550000333300003333000033330000333300003333000033330000333300003333000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff
  | 0, 3 => 0xfafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000f1f10000f1f10000f1f10000f1f10000f1f10000f1f10000f1f10000f1f10000ff880000ff880000ff880000ff880000ff880000ff880000ff880000ff880000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000ffff0000ffff0000ffff0000ffff000088880000888800008888000088880000ff000000ff000000ff550000ff550000ff000000ff000000ff550000ff5500000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e0000000000007777000000000000777700000000000077770000000000007777
  | 0, 4 => 0xffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f00000ffff0000f0f00000ffff0000f0f00000ffff0000f0f00000ffff0000f0f000000000000000000000555500005555000000000000000000005555000055550000ffff0000fcfc0000ffff0000fcfc0000ffff0000fcfc0000ffff0000fcfc0000ffff0000ffff0000fafa0000fafa0000ffff0000ffff0000fafa0000fafa0000ffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc0000ffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc
  | 0, 5 => 0xffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa00000303000003030000030300000303000003030000030300000303000003030000ffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa00000000000033330000000000003333000000000000333300000000000033330000ffff0000ffff0000ffff0000ffff0000ffaa0000ffaa0000ffaa0000ffaa
  | 0, 6 => 0xffff0000ffff0000fcfc0000fcfc0000ffff0000ffff0000fcfc0000fcfc0000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa00002222000022220000222200002222000022220000222200002222000022220000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff000000ffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc
  | 0, 7 => 0x333300003333000000000000000000003333000033330000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f00000fffc0000fffc0000fffc0000fffc0000fffc0000fffc0000fffc0000fffc0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000fff00000ffff0000fff00000ffff0000fff00000ffff0000fff00000000000000000000000000000000000000f0f00000f0f00000f0f00000f0f0000ffff0000ffff0000ffff0000ffff0000eeee0000eeee0000eeee0000eeee0000fff00000fff00000fff00000fff00000fff00000fff00000fff00000fff0
  | 0, 8 => 0xfefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000ffff0000eeee0000ffff0000eeee0000ffff0000eeee0000ffff0000eeee0000ffff0000ffff0000ffff0000f0f00000ffff0000ffff0000ffff0000f0f000000033000000330000003300000033000000330000003300000033000000330000ffff0000ffff0000ffff0000ffff0000ffcc0000ffcc0000ffcc0000ffcc0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000f0f00000f0f00000ffff0000ffff0000f0f00000f0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x80c08c0019820316280066080c1090019818202200066080c0870019828406080806
  | 7, 0, 0 => 0x80c70d2c543384342c70d0019c2031c346000ce1018e1a640067062c70d30003384062cb890019c18b025c4000ce1010e1a440067062c70d2c20338406085810019c284163899100e1420e1a548807080c58e1a500384164c9110019c804060870d0ce1478316386807
  | 7, 0, 1 => 0x201019c1c34338b1c4c8880019c2033c386800ce3869522200067063899510003385082c6922201c19c1c344000ce1421d16386807201018b1c34db85080c5932401c284063491500e14804062c6927080c09c2e0033840604b950019c804062c0970ce0c58e1a6c4007
  | 7, 0, 2 => 0x290080c70d2ae1018b26480067080c9922a003390080c6922a19c78b1c348800ce107132a4400670010182020033040680f810019c20338389800ce3c18e1a540067
  | 8, 0, 0 => 0x4ca818b1c340068080c58e1aa40068080d10e1a5400684c1018b1c4c0068001420b1c3488070a1018b1c34980808a018b1c340068080d38b1c4c006820982031638686800101821c340067080d01f1c340068080c58e1a940068481018b1c340068080d18b1c340068001058d24440067080c5a21c846868
  | 8, 0, 1 => 0x5a1018b1c4c0068640c58e1a20006808c418b603868085e0c58e1a200068080c58e1ab800685a1018e1a54006820b420316386868080c5a11a480068080d00b023400684c1058e1a440068581018b1a480068080c5a21c4c0068062c70d24200068089c58e1a4400680a1018b1c34b808080d38b1cac6808
  | 8, 0, 2 => 0x8e178b1c34006800142031634900708c818e1a54006866a818b1c340068001018b025c0067080c58e26480068080db8b1c340068661018b1c4c00686c1018b1c340068080c58d24d40068001018b1c34b067080c70d24540068080c58e1ad00068661018e1a5400685aa818b1c3400680a1018b1c846808
  | 8, 0, 3 => 0x20a820316386868062c08e1a200068000c70d2a200067080c70d2af000684c1018b1a480068761018b1c340068541018b02380068080c58e1ae80068087418b1c340068080c5b91c34006808c818b1c4c0068080d38b1a480068068058e1a200068082c70d24440068080d80e1a54006808bc18b1c4c0068
  | 8, 0, 4 => 0x80c10b1c34006808c418e1a540068080c58e8234006808e019f1c34006820101a016386868541018b1c4c0068080c5a21a480068082d80e1a440068080e00b1c8468684cb018b1c340068080c58e26f00068080c58e1afc0068080df0b1c340068067c58e1a20006808f418b1c340068080c58e1a240068
  | 8, 0, 5 => 0x80c5811c4c0068001018b1c4c0067001018e26540067080c09c1c340068080c5a260340068080c5811c340068201019f16386868080c08e1a540068080c58e1a6c0068201018b02386868062c70d2e20006800402031c34a8670a1018b44386808080d00b1c4c0068080e0271c340068002c70d22200067
  | 8, 0, 6 => 0x4c11c031c340068001018b26480067004020316349067082c72b1a44006854b018b1c340068581018b1c4c0068080c5b01a480068881018b1c340068001058e26440067080c58e1b0c0068090818b1c340068080c70d2e540068201018b1c34986808c418b1cac6808080cf8b1c4c0068003c18b1c340067
  | 8, 0, 7 => 0x80e30b1c3400688a1018b1c3400680a101c0163868080014804062c70d7
  | 9, 0, 0 => 0x80c5811c340068001018b1c340067080e00b1c340068001018e1a54006700402031638686708c418b1c340068080d00b1c340068000c58e1a200067080c58e1af00068080c5b01c34006808c818b1c340068080c58e1a480068661018b1c3400685a1018b1c340068080c5a21c3400684c1018b1c340068
  | 9, 0, 1 => 0x80c58e1a5c0068001018b1c4c0067
  | 10, 0, 0 => 0x1018b1c340067
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 46
  | 7 => 53
  | 8 => 60
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
  | 0, 0 => 0x3ffffff0000000000000000000000000000000000000000000000000000000000000000fffffffffffffff0000000000000000000000000000000000000000000000000ffe0003fffe00000000000000000000000000000000000000000000003ff80000000003fc01ff000000000000000000000000000000000000000000003c07800f01e003c381c0c000000000000000000000000000000000000000000003c07fc0f01ff000783c3f0000000000000000000000000000000000000000000000000ffffffc00000000
  | 0, 1 => 0xffe0003fffe000000000000000000000000000000000000000000000003c07800001f0000003c38000000000000000000000000000000000000000000000007c0f000f00078000700000000000000000000000000000000000000000003f87ff0fe1ffc3c7e3f3f0000000000000000000000000000000000000000003c07800f01e003c381c0c00000000000000000000000000000000000000000003c3f803f0fe00fff87c3c00000000000000000000000000000000000000000003c3f803f0fe00fff87c3c00000000000000000000000000000000000000000003ffffff001fffc0001ffff
  | 0, 2 => 0xffffffc0000000000000000000000000000000000000000000000000003f87ff0fe1ffc3c7e3f3f0000000000000000000000000000000000000000000000000fffffffffffffff0000000000000000000000000000000000000000003ffff83f0fff0fff87fff80000000000000000000000000000000000000000003c3f87ffffe0ffffffc3c70000000000000000000000000000000000000000000007fffffffffc03fe00ff0000000000000000000000000000000000000000003ffffff0000003ffffffff
  | 0, 3 => 0x3c0787cff1e0f3c3f9c0c70000000000000000000000000000000000000000003c3f803f0fe00fff87c3c00000000000000000000000000000000000000000003ff80000000003fc01ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffff830000003ff87fff800000000000000000000000000000000000000000003c07fc0f01ff000783c3f0000000000000000000000000000000000000000003ffffff001fffc0001ffff
  | 0, 4 => 0x3fffffff01e003c381c0c00000000000000000000000000000000000000000003c07800fffe003ffffc0c00000000000000000000000000000000000000000003ffff830000003ff87fff80000000000000000000000000000000000000000003fc7f80fffff03fffffcf80000000000000000000000000000000000000000003c0787cfffffffc3f9c0c700000000000000000000000000000000000000000003c0780ffffffc00003c38000000000000000000000000000000000000000000000007cffffffc007800070000000000000000000000000000000000000000003fc7f80f01ff03c381fcf8
  | 0, 5 => 0x3ff807c0f000f3fc79ff07000000000000000000000000000000000000000000003807f0fe00fc3c7e030700000000000000000000000000000000000000000003c0780ffe1f03fffe3c380000000000000000000000000000000000000000000000000ffffffffffe00000000000000000000000000000000000000000000003ffffff0f000f000780007000000000000000000000000000000000000000000000007cffe00f3fffe00070000000000000000000000000000000000000000003c3f87f001e0fc0001c3c70000000000000000000000000000000000000000003ffffff0f000f3fc79ff07
  | 0, 6 => 0x3fc7f80fffffffc381fcf80000000000000000000000000000000000000000003ff807cffe00f3ffffff07000000000000000000000000000000000000000000000007c0f000f00078000700000000000000000000000000000000000000000000007ff0fe1ffc007e003f0000000000000000000000000000000000000000003ff8000ffe0003ffffff000000000000000000000000000000000000000000003ff87800001f03fc01ff380000000000000000000000000000000000000000003ffffff0000003fc01ff000000000000000000000000000000000000000000003ffffff0001f0000003c38
  | 0, 7 => 0x3c3f87f0000003ffffc3c70000000000000000000000000000000000000000003fffffffffffffc381c0c00000000000000000000000000000000000000000003ffff80f01ff03ff81fff80000000000000000000000000000000000000000003ffffffffffffc000000000000000000000000000000000000000000000000003fff800fffe003ffffffc000000000000000000000000000000000000000000000000000fe1ffc3c7e3f3f0000000000000000000000000000000000000000003ffffff0f01ff000783c3f0000000000000000000000000000000000000000003fff800f01e003ff81ffc0
  | 0, 8 => 0x3fc7ffcff1fff3c3f9fcff00000000000000000000000000000000000000000003c07fcffe1ff3fffe3c3f0000000000000000000000000000000000000000003c07800fffffffffffc0c0000000000000000000000000000000000000000000000787ffffe0fc03fe00c70000000000000000000000000000000000000000003ffffff0001f03fc01ff380000000000000000000000000000000000000000003ffffffffffffc007800070000000000000000000000000000000000000000003c07800fffffffc381c0c0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xcc198c3306330c198ccdb0000000000000000000000000000000000000000003ffffff889108a224400000000000000000000000000000000000000000000000000000776ef75ddbbffff0000000000000000000000000000000000000000001112221ffe0803fffe10200000000000000000000000000000000000000000003ff80104448447fc21ff040000000000000000000000000000000000000000003cc798cf31e333c399ccdb0000000000000000000000000000000000000000000fc9ffc3f27ff0cdfafdff0000000000000000000000000000000000000000002224442ffffffd10012200
  | 0, 1 => 0x11522a5ffe0913fffe14290000000000000000000000000000000000000000000bc17842125f10890abcb900000000000000000000000000000000000000000004488fc1f021f044f8454f00000000000000000000000000000000000000000003386730ce1ccc3c6633240000000000000000000000000000000000000000003c87908f21e223c391c8d20000000000000000000000000000000000000000003076087c1d811f320d06090000000000000000000000000000000000000000003036003c0d800f320502000000000000000000000000000000000000000000002eeddde001f7fc0001efdf
  | 0, 2 => 0x4008401001100008040900000000000000000000000000000000000000000022644c6ffffffd1009260900000000000000000000000000000000000000000003786f70de1ddc3c6e372d0000000000000000000000000000000000000000000000000766ee65ddb3fbf60000000000000000000000000000000000000000003bb7703e0fde0fbb07bab0000000000000000000000000000000000000000000343e87bdeda0ef76f543460000000000000000000000000000000000000000000007fefbbb7bb803de00fb0000000000000000000000000000000000000000001ddbbbd0000002effeddff
  | 0, 3 => 0x3ccf9fcff1e3f3c7f9cddf0000000000000000000000000000000000000000003cb790bf2de22ff395cad20000000000000000000000000000000000000000003ff80944548557fc29ff0d0000000000000000000000000000000000000000000c819083206220c190c8d20000000000000000000000000000000000000000003ffffff899119a224c04090000000000000000000000000000000000000000003ffb3114448447ff27ffb400000000000000000000000000000000000000000003486f40d21dd00c6a352d0000000000000000000000000000000000000000002eadd5a001f6ec0001ebd6
  | 0, 4 => 0x3fffffffa9f2abe3d5c8d20000000000000000000000000000000000000000003d97b29fffea23ffffd8f200000000000000000000000000000000000000000019933010000002ab0698b00000000000000000000000000000000000000000003fd7fadfffff33fffffcfb0000000000000000000000000000000000000000003eefdfefffffffd7f9efdf0000000000000000000000000000000000000000002be57c6ffffffd990bbeb9000000000000000000000000000000000000000000266ccfeffffffd54f9674f0000000000000000000000000000000000000000003fc7f8cf33ff33cb9bfcfb
  | 0, 5 => 0x3ff88fc5f4a5f7fcf9ff4f00000000000000000000000000000000000000000000380730cc00cc346403040000000000000000000000000000000000000000001bd37a5ffe5f13fffebcb90000000000000000000000000000000000000000003336663fffffffffff32200000000000000000000000000000000000000000003ffffff9f931fa66fc454f000000000000000000000000000000000000000000155aafdffe29f3fffe556f000000000000000000000000000000000000000000242c85a001a0ec000143460000000000000000000000000000000000000000003ffffffdfdb5fffefdff4f
  | 0, 6 => 0x3fe7fcefffffffdb9bfefb0000000000000000000000000000000000000000003ffaafdffeadf7ffffff6f00000000000000000000000000000000000000000004088781e020e044f0414600000000000000000000000000000000000000000000006e709a1998004e00290000000000000000000000000000000000000000003ffa231ffe8c47ffffff240000000000000000000000000000000000000000003ff9794656df57fd2bffbd0000000000000000000000000000000000000000003ffffffccd94cffe65ff040000000000000000000000000000000000000000003ffffffa9b5f9aab4ebcb9
  | 0, 7 => 0x141a839000000266f441460000000000000000000000000000000000000000003ffffffffffffff3d5ead20000000000000000000000000000000000000000003ffff9cf77ff77ffbbffff0000000000000000000000000000000000000000003fffffffffffff324522000000000000000000000000000000000000000000003fffb39fffee67fffffff600000000000000000000000000000000000000000000000000560d541c2a372d0000000000000000000000000000000000000000003ffffffbfb7ffaeffefdff0000000000000000000000000000000000000000003fff918f65e667ffb1ffd6
  | 0, 8 => 0x3fcfffcff3fff3cffbfdff0000000000000000000000000000000000000000001fdbffdffe7ff3fffefdff0000000000000000000000000000000000000000003fb7f6bffffffffffffaf2000000000000000000000000000000000000000000000686b9a920a802d400420000000000000000000000000000000000000000003ffffffedfdfdfff6fffbd0000000000000000000000000000000000000000003fffffffffffff76fd674f0000000000000000000000000000000000000000003ea7d4afffffffd391ead2
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 71 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 71 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 71 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 71 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 6 => 2
  | 7 => 148
  | 8 => 296
  | 9 => 15
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0xa1a1b2f30eae5f84
  | 7, 0 => 0x4822c9bc47b58c3e46d6a4c445aea9b2442a724b4350969341cfbc8c40d44d943dfe5cb13c813a1d39e9b85e37a653c237a60f2235d7102d3414005d32f9557a325be2c03213a6633153469230c9dba32f75c4b52cbebfca2c0e1b9c2bedec352b4634b827ff421926cdd62b25ccf19d25887f8e24ae27ad23e8cf4d221f815721835402214efab6212e7d0e1e36c6481cbbb24e1bbccb1118e4553017646c24163aa2ce155d007e145c8190144602ad1219e563110c10d210950fae10499b590e19d47e0dcae02b0d47ff260d3c294b08badc4b082444ea07f99f6f06277bf404ff649d04eebdf40404ddd003e948b903e00b9603bb7e2d021488160051fda1
  | 7, 1 => 0xadce83d6ad6aa0edac3fe377aa9f4274a6432577a5f831bfa5b20a5a9f3444929f2068f59eac5d999c72f96f954d77e994433b6d935842e8922ca6f6910c844290f0dccd8ec019608a6742478a15219288da000c87adbb7787118e2280e73e017fb840ef7f1804fa7edec5f77d521a1f79eacc4d72d150346d0660166cd133b869aa76fe676c187964f2cb4464b5f28e6486cd9d61a2e36860504c5c5ee1ccd95eb6601e5aa7beb55924709058f92375580061c157f3b44a5768d28a55b0f827559268f054ec025e52967520521ecdce5218448e51e3a61951df9452515931234fd4f9bc4eb27bad4e8c837e4c6bc0764c55da504bb391454a176eea48fc927c
  | 7, 2 => 0xfd1054daf059c173e34245e7e2d82943e2ac905fe13e34e7df88e08bdcf24aead63fac90d48aa7cfd0a562cacda607f2cd93fd8dcd03b04ec6802671c1a5487cbd2e11b7b7910244b38a3cf6adee6f27
  | 8, 0 => 0x1e8885c71e34d6591e24312c1e0b539c1ddf7afe1db1f7b81cb250b41b620f191b1e85361b1cf7861a939fe71a7005511a1c32cf19e01af919bb665619a9f7a51967cfa518b71f1b186d22271836cfa6181af1c618196416178f9585178c3ae61754003b17521488174fdd2e16b7d2e615c87767144e81181362d1f9113a172910a241db108b623e0fda57d80faceb7d0f15ef520c3d620b0bcc6cfe0b7f311c0ae0ef7f0adc43f40aac4a4a0a8a258e0a1fb0a309f38f57094e6daf086099f307bb54b4071c1d33071370820617599d05df523c058b93f6055761f70557489f0553ee99054031150399c2aa02894ba8023c0fc601c96197019597e20021e58d
  | 8, 1 => 0x3cd5ac2f3c48fb433ba3b2173b42ad103b162b403b0784c23b054dbe3a0d753d3997ddc53894cb14382838a63820d10c381297d037db9a5d37038ee636a25bd2362d75d735e4bc2d35d1710c3594c624354a43d234221eb43307cfd932625b423248b3f031c8557631728edf3148f93e3143730e30e28f3e30d3a3a63015a6132fa9df852ca19ad72c8f4bfb2a70ed602a3a34bc299e076728d0850d289854fb289179b528349d0f280051b827aafaea274e74f22625121f2598eb9d254ef80524fcbe482495f1912486e7722465fac12461a68c246018dc2408735923a0b26123999b3d2373a15c22fe87ac22f755dc22ddf0951f1418711ee4b91d1eab266b
  | 8, 2 => 0x65fc317b65e64bc465438ab2652302f0650aa8fb6338a17762f89e0b60d7e31d6054b7425fc005475f0220365e74b7545e11d3e45d75a41d5c01d0825b9609f45b6e26035b03e0e959ffb90c5973a62558cd373d5880edfc57f34ceb57e2f4c7566e0cf0559aa56a54024872539725595252e89e522b821c513da990513b2274511a1dbb509db5a8501affc04feb82834f4f552e4ebd406b4e168a4b4deb44584b0042e04a7c8a56498d2fa7494d39fb48bf4cd648be8c3448160fcd47e0d420474e39884722bb554691d86644f46dae44e15ff2446785d243b30efd4353286242ae4aba4089519b406cf7473ff9d07a3e0b18323dacb0a53d6cb3d93d65400a
  | 8, 3 => 0x9bcd11a59b311deb9a4fd0f499334efa94d9d0178ec019608cd4569e8bcb0aa58b63c8e78a152192897007c88819d42b87adbb77875d213587118e2285b26e10853ca3f980badcfd8053a324802ce6727fb7dc827f8f410b7f7c1f1d7f48e9237dc580577d4e35eb7d2953027c89e0177c50f8467b82966f7a4e39c779c9f9d8797892d9789dcdab77e6d3ac7777266e770c770d76e520577662c1be75ea8b54746c98c373fe65cf73e7cb0b73d71d41738392f47346bec17302345d72ff04f5718f128870df58a670cd8a616f7f563d6f60c62d6e7f20e16e6470dd6d34f01a6cdc62566bfd41c06bb6e71e6ba394ca6ac0ca2a678a690b676c1879663a561d
  | 8, 4 => 0xff77baf5f74b68eff3658702ef9d2b69e776a78adfb544fcde3dfd0ddbdfb8a1d71c3ef1d66e00b8d578af8bd2d92041cf311162ca7919b3c9cb53b7c8e78c8cc8a33524c4d114a3c4c435b2c43fbb64c4365e06c3020f65b974df7eb3441b39ae727626ae2239ecac6b8d6faa18b71ba9afc4f4a8197075a813c66ba7677597a41cd653a35ed95ca34e6080a2d2a796a2901519a187cf109f38d7549c6e6706
  | 9, 0 => 0x802ce6727346bec1678a690b5252e89e3e0b18323d6cb3d92ca19ad7280051b81db1f7b81b1e85361b1cf78619bb66560a1fb0a302894ba8023c0fc6
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x1
  | 7, 0 => 0x1610400000000000070000000000000000000000a1010000000000004000000000a1020000000000007000000000e10300000000000000000000000003000000001610300000000021040000000000003000000000000100000000121020000000000007000000000000000000000121080000000000000000000000a101000000000210300000000000000000000000001000000000e101000000000000200000000000010000000000000000000000e1050000000006103000000000000000000000000020000000006103
  | 7, 1 => 0x1610100000000000000000000000002000000000a106000000000a1080000000002103000000001610100000000000000000000000001000000000210200000000000050000000006101000000000a103000000000000300000000000030000000000005000000000000100000000021010000000006101000000001110600000000061060000000000008000000000e1010000000000001000000000000500000000000010000000000001000000001210100000000000050000000006102000000000e108000000000a104
  | 7, 2 => 0x10000000000005000000000a1010000000000005000000001210500000000000000000000000005000000000000300000000000040000000000007000000000210500000000000070000000002103000000000210200000000000070000000000006000000000000100000000000070000000000007000000000610400000000161010000000000000000000000000100000000021060000000002108000000000210100000000061010000000000000000000000a103000000001210100000000000000000000000005
  | 7, 3 => 0x210300000000000020000000000004000000000e10400000000061010000000000002000000000a1030000000000000000000000a10800000000000020000000000004000000000610300000000000000000000002103000000000210800000000000080000000002101000000000000100000000161020000000000001000000000000700000000000010000000012105000000000000300000000000020000000002106000000000e10800000000000000000000006102000000001210600000000000070000000000000
  | 7, 4 => 0xa1030000000000007000000000000300000000061020000000000002000000000000700000000000050000000002106000000000610500000000000010000000000001000000000000000000000000000000000000001000000000a10200000000000000000000000001000000000000300000000000050000000000000
  | 8, 0 => 0x551020000000006102000000000000700000000000010000000000002000000000000600000000021030000000002101000000000000500000000000040000000000003000000000000500000000000010000000006101000000000000100000000000060000000000001000000001210100000000000040000000000003000000000000700000000000050000000000005000000000e1030000000000001000000000000500000000000050000000000003000000000000100000000000070000000000006000000000a103
  | 8, 1 => 0x300000000000010000000000002000000000000000000000000020000000000001000000000a1010000000012104000000000000400000000000010000000000004000000001610100000000000050000000000002000000000000400000000000020000000000005000000000a104000000000000500000000000010000000016104000000001210100000000000050000000000001000000000a1040000000000002000000000000300000000161040000000000003000000000000200000000021010000000000001
  | 8, 2 => 0xe1030000000000005000000000a1010000000000002000000000a106000000001210600000000000010000000000002000000000000400000000000050000000000003000000000e10800000000000000000000000005000000000a103000000000e1010000000012103000000000a10100000000000040000000000006000000000210400000000021010000000000000000000000000500000000000050000000000007000000000210400000000021020000000000000000000001210200000000000000000000000002
  | 8, 3 => 0x70000000000004000000000a104000000000000500000000000030000000016104000000000a105000000000000300000000000070000000000000000000000a101000000001210500000000000080000000000008000000000000a0000000006103000000000000500000000021060000000000002000000000e104000000000000600000000000000000000000008000000000000500000000000060000000000008000000000000100000000121030000000002103000000001610100000000000040000000012102
  | 8, 4 => 0x3000000000e1030000000000001000000000a1030000000012103000000000000300000000000080000000016103000000000210200000000000010000000000005000000000000400000000000050000000000005000000000000400000000000010000000002104000000000000800000000000030000000012101000000001210200000000021050000000000006000000000000600000000000030000000000007000000000000500000000000020000000000004000000000210100000000000050000000000000
  | 8, 5 => 0x200000000061010000000000004000000000a10200000000000020000000012105000000000000200000000000000000000000000000000000000100000000000050000000000001000000000000600000000000030000000002102000000000210300000000000030000000000001000000000000300000000d1103000000000000700000000000070000000000004000000000e1050000000000001000000000e105000000000000000000000021080000000000003000000000000400000000000000000000002101
  | 8, 6 => 0x61010000000000000000000000000100000000021030000000000003000000000610400000000161010000000000006000000000000700000000000060000000000002000000000000500000000000030000000000003000000001210500000000000020000000006103000000000a10300000000021020000000002105000000000000300000000161010000000000001000000000e10200000000000040000000000003000000000000200000000000080000000000004000000000000200000000000050000000000000
  | 8, 7 => 0x1210500000000000030000000000000000000000610500000000000060000000000001000000000000900000000000050000000000003000000000000100000000021030000000000001000000000000100000000000080000000000002000000000000100000000000070000000000003000000000000700000000000030000000000002000000000000800000000000000000000002105000000000a1030000000000002000000001210300000000021030000000000008000000000000100000000000010000000000001
  | 8, 8 => 0x3000000000000100000000000040000000000007000000000000100000000000000000000000002000000000a10100000000000010000000000001000000000000200000000000040000000000002000000000000300000000000010000000000004000000000000500000000000050000000000000000000001610500000000000030000000002105000000001610500000000000040000000000001000000000000800000000000040000000000008000000000000800000000000020000000000007
  | 8, 9 => 0x3000000000e1020000000000001000000000000b000000000e101000000000000000000000000050000000000001
  | 9, 0 => 0x300000000000030000000000002000000000000300000000000040000000000005000000000000600000000000030000000000001000000000000400000000000010000000000004000000000000100000000000030000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 10 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_238 roots_238 7 s ws hint
  | 1 => checkCutEntry dom_235 roots_235 8 s ws hint
  | 2 => checkCutEntry dom_175 roots_175 8 s ws hint
  | 3 => checkCutEntry dom_231 roots_231 8 s ws hint
  | 4 => checkCutEntry dom_111 roots_111 8 s ws hint
  | 5 => checkCutEntry dom_207 roots_207 8 s ws hint
  | 6 => checkCutEntry dom_79 roots_79 7 s ws hint
  | 7 => checkCutEntry dom_237 roots_237 7 s ws hint
  | 8 => checkCutEntry dom_167 roots_167 7 s ws hint
  | 9 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 10 => checkCutEntry dom_47 roots_47 6 s ws hint
  | 11 => checkCutEntry dom_199 roots_199 6 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_238 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_235 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_175 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_231 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_111 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_207 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_79 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_237 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_167 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_199 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_239 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_239 == dom_239) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_239 goalM u ys) : RunD dom_239 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_239 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 42 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 32 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 42 → Z 7 i = true := (range_split z7_0 (range_split z7_16 z7_32))
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
private theorem z8_112 : ∀ i, 112 ≤ i → i < 116 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 112 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 116 → Z 8 i = true := (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 18 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 2 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 18 → Z 9 i = true := (range_split z9_0 z9_16)
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

theorem low_247 : Lower dom_247 roots_247 goal_247 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_231

theorem low_254 : Lower dom_254 roots_254 goal_254 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5050505050505050505050505050505050505050505050505050505050505050, 2, 6)] (by decide +kernel) (by decide +kernel) low_250

def isoMv_223 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_223 : Lower dom_223 roots_223 goal_223 11 :=
  lower_iso isoMv_223 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_191

def isoMv_251 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_251 : Lower dom_251 roots_251 goal_251 11 :=
  lower_iso isoMv_251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_239

def isoMv_253 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_253 : Lower dom_253 roots_253 goal_253 9 :=
  lower_iso isoMv_253 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_247

namespace S_255
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 6), (2, 34), (4, 5), (4, 6), (8, 9), (8, 24), (8, 72), (10, 11), (10, 14), (10, 26), (10, 42), (10, 74), (12, 13), (12, 14), (12, 28), (12, 76), (16, 17), (16, 24), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (32, 34), (32, 160), (33, 35), (33, 37), (33, 41), (33, 49), (33, 161), (36, 37), (36, 38), (36, 164), (40, 41), (40, 42), (40, 56), (40, 104), (40, 168), (44, 45), (44, 46), (44, 60), (44, 108), (44, 172), (48, 49), (48, 50), (48, 56), (48, 176), (52, 53), (52, 54), (52, 60), (52, 180), (64, 72), (64, 192), (65, 67), (65, 69), (65, 73), (65, 81), (65, 193), (66, 67), (66, 70), (66, 74), (66, 98), (66, 194), (68, 69), (68, 70), (68, 76), (68, 196), (80, 81), (80, 88), (80, 208), (82, 83), (82, 86), (82, 90), (82, 114), (82, 210), (84, 85), (84, 86), (84, 92), (84, 212), (96, 98), (96, 104), (96, 224), (97, 99), (97, 101), (97, 105), (97, 113), (97, 225), (100, 101), (100, 102), (100, 108), (100, 228), (112, 113), (112, 114), (112, 120), (112, 240), (116, 117), (116, 118), (116, 124), (116, 244), (128, 160), (128, 192), (129, 131), (129, 133), (129, 137), (129, 145), (129, 161), (129, 193), (130, 131), (130, 134), (130, 162), (130, 194), (132, 133), (132, 134), (132, 164), (132, 196), (136, 137), (136, 152), (136, 168), (136, 200), (138, 139), (138, 142), (138, 154), (138, 170), (138, 202), (140, 141), (140, 142), (140, 156), (140, 172), (140, 204), (144, 145), (144, 152), (144, 176), (144, 208), (146, 147), (146, 150), (146, 154), (146, 178), (146, 210), (148, 149), (148, 150), (148, 156), (148, 180), (148, 212)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 8, 10, 10, 10, 10, 10, 12, 12, 12, 12, 16, 16, 18, 18, 18, 18, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 36, 36, 36, 40, 40, 40, 40, 40, 44, 44, 44, 44, 44, 48, 48, 48, 48, 52, 52, 52, 52, 64, 64, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 68, 68, 68, 68, 80, 80, 80, 82, 82, 82, 82, 82, 84, 84, 84, 84, 96, 96, 96, 97, 97, 97, 97, 97, 100, 100, 100, 100, 112, 112, 112, 112, 116, 116, 116, 116, 128, 128, 129, 129, 129, 129, 129, 129, 130, 130, 130, 130, 132, 132, 132, 132, 136, 136, 136, 136, 138, 138, 138, 138, 138, 140, 140, 140, 140, 140, 144, 144, 144, 144, 146, 146, 146, 146, 146, 148, 148, 148, 148, 148]
def r2sG : List Nat := [3, 5, 9, 17, 3, 6, 34, 5, 6, 9, 24, 72, 11, 14, 26, 42, 74, 13, 14, 28, 76, 17, 24, 19, 22, 26, 50, 21, 22, 28, 34, 160, 35, 37, 41, 49, 161, 37, 38, 164, 41, 42, 56, 104, 168, 45, 46, 60, 108, 172, 49, 50, 56, 176, 53, 54, 60, 180, 72, 192, 67, 69, 73, 81, 193, 67, 70, 74, 98, 194, 69, 70, 76, 196, 81, 88, 208, 83, 86, 90, 114, 210, 85, 86, 92, 212, 98, 104, 224, 99, 101, 105, 113, 225, 101, 102, 108, 228, 113, 114, 120, 240, 117, 118, 124, 244, 160, 192, 131, 133, 137, 145, 161, 193, 131, 134, 162, 194, 133, 134, 164, 196, 137, 152, 168, 200, 139, 142, 154, 170, 202, 141, 142, 156, 172, 204, 145, 152, 176, 208, 147, 150, 154, 178, 210, 149, 150, 156, 180, 212]
def mpG : Nat := 0x3fffffffffffffffffffffffffffffffffffff
def pool6G : List Nat := [90351394101320, 90351291860514, 36507961787665, 48878356334872, 154350555366149, 107006989959970, 71830409184005, 36913265771281, 106843783301448, 152149955577091, 90659799303430, 152151574054147, 107007140463377, 152150593897225, 142432054674819]
def xsM : List Nat := roots_255.map (· &&& dom_255)
def goalM : Nat := goal_255 &&& dom_255
def NN : Nat → Nat
  | 7 => 18
  | 8 => 125
  | 9 => 246
  | 10 => 96
  | 11 => 11
  | 12 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 7, 0 => 0xc3905142bec79410b155d1a3a40452199b242ce2938010e3872a88667e75ebf476b94bbe701fdc6e6f8f86ea4924f7844811481847f063ab162a616e15e7ece70b41d4c9096ba6fc
  | 8, 0 => 0x61b0dc6e602113045f8d1e3e5f71e0085f04329a5d586c8f5d57b0cc56de8559564bb4105535ebd75290c9094ad26383498a75a3494eab85492e910144f3ac3443a3ec714114a0d640aa2ba13ee45d853de59c903d68cc8c3cdf2f5d3c09c0c137f3a13635feff8c33ee91c92ee5f1a92e3ca4ca2a43e7342a37301a27689af126f5ab8325390b941fb45c451c62ea5b1b33e0891a06f2d919d8952119ca0e9a18bb9e461835ae5c17dcb97216cd323915392587142814791237b0bb10c18ee80c271a1b0b7232240af647570a0cc2c60a0232100a01053709a4d0f508f4fe00088acaa6081c99a00686a3fd04b42b9404a0ae88040ac09703bde7c6018d21bf
  | 8, 1 => 0xfa527651ed8c49bde1b6b549dd22551ad9f9c6add8b8851fd5c021d3d468e31fd30ef5ddcf4e25ddca221616c62b8abdbf8e73e3bcf4316fb9959b1fb660b4efb450d47fb40f6f0db222afdcaa1ebd71a8dffd21a5f4c892a51a627aa4ca36c5a3c76643a2a00b9aa09a80dd9e0f48209ccd3de795b86c3a9354a9e891c1c32c9187c2588ff214278f123ced8eec9c498cc6bd4885bde90a854e0c73843642ce82fac8e782a23fef824ce11976a668fa742ac1e37296ade770f93b566f7580726eb2ad136bd112d96b8733036b4a69b467ea8d1f669ba4dc65f3ff01657a368064edc3b3645d6e2f62ae99b0621aa53261d82c07
  | 9, 0 => 0x267a5c6a2673b630266cadc7264a6848257a3f48253dcbf42533a93024af03ec248df1af23b3d8ee23001be8223e1e792080485220107fbb1fbcb0251edbd98c1ebcbd521eb913c31cf218141cb8b1961b83163b1b3a0ffb1b20f9281af627a81a06f2d919dd8259189b2ba8185dbef01849aa4717b214b816c7120f14ec9eef13b780fd1388e779133db87c1130d1a010c1f64610323a580d97e6650d70325d0d3ceb900d0395a10cad06da0c4543790b4334eb0b1d9e490b1a16410ad1dab40a1b1d5c0a070ccc09b92a7908ccd71008c07af3075a7b0b062f08c205a1437f051b7ea504f005e902683aac020cbf4601ff282501e7f2150046e59c00401969
  | 9, 1 => 0x560a3a875549334e5332ea6552964424522653d451ad17d5518ae83f50d9035c50d380774d8bd85e4cc189ae4c8329074c24ddcb4bac6c9e4b199b554ac08d0848ef6713487c35ff44dd279743a43c0c431aeeb542e57182402bcfa33e1c92ca3d7af4503bedb44b3ba4d1413b8a1a7a3a397c9b39c86411399414a5397862d038ad2013388a75993871d3b637e8d5fa376ce35a36f6677b351ac29a346055a6344f8f1f34253f8933a3bc75337552fd32e7761432bd4e9432b383d53065c1eb302280b22f40cb062f3495922e6e40472dd0ab962d9ea3112c7383012b6787a72b54bd542b3321a9292e3ceb28bc790e286e0d562858195227f175d926f08b84
  | 9, 2 => 0xa03376649fb71f5a9dade46699f10a4b99d51905981e0db1963639c695de0a10947556859358bfd192dd2f6592d9a75d90d4e28d90acf0908ec300548e1a81778d2d0dd38bbb35bf89030fe788bc1f348822912d8699915385f3b2ae845662c8838535768383a3cf82f5a8e87cf494d57bec3d427bd586c97946c969777027347718cb9276a148fb742ac1e37354543a72740bb9707ecce57072ac2a6ec34b496e763f186e6214ab6ad19fad6991813067c7dc43678f56fb66b2140a644367b76415ae586373dd59629ab2d86158c08b6081020760527cfa5f9f86f25f8d1e3e5f5bf97e5dbd7f605bcc4c115acad3b85aa190175a920651594df7fd583ddcd6
  | 9, 3 => 0xf68715b7f485b628eb9ee13ceb75eee0e9cd42bde7f56c4fe73c4a06e72a8615e6312a04e1d0895edfc350c5dd74f6eed7984874d4b501d1d3e43c58d27a0976d1f03c5fd12f5449cea3c9e1ce7059a2cd717c1dcae6a08cca8e0918c92190a9c90498fac7dcdd22c5a27af1c39ed80fbfaa89e1befc3d24be06868db8255307b6ed2ceab5f40e10b57b247fb45c5b28b403f10bb250e0bcb1d3dcf8b1c218b4b11bd0c1b1097e02b0e88156b0db6144ad7a0636ad5b317eacd68a8dac30429aab6d327eaa3a0a7fa8dd5652a7ebc21fa7caafe2a6f09721
  | 10, 0 => 0x7c4dc7e07b1970a77b0da96378518b14756a15dc7365fced72e35c4e710946717079ace66f61ebef6a765dc8678662ba632940086167341b5f9f86f25e127f245c95c3885af3a9405ab3f8cb5520643f51a7f7d65186d5924f98bafd4b4a0daa4ad821cc4a8eb7c6467aff1a45a167bc442fac08418f70f340bcf3393fd63bc93caf49dc39ea358937e8d5fa36c691e334f9b6e8305801bf300e28c12f714a4f2a1753db292e3ceb28433a42272437a72681ab2a258dc8f32533a93020a23acc1cbf5d1e192341a516bf462d1437b37e13f952d713dd18700dffafcf0d6912ed0d17918c08e3a84908a562e7087d84c6065be3c3031afb1101f7e1070175eaae
  | 10, 1 => 0xf3e9acd1eb3e764ce36c6492dc62c8bfdc0a314bdaff1149cc662fb9c982e916c33e40e7c2578977bfcf9eaab967ea52b946d815b86cbf54ab9a0b4ba7e6a220a5e9b806a4d4e804a44a97b3a2493824a22918c3a0fe29df98243d2395015da994ffcc028f940b5a899734028894f3c58390e79981faf5188055fe257ea55972
  | 11, 0 => 0x89cdb34780de1422711baf255c5449ff57f7274d4675df1b3709f1262a9f69d81ee53b200df128ea09059ac3
  | 12, 0 => 0x1f6d511d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f91111111111111111111111111111111111111111111111111111111111111111ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | 0, 1 => 0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa553333333333333333333333333333333333333333333333333333333333333333f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f800ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffaa88aa88aa88aa88ffffffffffffffffaa88aa88aa88aa88ffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccfaf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8
  | 0, 2 => 0x5555555555555555555555555555555555555555555555555555555555555555ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffffaa00ffffaa00ffffaa00ffffaa00ffffaa00ffffaa00ffffaa00ffffaa00cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc005500550055005500550055005500550055005500550055005500550055005500000000000000000000000000000000ffffffffffffffffffffffffffffffff9999999999999999999999999999999999999999999999999999999999999999
  | 0, 3 => 0xffff0088ffff0088ffff0088ffff0088ffff0088ffff0088ffff0088ffff0088ffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaf1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffffffffffffffffffee00ee00ee00ee00ee00ee00ee00ee00cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33
  | 0, 4 => 0xffffffff00000000ffffffff00000000ffffffff33333333ffffffff33333333ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff5555005500550055005500550055005500550055005500550055005500550055000000777700007777000077770000777700007777000077770000777700007777ffff0055ffff0055ffff0055ffff0055ffff0055ffff0055ffff0055ffff0055aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa880000000055775577000000005577557700000000557755770000000055775577
  | 0, 5 => 0x1133113311331133113311331133113311331133113311331133113311331133ffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffcc88cc88cc88cc88cc88cc88cc88cc88faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0ffffffffffffffff0000000000000000ffffffffffffffff00ff00ff00ff00ffffffffffaa88aa88ffffffffaa88aa88ffffffffaa88aa88ffffffffaa88aa88ffff0000ffff0000ffff0000ffff0000ffff0055ffff0055ffff0055ffff0055ffff00ccffff00ccffff00ccffff00ccffff00ccffff00ccffff00ccffff00cc
  | 0, 6 => 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0088ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff050f050f050f050f050f050f050f050f050f050f050f050f050f050f050f050fcc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc880077007700770077007700770077007700770077007700770077007700770077ffffffffffffffffffffffffffffffffaa88aa88aa88aa88aa88aa88aa88aa8888888888888888888888888888888888888888888888888888888888888888880000000055ff55ff0000000055ff55ff0000000055ff55ff0000000055ff55ff
  | 0, 7 => 0xffff2200ffff2200ffff2200ffff2200ffff2200ffff2200ffff2200ffff2200ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffffffffaa00aa00ffffffffaa00aa00ffffffffaa00aa00ffffffffaa00aa000000000000000000000000000000000055ff55ff55ff55ff55ff55ff55ff55ffffffffff88888888ffffffff88888888ffffffff88888888ffffffff88888888ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa00ffffffffffffffff2200220022002200ffffffffffffffff2200220022002200
  | 0, 8 => 0xc0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0033003300330033003300330033003300330033003300330033003300330033ffffffffffffffffffffffffffffffffaa00aa00aa00aa00aa00aa00aa00aa000000000000000000000000000000000033ff33ff33ff33ff33ff33ff33ff33ffffffffffffffffff0000000000000000ffffffffffffffff0033003300330033ffffffffffffffffffffffffffffffffcc00cc00cc00cc00cc00cc00cc00cc00ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88888888888888888888888888888888
  | 0, 9 => 0xff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88cccccccccccccccccccccccccccccccc888888888888888888888888888888880000000000000000777777777777777700000000000000007777777777777777ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0ffffffffffffffff0000000000000000ffffffffffffffff0055005500550055ffffffffffffffffffffffffffffffff22002200220022002200220022002200
  | 0, 10 => 0xf0f1f0f1f0f1f0f1f0f1f0f1f0f1f0f1f0f1f0f1f0f1f0f1f0f1f0f1f0f1f0f1eecceecceecceecceecceecceecceecceecceecceecceecceecceecceecceecc000000000000000000000000000000005555555555555555555555555555555500000000000000000000000000000000777777777777777777777777777777771155115511551155115511551155115511551155115511551155115511551155ffffffff22002200ffffffff22002200ffffffff22002200ffffffff22002200cccccccccccccccccccccccccccccccccc00cc00cc00cc00cc00cc00cc00cc000000000000000000000000000000000055775577557755775577557755775577
  | 0, 11 => 0x3300330033003300330033003300330033003300330033003300330033003300dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd0000000000000000000000000000000033333333333333333333333333333333ffffffffffffffffffffffffffffffff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff55ff55ff55ff55ff55ff55ff55ff55ffffffffffffffffffffffffffffffffeecceecceecceecceecceecceecceeccffffffffffffffffffffffffffffffffffff8888ffff8888ffff8888ffff8888cceecceecceecceecceecceecceecceecceecceecceecceecceecceecceeccee
  | 0, 12 => 0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00eeffffffffffffffffffffffffffffffff888888888888888888888888888888880088008800880088008800880088008800880088008800880088008800880088cccccccccccccccccccccccccccccccc444444444444444444444444444444445544554455445544554455445544554455445544554455445544554455445544ffffffffffffffffffffffffffffffffff88ff88ff88ff88ff88ff88ff88ff88ffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
  | 0, 13 => 0xcc44cc44cc44cc44cc44cc44cc44cc44cc44cc44cc44cc44cc44cc44cc44cc44ffffffffffffffffffffffffffffffff55555555555555555555555555555555ffffffffffffffffffffffffffffffff00330033003300330033003300330033444444444444444444444444444444444444444444444444444444444444444400cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffcc00000000000000000000000000000000003300330033003300330033003300330000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff
  | 0, 14 => 0x22222222222222222222222222222222222222222222222222222222222222223333333333333333333333333333333322222222222222222222222222222222ffffffffffffffffffffffffffffffff00550055005500550055005500550055ffffff88ffffff88ffffff88ffffff88ffffff88ffffff88ffffff88ffffff88aaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaee3333333333333333333333333333333333003300330033003300330033003300ffffffffffffffff8888888888888888ffffffffffffffff88888888888888880000000000000000000000000000000000550055005500550055005500550055
  | 0, 15 => 0x5555555555555555555555555555555555005500550055005500550055005500ffffffffffffffffffffffffffffffffeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaffffffffffffffffffffffffffffffff33003300330033003300330033003300eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeecceecceecceecceecceecceecceecc3322332233223322332233223322332233223322332233223322332233223322aabbaabbaabbaabbaabbaabbaabbaabbaabbaabbaabbaabbaabbaabbaabbaabbff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc00ddccddccddccddccddccddccddccddccddccddccddccddccddccddccddccddcc
  | 1, 0 => 0xffccffccffccffccffccffccffccffccaa88aa88aa88aa88aa88aa88aa88aa88ffffffffffffffffaa00aa00aa00aa00ffffffffffffffffaa00aa00aa00aa00ffffffffeecceeccffffffffeecceeccffffffffeecceeccffffffffeecceeccffffffffffffffffffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeff11ff11ff11ff11ff11ff11ff11ff11ff11ff11ff11ff11ff11ff11ff11ff1100ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa0011001100110011001100110011001100110011001100110011001100110011ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22
  | 1, 1 => 0xffffffffffffffffffffffffffffffff44444444444444444444444444444444
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x605040802010070605081a0c010071106050b181c0170605041b10010070605040d1a1901706050b181701007110614150b0e017110616150b130171106140b1312017060504031001007110605040b1001706050b0f0e0100706050d020c010070605090b070a007060509080701007060504030201007
  | 7, 0, 1 => 0x60504031a0100706051e0d1d01007
  | 8, 0, 0 => 0x60508131c0c0100800110614150b130172a05040b1a13010080629040b131c010081106280b131c0c0180614150b1312010082705040b1317010080605260b250e010080623040b131701008060b131c0c2401008110614150b131c018060509150b130a00806230b132212010080605090b07210100805040b131c2001008061f0b131c0c01008
  | 8, 0, 1 => 0x6050d13170c01008110623040b131c01806050b131c320c018110605150b220e01806051e0b1d31010080623040b131c0100805040b131730010080605090b1d170100806141e150b1301008110605040b1c2f0180614150b2e130100806050b131c0a0c0081106050b13221201806050b132d1c0c0180605042c170e010080605040b1c0e2b008
  | 8, 0, 2 => 0x1106050d131c0c01806230b13170c010080605090b071701008060504081c0e01008110614040b1317018060515040d1a01008000605040b100100706051e0b3721010080605040b1c100100806050b1336170100811060504131c35018110605042c1c0e0180614150b1334010080614150b130e01008060504081a130100806050b1a1c3301008
  | 8, 0, 3 => 0x614150b1341010080605040b131c430080605040b13421701806140b131c120100806050b1341400c018110605090b071c018063f040b1c0e0100811063e040b1a1c018113d05040b13170180605040b133c1701806230b131c0c010080605041b1a31010080605040b1c0a0e008113b05040b131701806053a0b1c390e0180605040b1c0e38008
  | 8, 0, 4 => 0x6050b31020c010082a05090b371c01008110605040b1a210180605044a1317010080605040b131c49008000614150b0e010070605040b1c0e480180605041c0e47010080614150b1c0e0100806050b371746010080616090b371c01008000616150b13010070006140b1312010070605040b45170e0180605150b132d220180605040b131744018
  | 8, 0, 5 => 0x6050b181c4601008113b050b131c0c01806280b1a1c0c01008063e040b1c02010080006050b181c010070605040b2e4e1701806050b131c4d0c0080605090b4c1c0100806144b150b13010080623040b1c0e01008063e0b1a1c0c0100806050b131733010081106050b371c460180605150b130f010083b050b13170c010080605040b1c450e018
  | 8, 0, 6 => 0x1106050b170e0c0180605040b1340550183d05040b170e0100806050b131c540c018110616040b131c018110605042c13170180605040b210201008110605260b132501806050b341c46010080605090b1c53010085205040b1c0e010080605090b371c320180605040b2e51170180605040b131c500181106054f0b1a1c01806050b1a210c01008
  | 8, 0, 7 => 0x605090b181c0100806050b071c460100806050457131c01008110605040b56170180605044a170e0100806054f0b1c0201008110605090b37170180605040b100201008113d05040b1c0e018061609150b13010080605040b132d170180605152c1a1301008112a05040b131c018
  | 9, 0, 0 => 0x605042c1a131c010090006050b1322120100806050b131c0c5c01009110605150b131c0c01906055b040b131c010090605150b134122010090605040b5a131c450193b053a040b131c0100906050b131c22120100906050b131c210c0100906593e040b131c010090605260b13170c010090605040b2e411c4e01906050b58131c0c0100911060509040b1c0e01900000614150b1301007
  | 9, 0, 1 => 0x605040b131746010090605260b131c0c01009061609040b131c01009000605150b220e010080605040b170e020100906054b040b1c0e010090605041b131c02010090605040b561c0e0100906050b5e13170c01009000605040b1c2f0100806051e040b1a31010090605150b1c220e01009060509040b1a1701009001106054f0b131c01800110605040d131c01806053a040b131c5d019
  | 9, 0, 2 => 0x2a0509040b131c0100906050b5e131c0c010090605040b131763010090605040b5a131c010090605624f0b131c010090605040b1a310c01009002705040b131c010080605040b131c3201009000623040b131c010080605042c13411c01009110605040b1337170190605040b611c4e01009110605040b131c600190605040b131712010090605040b170e5f0100906050b1a1c0e0c01009
  | 9, 0, 3 => 0x605040b1341400180605040b13411c6801906051e040b1317010090605040b131c67010090605040b17250e010090605040b13411c660190605040b131c460100906050b411c0e0c0100906053a040b2e1c0e019000605042c1c0e010080605040b1a1321010090605040b1c0e02010090605040b2e131c4501906050b131c0c65010090605040b13176401009060515040b170e01009
  | 9, 0, 4 => 0x6050b131c660c0100906053a040b170e01009060509040b176c010090605040b131c630100906050b1a1c0c6b010090605090b1c0e0c0100906050b131c400c0100906054b150b1322010090005040b131c30010080605040b134517010090605040b131c120100900060504131c350100806056a040b1317010090605040b131c690100911060509040b1a1c0190605040d131c0c01009
  | 9, 0, 5 => 0x605040b13391701009060515040b131c710090006050d131c0c0100806051e040b131c010090605040b131c70010090605040b1c250e010090605040b1a561c01009110605040b131c120190605040b136f170100906050b13170c60010090605040b131c6e55019110605040b1c0e5f0190605040b131c450e0190605040b131c6d01009000614040b131701008110605040b131c46019
  | 9, 0, 6 => 0x6053a040b131c710090605040b131c76010090605040b56411c010090605040b22170e010091106051e040b131c0190605040b1a1d3101009110605040b13170c019003b05040b1317010080605090b37411c010090605040b1334170100906053a0b13411c0c01911060515040b1c0e0190605040b131c750100906743e040b131c0100906050b13731c0c010090605040b1c0e7201009
  | 9, 0, 7 => 0x110605040b1331170190605090b1a1c0c010090605040b2e1341170190605040b137a1c01009000605090b071c01008001106050b13170c018060509040b131c320190605040b13176b010091106050b131c0c600190605040b137917010091106050b131c170c01906050b131c550c010090605040b7813170100900063e040b1a1c01008003d05040b13170100806050b131c770c01009
  | 9, 0, 8 => 0x605040b1c0e680100906054f0b131c3301009060509040b1c02010090605040d13411c010090605040b1a19131c019110605040b1c220e0190605040b1a131701009000605040b1342170180605040b7c131c0100906050b131c0c46010090614040b2e131c0100900113b05040b131c0180605040b13421c170190605040b1a131c450190605150b56131c010090605040b1c0e7b01009
  | 9, 0, 9 => 0x605040b13175d010093b05040b131c0c01009000605040b1c450e018000605040b131c4401806056a0b131c0c0100906050b13170e0c0100906051e0b131c0c01009063e3a040b131c010090605040b1c0e7d0100906053a040b411c0e019110605040b1a13170190605040b6113170100900113d05040b131c01806056a040b13411c019000605040b131c3c018000605040b1a2101008
  | 9, 0, 10 => 0x1106050b131c0e0c0190605040b1a3102010090605090b371c210100906054b040b2e131c019003b050b131c0c010083d05040b131c0e0100906050b13341c0c01009060580040b131c010090605040b0713170100911060509040b13170190605040b131c33010090605090b1a1d1c010090605040b13177f010090605040b7e131c0100906053a0b1c0e0c010090006050b371c4601008
  | 9, 0, 11 => 0x110605040b07131c01906050b131c0c8201009000605260b13250100806050b136e170c01009060515040b1a310100906051e0b1d131c0100906053a040b131c550190614040b1a131c010090605040b1c0e12010090605040b134217010090006054f0b1a1c01008000605040d1a1c010080605040b2e170e010090605040b56131701009110605040b13176c0190605040b131c8101009
  | 9, 0, 12 => 0x60584040b131c010090006050b170e0c0100800110605150b13220183b05040b13411c0100906050b1c0e0c60010090605090b13170c01009060583040b131c01009110605040b56131c01906050b1c170e0c01009110605150b131c2201906050b131c6e0c0100906053a040b1a3101009000616040b131c0100806050b1341170c0100906053a040b2e1317019000605042c131701008
  | 9, 0, 13 => 0x605090b3717010080605040b131c870100906050b1c0e0c4601009003d05040b1c0e010080605090b371c170100900110605042c131c018062315040b131c010090605040b5e1c02010093d05040b13411c010090605040b1a1c46010090605040b1a131c8600906054f3a0b131c01009853d05040b131c01009002a05040b131c0100806050b131c4e0c01009000605040b136617018
  | 9, 0, 14 => 0x110605090b371c018000605040b131c3201811060526040b131c0190605090b371c4601009063e040b131c0c0100906054b0b131c0c01009110605040b131c2101911060526040b1317019060509150b1a1c010090605040b1342411c019000605040b5617010080605040b131c5c01009060509040b1a2101009001106050b1c0e0c0180605040b7e13421c0190605040b1a170e01009
  | 9, 0, 15 => 0x6056a090b371c0100906051e090b371c010090605040b13178801009000605044a1c0e0100806051e040b1321010090605040b131c5301009
  | 10, 0, 0 => 0x60509040b1a1c010090000110605040b1317018060515040b1a131c0100a00110605040b131c17019000605040b131c55010090605040b131c220e0100a0006053a0b131c0c01009000605040b13371701009000605040b131c600100900000605040b131c450180605040b1a131c020100a0605040b13371c170100a06054b040b13411c0100a0006053a040b13411c019060515040b131c310100a0605040b2e131c220100a
  | 10, 0, 1 => 0x605040b131c45010090006056a040b131c010090006051e040b131c01009060509040b131c210100a000605040b13170c0100900060515040b1c0e010090605040b131c170c0100a06050915040b131c0100a00110605040b13371c019000605040b131c1201009000605040b1c0e5f0100906053a040b1a131c0100a060515040b13411c0100a000605040b2e131701009000605040b131c46010090605040b2e131c170100a
  | 10, 0, 2 => 0x3d05040b131c0100806054b3a040b131c0100a0605040b1a131c170100a000605040b1c220e0100900110605040b131c0c01906056a040b2e131c0100a00003b05040b131c010080605040b13411c220100a000605040b1331170100906054b15040b131c0100a000006050b13170c010080006050b131c0c600100900000614040b131c010080006050b131c170c010090006053a040b1c0e010090605093a040b131c0100a
  | 10, 0, 3 => 0x110605040b1a131c0190605153a040b131c0100a000605040b61131c0100900060509040b1317010090605040b13411c550100a060509040b131c170100a000605040b131c6e0100900000605040b13421c0180605040b131c0e0c0100a000605040b134117010090605040b13411c170100a00110605040b131c3101900001106050b131c0c018000605040b136e1701009000605040b1a1317010090605040b2e131c0c0100a
  | 10, 0, 4 => 0x605150b132201008000605040b13421c0100906056a09040b131c0100a06051e09040b131c0100a000605040b56131c01009000605150b131c22010090605040b1a131c0c0100a000605040b07131c010090011060509040b131c019060509040b131c460100a06051e040b1a131c0100a000605040b131c5d01009000605040b13176c010090006050b131c0e0c010090605040b1337411c0100a0605040b131c176c0100a
  | 10, 0, 5 => 0x605040b131c4001009060509040b13411c0100a00000605040b561c01008000605040b1a1c0e0100900000605090b371c0100800060526040b131c01009000605040b131c210100900060526040b131701009000006050b1c0e0c01008000605090b131c0c010090605040b1a1d131c0100a0006050b13411c0c010090006053a040b2e131c01900000605042c131c010080605040b13411c390100a0605040b13411c0c0100a
  | 11, 0, 0 => 0x60509040b131c010090605040b13411c010090605040b1a131c010090605040b131c31010090006050b131c0c010080605040b131c0c010090605040b2e131c0100900110605040b131c0180605040b13371c01009000605040b1317010080605040b131c1701009
  | 12, 0, 0 => 0x605040b131c01008
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
  | 0, 0 => 0x7c003f0003e000001f000001f0001f00f00000000000000000000000000000000000003ffffc0000003ffffffc0000000000000000000000000000000003fff00000003fc003ffc0003fc00003fe00000000000000000000000000000000000fffc000000000000000003ff00001ffe00000000000000000000000000003e0ff83fc00fffc1fc1fc00fffffe0f87e0f80000000000000000000000000003e0ff83fc00fffc1fc1fc00fffffe0f87e0f8000000000000000000000000000000000000003fffffffffffc00000000000000000000000000000000000000003ffffffffffc00000000000000000000000000
  | 0, 1 => 0x3fff0003fc0fffc1fffffe0ffc00e0ffe001f0000000000000000000000000003e0ff83fc3fffffffc1fc1fffffffff87e0f8f000000000000000000000000003e00f803c003c3c03c03c003c3e0e0381e0180000000000000000000000000003fff0003fffffffffffffffffc00ffffe001ff000000000000000000000000003e00f803c003c3c03c03c003c3e0e0381e018000000000000000000000000000000000000003fffffffffffc000000000000000000000000000000000000000001f0fffc3c00000003e03e0003ff00079ffe70000000000000000000000000003e00f803c003c3c03c03c003c3e0e0381e0180
  | 0, 2 => 0x3ffffffffc0fffc1fffffe0fffffe0fffffff0000000000000000000000000003fff00000003fc003ffc0003fc00003fe00000000000000000000000000000000000fffc03f0003e000001f003ff1f001ffe0f000000000000000000000000003fff00000003fc003ffc0003fc00003fe000000000000000000000000000000001f007c03c00000003e03e000000000781f070000000000000000000000000003fff0003fc0fffc1fffffe0ffc00e0ffe001f000000000000000000000000000000000000003ffffffffffffffffffffffffff000000000000000000000000003e0ff83fc00fffc1fc1fc00fffffe0f87e0f80
  | 0, 3 => 0x3fff00000003fc003ffc0003fc00003fe000000000000000000000000000000001f0fffc3ff0003e03e03ff003ff1f079ffe7f00000000000000000000000000000007c000000000000000000000000001f000000000000000000000000000000000000003f0003e000001f000001f0000000f000000000000000000000000003e0ff83fc00fffc1fc1fc00fffffe0f87e0f800000000000000000000000000001f007c03ff0003e03e03ff000001f0781f07f000000000000000000000000003ffffffffffc0000000000000000000001f000000000000000000000000000003e0f07c3c3fffffffc1fc1fffc00fff861f18f
  | 0, 4 => 0x3fffffc1fc1fffffffff87e0f8f000000000000000000000000003ffffffffc0fffc1fffffe0fffffe0fffffff0000000000000000000000000000000fffc000000000000000003ff00001ffe00000000000000000000000000000000fffffffc03ffc003fffc03ffffc01fffff000000000000000000000000003fff0003fc0fffc1fffffe0ffc00e0ffe001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffc00003ffffffc0000003fffffff
  | 0, 5 => 0x3e0ff83fc3fffffffc1fc1fffffffff87e0f8f000000000000000000000000003ffffffffffc000003e03e000000000781f070000000000000000000000000003ffffffffffc0000000000000000000001f000000000000000000000000000003e00f803c003c3c03c03c003c3e0e0381e018000000000000000000000000000000000000003fffffffffffffc00ffffe001ff00000000000000000000000000000000000003ffffc0000003ffffffc0000000000000000000000000000000003fff00000003ffc1fffffe0ffc00e0ffe001f0000000000000000000000000003fff00003c03fc003ffc3e03fc00003fe00070
  | 0, 6 => 0x7c000000000000000000000000001f000000000000000000000000000003fff0003fffffffffffffffffc00ffffe001ff0000000000000000000000000001ff07fc3ffc3c3fc3fc3ffc3c1f1fc7e1fe7f00000000000000000000000000000007c000000000000000000000000001f000000000000000000000000000003fff0003fffffffffffffffffc00ffffe001ff000000000000000000000000003ffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffc00003ffffffc0000003fffffff
  | 0, 7 => 0x3fff00000003fc003ffc0003fc00003fe00000000000000000000000000000003fff00000003fc003ffc0003fc00003fe0000000000000000000000000000000000000000003ffffc0000003ffffffc000000000000000000000000000000000000000000003ffffffffffffffffffffffffff00000000000000000000000000000000000003ffffc0000003ffffffc0000000000000000000000000000000003ffffffffffc00000000000003ff00001ffe00000000000000000000000000000000fffc00000000000000000000000000000000000000000000000000000000000000000003fffffffffffc00000000000000
  | 0, 8 => 0x1ff07c03ffc3c3fc3fc3ffc3c001fc7e1f07f000000000000000000000000003e0f0003c3fffffffc1fc1fffc00fff860018f000000000000000000000000003ffffffffffc0000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffffffe0fff00000000000000000000000000000000000003fffffffffffffc00fff860018f000000000000000000000000003ffffffffffc0000000000000000000001f000000000000000000000000000003ffffffffffc003e000001f000001f0000000f000000000000000000000000000000000003f000000000000000000000000000
  | 0, 9 => 0xfffc000000000000000003ff00001ffe000000000000000000000000000001f007c03c0000000000000000000000000000000000000000000000000000003ffffffffffc000000000003ffffffffffffff00000000000000000000000000000007c000000000000000000000000001f000000000000000000000000000003ffffffffffc003e000001f003ff1f001ffe0f000000000000000000000000003e00f83fc003c3c03c03c003c3ffe0381e0f8000000000000000000000000000000000000003fffffffffffffc00e0ffe001f0000000000000000000000000003ffffffffffc00000000000000000000000000
  | 0, 10 => 0x3e0ff803c00fffc1fc1fc00fffe0e0f87e01800000000000000000000000000001f007c03c00000003e03e000000000781f07000000000000000000000000000000000000003ffc1fffffe0fffffe0fffffff000000000000000000000000000000000000003ffffffffffffffffffffffffff000000000000000000000000003ffff83ffc0fffc1fffffe0fffffe0fffe0ff000000000000000000000000000000000000003ffffc0000003ffffffc00000000000000000000000000000000001f007c03c000000000000000000000001f00000000000000000000000000000000000000003ffffffffffffffffffffffffff
  | 0, 11 => 0xf83c000000000000000003ff00001e0e00000000000000000000000000003ffffffffc0fffc1fffffe0fffffe0fffffff000000000000000000000000000000000000003fffffc1fc1fffffffff87e0f8f000000000000000000000000003ffffffffffc003e000001f000001f0000000f000000000000000000000000000000fffc0003ffc1fffffe0fffffe0fffffff0000000000000000000000000003ffffffffffc000003e03e000000000781f070000000000000000000000000003ffffffffffffc003ffc0003fc00003fe000000000000000000000000000000001f007c03ff0003e03e03ff000001f0781f07f
  | 0, 12 => 0x1f000003ff0003e03e03ff000001f0780007f000000000000000000000000003ffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f007c03c00000003e03e000000000781f0700000000000000000000000000001f0fffc3c00000003e03e0003ff00079ffe70000000000000000000000000003ffffffffffc00000000000003ff00001ffe00000000000000000000000000003ffffffffffc003e03e03ff000001f0781f07f000000000000000000000000000000000003f0003e000001f000001f0000000f
  | 0, 13 => 0x1f007c03c00000003e03e000000000781f070000000000000000000000000003fffffffffffffc1fffffe0fffffe0fffffff0000000000000000000000000003ffffffffffffffffc1fc1fffc00fff860018f0000000000000000000000000001f007c03c00000003e03e000000000781f0700000000000000000000000000001f000003c00000003e03e0000000007800070000000000000000000000000003ffffffffffc000003e03e0003ff00079ffe7000000000000000000000000000000000000003fffffc1fc1fffc00fff860018f00000000000000000000000000000000000003fffffffffffffc00ffffe001ff
  | 0, 14 => 0x3f0003e000001f000001f0000000f000000000000000000000000003e0ff83fc3fc003e000001f000001f0000000f000000000000000000000000003fffffffffffffc1fffffe0ffc00e0ffe001f0000000000000000000000000003ffffffc0003fc003ffc0003ffff003ffffe000000000000000000000000000001f000003ff0003e03e03ff000001f0780007f000000000000000000000000003e0ff83fc3fc00000000000003ff00001e0e0000000000000000000000000000000000000003fffffffffffc0000000000000000000000000000000000000000000000000003ffc1fffffe0ffc00e0ffe001f0
  | 0, 15 => 0x3ffffffffc0c00000000000003ff00001ffe00000000000000000000000000003ffffffffffc003e000001f000001f0001f00f000000000000000000000000003ffffffffffc00000000000003ff00001e0e000000000000000000000000000001f007c03ff0000003e03e000000000781f070000000000000000000000000000000f83c03f0003e000001f003ff1f001e0e0f000000000000000000000000003e0f0003c3fffffffc1fc1fffc00fff860018f000000000000000000000000000000fffc00000000000000000000000001f0000000000000000000000000000001f0fffc3c00000003e03e0003ff00079ffe70
  | 1, 0 => 0x1f0fffc3c000000000000000000000000000000000000000000000000000000000000000003fffffffffffc000000000000000000000000000000000000000001f007c03c03ffffc3e03e03ffffffc781f070000000000000000000000000003ffffffffffc003e03e03ff003ff1f079ffe7f000000000000000000000000003e0fffffc00fffc1fc1fc00fffffe0f87fff80000000000000000000000000003fff0003fffc003e000001f000001f0000000f000000000000000000000000003e0f0003c00fffc1fc1fc00ffc00e0f8600180000000000000000000000000000000fffc03f0003e000001f003ff1f001ffe0f
  | 1, 1 => 0x3ffffffffffc000003e03e000000000781f070
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2511fc447f0447e04a44bf044633f0aa7f29f00000000000000000000000000108442111107ffffc1001003ffffffc4008040000000000000000000000000003fff21080083fc103ffc0083fc84083fe84408000000000000000000000000000842fffc004111089089084513ff04225ffe04000000000000000000000000003e3ef8fbcc3ff3c7bc7bc63ff3fce3b9de3db300000000000000000000000000380ee03b000f3301b01b000f339c80a0580c000000000000000000000000000021088422220bfffffffffffc01080000110800000000000000000000000000003ffffffffffe22212212210a22109080000000
  | 0, 1 => 0x35ac0847b84eaa896b52b44aa821c4d5021364000000000000000000000000003a0fe83f43ef777db41f41ef77bdbea87a0e8e000000000000000000000000003e30f8c3cc33c3c63c63c633c3e0e3399e31b30000000000000000000000000037bd0003ffbeeef76f76f7baec00fbdda001fb000000000000000000000000003e20f883c823c3c43c43c423c3e0e2391e21a20000000000000000000000000021188c66265bfffffffffffc01290500931a15000000000000000000000000000df2fffcbc51998adbe9be559bff4577dfff75000000000000000000000000003e30f8c7cc73c3ce3c63c673c3e1e7399e33b7
  | 0, 2 => 0x3deef7bbb80fbb81fbdbbc0fbbdec0f75ded60000000000000000000000000003fff294c04d3fc1a3ffc02d3fca50d3fea561d000000000000000000000000000a53fffc47f1557e94ad4bf557ff3f2afffe9f000000000000000000000000003fff294c00c3fc183ffc00c3fca50c3fea560c0000000000000000000000000005f017c0bc1088824be0be108842415785f1710000000000000000000000000035ac0003b80eaa816b52b40aa800c0d500016000000000000000000000000000000000000001dddeddeddef5ddef6f7fffffff00000000000000000000000000381ee07b041f3303b03b021f339c81a0d81c11
  | 0, 3 => 0x3fff21080493fc123ffc0293fc84093fe84419000000000000000000000000000ff3fffcfff1ddfedfedfff5dfff7f7fffffff0000000000000000000000000000401fc400400008008008400063040207f204000000000000000000000000000211084447f0447e042443f044213f08a2129f000000000000000000000000003e2ef8bbc82ff3c5bc5bc42ff3fce2b95e2da20000000000000000000000000007f11fc4fff0ccfe4fe4fff0cc637f5fa7f3ff000000000000000000000000003ffffffffffe22292292294a2273948207f20400000000000000000000000000324d17c343ae6675249649aa6442ba8a25f08a
  | 0, 4 => 0x108442111107ffffd50d50e7ffffffec7a8ece000000000000000000000000003deeffffb84fbb89fbdbbc4fbbffc4f75fff64000000000000000000000000000842f7b8000111009089080513de00225dec00000000000000000000000000000000deb7fb6c03edc003fd6c037bf6c017abe6000000000000000000000000003fff210bb88ffe917ffeb48bfc84c8ffe84568000000000000000000000000000000084400400008000000400021040002120400000000000000000000000000001008440450000a0020025000210500821215000000000000000000000000002f6bb5aaeaa800003edfedac0000003b7d6daa
  | 0, 5 => 0x3a0fe03b43af7775b41f41af779cbaa8780c8a000000000000000000000000003ffffffffffeaaa36bf2bf1aaa52d1d785f171000000000000000000000000003ffffffffffe222322b22b1a2252918285f011000000000000000000000000003e20f8c7c863c3cc3c43c463c3e1e6391e33a60000000000000000000000000021088422220bfffffffffffccd086b5db109fb0000000000000000000000000010944a551557ffffc1201253ffffffc4829255000000000000000000000000003fff21080083fc907ffc9483fc84487fe84568000000000000000000000000003fff2108bc93fc927ffcb693fc84497fe84579
  | 0, 6 => 0x4017c000000000008008000042000205f0000000000000000000000000000037bd0043ffbeeef76f76f7baec00fbdda011fb0000000000000000000000000001df0738379c3c33c3bc3b9c3c1e19c6e1cc5900000000000000000000000000005017c00410000200a00a100042010285f0110000000000000000000000000037ad0003fbaeeef56f56f5aaec00fadd2001ea000000000000000000000000003ffffffffffe222b2232235a223195808212150000000000000000000000000000100040041000020020021000000100801011000000000000000000000000002f7bb5aaeeb800003effefbc0000003bfd6dbb
  | 0, 7 => 0x3fff290c00c3fc183ffc00c3fca50c3fea460c000000000000000000000000003fff21480493fc123ffc0293fc84093fe854190000000000000000000000000010844a551147ffffc1001043ffffffc402924400000000000000000000000000000000000001ddd6ddeddeb5ddce6b7ffdedfb00000000000000000000000000109442511517ffffc1201213ffffffc4809051000000000000000000000000003fffffffffff3329b29b294f33ff94a25ffe04000000000000000000000000000842fffc0040000800000040023104000212040000000000000000000000000021088c26224bfffffffffffc01290400130a04
  | 0, 8 => 0x1dd0740379c2c3343b43b982c0219c6a1d05900000000000000000000000000320d000343ae6675241641aa6400ba8820008a000000000000000000000000003ffffffffffe22292212214a2231948002120400000000000000000000000000000000000001dddedd6dd6f5ddad6f7dfa0fff0000000000000000000000000021088422220bfffffffffffc45082a0831088a000000000000000000000000003ffffffffffe22212292290a2252908205f000000000000000000000000000003ffffffffffe667f263663fa6631bf88a2129f000000000000000000000000000211084447f000220020031000001100801011
  | 0, 9 => 0x852fffc0451110a90a90a5513ff0522dffe150000000000000000000000000005f017c0bc1000020220221000000100801011000000000000000000000000001ee77b9dd9e4000000000003fef7feff6ee7ee0000000000000000000000000000501fc40450000a00a00a500063050287f215000000000000000000000000003fffffffffff777fb6bf6bff77ffbfaafffe9f000000000000000000000000003e22f8bfc863d3ccbc4bc467d3fde6395e2fa60000000000000000000000000021088422220bfffffffffffc89084055110960000000000000000000000000003ffffffffffe22292212214a22319480020204
  | 0, 10 => 0x3e2cf883c82fe3c53c53c42be3e0e2b91e21a20000000000000000000000000005f01fc4bc50888a4be0be508863455787f375000000000000000000000000000000000000019980d9c99c0599ce40775ded6000000000000000000000000000000000000001dddcddcddce5ddef6e7f7fefee000000000000000000000000003daee03bb80fbb81fb5bb40fbb9cc0f5580d600000000000000000000000000010844a151147ffffc1001043ffffffc40282440000000000000000000000000005f017c0bc100000028028000042000205f00000000000000000000000000000000000000001ddd4ddcddca5ddce6a7f7dedea
  | 0, 11 => 0x802e83c004111089009004513bd04205a0e04000000000000000000000000003dfef7fbbc1fbb83fbfbbe1fbbdec1f7ddfd7100000000000000000000000000000000000001555c940d40e555ad2e287a0e8e000000000000000000000000003ffffffffffe6677263663ba6610bb88a0009b000000000000000000000000000842fffc00419988d9c99c459bff44775fff64000000000000000000000000003ffffffffffeaaab6bf2bf5aaa73d5d787f375000000000000000000000000003ffffffffffffe333ffe239bfe9499bfe854190000000000000000000000000007f117c0ffb0ccf64fe4ffb0cc427b5fa5f1fb
  | 0, 12 => 0x7b10000ffb0ccf64f64f7b0cc007b5da001fb000000000000000000000000003ffffffffffe22232232231a2210918080101100000000000000000000000000001000000410000200200210000001008000110000000000000000000000000005f017c0bc1088804bc0bc008842405705e160000000000000000000000000000de2f7b8b8019980dbc9bc059bde40775ded60000000000000000000000000003fffffffffff332bb2bb2b5f33ff95a2dffe15000000000000000000000000003ffffffffffeeeff6ff6fffaee73ffdfa7f3ff000000000000000000000000000211000047b04476042443b044003b08a0009b
  | 0, 13 => 0x5e017c0b80088804bc0bc008842405705f160000000000000000000000000003fffffffffffbba1fbdbbd0fbbded0f75ded60000000000000000000000000003ffffffffffe6675261661aa6610ba8820008a0000000000000000000000000005e01780b80088804bc0bc008842405705e1600000000000000000000000000005b00000bc1088824b60b61088004155800171000000000000000000000000003fffffffffffbbabfbfbbf5fbbffd5f7dfff75000000000000000000000000000000000000004454040440a044002a0820008a00000000000000000000000000000000000000ccd64d64d6b0cc006b5da001fb
  | 0, 14 => 0x201080443e0447c040441e044213e0822028e000000000000000000000000003a0fe83f43ee667d241641ea6631be8822028e000000000000000000000000003ffffffffffeaaa16b52b50aaa10d0d5000160000000000000000000000000003ffffffc04d3fd1abffd0ad7ffff0d3ffffe1d0000000000000000000000000007b10844fff0ccfe4f64f7f0cc217f5da213ff000000000000000000000000003a0fe83f43ef3329b01b014f33bd94a05a0e040000000000000000000000000021188462261bfffffffffffc010801009118110000000000000000000000000000000000000088804940940088004055000160
  | 0, 15 => 0x3deef7bbb80f3301b29b280f33de80a25dec00000000000000000000000000003ffffffffffe667f26b66bfa6673bf8aa7f29f000000000000000000000000003fffffffffff3329b21b214f33bd94a05a0e040000000000000000000000000007f11fc4fff088aa4be0bf508863555787f375000000000000000000000000000a03e83c43e1557c940d41e557bd3e287a0e8e00000000000000000000000000321d084747fe667f243643fa6421bf88a2129f000000000000000000000000000842fffc00400000008008000252000205f000000000000000000000000000000df2f7f8bc119982dbe9be159bde4177ddfd71
  | 1, 0 => 0xdf2fffcbc50000a02202250023105008212150000000000000000000000000021088c66224bfffffffffffc01290400131a040000000000000000000000000015f45fd5bd57ffffcbe0be53ffffffd787f375000000000000000000000000003fffffffffffffffffffffffffffffffffffff00000000000000000000000000384effff004f3309b09b084f33ff84a25ffe040000000000000000000000000037bd0003ffbe6677263663ba6400bb88a0009b00000000000000000000000000300c0003000e22012012000a20008080000000000000000000000000000000000a43fffc43e1557c948d49e557ff3e2a7ffe8e
  | 1, 1 => 0x3ffffffffffeaaa16bd2bd0aaa52d0d705e160
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 137 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 137 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 137 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 137 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 7 => 39
  | 8 => 463
  | 9 => 1743
  | 10 => 677
  | 11 => 32
  | _ => 0
def CH : Nat → Nat → Nat
  | 7, 0 => 0xe764bfecdfa149d2dd175710bf338ea5b02bc70eaf634869a6bf474f98652e88976ded5b8b13aefe864b3dcc8128daef71bbb4ad6f671fa1660ab15b5eb67a955e2aaabd5dbbf18957408b0354f3d75e4edb22904e5d1c034948b07a47b15dbc444ff7a6410b9c793a4b99713a3ee25733b22a213321d49d2c86fb5e263f1f3324b2727f20331eea0f0c77d00ba395cb0937bcaa083ca17400401969
  | 8, 0 => 0x158f7702157fec9c133259c612dbd1191285b42e1224ef5a11e6a24f114818f3112769631101e41a10cb1b00107adce3100f47ba0fb4022a0ed2a3ff0ea8ace10e8749f90d3604960ceaf71e0ce4e3df0cc17e670c71bb1f0c10689b0bfc6ccf0bede8fb0b27bcb20b1d9e490a7a128f0a6874ca0a070ccc09d81f4609ce4bf7096b1293096010e6090fbeac08e3a84908d13e250881c64907c94ad10787ec790772b11907363a240707c87b05de3e9f05a7366c05828599056e745604bffe9d04acfa5b03963822032cef8d032321440317809f02d4c17802969656020cf07101fbad0301e46f7d0177ea4301688d090140328600c12a67006d1e7a0066b352
  | 8, 1 => 0x27b61024278d491b2728537d267a5c6a265311e3262a90732619538125c304a6245628aa2432441e23ffc5102355285e22964b2621cc69d621aecdfc2176b75421708257212eeb962127e39f2106e9af20eaba42209a667d20717e43202f62511f8927e11f6d511d1eecd50b1edcedec1e262b311dc5029b1d97fa561d65a7251d60c7441d3401031d30fa521c7d7a6e1c3f589f1c29fe6c1c1c60b01bf63ac21bc5c3431bc00e181b8d09721b6846f11b46359a1b000ccc1a8b0c281a8784201a70d30c1a5b8be11a51c1881a4863851a456b6b1963457a192341a518f3dce818c200eb182c01d6174050db16638499164b7e4a1607736215f871b315c0eb64
  | 8, 2 => 0x3f71a0b33f3dd3b73f3729b03f2efe893ecbdb7e3ec7b8533e1ec3453d3f887b3d27124b3cdf55fc3ca68fe83c3768cf3c2f59a83bcf00293ad9dd0a3a30446b3a2d4c723a03cd393a02ffc2382bb7c03826eb3f373897d2372190ef370b4a2e368ba1993686d60f360001b635767a7835015f3c350107623500b468341c8b0833e95320335f5d5c3323e1cc3307ce2532bc966a32b5b45032470b3a3234ca7e3162f38230d2d5ed30790e5b3031b2822f8f04982f33f51c2f1422892f005c2b2eef652d2e6e42992e6d8ae22e5184ac2e18f7842ca6e8752c009caf2b358ae72aa6d89c2aa69a9a2a9b6e092a5641d82a0ca60129665e0e28ce24b427c152ef
  | 8, 3 => 0x59b2eeed5962223058dd9a9658af5f39582c66e6577eb17057024f65568de956559569ab54fa7fc954675cc753ff6e8753517397531c4f9152ad407a5289d8ce523ad47c522653d44fd88a914f98bafd4f3b94644e59440b4df304724d9e4aa74d2d53db4d274f494cb348604cafc0584c0e72484b1bcbd04a496fd84a3ac9ac4a1b3ef84a06039749b1b6a647dd50bd4797574447813161474ca806472f7f374722e421471c05ee46bae6ef467aff1a46348da2458d6bd144d2991144c19c28442fac084419417843dd66c843d10c6543bb420e43ad464a437b507543513bdd433b406442ef285142e7347742d89665427145944218baa840276a6f3f8b75f9
  | 8, 4 => 0x7945fee577cae0a777a1bcc07770273477603490771aa6a276612fdb762d96ea76222e9b7603010275b4fd8f753f4d4b751ae436743edbbc72dd282c72c1e10f71a8c0b771094671710503bf70c23ca670aeaff26f99731f6f8fe25f6d1584066c724ad46be0740b6b7680ba698f2644696ffded6955aa3a68f6b7ec679df8b966e90a9a66b9eaa866899bf2668378d1667dff966536fc796528001a644367b763de938463b6fcaf6381d82b633b57886329400862846d476234b71461b4027061a195d3619e0dcb60c78266603f18986002358c5f86d7535f7513625e3126495e21a5125e0d494c5d90b3525d6ced375c95c3885c3daf1e5a1a8d535a05ead1
  | 8, 5 => 0x9fa3d0149f3bea3a9ec4e9b79d34c0109acd50949a43e9699a351b2f9a17392e99526f86992783789816f46e97b04ab597612e1f96b4936995a4d04994ec95fe946fc04e92dd2f6592b141f092633e7d919e67a19185b0d78fb381558f69fe2a8c4c7cdf8c3145df8b50c41b8b3bf6c68acbaca88a11094b897b5eed89154a6288dca57d8879579a8804521286d7dfb0866812c2866202a685386b3683ec6d4883a3718583682b96831cd53082519a198231b62381610732815d7f2a8115472a80867f22802ed5467fe0372f7f9993ed7f9803457f84a5407e5683497df748797d02a5997c065e1d7b37c58e7b1925117b150dab7aefc2417a3e74cb79c6283f
  | 8, 6 => 0xd5c90be1d5ae5de2d4988884d4647217d1f26cdad1f03c5fd11b0fffcead5366ce054f7dcd947fc3cc0d33fcc99681eac90c1c88c7e754e6c7d71d85c5deb98bc48df491c3ef3356c33e40e7c2d4f4b9c28b8957bf773313bd81ee16bd62e3bbbd2ddfb3bc0a0da2bb8f1d4bba3a554eb86cbf54b71b8269b66b2cb3b600b074b5eeec83b58c7bc9b5442becb52aa43db2e6b2fdb2576504b250e0bcb222d7c9aeac04cbabde2a6aabb1b780ab936161aa303fd7a9931ca1a9887a74a930789da92e647ba8fabdcda706035ba63eb6b3a612bfe6a5e9b806a54edfd1a505e57aa3b8ed50a3067b03a2e032f5a1e6ac24a0bc441fa0b4a2cda0a2a0be9fca1ff1
  | 8, 7 => 0xf484c12df149c274f0fb5f94edbf5a4dec95687aeae0ad87e72a8615e590515de4b3a149e36c6492e300689adfa786b4de6c8f89dc0a314bd5de2bac
  | 9, 0 => 0x4456a97042abc8d040167e70400ad7903eaab8703be1d5603b78d1a038bc75d03799b140367a954033f76d60338199a032071880309326602fec78202defb5902cac33d0292f9b2027d2aa40275758c026f54b202686a05024242e3023bfb3502395a90021235a1020d737d020bcebe02093915020578ba01ec857e01cecd6701be398601bb2c4a019f648e0192401601853c1f017cb78101640c3a0153de48014e2780013fa2640114f593011368510102590a01017fef00ffc1bb00e3357300df811200d3d46400ba8ea500b401d100ae556e007f6d230079639a006c458200660b0600542966004d2c9c004877430036957d002539c900208da900134cab
  | 9, 1 => 0x9e77a3609e1673b09800247097c7a3f0965f294095a93b7092389750920353d091231860906516709059ac308fbe68508e3a84908e1b88008df0c2108d7d9a508d1f19a08c6592508ae9bf7088798bd0883ee27085b924c0857ada308554f07080f246f080e5af4079e9589079b4c9e0792a6e1075baf5c0759c0b7071e1d3e071a953606b95d2306ad3c6806a282890695928806508c33064ba7b006290c6706261b59061657ee05f16c3905c4741105a15637059cc5160569545705656b28050c52c604e0b1cc04d64d9c04d523c304c542d704c0a81104bd200904ae1ead049b4e20049b2a4d0484e38c048345d10481e96f047ae151045a1bd60451e9c4
  | 9, 2 => 0xdb8cacc0daf435f0d94673b0d7a80d40d6b43680d4beaf60d4a594f0d2f51ff0d28ad7c0d17f8cc0d17918c0d105e8f0cf9e91b0cf4c6b30cccfda90ca3bb3f0c822c780c7df23c0c7ceb440c7ac0070c70f2710c6c9b200c576db10c499b7c0c3242900c19a79a0c12aedd0c0f26d50c00a7570becc40d0bded8210bce22060b999c320b9729cf0b73b04a0b62700a0b614d100b51039a0b316bde0b2692f80b0df76c0b06e7ba0ae265ea0adf2c560ac25ebb0abd6d180a96c99a0a92444f0a8ed2a90a88746d0a74f2900a6eb71e0a6920cf0a64ee330a62cfbb0a5d5e470a4c3b0a0a4131b40a39faae0a36fd320a219e4c0a0f7de40a04d4b609ea01bb
  | 9, 3 => 0x139db2821368adb113556fba13298f0c130f285d12fe4fdf12f4127612beaecd12b988ac129e4c0a129536b11284e11b1278a44412782502127698ae1218fdce12095b511206eb5211f58bcd11e4801a11d05b7f11ccd37711c4df2611bc9b3011804e5c11758676116bcdc6114e1ed310fcd1c610f4e9d310edeeca10e6f8a210e3080510ddff0e10aa1e34109e0da1107bda961065a1dc1053d761104f5b1b104a1a30101c019e10163ff90fcdf4110fb574780faa62c10f8159a70f67daed0f264bbb0f1a10500f0a44c40ef75b310eec68ee0ed848480ecc10510e9ba5900e8244aa0e6aa74c0e5ae6310e5366cd0e4671110e3110bf0df128ea0dc2e70f
  | 9, 4 => 0x19c4ee9b19bf853119a9c9db199c883a199ac9d91993ece5195cdb26194e5a931948b72c194276731931c88a192aefc21917af0718ae4fa818ac13b518a96dde187e572e1866b9591852a5661813cadc180cfdd117a41ae017a15ad91788259717849d8f17730eb6176d946c1764326b175cf54b1735191b172b500416f5c8ea16ea9c8916dbecee16acdd7916a537ef16202c9a15f3fe3f159b6b07158b48b2158594dd157b66f715760903155a7b6f1549a2f1153f65881515c12a150ad19814f73d7214f0687814b82f4914b270d1146b226d1465ce2a145e44351450e9ab1437b37e142fa36a1428e86d1405bc0813e437c213cd31fa13cac27b13abf14c
  | 9, 5 => 0x1f0ae9011eef9d821eec20fa1ee53b201ebbb46b1e8c86c21e885a111e852b931e84d2091e5bf6131e3445531e30136d1e2ef7fd1e2ea0371e2af86f1df864281db099f81da77cd91d7ee2b71d7b5aaf1d69605e1d5456261d35ae0b1d1f75511d18b4d11cee12e31cd054471cbf61621cb7ce731c2bd7651c254ab81c12b8ef1bf63ac21bbc0f8a1bb0dce71b9dc67f1b90c6161b8b8a2c1b4757641b17d6cb1b07eb991af25f791ae73ac61ad816471ac87e3a1ab4beff1aa652021a9b980d1a848a711a73a6101a6fa04a1a642a3c1a42973b1a3b841e1a3891e31a2959b61a26ffc01a219cd71a0911691a04b48519fb875e19f8bc3d19e79f2e19cdbe4b
  | 9, 6 => 0x24d076c824bc937924800d6f2472c457245cebdd24573fd12446820e242cd5a42429723c2414a2cc241134302410e2c6240c5d502401dc6123efcdc123e7f5a423e4caad23db634423c3152823a287d42397f609237d954823679e1122ecc9a122e07fc522cd217e22c0cd9322b7be5e22a049e6226a1ee0224b597b224b06042225c36821f2bf6721f012a221ec85d721c7109d218ece43217172862163347221556e982151e6902140809221319cab210027d520ac7451206c5e4420535d74200ba1252003722c200339691ffac9661fede8c81fedb7c41fd9d2ad1fc486831fb773541f8635f11f73b5e21f715db61f6d511d1f48168b1f2b6b921f270b8c
  | 9, 7 => 0x29b7bf1b29a58bd7296f7ca5296d86b5292c332a291d6ac529197cbb290efc5728f5574928d05bf528a57fac289c52a7288d190f287163082870b4a5286cc0632869eded28433a42283e390f2824e440280884cd2801c49c27f3829627e33a1927bc385a27b00d5627a6cfef27839b9527807ccc275a38c5274303482724c4812711cef3270770e52701bd1026fb5b8d26f7eda526f4449a268c58c3268776c126770572266c90ab266acd9826509fd6264a4c60263061dc2627b1c72621450b260724c925f3d14525f1291225c843a725c32b4625c072742581e672254a6af425495a2d25461fdc2545bdda24f8a42a24f31e6a24ee5d7524ec4f5a24e36080
  | 9, 8 => 0x2f874bb42f41922c2f1422892f1157a72ee588912ed040262ebee8ff2e873c922e63ed602e6163f32e4eec982e4c7c7a2e43c2a72e2d6b192e2c11592e2b91d92e22cd582df9a2a12de810ef2dc7f5ae2db88f532da7ff982da6269f2d9ab2582d9539902d8c3ffc2d87da9b2d85ad832d68d6442d30e99d2d2c59062cf6a4042cb975492cad49b12c99c45b2c48428c2c3d9b8b2c21601e2c1b66532bcff1872bcde9bb2b64675f2b56563d2b52ce352b24c3a62b0817962aca03862ab754d82aaff0f82aa913b72a9f69d82a93d73a2a7c0b2c2a5e7b062a586aa02a51d4c72a42a8292a27cd052a268f392a07860229ebcb5129e4909a29ceeea729c50508
  | 9, 9 => 0x34e3c25e34b54dee34b17e2c3482825b34214fa4341e4b37341121b2340d72b933fce5ce33fa3ffe33ed4ffd33d51aef33d0abbb33c0edd1338f9f683383936533737906334965e6332f3c4b33162e5e32fb3e3d32f9a4be32ecaa8a32b887a932932982327db2fb3275ba3f3264103b325446c4323989a03233d5cb32316537322fa06c322cf33b320469e23202823431eda67631b2779f31aeecec31955352319165623164a49631586aee3138d8583121aac33105501430dde45830d35ff430d0be9030bfe1ae30b3fcf63074c795302b9a89302740ed301ad7eb300f24613001ce432ffa837f2fec36472fdacf012fbaa7e82fba89102faac86a2f8a6b44
  | 9, 10 => 0x3aa216c43a8d2aaf3a681c043a5d373e3a380adf3a011e9f39fd981639ea358939d7ed863999c216398c2f3a396e23c2393dd801393104a338d38ba638cb1d1c38bb02dd38b9850e38ac7bf8387b2d8f387453cc384675d2384273bc3836e42137ea01c437ccc80937c0162837bf6cee379d6d3e3781245e3753e96d373ff1b7373f2cd937208d7e371d90e737126b2a370cb57a3709f126370955be3702ae0136f2a73636f074e236d85e3f36b69ece3671f1d736587569364ac92836490ac736393193362cdb653624ecbe3623ee6435f9df8d35f193d435e4a53535ddb4f235c3a708354c7cb835452ada35404634353bbebb352c981c3505dee934f9b6e8
  | 9, 11 => 0x40e118ec40c2e3ba40b0bdc54095e4ef406549fa4048460f3fefccf23fedf4df3fe9b3153fe8c2c63fce56233fcdacdf3fb950ed3f8ec0b33f6b18ed3f46817f3ee9263d3ee5b7d43eca73503eb9cfad3ead956c3eabf6473ea7482c3ea100553e9cf9823e8a2d783e26525d3e16fc733dbf0ece3d5ef9f33d540d043d17fbe13d097e743cd2ee6b3cd27e703cb59b5b3caf49dc3c8ac2213c8a83a93c873a193c6797e83c51c5893c4985ac3c443eb93c425f633c41634a3c34a5373c17963c3bfa592d3bb929ef3bab24423b91c2933b88ce343b753ff93b2398053b1ccfe23aff8ca93af05aa93aecf53b3ae9aee83add38eb3adce1253acc67d93aab9781
  | 9, 12 => 0x475e31e64739197b472b77044715f182467d2f954675df1b4653ccc5464d3ed6462e0d2e45fb097445f2e91d45cbb75245caa12b45be76ce45a167bc4582e4dc457e9ce345461371452fccb045214215451c4e4444efcd2644eb089144e143e144b0bd0644b0406c44abb27444a1c3844448b0d0443b0ff44432c9e04424843843ba153043abb8f343a7960b4359970f43265264431e18b2431871f14316ed2a42fabd7342f88d4e42f3767f42c1f71942a31ed6428bb2a9427d8a284273f3a64272b7e2422e3b8a41f5368e41db777f41cd766341b7f3c741a7c2bc418f70f3417eb7b6416800364127eab6410dcf2340ff2e6b40fba66340f8789540f56ff7
  | 9, 13 => 0x4e2b8e694e22e8084e0bf5e74dd43d414dccc6bc4dab81db4d7d6e904d69dc7e4d6752104d4f46554d4575394d3c47014d16e77e4d110cbe4d0f30c94cffdaa54cfda2ad4ceee3384cc8e40b4ca239e84c4841464c44c9cf4c26072f4c1a1e904bef0bf44be444374b89761b4b6ec9204b6243b84b55a0064b4e246a4b122e4e4af097fc4ada52474ad10e464a9077af4a8399004a751e2c4a2948464a15046c4a1209de4a058d7549f7512649e0e1fd49d20fd149d1a2b749a7dff349a6005e498439e74975ae8448d1f78248c9a74148c12883486e70f5483643db4833e75b4817bed94806e65b4804972b4803022547f0ab5847d1696547c7e183477b27bf
  | 9, 14 => 0x550d53ae54f176b954e5250f54dfa1d754d5f81f54ad560c5477a01d5475933e5470d65e546ddd80546aec965454be98544730175433d32e54093de153fc527753f257b453ee32a553a6f7f15379028053648c8f5364203a53499e9653182fe952bec63352be0fc652a22869529d7b4f52554e075252c00c523ad47c522e4b8951d28ad151cc176f51a7f7d651a14b01519fd2f7519e3dd7519b7e115199e39651965b8e5175e2e05174af1e514b20b050dd37d450bf5b8650ab26bc50a880ec50966e8e508996e2504803b15029bd9f5002b4614fff2c594fa2c3794f66c8974f5c67a94f466f014f10a5004ed776a44eb2aad04e70bf524e4473c14e422948
  | 9, 15 => 0x5d52d8195d15ae0a5d059e4e5cf1ee3c5cedbc0d5cadc4395ca449ff5ca2c4f55c9423795c8377cb5c724a0e5c62bfce5c5449ff5c4ceb585c1efc315c0dad8b5bfbe9e25bc2cd295bbfe44c5bb6f1df5b5a37355a876ee65a45fdfd5a36ea8259c1605b59b156f659722cdb592d37b6591d4a1c58fad71c589bf539585fd50b5809d6aa57f7274d57c91abf57c2f69957b2d3fe579a659e576bf1f757595a335757df9d56b24b5356ae6e0556a9e85056a9b9a25683f09f5681e9b55674007956570e82565662c05653867a563a7028561fa5fd561481f955f4880855f095a055d634ee55b7382755a3a50955a2bdd7559569ab554cacf1553500655513f5cf
  | 9, 16 => 0x646fbb09646a289f6458e55863c5c41763c4327063a088ea637b9e50637410346329645a631dad6a62dfc41c62cc808b62bf814a62be1c3362b6955662a12a0b629a9c526284559162552b8f6224ea65621a4e866207d52161c65ae661c3093161b5826861a740f5619cdb09618d62fe617d90ee6171c8326167341b615539c4610908b060f3f2c960eda24260ba8a6960ae5b5060aaa27760a5ef56605965dd602ad9ef601f821460109297600509df5ff69c235fafc4085fa1b76d5f6e82575f677d605f57d9905f4b19515f0800915f0508415eda76065ec469d55eb2a6185e8d69445e8a67325e8887555e79cae05e6198f05e3f65d15e35a1cd5de919b5
  | 9, 17 => 0x6d5a55a56d52e8586d3ab50f6d255f6e6d13289c6d13207b6ce67e286ce150c06c994cd66c8437596c819bff6c7166926c343a1e6c064c356c0638f16be8e3526be4204d6b7770e96b6932d56b2f17206ad2b6f46ac4e81d6aa7452e6a80b6566a485fb06a1c23c169e8cb7b695cd9be693a70786922fcaa6910e76468fc0fd168f1fce868d1faca68bcecd768a3f975689fcea167e4e82467ab0f7167a4bf37677602d967673d26675a54896727ff66671f5bf166e4d72666b7836866ad52dd6676a7fc664e785a6631177e65ec9a7965ec7ea865db212d65bb2dc865a133ae6567a702654ee4a564fd3d5464f52ab364c5ffc764c31f8c64a58897648fe230
  | 9, 18 => 0x74eaec9574d6210b74c9345b74b85bdd74ae1e74747553c2746a6597742360dc7420ffe274113d3a74047a7c73ae071a73a84de973994e7273757b087346539473098b3172f3c32172e35c4e72d8e7fe72bcc11072acd0de729e3c397272bec672536cc672116f9671f980f971e8b10d71bba82971771317715c90a97136a074711baf257115712e710946717102efa97102a40770ed7f3170cd1dda7081307470681e3670569e397014f436700b71b86fe337cf6fc2904d6f8eca996f8323e06f6541e86f5069576f3e87c36eeb96616ee9156a6ed34b9b6e83b5bd6e7547d66e6102d96e59633c6e049eed6e03ac726d8b78c26d87444a6d7398e46d5f5a2e
  | 9, 19 => 0x7e3ff94e7e3e7e3d7e38b64f7e32f14c7e2bc16e7e1575097e0d65077e0271df7dffac927dc59ad77da458547da2b49e7d306fc07d06b2f67ccdc3027cb4a1697ca4dd117c4d1fdc7c32818c7c15be4e7c0a68457b668cb67b539cb87b5045f57b2e47e97b0da9637aec26207ae654a17ae134a37ad81f287aae05c67a9404aa7a2cca0479b1a72f79a8edc4799c88c87931b8b97920e76a78ede30278b96b0778a2faf5783a4d51783612db782dd56277990da8776d83d677261d347725f1bb7723a4d37701923176516153764dc9a8763e731076222e9b76206dc975e54ba275de68f475b98a117594df817566fac47558cc987542197a750d4a0374f7c8f8
  | 9, 20 => 0x863fc21e863645ea85b3a03a85a4fa4d857d08508578b968856256c085621ed984e3e85184cceddb84b29d6884932912846220a18452196c843e09428439b7ab840debee84045d6183e65e2283e2d61a83dba36583b30f0e839e51868390e7998382b7fa8365c4568326bc4f82ee1c6282d8b8dc82d22c0b82ccbf3d82c8bffd82c09e8282b31e7682b2793c826bbb75822ad8258215e7f081faf51881bc3dc181a730c481a2c2288171607a813e231e8116a4ea80f926d880f6734580e0556380de142280d2624c80cee89b806ada3480661f75804ec9d880199293801602117f9993ed7f8a0caf7f0584b07edbb8ef7ebe54b67ea187a17e91ac397e63c578
  | 9, 21 => 0x9202a75591c13a7691a69c01916dcef291688ec5911c1fe3911befe590f0ecb690ec2a3a9065432e902e6161902d10748fb77e3a8f8201ac8f600f328f4313db8f0c558d8eedf4518eb026288e96754b8e602b998e4d58758d6865758d53a97f8cf974e28c8240cb8c43e0248bca5b098ba594948b63de308b1d18758b07a42a8b062d2f8abf8aad8a967eea8a8144258a74810b8a476a0989f2b9e089cdb34789bc7570894abd49893da793891444c38911f7d788f21d6288bd2e7f88b4dc2e88b1bf26888da6b4882c50c08811e1f6880b3e8387b06a31877f293587462e0c873125c2872a64db870f9d0d86f44b4d86bb757e86a97b8e86a8b7ec869ad759
  | 9, 22 => 0x9bc50d5f9bc3923c9ba3778c9b974c119b937dd69b2a96279af1e2049adf5e6c9ada025c9abba5f59ab95d319aa22b8e9a7db59d9a63f7bd9a4d20669a4af46c9a31046198c2563f98707380984bafd9984964a398474f849811d46f97f4ed7c97ef012697d5170797b68cd597b26e1d9791d6c19705d25196f4e19b96cb9fad96bf4a0e96b493699612f7e9960b3b3295f70a9295f54f7b95a594a09558e5b4951f99b8950d0fcc9509ea6b95015da994dc165094752ad29447aa459446dadb942364b19417f73793d432a9937796a793706830933865f49321c5bc92eadc9b92cceaa492c7a5af92b4982b929bacc692916f5d92732f7b924e8a7f9212b9cd
  | 9, 23 => 0xa7cb5963a7aac7d6a7a9a8f4a75fcd14a7548b58a74df263a74da0f9a720f87ca71ff5cda6f795aca6ab16d2a6758196a668cda4a65277bfa604485da60443f1a5f8fe37a5dcbe88a5ab7904a5939dc2a5300230a52860afa4cbb482a468bc1ea435096ca3a28c3ba3777bcea3138798a30d8e2da2ecc20fa261e128a22918c3a20508faa1a938a7a193b895a0e7f899a0d7e499a0c47845a091c078a08e6520a0887dc0a05cca61a03f28879fe069159f9a888f9f7b002b9f47e0f99f415ad39f319a389f1e6dbb9f0e20069e9a4da19e6a7eaf9e3efcf49e2919359e22c9b89dd0f61c9dc8a5129d7e367d9d3fcd009d2c23769cbbd9df9c7b5b4a9c42db12
  | 9, 24 => 0xb79ee85bb7506c7cb6f00419b6a200a6b6617d9db64f7107b614953cb5111867b5036e2fb4f3a401b49af239b4780759b450c79bb41c33cdb41aa28bb4056ec6b3e63daeb2be4841b2a54b80b2a49c40b26aec34b25d4dccb23c863cb234c2d6b230cb00b203fcefb1d47ea8b14d9880b0a3f5e5b076404db03f8402b0336347b022bfafb00700bfafd006aaaf6b077caf566b4faf301846aeb64ec6ae8c9b8dadafe126ad655295ad444435ad16d71bac65bf28ac5a28f8abc94899ab9e1877ab9c353fab272f2dab24a5c0aace97b9a9edd02ea9c377b7a9931ca1a91c0cd1a917211fa8fd30a7a8d68e2aa895c183a883a8e1a82fdc9da829bcf3a8212d88
  | 9, 25 => 0xce20a72bce10f389cd9c4529cd4cd8afcd04ae38cc9f398ccc662fb9caac12f1ca59722dca27e03bc9a36077c982e916c94f7157c791bfb8c774cf65c7332b9bc6f625b2c6c0541fc696f14fc67f9662c5c084cac54c7353c49a030dc493e8a3c45bd5c7c44d3677c3fc3351c32bb0c5c2b62aeac2ae133fc1d3799ec1939dcfc1738239c15c71a7c1289273c10bf842c100e957c07bf639bfbe2e40bfb6b84cbf81a3f0bf80e496bf34be08bf134866beec30cbbe9d7b85bddf9e5bbc6fc46bbbc4a6a1bb6f3814baea0786baaca0d0ba871711ba4beb61ba462d4cba16e278ba11e9b6b9f91d27b9b1cf92b961aaf1b93d1fceb91ae26ab7ee3c5fb7e4a957
  | 9, 26 => 0xeed80133ed5e9bb2ec9741aaebfe7101eb780c5eea02eafeea00f7f3e8a1c7a5e7e7a813e7de54a3e7d99605e76a5ddee71364f8e4cbd392e4c65225e4813e2fe3f6615ee36c6492e35a8d90e2fc19ece2e44e95e2bdb945e288f499e27ed9e9e27c83b6e26d849ee10a16b5e0fb1d46e0a1aa2de0760cc9dfa07e8cdf754d52df72a9ffdce2c3e1dc73e58fdc2f2584dc2d795bdc2a6379dbdbf7fadb69a89bdaff1149d95d3962d8a16f3fd7bc3b21d792f1a0d6c89b86d6356ea8d60560f0d5b8ff0dd510e05ad42a0999d4245c74d3fa876ed32fda18d2be23f4d27a392bd22394a5d0aec09cd07e8c0ed021015dcf7154bbcf656a36cf503013ce36e05a
  | 9, 27 => 0xfc4dce62fafbefeff955be38f9463688f8bbeb21f8bad4fff885c49af7eaf165f76a79a2f55b1a63f46cc766f3e9acd1f2311a0bf0f98e46f0421153
  | 10, 0 => 0xc4de92e0c266a3c0c13100b0b864cda0b4333af0ae548740aaf04040a70e7430a7018280a3cdacc09fc6a6f09e3a86f09b3451b09059ac308761f28086fc085086b99c7082e616e080a64f00784e25707447ff3073adc15072f7abd071b436406d7429606b2675f062ff97d0624910205e96d7b05d894fd05ce579405bbd60f0577d3dc04d8ecb604cdda9c048d7a01048a7efa0435c232040ea27303fd143b03ba503303ad423e035e4a0903214e1202fef80402f1640d02d398c30275b67902392aad0226f07c02249e550218409402105737020fc7dd020bcebe01de45d401c2adf801b024b8013a826500f59e2700d047e800b401d100312cad0030574f
  | 10, 1 => 0x18509b3d18443852183fc2bf18358556181eaabc1785a5a31718ed4917165b5e16ee55a216d2917916afe8451689827c162a46e016039e2915f7098415555b70154482f2153a4589153a38d9152cc412152816f81523c09a14bb9f0914855a99147393ed13d4e79913bf793813be6b16139ea32913899bb01368adb1135a6e0712f8dfb412c64b6d12b3c90a12a2e440129a177c127e813d121516321200862811e70352113ed4d311363b3110e1d8a310b80324108f117310780a901061c3cf103832730fc046be0f567b570eb027b90e9ba5900e61d42a0e40cb210df359650ddabd460dc9f6950dc88bdb0d7c98e10d34a09e0ce1b2210c8b84200c647c04
  | 10, 2 => 0x2678873826509fd626452c61262d646c2617d2d025abcb9d25a510a0258d08722581e43b25503c8624f9ce3e24c5142d2489320a23ba5da3239d68f3239526012308304722ae6e912294ce2e226a16fd226320d5226190d2225a2741216511af2152e94621409b7720a2292620866cf7203a6f8d202428cc1fd6ef371fd5fedb1f6d511d1f108f6e1eeb5c0f1ecc1ac61e29d7fe1dfa1a6f1d95cfcd1d5b00541d49e9221d1a7c721cd1ca161caf185d1c8a1f9f1c1ad27d1be116661bd575081bbd59e71ba3682f1b7c71191aef2c501aea70b41ad6a2771aa4d2bc1a8e59b91a5de0b31a347de31a1852391a13a51f19becf6c19a7a2491954df27191774d1
  | 10, 3 => 0x366a85a8364c9efb35c89ef63590caff34fbfbf034c8be9434808907345ca7f83433e69134201f8a33f51fff336ee79a32e6d19d328162fe3206e3493200bc2331cd7ec731154e4330ca1111308711342fab20302faac86a2fa059c42f9954342f748c5b2f5b11f42f504d892ed49e4b2da172eb2c8dfd6d2c6b54832be162932be0526f2b8486132b51363e2b33c6542b22edd62b18b06d2b16f20c2b0c646f2aecf3822a93d73a2a6f83cd2a303a9c29fa7f6129a06bd8292a0eb22917442429145cbc2913c7f128ef36e928d704f328cb3bf628b1414e2879b7d927a26f46270770e52701bd1026c5cb2426c5c5a826c0438726bb8dbb26b0ba9f2698f7ec
  | 10, 4 => 0x4675df1b45edc91e45ec93a545790e01457668314510720a44ab206d4434afdc442b78d5440f51b543b3be8f4380921543311a7542c8173542abe50f423c09e1413bcc0d41069377409e6ddf404f242a4044d3993ffb2b7a3fea52fc3fe015933fdd8c263fa8398c3f9ef58b3f7ed6bc3eb83e1b3e408c403e3c88d63e16cda13d978e863d820fa33d0f78893cd27e703c843fc93c7898493c2c192b3bdf13a93ba2b76c3b4b16da3b21b40a3aeba4d83ab42d1d3a95a4ee3a4c84283a04ed6839e8e89639e5b06939870f3b396faac93902a5d43888f35937ccc80937c67493372ab72236f05fcc36e69ca436c6932736c132ed3684256a3681db293680940a
  | 10, 5 => 0x5bcc34025b55f4d95b4c87ea5993e70c59830e8e5970b233596d0cdc591cc99658a79f37589219b5585ab50c576f115056e69d0d566f365d562c689f55a6c5a955984837549d4e4f546f9eb254463be25439accf541ef724539e41ad53059ba1529d086a50a3b698506c7de350281e7a500a5bd44fa27a904f181c774f04d1c74ee1d8074e7bbf1b4e46416b4e2ec5694de6191e4dc066ec4da876cb4d69dc7e4d1269d74ceee3384c0952e24bb433124b8e28284b4b019e4b47f9304b08576d4a2948464a28a42b4a1943a049d38ae349b30c54493c3e5b48eec71748bc19ea486c9d154832c7014803551147df270747abe9ab47a6603a475ece1f46e916e4
  | 10, 6 => 0x73a92db972ae7b9e725cc2b0719baa477172c45670e3a59370c703167093992870813074706d3a856fc4a7e86fa6066d6efc69f36e6d9f206e5d55066e5694e96e307d4b6dff9ffe6d81b03c6cf840046bb312b56aee550e6ae38ea26adb07f26aba78466944ef24687b734e680df36b67dfc825679079b56770b03b67047c11667ec8cf662fe6f665e8c6b865736f7a654fc8a16512b39e64e0b4c2645cb1de6456fccf641e509c64093c446408a0df63ee69c763b6fcaf6386e1af62df30216259600762552b8f6205bf15615acbb361296c82610dbef1601fa8b45ff8e3fd5f7123b75f0800915e6b0b6b5e4b0a985e0857bd5de2f56e5c7ba5f45c6cc02f
  | 10, 7 => 0x8d053d718d0073578c54475b8c102cdd8b85d0aa8a84c7c58a3bd1fa89a9fd95895db98d89459d4a88e9ac0988a2456788a219ee881416d78802f499878987f887625ac1875c5813872427d687211ff986897236863bb6378573996984faf7b984d0ab8b8336141e82d8b8dc82ba05ef827f17dc81502810812bf490810af2cc809a18a3800f69927fd58b6f7fcb138f7fa48a517f7fd4a57f64662f7f1355747e921aa37daf09a17d42d8747af11e827ae239d57ab698ab7a78d80879fb72f979e7a72879b339a7796110577833ab9b774cf42b76e3cf35763f47bf760c0a6375d860f47550c41475482246752f2e1b751cb11d73f0ea0873cc283773b0a5d1
  | 10, 8 => 0xa4447d76a3fcfba9a3e97feaa2e9f725a2e013b4a247fd2ca1e6560da1657107a133a66da0e79d00a0d28e00a06a1c84a03193ce9fdca7dc9fc6ddd29efa181a9ec3d5799dcb17ec9ce1680f9ca54a5d9c9940a89c12a71d9be6ffd99b1f7cf09b1c6cc09adb4fab9ac6e57c9a0e89f3998e0a2999884dbb98f3869298df89c59870738097f85d3c97e85d8397494587972fc86d96f4e19b968d0dee96771fec95f4dc9695b5dfde958f6596952f3741952dc9e1950d0fcc94a72144947947ac94686fd49448e77093f0647a933865f4930ccf1592c2ea13925c7d9691ec017e90e4651090715ed190587865903a7ce98fa7e9a18f898d3a8f7ce1ad8d73cc86
  | 10, 9 => 0xd30fc602d2d899dad27d118ad0fd0cc9cd6bf77ccd4086c4cbc81394cb6615ddcaf6230fca70b7afc9e60aa8c96a6492c8cb6d95c7482070c71e6b22c596cabec4975aefc420c473c40594b0c3802522c25c9249c100b6a7c0dae108c0cd794bc0969827bfdbce70be41968bbdd6512bbc939e60ba7958dab9dc9c06b8ca1a96b8b8c6fab8a7ee7cb8420499b7e91c60b7c5f66ab62a58ecb4c12036b2902909b203a9ffb1c6a036b13ecac5b0d64145b09bc52dafee2a50afa223aaaebf2a22adbaebb8ad4d8455ad1f9fbfac1e53c1ab379c51ab25fc6ba97115afa8e889d0a861f62ea847c7e0a82abc9ea77332c5a6d1e434a49dedefa45555f4a44cd207
  | 10, 10 => 0xfb40f08cf2515167f1aa4eeaf11bb5a7f0e9d460f0b06eb6eeaf0f1deda68baced1279a8ec302780e62539e1e5c53138e39fbcd8e306efe6e292f1a5e251da32e1fab441e1a3f7cae19d2990e16d4001e0cc5846df569a65deb9c9d0de1b61bfdcdc97a3dcb58f58dca8714fdbe14c3dda0b790fd8c448a3d7ca0131d77ece4bd6f5be16d64fce1dd5d7fdfad56427add530ea51
  | 11, 0 => 0xc7a6811fbec9ac88ba64b203b84e0c67b24eb633b076404daf47401fa36829b1a1ed870497b7de6a90e08e6281222ea075d8da116f847ff06080f9fa5e6b0b6b40d73a273e0a25a03d00ae463152270e2b947a6c2901cdd6269fe8cd244273a01f6d511d1da2926f1737fe420cec92010af82e250ac4f0c902c140aa0297ddda
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 7, 0 => 0x889d10440400984c0078c14001049d038404000689d1044040898440078414050689d104404010008110480305000c0764c13009844c0784d401000a1100413030689d104404000001a304c030098480078814053051d018c0408000000000210200205304c03000891d304c0408274413044040000000000061023051d018c0401104a1700c5401305217004d4010891d304c04010011d304c0303104a1700c5400000000000000698440078414088349d10440400984400784140100000000161079848407885405088dd20480405
  | 7, 1 => 0x2944076441401000000000000900000000000041651d304c040100022304c03000004102840305000c17004d300
  | 8, 0 => 0x2109000000001a109000000000610600022764803050004007841301000000000000200000474c020300006028413050011d304c03030009d038403010009d018c030800002744c0300000000000000b00041474403010000e164023010000000002109000000000210600000000000020011d304c03080011d164c030100000274c0203002193040230000000000061060000000000001001c1018c5300000000000000f001213000230100000304c0203000000000000d0020012481305001d1028403050000000006106
  | 8, 1 => 0x1211001a3000009d1044030500000754402030005d20480305000000000210900000304c0200000000000000a00200364193080002275440300000c0018c13000009d104403010009d104403010004003841308000c10381a300000000000000600022754c030800002574c0300000000000a109002011304d300000c4764c530800022274403050000e0081a30000022274c0308002011304d301000000000000a0009d10440305000000000000b000000000210600200134c13000000000002106000c0078c13000020016419308
  | 8, 2 => 0x40078413080005d2048030500205304c0300000d916402308000000000a1090000000002109000c1274c030000000000000060009d038403080009d104403080006136406301000000000000a0000000002109000000001a1060000000002109000000000210900041474403010000000000009000027644c3000005d170023050009d10440300000000000000a0000a0081a305000000000000a0009d10440308000411001a305000000000000e002151001a30500000304c020000121300023080009d27002305000000000000b
  | 8, 3 => 0x5d10480305000000000a10c000000001a10600000000401030000057406203000000000000a000000001a10900002018c1300001c101885305001d5164c030100000000061060009d10440301000000001a1090009d10440301002193744030800022764c03000000257440308000000000000e000e1700493050000000000004002011304d3010009d104403010000e0081a30100000574c02030000237440305000000000000500040364413080011d304c0301001213001a30100161078993050000000002109000000000000a
  | 8, 4 => 0x384020300000174c02030009d1044030800200314413010009d10440301001213001a30800201164063050004c0784d30000000174c0203000a10784130000000000021070000030440200000000001a109000000001a10900000000000090004147440308001d9018c0300000000000000300002754c0308000027644c301000227644c3000021170049305000000000000a001613001a300000d9374403080009d104403000021910002305000c1274c0300000020180a305000812001a3050009d10440303000dd01880305
  | 8, 5 => 0x1d5304403000011d304c0303000000000000a000060081a300000e11640230800000310c5203001611001a308000dd20480305000000000000a0011d304c0308000000000000a000e11001a3050000275440300000000000000a000000000e109000000000000a000000000000300000078c1200000000000000a000061640230100000100412030009d104403010009d104403000009d10440300000227644030000000000000100009d1044030000022764c030100200134c13000000e0081a30800000300c12030000000000002
  | 8, 6 => 0x1a10600022764c03080009d1044030800022374403050020031441308002013640e308000000000000a000000000210600000304c02000005d304c03000001a0180a3050000a0081a3050004c0784d3010000000006106000a107841301000000000000a000dd018803050000000002109000002744020300040764413010015d02840305000411001a3050009d1044030100000300c120300200134c1300001d9018c0301001d10384030000085210023050001a018c1300000227644c3010011d018803050020520480305
  | 8, 7 => 0x2109000a107841308002151001a3000009d104403000000000000002001d9018c030800000000061060021570085305000000000000900000000021110005d304c03010011d304c03030004c7044d3000021927041305000000000000d0009d10440300000211700230500000000000090000000002106001d1028403050002237440300000000000610600000304c02000009d10440300001d9104803050000000016107000dd104403010009d1044030100000304c0200002153001a308000000000000a0006120002305
  | 8, 8 => 0x612001a305000a1100023050009d10440301000d91640e308000000000000d00000000021060021937002308000000000000a00000000121060000000000005000000000000600022374403010000a0081a3050000000000004000000000000a000000001a109000dd104403010009d10440301000000001a10900161078d9300000000000000a000842141a305002197008530500000000000020000000002109000000000000b00219104023010001a104023050011d018803050000000006106000dd204803050000000006106
  | 8, 9 => 0x11d304c03010002237440308001217004d301000000000a10900059274c0301000e11700a305000000001a1090009d104403080000000002103000024744030100002274c03010000003802203000000001a10600161078d9301000000001a10900000038022030000000016111000227648430500040028413050005d1700230100000310022030009d104403080009c214413050021910002300000dd37002301000c13001a300001d503840308000dd0284030500000008c02030005d304c0301002011304d300000000000a109
  | 8, 10 => 0x754c0203000dd104803050009d10440303000000180e2030000057406203000c1274c0300000613040230000000000000050000000002106000a11001a3050009d104403000008007881305000590180e301000000000000a000000000000a002191000230100002038063010000027006205000c13001a3010000000000006001d9018c1300000d9078593080004007841305000dd20480305000000000000500000274c020300000000000020009d1044030800000000061060009d10440301001d9018c13080000000002109
  | 8, 11 => 0x314c4203000000001a10600200164193050001a03806301000c0764c1300000dd204803050015d038403010000e764023080004d13002301000d91640e3010000000002106002157004d308000000000000a000000000000000219100023080000003802203000c13001a3080000000000009001211001a301000a13001a301000dd2048030500000764c02030000000002106000000000a1090000000002106001217004d308000001044020500000078d9208000000001a106000dd2048030500080018813050011d304c0301
  | 8, 12 => 0x2197004d301000610700a30500061300023080011d304c030100022474403080004007841305000000000000a000000000000d0000003802203000000001a1060000e764023010000e76402308000000000610600000000000060015d10480305000a1100023000000000006102000000001a10600000174c020300200264193050011d304c0308000800188130500000000021090004002841305000000000a1090000000002106000000000000a002011341a30000041304403000006130002301000dd204803050000000000001
  | 8, 13 => 0x3806203000000000000a0011d038403080009d10440308000613001a308000000000000a000000000a10900022754403050000000000009001211700e3010000257480305000000000000a000000000a1090000000000009001d9164c0301000a11001a300000000000000b0000000000012000020180a30500000000021030011d304c030100000310c52030000610402305000613001a3010000e7640230100000104402000006136406308000a137006301000002001a205001d90384030000000000021090004c1341a301
  | 8, 14 => 0xc0018c1308001c136459301000000000a109000dd2048030500000000000090000000006106000000000000a000e17644030800000274c0203000612001a3050000000000003000000000000a0000000002109000842141a305000000001a106
  | 9, 0 => 0x18022050000000002109000000180e201000000281a20500000574402080000010402205000000381a20000000038c120100000000000060000003802200000007044d200000003640e2080000002802205000000000000300000174c020100000764842050000007859205000000001a109000000000000a00000764402050000076480205000000785920100000174022000000076440208000000700e2000000000000009000000000000100000000000090000076484205000000000a10900000070062050000031441208
  | 9, 1 => 0xe103000003640620800000078d9200000000000e103000007644c20000000038022010000000000009000000281a20500000574c0200000000281a2050000001802201000001700e208000000381a2000000001802205000007640220100000764842050000000040103000000380620000000000021030000000006103000000381a20000000754c02080000000819208000000180e203000000000000600000000c41030000001802201000000000e10300000174c0201000000000000800000018022030000007841200
  | 9, 2 => 0x27440203000000180220100000174c1201000000081a20500000000c010300000174d9208000007644020300000304c0200000000000a10900000104402000000037402208000007644020000000574802050000010002200000001640e2010000076448205000001001a201000007644020000000174c02000000003806203000000000000500000374402000000027440200000000081a208000000000000300000574c020000000574c0200000000004010100000038c1200000000081a20000000754402050000003806200
  | 9, 3 => 0xc51030000000006103000003744020000000274402000000000000009000002044120500000744c02000000000000005000000180220500000000c1103000000081a205000000381a208000000000000600000164022080000030440200000000000210300000474402080000000000003000007644d20100000078c520800000274c02080000000000006000000000a1090000070059200000000384d208000001044020500000304c0208000000081920500000274c0203000000181a200000000181a2050000037440203
  | 9, 4 => 0x3819208000003700620800000764c0201000000381a201000000788120500000754c0208000007544020500000364062010000001802205000001640a205000000000000600000164d920100000000000090000027441205000001640a205000001041a200000000000000900000070062010000000000006000000001a10600000000000090000000819205000000000000b0000047440200000001640a20500000018022030000010440205000000000000a0000000002103000000000e10300000474c02010000076484205
  | 9, 5 => 0x764c0200000000000210300000018022050000076440200000003101a2080000070484205000002141a205000000384d20000000028402050000037440208000000700a205000000081a2000000010440205000000381a20100000754c0203000001640220800000078c1208000001000220000000304c020000000018c1208000007644d201000000381a200000000380620000000078c5208000000000000700000018022000000037440200000002744020000000764c4201000007544020100000018022050000000000009
  | 9, 6 => 0x90000030402208000001700e20800000754402050000037419200000007644c2000000003802201000007644c2000000000000006000000000000900000000c01030000000000006000000380220800000000000010000036406201000000181a2000000047440208000000000000600000164022010000000000008000000181a20100000274c020800000574c0201000003748020500000754c020800000038192080000000000004000002141a2050000017419200000000181a205000000081a20500000000c0103
  | 9, 7 => 0x181a2050000000006103000000180e208000001700a2050000037480205000003748020500000474c0201000000000000f000000381920100000000000060000037440205000000700e208000000000000900000764c0200000001001a2080000001802205000003001a20100000000000000000017402200000000381a208000003744020000000274402000000010440201000000000000900000000c0101000000284120500000764842050000003802201000001640e20100000574c0201000000081a2050000000002106
  | 9, 8 => 0x1640e20100000764c42080000000000006000000000e10300000000c01030000027440205000001044020000000000021090000000002106000000000000900000674c0203000000280220500000028022050000003802201000000381a20800000764c0200000000000000c000000000000a0000000006103000000000000000000038c1200000000700e20100000000000080000000000000000000081a20500000018022010000036402208000001300220100000764402080000076402205000000700620300000018c1208
  | 9, 9 => 0x60000026441205000000180e20800000100022010000001802205000000381a208000000384120100000000000010000020480205000007644c201000000000e10300000018852050000000002109000007644120500000274c020000000310c52080000001802200000000181a2000000057480205000000381a20100000474402010000070484205000007644d200000000000000900000000000090000001802200000003740220800000000000090000020480205000003640220000000000c0108000000000a109
  | 9, 10 => 0x6000007544020100000000061030000000000003000000000e10300000018c52080000000000006000001740220500000310c5203000000381a2010000000000009000004744020800000764c0200000000180e208000007644d2010000016406205000000000e10300000174802050000047440208000001040220000000038c12010000016406201000007644020800000574c0201000000381a20800000274c02080000017480205000000000000a000000000001100000078592080000017002201000000001a106
  | 9, 11 => 0x180220800000304c020100000764802050000021002205000000181a201000000081a20000000374402010000016419201000002744020100000374802050000020480205000000000000000000124022050000000002106000001041a205000000081a200000000281a2050000076440205000003744020100000274402010000076402201000000180220800000274192050000076484205000000180a20500000754402010000037402201000007644c2010000075440205000007640220000000200022050000001881205
  | 9, 12 => 0x764c42080000021002205000000284120500000274c02010000007859200000000000000a0000001802201000001340220000000374402000000027440200000000004c103000000380220800000764c52080000001841205000000381a201000000000000a00000174c020800000574c020000000764c020800000170022050000000040103000000181a201000000000000900000764c4208000000181a205000000000000f00000164192000000000000009000000000000500000370022030000000002103000000700e201
  | 9, 13 => 0x13402200000007544020500000174c020000000000000070000000000009000000000000000000134c1208000000004010000000018c5201000001340220100000000000090000036406208000007644020000000000000090000076440203000000700e20000000018c020100000078d9208000000700e200000001641920100000078592050000003806200000000181a2010000000040108000000180220100000000000060000075440205000000081a200000001741920500000174c02030000000000009000001001a200
  | 9, 14 => 0x60000000000009000007448020500000274c020000000000000060000000000001000000784d200000000000000000000764c0201000000000000a000003640e20000000000021030000000002106000000381a2080000000000000000000081a20100000078c1200000007644c2010000001819200000007544020000000018c1200000000181a2050000076440208000000081a20000000000000050000000000006000003041a2080000003819200000000180e208000000180220100000104402000000003802208
  | 9, 15 => 0x7819201000000380220100000018022030000001802200000001001a20000000028062050000000002106000000381a201000000700e208000000380220100000000000060000000000003000000181a20500000764842050000017419205000001640220800000304c020000000000000090000000000001000003700620300000134c12080000000002109000000180220800000078d9201000000181a20500000304c0208000000000000800000474c020800000764c020100000474c0201000007544020500000474c0208
  | 9, 16 => 0x7640220100000124812050000000000008000000284120500000164d920100000310c52080000013002200000000180e201000007644c2000000074480205000000000210900000000021090000001802208000000081a2000000027440200000000381920000000018022050000000000011000000081a2050000000000009000002640a2050000000000003000001640e200000000381a201000000181a205000000184120100000008192000000002806205000000000000900000304c020800000038022080000047440205
  | 9, 17 => 0xc01000000007841205000000000000900000018022000000000000001000000000610600000304c0201000001640e2010000010402201000001640220800000018c02080000037402201000000000000500000000000090000010002208000000000a109000000180220100000364592080000000000009000000000000a00000000000090000076402200000000000000900000764c0201000000001a106000003041a20800000000000010000000000003000003041920000000018c12000000000040101000000000000b
  | 9, 18 => 0x36419201000007544020000000100022050000030402208000000381a201000000281920500000374802050000000006103000002645920500000000c1103000000000e103000000000000900000754402000000037440205000000181a201000000000000800000104402080000000002103000001301a201000000700a2050000076402201000000700e201000000000000300000164412010000037402208000007544020100000000000060000000040100000002048020500000474c020800000574802050000036402200
  | 9, 19 => 0x174192010000000041103000000180a2050000010440203000000181a200000005748020500000018c1201000005748020500000018022000000002802205000000000000d000002641920500000364062080000036402208000001044020500000174c0208000001641920100000754402050000010440203000001340220000000474402010000010440200000005744020800000104022050000000002103000002700220500000310c520800000038402010000000000006000000001a109000000001a1060000075440201
  | 9, 20 => 0x18c120000000070062080000010440208000001041a200000003700620000000164022050000000006106000000000610300000304c020300000364022010000017002200000000081a201000003744020500000134c1200000001001a201000000181a2050000000000013000000000a109000000181a2050000000080105000000000000600000370022010000021085205000000181a20000000204802050000000002103000001044020000000764402050000007841201000000181a20000000000000090000002802205
  | 9, 21 => 0x2849205000000081a20000000038022000000000000003000000000210300000704592010000000000006000000004d10300000174c0208000000784120500000028022050000000000003000000000a109000000000000a000002001a20500000304c0200000003640e20800000000401080000036402208000001044020500000018c020800000000401030000007006200000000000210900000038412000000000000003000000081a2010000020480205000000081a201000000004110300000070062010000003802208
  | 9, 22 => 0x1640620500000764402010000027440205000004744020800000000c01030000037440208000000000e103000002744020800000274c020800000174c0201000001304d20000000264022050000000000001000000000a109000000000000500000764402050000037480205000000181a20800000028492050000017002208000000180a20500000000000060000057440208000000180e20000000038c1203000004744020000000274c02000000001802200000001241a205000000001a10600000018c52080000000000009
  | 9, 23 => 0x304c0201000001341a20100000000000090000000000005000000000210300000000000030000000040105000000004010100000754c020800000764482050000003840208000007644c201000001640e200000000181a20100000574802050000000000006000000000000600000274402030000020480205000002640a205000007640220500000104022000000000041103000002101a205000007544020100000000021090000000819201000000000000b00000310c5208000000180e20300000164062050000047440205
  | 9, 24 => 0x1640620100000174c02000000000000006000000785920000000310c52030000076440203000000000000900000474c0208000000000e103000000001a1060000010402208000004744020100000274402050000037440205000000380620100000274c0201000000180220800000754402050000000000007000000000a1090000027402205000000000a10900000764022010000002802205000001341a2000000000000009000000181920800000000061030000037440200000002744020000000304c0200000000180a205
  | 9, 25 => 0x181a205000000180e20800000364022080000013402201000000381a208000000281a205000000381a2010000076440200000000000000a000000000210300000000021060000000000009000000000000a000000180e200000000000000600000764c0208000000381a20100000304c020000000304c020000000174c020800000000c510300000000000000000000000009000000180e2000000070085205000000380220100000134c1201000000181a20800000104402080000027402205000000184120500000304c0200
  | 9, 26 => 0x20402205000001001a208000000181a2010000037440205000000000000b000000000000b00000000c010300000744802050000000000005000000000000600000764c02000000010440205000001741920100000038402080000016406201000000000000b00000304c020800000274c02030000070085205000001301a20000000164c520100000078c5208000000384120300000574c020000000018022050000001802205000000001a10900000164192080000037402208000007544020100000764402080000000000006
  | 9, 27 => 0x1641920100000304c020100000104402050000076440201000000000000600000754402000000021085205000000000000900000000c510300000104022050000003806201000000700e20000000374402050000001802201000000280620500000018c12010000017402205000000081a205000000008010500000764402010000003819208000001304d20100000164062010000001841201000000000610300000038022000000017402203000003744120800000474c020300000000c010000000274c0200000001041a201
  | 9, 28 => 0x7648420500000310c5203000000281a205000000281920500000304c0201000000000000900000374402050000000000009000000000000900000764c1200000000000000300000000000060000010402208000000180e201000000181a200000000281a20500000574c0200000000081920500000000000080000076402205000003744020800000274402080000003840200000001041a205000000000e10300000304c02010000000000009000007044c201000001001a20500000038c1200000007644c2010000010002203
  | 9, 29 => 0x900000018c0200000000001a109000001748020500000000401030000001841205000001700e201000000000000b0000010440200000004744020000000028192050000021085205000000180e20300000764c420100000000000090000017002205000000000000b000000381a20800000764402050000003802201000000180220500000274c02010000027402205000000180a20500000000000090000057480205000000380220000000038c1208000001700220100000310c520800000104022050000017002200
  | 9, 30 => 0x74480205000000280620500000274c020000000134c120000000274c02000000002806205000004744020500000078592010000037006201000001640220000000764402000000017002205000001640e20800000038402000000000000009000000000000a000003744020800000364192000000027440208000000281a205000000380620000000000c010000000018022000000047440200000000000000a0000000000005000001700e2000000076440205000000000000900000364192080000000000005000000180a205
  | 9, 31 => 0xa00000164062000000000000003000007648020500000174c0200000007644020500000700c5208000000000000300000764c4208000000280220500000174c020100000000021030000002840205000000700e200000000180a2050000000000006000000000610300000304c020000000474402000000017480205000001041a20000000000000010000000040103000000081a2000000021085205000000000000900000204022050000047440200000003744020500000764c0208000000000000b0000003802200
  | 9, 32 => 0x2144120500000474402010000000000005000000000210900000304c0200000002700620500000274c0201000003741920100000374402000000030402200000002700220500000310c520800000304022000000037419200000001041a20800000000000080000031402208000000000000a0000000000009000000004c1030000000002109000000380220300000764402010000017481205000004744020800000310c520000000764842050000017402205000001741920800000274c0208000000180e2010000037402200
  | 9, 33 => 0x181920500000038412000000000000006000007044c201000001341a2010000010002205000000384120100000574c02010000076440200000000000a109000000000000900000474c0201000000000000900000764802050000000000000000000001a10600000038062000000003806200000001700a2050000000000005000000700e2080000076440200000007544020500000474c02010000075440205000000180a20500000274402080000076402208000004744020000000000000090000076402205000000000000a
  | 9, 34 => 0x47440203000001740220500000744c020000000274c0203000000000000600000038022000000000000009000000000000a000004744020800000174c0208000000180e20800000274c020800000764402080000017002208000000180220500000310c5208000000000001100000174d920100000000c510300000174c020000000000000090000012049205000000784120800000474402050000001802208000000180e20800000000000060000003802201000000181a205000000180220800000174d92080000001802200
  | 9, 35 => 0x9000000000610600000000c51030000001802200000007544020500000310c5203000000380620100000310c520800000000021030000037440208000000380620000000674c0203000007005920500000274c0200000007644020100000078592080000021085205000000180e201000000384d2000000000000009000000000000100000764c520800000018412000000021085205000000000000900000304c020800000000000060000000000006000000081a20800000764c0200000000180e2080000007819208
  | 9, 36 => 0x2841205000001640620100000000000090000001802205000004744020000000174c0201000000784120100000764842050000037419208000000380220300000018c020300000078c5200000007644020500000304c0201000000081a20800000764402010000000000000000000381a200000007644c201000001304d200000001041a20500000574c0200000000000000600000000000060000037419200000003040220000000700d92010000000002103000001041a208000000000000b00000174c02010000001885205
  | 9, 37 => 0x2108520500000744802050000020480205000002048020500000304c020100000174c02030000036419200000000000000b0000000000006000000700620100000000c01010000070099205000000700a205000007644c201000000380620300000174802050000000000008000007044c20100000764022050000000000009000000000e10300000000000030000074480205000001640e20800000000000010000007859201000000380620800000104402050000007841200000002640620500000000021060000000002103
  | 9, 38 => 0x50000000040103000000180e2080000000000009000000281a205000000000000a000002744020100000764c0200000000000000c00000164d92010000027440205000001000220100000304c020100000018022010000016402201000000180220500000574c020000000310c5201000000000000600000174c020000000000000060000000002103000002041a205000000288120500000764c4200000007644020800000210852050000000000009000000000a109000001748020500000314022030000037002200
  | 9, 39 => 0x184120500000754402000000010440201000001700e208000001340220100000000021030000001802200000001044020500000744c02000000002806205000000384d201000002744020500000764c42000000010440201000003041a2000000036459208000003041a20000000174802050000027441205000003141a2080000002840205000001304d2000000016441205000001304d200000003744020300000000411030000000000003000001304d2000000000002109000000081a20800000000000060000000002103
  | 9, 40 => 0x37441200000000000000600000174c020000000374402000000000000003000000181a2080000002806205000000000210600000174c020000000000c4103000000181a208000000181a200000000000000a0000037440200000003640e20100000000021030000000000003000000000210900000474c020800000018022030000075440205000001001a20500000000000060000020480205000000000000600000078192000000001819208000000000000d00000364022000000001802200000007644020000000174c0201
  | 9, 41 => 0x4110300000018022010000021002205000001640620800000174c02080000003802203000000001a109000000700a205000000000000300000764022010000000000003000000381a200000000000a10900000304c0208000000000e1030000031002208000003700620000000164c12010000037440208000002744020800000574c02010000031002203000000000000600000000021090000000000000000000181a205000000000000a000007644c200000000008010500000574c0201000000180220000000174c0200
  | 9, 42 => 0xb0000002841205000000081a205000000700620500000000000060000037402208000003744020100000000000090000027440205000000000210900000304c020800000304c020100000764c020100000304c020300000274402010000000002103000002700620500000104402050000003819201000000380220300000164d920100000164062080000047440201000000000000a00000274c0201000000000000300000364402080000000002109000000000e103000007045920100000574c02000000076480205
  | 9, 43 => 0x380620100000274402050000037419208000000081a20500000078592080000075440201000000384d20100000274402030000036406208000000000000a0000000002103000000081a2050000030402208000000000000a000000000000600000764c0200000000000000a0000010402208000003700620800000574402030000002849205000000000000a000000000000d00000304c02010000003841208000000081a205000000781920500000134c120000000174c020100000764c02000000001802200000003041a200
  | 9, 44 => 0x3840200000000000000000000214412050000070059205000000180220500000134c1208000000000610300000174c02080000000000006000001700220500000214412050000000000009000001001a2010000037419208000002744020500000474c0208000000000000a00000574c0201000000181a205000001044020000000174802050000000000006000003000220000000764c020100000374402000000000819201000007648020500000764402050000076440201000007644c20000000000000090000000000006
  | 9, 45 => 0x764c02000000000000008000000081a20000000274c020100000754c0203000007004d20100000000061060000027440201000001341a201000000181a20000000764802050000001802200000000000000d00000700d9208000003740220000000078412080000000000003000000000000a0000000000009000000000000d000000000000a00000374022010000000000006000000000210300000474c02030000001802201000000000210300000018022010000000000006000000000000a000000281a2050000001802201
  | 9, 46 => 0xa000000081a20500000018c5200000003101a20800000018c52010000000000003000001640e2080000000000009000000000000a0000036459208000000000000b000007644c201000000001a106000000181a200000003744020000000000000010000037440200000000000000900000000000090000000000003000000001a10600000000000030000000000003000002744020000000764402010000000000006000000788520500000764802050000000000006000000381920800000754402000000027440205
  | 9, 47 => 0x181a20000000174c0208000001700220100000000000090000000041103000000000210900000364022080000076440208000000000000b000007644020100000000000060000000000009000000180e20100000574c020000000104022050000057440208000000001a1090000000006106000000384d20800000038062010000016406208000000000000a000007544020000000104402030000000000004000000001a1090000017402201000007644020500000000061060000010440208000002101a2050000000000006
  | 9, 48 => 0x3744020300000000c4103000003001a20000000174c0208000000000610300000174c120000000764c020800000078192050000010440205000000000000a0000002802205000000000000a000003041a208000000280220500000374022000000027440201000001041a20800000018412010000016406208000001304d20100000000021030000037402201000000000000600000104402010000000000003000000081a20500000304c020800000174022080000000000003000000380220800000764c02000000027440201
  | 9, 49 => 0x764c0208000000181a200000004744020100000274c02010000000000006000000180a20500000000c510300000000411030000076402208000001740220100000764c1208000007640220800000754402000000000000009000000081a201000000000000700000574402030000037480205000000181a205000000081a205000002704120500000764402000000000000001000007648520500000174c0201000000081a205000002744020800000574402080000000000006000000000000300000018022050000027441205
  | 9, 50 => 0x3806201000000081a20100000000000030000047440205000001640220500000764c02080000021085205000000184120800000078c1200000000380220100000310c5201000000384d2030000000000006000000000000a0000036419200000000000000a00000274402050000001841200000000000000a0000027440200000000000e1030000001802200000001248120500000174c1200000000000000800000000000090000016419208000000081a205000001248120500000000c010300000028022050000000000006
  | 9, 51 => 0x27006205000002048020500000000000090000001819205000000000000a0000000002103000000000000a000000000000600000704d920000000700d92010000002881205000000000000a0000001802208000000000000d00000764c42080000000000003000000000000600000174c020800000174c0201000007640220800000000000060000000002103000000000e10300000274c020000000038022080000000000008000000001a1090000000000006000000000a109000007005920100000000021060000000819208
  | 9, 52 => 0x4744020500000018c12000000000000001000000381a2010000013002201000000081a208000000700e2010000000000009000000000000a000000000000a00000000000090000027440208000000000210300000000000030000001881205000003748020500000078c1200000000000000300000764c020800000104402000000075440200000000000000100000764c4208000000081a201000003000220800000018022080000000002103000000081a2080000000000005000000180e200000000380220100000474c0201
  | 9, 53 => 0x210900000364192010000001802205000000381a201000000000a10900000000000060000016499205000000000000b000000081a201000001640a205000000000000a000007044c200000003041a200000003744020100000204802050000016402201000000081a20100000000000060000000000002000000081a2010000000000006000000781920100000304c020800000000c41030000076484205000000000000a000000381a20800000070062010000057440203000002640220500000300022010000000000006
  | 9, 54 => 0x81a20100000000c4103000000000000a0000000002109000000000000b000000000000a0000000002106000000700a20500000274c0203000003000220100000000000000000000040103000000380220100000304022030000001802205
  | 10, 0 => 0x4110500000000191080000000000003000000004010100000000d9101000000000610000000000c110300000000411000000000006101000000000e1010000000019100000000008510500000000061050000000041105000000004d101000000000000300000000c4108000000004010800000000411030000000085105000000008110500000000c410100000000000060000000002100000000000e10100000000c1108000000000e10000000000411050000000002105000000000000900000000d9108000000000e101
  | 10, 1 => 0xc510000000000021010000000041101000000000000b00000000c010000000000191010000000019105000000000000300000000c4108000000004c1000000000041105000000000e1080000000019101000000000210500000000c010100000000000090000000006105000000000e10300000000401010000000085105000000000000800000000021010000000000000000000000000600000000c0101000000000e108000000009910500000000c11000000000059105000000005910500000000591010000000002105
  | 10, 2 => 0x4110500000000021000000000019105000000004d1010000000002100000000000a10500000000d91080000000080105000000000000300000000401010000000059105000000000000600000000191050000000041101000000004110000000000411000000000002103000000000e101000000004110000000000d91080000000000006000000000e1080000000040108000000001a1080000000002100000000001a10100000000c5108000000001a1000000000006100000000000e10100000000401030000000084105
  | 10, 3 => 0x6105000000008510500000000061050000000006101000000001a1050000000002100000000004010000000000c110000000000411080000000000003000000008410500000000d9100000000001a1080000000002101000000001a100000000000a105000000000a105000000000e1010000000019105000000000210000000000c11080000000002103000000000610100000000061050000000000003000000004d101000000001910000000000000080000000049105000000000610100000000061030000000002100
  | 10, 4 => 0x500000000061050000000081105000000005910000000000491050000000000000000000000610000000000061050000000006101000000004c1010000000041101000000004d10000000000061050000000019100000000001910500000000191010000000006103000000008510500000000c11080000000002101000000000210000000000c510300000000c5108000000000610500000000591080000000059101000000000210000000000c11080000000019105000000008510500000000411010000000019105
  | 10, 5 => 0xc010800000000021030000000000006000000000610000000000c4103000000000610100000000d910800000000d9108000000000000100000000c1100000000004c10100000000c5101000000005910500000000c410000000000061050000000006105000000004110800000000851050000000059108000000001a105000000000000600000000591000000000000008000000000210300000000411030000000019105000000000a10500000000591010000000019100000000001910000000000411080000000002100
  | 10, 6 => 0x4110000000000021010000000000009000000004010500000000401050000000040101000000000610500000000c410000000000c01000000000000009000000000210000000000851050000000006100000000000e101000000004d10000000000191010000000000006000000004d100000000000610000000000c0103000000000e10100000000d910000000000c4100000000000210100000000000090000000000006000000000a10500000000c1108000000000000a000000000e10100000000191080000000002101
  | 10, 7 => 0x610100000000000000000000019101000000004d1010000000006108000000000610000000000191080000000006101000000001a1000000000000006000000000a105000000008410500000000841050000000041101000000004d101000000000e108000000000e1000000000000003000000004c10000000000061080000000049105000000000000600000000c51080000000019108000000001a10000000000021000000000099105000000005910500000000801050000000002101000000000210100000000d9108
  | 10, 8 => 0x4c101000000004c1000000000000009000000001a100000000004c101000000000000500000000591000000000019100000000000e108000000000e101000000000610300000000191010000000000006000000000e101000000004d103000000000000800000000c5108000000000a1050000000006108000000000210500000000c51080000000000003000000000000600000000d910800000000061050000000000003000000001a1000000000040101000000008110500000000000090000000040105
  | 10, 9 => 0xa1050000000000006000000000000a0000000006100000000000a105000000000000d000000000e101000000004110500000000401080000000000003000000008010500000000000050000000059100000000008110500000000d91010000000000003000000000610500000000d91000000000059100000000004c10000000000c01080000000041105000000004110500000000411010000000059108000000004010800000000061010000000040101000000004d101000000000a105000000000000300000000c1101
  | 10, 10 => 0x8110500000000d91010000000006100000000004010800000000c11010000000099105000000000e103000000000000900000000591050000000002103000000001a100000000000000300000000c0108000000000e1000000000041105000000000a10500000000000060000000000008000000000210000000000401050000000000009000000001a1010000000059100000000000000800000000d9101000000001a101000000000210300000000401080000000040100000000000610100000000061050000000099105
  | 10, 11 => 0x9000000000610000000000801050000000006105000000000610500000000d91080000000081105000000000210800000000d9108000000004d101000000000e100000000000000600000000811050000000081105000000000e101000000005910100000000061000000000059101000000004110800000000411010000000000006000000004010500000000191000000000006100000000000e100000000000610300000000c01000000000041100000000000e100000000001910100000000c11010000000002100
  | 10, 12 => 0x30000000006105000000004010000000000811050000000099105000000000e1010000000006105000000000210800000000c1100000000000e100000000000e101000000001910100000000000090000000000005000000004010300000000c010100000000000080000000000009000000000000500000000411030000000040100000000000000900000000c1100000000004c10000000000021080000000000006000000001a10500000000d9101000000000210800000000c4103000000000000a0000000000005
  | 10, 13 => 0x5910800000000c0101000000004010500000000c1100000000000000000000000c510800000000c11010000000000009000000000000900000000d9101000000000e108000000000210800000000c410800000000c1101000000001910500000000991050000000002100000000000a105000000008510500000000c5101000000001a100000000008110500000000c110800000000061000000000002108000000000210000000000401000000000006101000000000e100000000008010500000000061000000000006101
  | 10, 14 => 0xc4108000000000210500000000c11000000000059100000000005910800000000000030000000002105000000001910100000000d910800000000d91010000000041100000000004010100000000c0103000000001a108000000000210500000000c110100000000401010000000080105000000000e10000000000061050000000085105000000000000800000000061080000000006100000000009910500000000c410800000000c110300000000191080000000040105000000000000900000000c110800000000d9100
  | 10, 15 => 0x191000000000002108000000001a108000000000000300000000021000000000006100000000008010500000000000010000000000006000000000000900000000061010000000000001000000000610500000000c0100000000004d101000000000e10000000000d910800000000c11010000000041105000000005910800000000000030000000002105000000000e103000000000210500000000c01010000000000006000000000000600000000801050000000006105000000000210500000000d9101000000001a108
  | 10, 16 => 0x90000000002101000000000000900000000591000000000084105000000000e103000000000e108000000000000500000000c510000000000c410800000000c0101000000000000300000000c4108000000000000900000000c410300000000000090000000000006000000000610000000000811050000000000006000000000210100000000191000000000000003000000000210800000000591050000000002100000000008410500000000d910000000000000010000000006100000000000000600000000c0108
  | 10, 17 => 0x99105000000000210100000000d9100000000001a10500000000c41080000000019100000000000210500000000c410000000000c1108000000000610800000000021000000000041108000000000000b00000000061080000000002105000000000210300000000c01010000000002105000000000e10800000000401030000000006100000000001a1050000000002100000000000000900000000401000000000002105000000000000900000000021030000000000003000000000610800000000401080000000002105
  | 10, 18 => 0x8010500000000801050000000000009000000000a10500000000841050000000002101000000005910500000000811050000000040105000000004c1000000000002101000000000000600000000c110800000000c41030000000099105000000008410500000000411080000000002100000000001a1000000000006100000000004d10000000000061080000000000003000000000210100000000021000000000006101000000000e1080000000006105000000000210500000000c010000000000991050000000000009
  | 10, 19 => 0x19108000000001a1010000000000005000000000e10100000000061080000000099105000000000610000000000591050000000041105000000000e10800000000c1100000000000a10500000000c51030000000002101000000004c101000000001a101000000000000a000000001a1050000000080105000000001a105000000000210100000000d9108000000005910500000000d9100000000000e1030000000000003000000004c10000000000000050000000040100000000001a10500000000c41010000000000009
  | 10, 20 => 0x40105000000000e101000000001a108000000000000300000000021010000000040105000000005910800000000c010800000000000030000000019108000000000610500000000000030000000080105000000001a108000000000e101000000000e101000000000a10500000000d9100000000000000300000000591080000000002101000000000000300000000c1100000000004010500000000000010000000002101000000000e10300000000c1100000000000a105000000000e10800000000c010800000000c0100
  | 10, 21 => 0x8510500000000191050000000006101000000000210100000000c5103
  | 11, 0 => 0x10000000000000000000000000100000000000050000000000000000000000000300000000000050000000000008000000000000000000000000050000000000005000000000000800000000000080000000000008000000000000000000000000030000000000000000000000000100000000000010000000000000000000000000000000000000000000000000003000000000000000000000000050000000000001000000000000500000000000050000000000008000000000000000000000000080000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_239 roots_239 11 s ws hint
  | 1 => checkCutEntry dom_223 roots_223 11 s ws hint
  | 2 => checkCutEntry dom_249 roots_249 8 s ws hint
  | 3 => checkCutEntry dom_127 roots_127 10 s ws hint
  | 4 => checkCutEntry dom_238 roots_238 7 s ws hint
  | 5 => checkCutEntry dom_251 roots_251 11 s ws hint
  | 6 => checkCutEntry dom_247 roots_247 9 s ws hint
  | 7 => checkCutEntry dom_231 roots_231 8 s ws hint
  | 8 => checkCutEntry dom_191 roots_191 11 s ws hint
  | 9 => checkCutEntry dom_253 roots_253 9 s ws hint
  | 10 => checkCutEntry dom_254 roots_254 8 s ws hint
  | 11 => checkCutEntry dom_93 roots_93 6 s ws hint
  | 12 => checkCutEntry dom_221 roots_221 8 s ws hint
  | 13 => checkCutEntry dom_55 roots_55 6 s ws hint
  | 14 => checkCutEntry dom_250 roots_250 7 s ws hint
  | 15 => checkCutEntry dom_215 roots_215 7 s ws hint
  | 16 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 17 => checkCutEntry dom_183 roots_183 8 s ws hint
  | 18 => checkCutEntry dom_189 roots_189 7 s ws hint
  | 19 => checkCutEntry dom_29 roots_29 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_239 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_223 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_249 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_127 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_238 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_251 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_247 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_231 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_191 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_253 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_254 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_93 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_221 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_250 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_215 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_183 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_189 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_255 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 16 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := (range_split z7_0 z7_16)
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
private theorem z8_112 : ∀ i, 112 ≤ i → i < 125 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 13 112 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 125 → Z 8 i = true := (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112)))
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
private theorem z9_240 : ∀ i, 240 ≤ i → i < 246 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 240 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 246 → Z 9 i = true := (range_split (range_split (range_split (range_split z9_0 z9_16) (range_split z9_32 z9_48)) (range_split (range_split z9_64 z9_80) (range_split z9_96 z9_112))) (range_split (range_split (range_split z9_128 z9_144) (range_split z9_160 z9_176)) (range_split (range_split z9_192 z9_208) (range_split z9_224 z9_240))))
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
private theorem z10 : ∀ i, 0 ≤ i → i < 96 → Z 10 i = true := (range_split (range_split z10_0 (range_split z10_16 z10_32)) (range_split z10_48 (range_split z10_64 z10_80)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11 : ∀ i, 0 ≤ i → i < 11 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 11 0 = true)
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

abbrev fMain : (Fin 8 → Bool) → Bool := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 7) || (x 6 && x 7)
theorem hTMain : ∀ r : Fin 256, goal_255.testBit r.val = fMain (pt8 r.val) := by decide +kernel
theorem mainThm : ∀ t : ℕ, HasCircuitSize 8 fMain t → 13 ≤ t := lower_to_circuit fMain goal_255 13 hTMain low_255
end PEqualNP.Outside.L_meta_10658_aux.Base_aux

theorem PEqualNP.Outside.L_meta_10658_aux.Base : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 13 ≤ t := PEqualNP.Outside.L_meta_10658_aux.Base_aux.mainThm


namespace PEqualNP.Outside.L_meta_10658_aux
open PEqualNP.MetaComplexity

def extended (x : Fin 9 → Bool) : Bool := (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8) || (x 7 && x 8)

theorem inherited (s : ℕ) (h : HasCircuitSize 9 extended s) : 14 ≤ s := by
  have dep : ∃ x : Fin 9 → Bool,
      extended (Function.update x 4 (!x 4)) ≠ extended x :=
    ⟨fun i => decide (i = 8), by decide +kernel⟩
  have nc : ∃ x y : Fin 9 → Bool,
      extended (Function.update x 4 false) ≠ extended (Function.update y 4 false) :=
    ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 5), by decide +kernel⟩
  obtain ⟨t, saved, pin⟩ := Deletion.one_gate_at 8 extended 4 false s dep nc h
  let labels : Fin 9 → Fin 8 := ![5, 6, 2, 4, 0, 7, 1, 3, 0]
  have smaller := Deletion.relabel_size labels _ t pin
  have eq : (fun x : Fin 8 → Bool => extended (Function.update (x ∘ labels) 4 false)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 7) || (x 6 && x 7)) := by
    funext x
    simp [extended, labels, Function.update, Function.comp_def]
    ac_rfl
  rw [eq] at smaller
  have := Base t smaller
  omega

end PEqualNP.Outside.L_meta_10658_aux

theorem PEqualNP.Outside.L_meta_10658 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 14 ≤ t :=
  PEqualNP.Outside.L_meta_10658_aux.inherited
