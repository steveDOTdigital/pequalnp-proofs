import PEqualNP.Defs.Represents

-- Search soundness adapted from Nico Habets and Lewis Watson, as credited in Mask53Exact.lean.
-- Original source: https://github.com/open-goat/pequalnp-proofs/blob/62a08312807b6a9ea0e9f8319897c74bf63e8be2/lean/PEqualNP/Outside/L_meta_5601.lean
-- For the two-lit graph 820 the support argument, separation certificates, input tables and theorem are new.
namespace TwoLit820

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 21
private def ins : List T := [63, 1986, 30852, 233736, 860688, 1721376]
private def target : T := 436
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 21) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin 21) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List T) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List T} {x : T} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List T} {x y : T} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], atom hy⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], atom (.inr hx)⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table (w ws : List T) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i), by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i), by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

private def safe : ℕ → List T → Prop
  | 0, ws => ws.contains target = false
  | n + 1, ws => ∀ z, possible ws z → safe n (z :: ws)

private theorem absent {n : ℕ} {ws : List T} (h : safe n ws) : target ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w ws : List T) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe m ws)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k target) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target ≠ 0) hz
    · exact absent hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices (ws : List T) : List T :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff (ws : List T) (z : T) : z ∈ choices ws ↔ possible ws z := by
  simp [choices, possible, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit of
-- the target can serve as the other input to an AND. OR has the dual test.
private def lastTwo (ws : List T) : Bool :=
  let above := ws.filter (fun x => (x &&& target) == target)
  let below := ws.filter (fun x => (x ||| target) == target)
  (choices ws).all fun z => !(z == target ||
    above.any (fun x => (x &&& z) == target) ||
    below.any (fun x => (x ||| z) == target))

private theorem lastTwo_safe {ws : List T} (h : lastTwo ws) : safe 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff ws z).2 hz
  have ht (u : T) (hu : u ∈ choices ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T) (hu : u ∈ choices ws) : u ≠ target ∧
      (∀ x ∈ ws, x &&& u ≠ target) ∧ (∀ x ∈ ws, x ||| u ≠ target) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨h1,h3⟩,h4⟩ := H
    refine ⟨h1,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T) (hx : x ∈ ws) := hnot x ((choice_iff ws x).2 (atom (.inr hx)))
  have unary (x : T) (hx : x ∈ z :: ws) : x ≠ target := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact H.1
    · exact (base x hx).1
  have binary (x y : T) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target ∧ x ||| y ≠ target := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.1 y hym) (H.2.2 y hym)
    · simpa [hye] using And.intro (H.2.1 x hxm) (H.2.2 x hxm)
    · exact ⟨(base y hym).2.1 x hxm, (base y hym).2.2 x hxm⟩
  have hv' : v ≠ target := by
    simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, (h | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact unary x hx
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target = false
  suffices target ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact unary target hm rfl

private def masked (ws : List T) (mask want : T) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo (ws : List T) : Bool :=
  !(masked ws (-1) target ||
    ws.any fun x =>
      ((x &&& target) == target && masked ws x target) ||
      ((x ||| target) == target && masked ws (~~~x) (target &&& ~~~x)))

private theorem masked_of_possible {ws : List T} {u : T} (hu : possible ws u) (m : T) :
    masked ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, (h | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl rfl)⟩
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last {ws : List T} (hf : fastTwo ws) : lastTwo ws := by
  simp [fastTwo] at hf
  obtain ⟨hn, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff _ _).1 hz
  simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible hz' (-1)
    rw [show z &&& (-1 : T) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' (~~~x)
    have he' : z &&& ~~~x = target &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

private def search : ℕ → List T → Bool
  | 0, ws => fastTwo ws
  | n+1, ws => (choices ws).all (fun z => search n (z :: ws))

private theorem search_safe {n : ℕ} {ws : List T} (h : search n ws) : safe (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe (fast_implies_last h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff _ _).2 hz))

private def sep (x : T) (pq : Fin 21 × Fin 21) : Prop :=
  bit pq.1 x = true ∧ bit pq.2 x = false

private def covers (s : Finset T) : Prop :=
  ∀ pq, sep target pq → ∃ x ∈ s, sep x pq

private def feasible (w : List T) (b : ℕ) : Prop :=
  ∃ s : Finset T, (∀ x ∈ s, x ∈ w) ∧ s.card ≤ b ∧ covers s

-- A decrease across one monotone gate is witnessed by one of its operands.
private theorem factors {w : List T} {z : T} (h : possible w z) :
    ∃ a : Finset T, (∀ x ∈ a, x ∈ w) ∧ a.card ≤ 2 ∧
      ∀ pq, sep z pq → ∃ x ∈ a, sep x pq := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with ((h | h) | ⟨x, hx, (h | ⟨y, hy, h | h⟩)⟩) <;> subst z
  · refine ⟨∅, by simp, by simp, ?_⟩
    simp [sep, bit]
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro pq hs
    have ha : ∀ i : Fin 21, bit i (-1) = true := by decide +kernel
    exact False.elim (by have h := hs.2; rw [ha] at h; contradiction)
  · exact ⟨{x}, by simpa using hx, by simp, fun pq hs => ⟨x, by simp, hs⟩⟩
  · refine ⟨{x,y}, by simpa using And.intro hx hy, by simpa using (Finset.card_insert_le x ({y} : Finset T)), ?_⟩
    intro pq h
    simp only [sep, bit, BitVec.getElem_and] at h ⊢
    cases h1 : x[pq.1.val] <;> cases h2 : y[pq.1.val] <;>
      cases h3 : x[pq.2.val] <;> cases h4 : y[pq.2.val] <;> simp_all
  · refine ⟨{x,y}, by simpa using And.intro hx hy, by simpa using (Finset.card_insert_le x ({y} : Finset T)), ?_⟩
    intro pq h
    simp only [sep, bit, BitVec.getElem_or] at h ⊢
    cases h1 : x[pq.1.val] <;> cases h2 : y[pq.1.val] <;>
      cases h3 : x[pq.2.val] <;> cases h4 : y[pq.2.val] <;> simp_all

private theorem pull {z : T} {w : List T} {b : ℕ} (hz : possible w z)
    (hf : feasible (z :: w) b) : feasible w (b + 1) := by
  obtain ⟨s, sub, lim, cov⟩ := hf
  by_cases hs : z ∈ s
  · obtain ⟨a, ha, ca, fac⟩ := factors hz
    refine ⟨s.erase z ∪ a, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (List.mem_cons.mp (sub x (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
      · exact ha x hx
    · have hu := Finset.card_union_le (s.erase z) a
      rw [Finset.card_erase_of_mem hs] at hu
      have hp := Finset.card_pos.mpr ⟨z,hs⟩
      omega
    · intro pq hpq
      obtain ⟨x,hx,hsep⟩ := cov pq hpq
      by_cases e : x = z
      · subst x
        obtain ⟨y,hy,hy'⟩ := fac pq hsep
        exact ⟨y,Finset.mem_union_right _ hy,hy'⟩
      · exact ⟨x,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hx⟩),hsep⟩
  · refine ⟨s, ?_, by omega, cov⟩
    intro x hx
    exact (List.mem_cons.mp (sub x hx)).resolve_left (fun e => hs (e ▸ hx))

private theorem infeasible_safe (n : ℕ) (w : List T) (h : ¬ feasible w (n+1)) : safe n w := by
  induction n generalizing w with
  | zero =>
    change w.contains target = false
    suffices hn : target ∉ w by simpa using hn
    intro ht
    exact h ⟨{target}, by simpa using ht, by simp, fun pq hp => ⟨target,by simp,hp⟩⟩
  | succ n ih =>
    intro z hz
    exact ih (z::w) (fun hf => h (pull hz hf))

private instance decidableSep (x : T) (pq : Fin 21 × Fin 21) : Decidable (sep x pq) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- More pairwise incompatible decreases than available inputs rule out the cone.
private theorem packing {b : ℕ} {w : List T} (p : Fin (b+1) → Fin 21 × Fin 21)
    (hpos : ∀ i, sep target (p i))
    (huniq : w.all (fun x => decide (∀ i j, sep x (p i) → sep x (p j) → i = j)) = true) :
    ¬ feasible w b := by
  rintro ⟨s, hsub, hcard, hcov⟩
  classical
  have H (i : Fin (b+1)) : ∃ x : s, sep x.val (p i) := by
    obtain ⟨x,hx,hs⟩ := hcov _ (hpos i)
    exact ⟨⟨x,hx⟩,hs⟩
  let f (i : Fin (b+1)) : s := (H i).choose
  have prop (i) : sep (f i).val (p i) := (H i).choose_spec
  have inj : Function.Injective f := by
    intro i j e
    have hi := prop i
    rw [e] at hi
    exact of_decide_eq_true ((List.all_eq_true.mp huniq) (f j).val (hsub _ (f j).property)) i j hi (prop j)
  have hc := Fintype.card_le_of_injective f inj
  simp at hc
  omega

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private def cut0Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (5, 0), (7, 11), (8, 1)]
private theorem cut0 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut0Pairs i) → sep x (cut0Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut0Pairs (by decide +kernel) h)

private def cut1Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (4, 0), (4, 9), (5, 0), (8, 1), (8, 3)]
private theorem cut1 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut1Pairs i) → sep x (cut1Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut1Pairs (by decide +kernel) h)

private def cut2Pairs : Fin 6 → Fin 21 × Fin 21 := ![(4, 0), (4, 9), (5, 0), (7, 1), (7, 11), (8, 1)]
private theorem cut2 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut2Pairs i) → sep x (cut2Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut2Pairs (by decide +kernel) h)

private def cut3Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 12), (4, 0), (5, 0), (7, 11), (8, 1)]
private theorem cut3 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut3Pairs i) → sep x (cut3Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut3Pairs (by decide +kernel) h)

private def cut4Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 13), (4, 0), (5, 0), (7, 11), (8, 1)]
private theorem cut4 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut4Pairs i) → sep x (cut4Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut4Pairs (by decide +kernel) h)

private def cut5Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 14), (4, 0), (5, 0), (7, 11), (8, 1)]
private theorem cut5 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut5Pairs i) → sep x (cut5Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut5Pairs (by decide +kernel) h)

private def cut6Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (5, 0), (8, 1), (8, 3)]
private theorem cut6 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut6Pairs i) → sep x (cut6Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut6Pairs (by decide +kernel) h)

private def cut7Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 1), (2, 11), (4, 0), (5, 0), (7, 11), (8, 1)]
private theorem cut7 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut7Pairs i) → sep x (cut7Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut7Pairs (by decide +kernel) h)

private def cut8Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (5, 0), (7, 12), (8, 1)]
private theorem cut8 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut8Pairs i) → sep x (cut8Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut8Pairs (by decide +kernel) h)

private def cut9Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 1), (5, 0), (7, 13), (8, 1)]
private theorem cut9 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut9Pairs i) → sep x (cut9Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut9Pairs (by decide +kernel) h)

private def cut10Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (5, 1), (7, 14), (8, 1)]
private theorem cut10 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut10Pairs i) → sep x (cut10Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut10Pairs (by decide +kernel) h)

private def cut11Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 3), (2, 11), (4, 0), (5, 0), (7, 11), (8, 1)]
private theorem cut11 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut11Pairs i) → sep x (cut11Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut11Pairs (by decide +kernel) h)

private def cut12Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 11), (4, 0), (5, 0), (7, 9), (7, 11), (8, 1)]
private theorem cut12 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut12Pairs i) → sep x (cut12Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut12Pairs (by decide +kernel) h)

private def cut13Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 11), (4, 0), (5, 0), (7, 10), (7, 11), (8, 1)]
private theorem cut13 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut13Pairs i) → sep x (cut13Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut13Pairs (by decide +kernel) h)

private def cut14Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 3), (5, 0), (7, 11), (8, 9)]
private theorem cut14 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut14Pairs i) → sep x (cut14Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut14Pairs (by decide +kernel) h)

private def cut15Pairs : Fin 6 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (5, 3), (7, 11), (8, 10)]
private theorem cut15 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut15Pairs i) → sep x (cut15Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut15Pairs (by decide +kernel) h)

private def cut16Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (7, 11), (8, 1)]
private theorem cut16 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut16Pairs i) → sep x (cut16Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut16Pairs (by decide +kernel) h)

private def cut17Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 13), (4, 0), (7, 11), (8, 1)]
private theorem cut17 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut17Pairs i) → sep x (cut17Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut17Pairs (by decide +kernel) h)

private def cut18Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 1), (7, 13), (8, 1)]
private theorem cut18 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut18Pairs i) → sep x (cut18Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut18Pairs (by decide +kernel) h)

private def cut19Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 11), (4, 0), (7, 9), (7, 11), (8, 1)]
private theorem cut19 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut19Pairs i) → sep x (cut19Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut19Pairs (by decide +kernel) h)

private def cut20Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 3), (7, 11), (8, 9)]
private theorem cut20 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut20Pairs i) → sep x (cut20Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut20Pairs (by decide +kernel) h)

private def cut21Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (5, 0), (7, 11), (8, 1)]
private theorem cut21 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut21Pairs i) → sep x (cut21Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut21Pairs (by decide +kernel) h)

private def cut22Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (4, 0), (4, 9), (8, 1), (8, 3)]
private theorem cut22 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut22Pairs i) → sep x (cut22Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut22Pairs (by decide +kernel) h)

private def cut23Pairs : Fin 5 → Fin 21 × Fin 21 := ![(4, 0), (4, 9), (7, 1), (7, 11), (8, 1)]
private theorem cut23 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut23Pairs i) → sep x (cut23Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut23Pairs (by decide +kernel) h)

private def cut24Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 12), (4, 0), (7, 11), (8, 1)]
private theorem cut24 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut24Pairs i) → sep x (cut24Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut24Pairs (by decide +kernel) h)

private def cut25Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 14), (4, 0), (7, 11), (8, 1)]
private theorem cut25 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut25Pairs i) → sep x (cut25Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut25Pairs (by decide +kernel) h)

private def cut26Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (8, 1), (8, 3)]
private theorem cut26 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut26Pairs i) → sep x (cut26Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut26Pairs (by decide +kernel) h)

private def cut27Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 1), (2, 11), (4, 0), (7, 11), (8, 1)]
private theorem cut27 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut27Pairs i) → sep x (cut27Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut27Pairs (by decide +kernel) h)

private def cut28Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (7, 12), (8, 1)]
private theorem cut28 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut28Pairs i) → sep x (cut28Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut28Pairs (by decide +kernel) h)

private def cut29Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (7, 14), (8, 1)]
private theorem cut29 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut29Pairs i) → sep x (cut29Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut29Pairs (by decide +kernel) h)

private def cut30Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 3), (2, 11), (4, 0), (7, 11), (8, 1)]
private theorem cut30 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut30Pairs i) → sep x (cut30Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut30Pairs (by decide +kernel) h)

private def cut31Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 11), (5, 0), (7, 9), (7, 11), (8, 1)]
private theorem cut31 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut31Pairs i) → sep x (cut31Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut31Pairs (by decide +kernel) h)

private def cut32Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 11), (4, 0), (7, 10), (7, 11), (8, 1)]
private theorem cut32 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut32Pairs i) → sep x (cut32Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut32Pairs (by decide +kernel) h)

private def cut33Pairs : Fin 5 → Fin 21 × Fin 21 := ![(2, 0), (2, 11), (4, 0), (7, 11), (8, 10)]
private theorem cut33 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut33Pairs i) → sep x (cut33Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut33Pairs (by decide +kernel) h)

private theorem branch0 : safe 4 [2057776, 63, 1986, 30852, 233736, 860688, 1721376] := by
  intro z hz
  have h := (choice_iff _ _).2 hz
  rw [show choices [2057776, 63, 1986, 30852, 233736, 860688, 1721376] = [0, 2097151, 2057776, 48, 2057791, 1536, 2058226, 24576, 2064052, 196608, 2094904, 860688, 1721376, 63, 2, 2047, 4, 30911, 8, 233791, 16, 860735, 32, 1721407, 1986, 128, 32710, 256, 235466, 512, 862162, 1024, 1722338, 30852, 4096, 260492, 8192, 883348, 16384, 1735844, 233736, 65536, 1028888, 131072, 1824040, 524288] by decide +kernel] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cut16 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut17 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut18 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut19 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut20 (by decide +kernel)
  · exact cut21 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut22 (by decide +kernel)
  · exact cut23 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut24 (by decide +kernel)
  · exact cut21 (by decide +kernel)
  · exact cut17 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut26 (by decide +kernel)
  · exact cut27 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut28 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut18 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut29 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut30 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut31 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut32 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut20 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut33 (by decide +kernel)
  · exact cut16 (by decide +kernel)

private theorem branch1 : safe 5 [63, 1986, 30852, 233736, 860688, 1721376] := by
  intro z hz
  have h := (choice_iff _ _).2 hz
  rw [show choices [63, 1986, 30852, 233736, 860688, 1721376] = [0, 2097151, 63, 2, 2047, 4, 30911, 8, 233791, 16, 860735, 32, 1721407, 1986, 128, 32710, 256, 235466, 512, 862162, 1024, 1722338, 30852, 4096, 260492, 8192, 883348, 16384, 1735844, 233736, 65536, 1028888, 131072, 1824040, 860688, 524288, 2057776, 1721376] by decide +kernel] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut1 (by decide +kernel)
  · exact cut2 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut3 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut4 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut5 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut6 (by decide +kernel)
  · exact cut7 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut8 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut10 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut11 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut12 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut13 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut14 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut15 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact branch0
  · exact cut0 (by decide +kernel)

private def samples : Fin 21 → Fin 6 × Fin 6 := ![(0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (1,1), (1,2), (1,3), (1,4), (1,5), (2,2), (2,3), (2,4), (2,5), (3,3), (3,4), (3,5), (4,4), (4,5), (5,5)]
private def inputs (i : Fin 21) :=
  List.ofFn fun k : Fin 6 => decide (k = (samples i).1 ∨ k = (samples i).2)

private theorem tables (C : Circuit)
    (he : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (820 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :
    ∀ k, (C.gates.foldl step (ins.map (bit k))).getD C.output false = bit k target := by
  intro k
  have hi : ∀ i : Fin 21, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 21, (820 : Nat).testBit
      (6 * min (samples i).1.val (samples i).2.val + max (samples i).1.val (samples i).2.val) = bit i target := by decide +kernel
  have h := he (samples k).1 (samples k).2
  change C.eval (inputs k) = _ at h
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using h

theorem monotoneLower : ¬ (∃ C : Circuit, Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (820 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hg,hs,he⟩
  exact exclude _ _ (fun g hm => hg g hm) ins ins (fun ⦃_⦄ h => h) 5 hs branch1 (tables C he)

def construction : Circuit :=
  {gates := [⟨.or,[2,3]⟩, ⟨.and,[1,6]⟩, ⟨.or,[2,4]⟩,
             ⟨.or,[8,5]⟩, ⟨.and,[0,9]⟩, ⟨.or,[10,7]⟩], output := 11 }

theorem catalogue21901 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (820 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨construction, ?_, ?_, ?_⟩
  · intro g hg
    simp only [construction, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms monotoneLower
#print axioms catalogue21901
-- Six accepted/rejected comparisons, each differing on just one input wire.
private def comparisons : Fin 6 → Fin 21 × Fin 21 := ![(11,2), (11,7), (0,2), (6,8), (0,4), (0,5)]
private def changes (z : T) : Finset (Fin 6) :=
  Finset.univ.filter fun i => bit (comparisons i).1 z ≠ bit (comparisons i).2 z

private def mass (w : List T) (t : ℕ) : Prop :=
  ∀ s : Finset T, (∀ x ∈ s, x ∈ w) → (s.biUnion changes).card ≤ t + s.card

-- Replacing a selected wire by at most k+1 gate operands costs at most k.
private theorem massStep {w : List T} {z : T} {t k : ℕ} (h : mass w t)
    (a : Finset T) (ha : ∀ x ∈ a, x ∈ w) (hc : a.card ≤ k+1)
    (hd : changes z ⊆ a.biUnion changes) : mass (w ++ [z]) (t+k) := by
  intro s sub
  by_cases hs : z ∈ s
  · let old := s.erase z ∪ a
    have hold : ∀ x ∈ old, x ∈ w := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · have hh := sub x (Finset.mem_of_mem_erase hx)
        simpa [List.mem_append, Finset.ne_of_mem_erase hx] using hh
      · exact ha x hx
    have hsub : s.biUnion changes ⊆ old.biUnion changes := by
      intro i hi
      obtain ⟨x,hx,hi⟩ := Finset.mem_biUnion.mp hi
      by_cases e : x = z
      · subst x
        obtain ⟨y,hy,hi⟩ := Finset.mem_biUnion.mp (hd hi)
        exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_union_right _ hy,hi⟩
      · exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hx⟩),hi⟩
    have h1 := Finset.card_le_card hsub
    have h2 := h old hold
    have h3 : old.card ≤ (s.card-1) + a.card := by
      simpa [old, Finset.card_erase_of_mem hs] using Finset.card_union_le (s.erase z) a
    have hp := Finset.card_pos.mpr ⟨z,hs⟩
    omega
  · have hold : ∀ x ∈ s, x ∈ w := by
      intro x hx
      have hn : x ≠ z := fun e => hs (e ▸ hx)
      simpa [List.mem_append,hn] using sub x hx
    have := h s hold
    omega

private theorem memChanges {i : Fin 6} {x : T} : i ∈ changes x ↔ bit (comparisons i).1 x ≠ bit (comparisons i).2 x := by simp [changes]

private theorem constChanges : changes (0:T) = ∅ ∧ changes (-1:T) = ∅ := by decide +kernel

private theorem monotoneMass {w : List T} {t : ℕ} (h : mass w t) {z : T}
    (hz : possible w z) : mass (w ++ [z]) (t+1) := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((e | e) | ⟨x,hx,(e | ⟨y,hy,e | e⟩)⟩) <;> subst z
  · exact massStep h (z := (0:T)) ∅ (by simp) (by simp) (by rw [constChanges.1]; simp)
  · exact massStep h (z := (-1:T)) ∅ (by simp) (by simp) (by rw [constChanges.2]; simp)
  · exact massStep h {x} (by simpa using hx) (by simp) (by simp)
  · apply massStep h {x,y} (by simpa using And.intro hx hy) (by simpa using (Finset.card_insert_le x ({y} : Finset T)))
    intro i hi
    simp only [memChanges, bit, BitVec.getElem_and] at hi
    simp only [Finset.biUnion_insert,Finset.singleton_biUnion,Finset.mem_union,memChanges,bit]
    by_contra! bad
    simp_all
  · apply massStep h {x,y} (by simpa using And.intro hx hy) (by simpa using (Finset.card_insert_le x ({y} : Finset T)))
    intro i hi
    simp only [memChanges, bit, BitVec.getElem_or] at hi
    simp only [Finset.biUnion_insert,Finset.singleton_biUnion,Finset.mem_union,memChanges,bit]
    by_contra! bad
    simp_all

private theorem negMass {w : List T} {t : ℕ} (h : mass w t) {x : T} (hx : x ∈ w) :
    mass (w ++ [~~~x]) t := by
  apply massStep (k := 0) h {x} (by simpa using hx) (by simp)
  intro i hi
  rw [Finset.singleton_biUnion]
  apply memChanges.mpr
  intro e
  apply (memChanges.mp hi)
  simp only [bit,BitVec.getElem_not] at *
  rw [e]

private def binaryCost (g : Gate) := match g.op with | .not => 0 | _ => 1
private theorem binaryCost_of_ne {g : Gate} (h : g.op ≠ .not) : binaryCost g = 1 := by
  cases e : g.op <;> simp_all [binaryCost]
private theorem binaryCost_of_eq {g : Gate} (h : g.op = .not) : binaryCost g = 0 := by simp [binaryCost,h]
private def cost (gs : List Gate) := (gs.map binaryCost).sum

private theorem lowerCost (gs : List Gate) (o : ℕ)
    (ok : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List T) (t : ℕ) (h : mass w t)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD o false = bit k target) :
    (changes target).card ≤ t + cost gs + 1 := by
  induction gs generalizing w t with
  | nil =>
    have e : w.getD o 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil,read_bit,bit] using he ⟨i,hi⟩
    have hv := read_wire w o
    rw [e] at hv
    rcases hv with hz | hm
    · exact False.elim ((by decide : target ≠ 0) hz)
    · have hh := h {target} (by simpa using hm)
      simpa [cost] using hh
  | cons g gs ih =>
    have hg := ok g List.mem_cons_self
    have hh (z : T) (hs : ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k))
        (hm : mass (w ++ [z]) (t + binaryCost g)) : (changes target).card ≤ t + cost (g::gs) + 1 := by
      have H := ih (fun g' h' => ok g' (List.mem_cons_of_mem _ h')) (w++[z]) (t+binaryCost g) hm
        (fun k => by simpa only [List.foldl_cons,hs] using he k)
      simpa [cost,Nat.add_assoc] using H
    by_cases hn : g.op = .not
    · obtain ⟨op,args⟩ := g
      change op = .not at hn
      subst op
      cases args with
      | nil =>
        apply hh (-1)
        · intro k; simp [step,GateOp.eval,bit]; revert k; decide +kernel
        · simpa [binaryCost] using (massStep (k:=0) h (z := (-1:T)) ∅ (by simp) (by simp) (by rw [constChanges.2]; simp) : mass (w ++ [-1]) (t+0))
      | cons j rest =>
        apply hh (~~~(w.getD j 0))
        · intro k; simp only [step,List.map_cons,List.map_nil,read_bit,List.map_append]; simp [GateOp.eval,bit]
        · rcases read_wire w j with e | hm
          · rw [e]
            simpa [binaryCost] using (massStep (k:=0) h (z := (-1:T)) ∅ (by simp) (by simp) (by rw [constChanges.2]; simp) : mass (w ++ [-1]) (t+0))
          · simpa [binaryCost] using negMass h hm
    · have hl : legal g := by
        obtain ⟨ho,ha⟩ := hg
        change g.op = .and ∨ g.op = .or ∨ g.op = .not at ho
        exact ⟨ho.elim Or.inl (fun ho' => Or.inr (ho'.resolve_right hn)),ha⟩
      obtain ⟨z,hz,hs⟩ := gate_table w w (fun ⦃_⦄ h' => h') g hl
      apply hh z hs
      simpa [binaryCost_of_ne hn] using monotoneMass h hz

private theorem cost_le (gs : List Gate) : cost gs ≤ gs.length := by
  induction gs with
  | nil => simp [cost]
  | cons g gs ih =>
    by_cases h : g.op = .not
    · simp [cost,binaryCost_of_eq h] at *; omega
    · simp [cost,binaryCost_of_ne h] at *; omega

private theorem cost_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = .not) : cost gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    by_cases hn : g.op = .not
    · have hle := cost_le gs
      simpa [cost,binaryCost_of_eq hn] using Nat.lt_succ_of_le hle
    · have ht : ∃ f ∈ gs, f.op = .not := by
        obtain ⟨f,hf,hnf⟩ := h
        rcases List.mem_cons.mp hf with rfl | hf
        · contradiction
        · exact ⟨f,hf,hnf⟩
      have hh := ih ht
      simp [cost,binaryCost_of_ne hn] at *
      omega

private theorem startMass : mass ins 0 := by
  intro s sub
  have hraw : ins.all (fun v => decide ((changes v).card ≤ 1)) = true := by decide +kernel
  have hh (x) (hx : x ∈ s) : (changes x).card ≤ 1 := of_decide_eq_true ((List.all_eq_true.mp hraw) x (sub x hx))
  exact le_trans Finset.card_biUnion_le (by simpa using Finset.sum_le_sum hh)

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (820 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hfan,hs,he⟩
  classical
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hcost := lowerCost C.gates C.output hfan ins 0 startMass (tables C he)
    have hc : (changes target).card = 6 := by decide +kernel
    rw [hc] at hcost
    have hl := cost_lt C.gates hn
    change C.gates.length ≤ 5 at hs
    omega
  · have hm : Monotone2 C := by
      intro g hg
      obtain ⟨ho,ha⟩ := hfan g hg
      change g.op = .and ∨ g.op = .or ∨ g.op = .not at ho
      exact ⟨ho.elim Or.inl (fun h => Or.inr (h.resolve_right (fun e => hn ⟨g,hg,e⟩))),ha⟩
    exact monotoneLower ⟨C,hm,hs,he⟩

#print axioms generalLower
end TwoLit820
