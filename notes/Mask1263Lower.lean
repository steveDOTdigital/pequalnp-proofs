import PEqualNP.Defs.Represents

-- Search soundness adapted from Nico Habets and Lewis Watson, as credited in Mask53Exact.lean.
-- Original source: https://github.com/open-goat/pequalnp-proofs/blob/62a08312807b6a9ea0e9f8319897c74bf63e8be2/lean/PEqualNP/Outside/L_meta_5601.lean
-- For graph 1263 the support argument, separation certificates, input tables and theorem are new.
namespace Mask1263

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 15
private def ins : List T := [31, 992, 31744, 1057, 2114, 4228, 8456, 16912]
private def target : T := 1263
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 15) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin 15) :
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

private def sep (x : T) (pq : Fin 15 × Fin 15) : Prop :=
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
    have ha : ∀ i : Fin 15, bit i (-1) = true := by decide +kernel
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

private instance decidableSep (x : T) (pq : Fin 15 × Fin 15) : Decidable (sep x pq) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- More pairwise incompatible decreases than available inputs rule out the cone.
private theorem packing {b : ℕ} {w : List T} (p : Fin (b+1) → Fin 15 × Fin 15)
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

private def cut0Pairs : Fin 6 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (2, 4), (3, 4), (6, 11)]
private theorem cut0 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut0Pairs i) → sep x (cut0Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut0Pairs (by decide +kernel) h)

private def cut1Pairs : Fin 6 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (2, 4), (3, 4), (3, 8), (6, 11)]
private theorem cut1 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut1Pairs i) → sep x (cut1Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut1Pairs (by decide +kernel) h)

private def cut2Pairs : Fin 6 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (2, 4), (3, 4), (5, 8), (6, 11)]
private theorem cut2 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut2Pairs i) → sep x (cut2Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut2Pairs (by decide +kernel) h)

private def cut3Pairs : Fin 6 → Fin 15 × Fin 15 := ![(0, 4), (2, 4), (2, 12), (3, 4), (6, 8), (6, 11)]
private theorem cut3 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut3Pairs i) → sep x (cut3Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut3Pairs (by decide +kernel) h)

private def cut4Pairs : Fin 6 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (3, 4), (6, 11), (7, 8)]
private theorem cut4 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut4Pairs i) → sep x (cut4Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut4Pairs (by decide +kernel) h)

private def cut5Pairs : Fin 6 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (2, 4), (2, 12), (3, 4), (6, 11)]
private theorem cut5 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut5Pairs i) → sep x (cut5Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut5Pairs (by decide +kernel) h)

private def cut6Pairs : Fin 6 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (2, 4), (3, 4), (7, 12)]
private theorem cut6 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut6Pairs i) → sep x (cut6Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut6Pairs (by decide +kernel) h)

private def cut7Pairs : Fin 6 → Fin 15 × Fin 15 := ![(0, 4), (1, 11), (2, 4), (3, 4), (6, 8), (6, 11)]
private theorem cut7 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut7Pairs i) → sep x (cut7Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut7Pairs (by decide +kernel) h)

private def cut8Pairs : Fin 6 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (3, 4), (7, 8), (7, 12)]
private theorem cut8 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut8Pairs i) → sep x (cut8Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut8Pairs (by decide +kernel) h)

private def cut9Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (2, 4), (3, 4)]
private theorem cut9 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut9Pairs i) → sep x (cut9Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut9Pairs (by decide +kernel) h)

private def cut10Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (2, 4), (6, 11)]
private theorem cut10 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut10Pairs i) → sep x (cut10Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut10Pairs (by decide +kernel) h)

private def cut11Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (2, 4), (3, 4), (3, 8)]
private theorem cut11 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut11Pairs i) → sep x (cut11Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut11Pairs (by decide +kernel) h)

private def cut12Pairs : Fin 5 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (2, 4), (3, 4), (5, 8)]
private theorem cut12 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut12Pairs i) → sep x (cut12Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut12Pairs (by decide +kernel) h)

private def cut13Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 11), (2, 4), (6, 8), (6, 11)]
private theorem cut13 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut13Pairs i) → sep x (cut13Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut13Pairs (by decide +kernel) h)

private def cut14Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (7, 8), (7, 12)]
private theorem cut14 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut14Pairs i) → sep x (cut14Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut14Pairs (by decide +kernel) h)

private def cut15Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (2, 4), (2, 12), (3, 4), (6, 8)]
private theorem cut15 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut15Pairs i) → sep x (cut15Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut15Pairs (by decide +kernel) h)

private def cut16Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (3, 4), (7, 8)]
private theorem cut16 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut16Pairs i) → sep x (cut16Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut16Pairs (by decide +kernel) h)

private def cut17Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (2, 4), (2, 12), (3, 4)]
private theorem cut17 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut17Pairs i) → sep x (cut17Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut17Pairs (by decide +kernel) h)

private def cut18Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 11), (2, 4), (3, 4), (6, 8)]
private theorem cut18 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut18Pairs i) → sep x (cut18Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut18Pairs (by decide +kernel) h)

private def cut19Pairs : Fin 5 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (2, 4), (3, 4), (10, 11)]
private theorem cut19 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut19Pairs i) → sep x (cut19Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut19Pairs (by decide +kernel) h)

private def cut20Pairs : Fin 5 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (2, 4), (3, 4), (10, 12)]
private theorem cut20 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut20Pairs i) → sep x (cut20Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut20Pairs (by decide +kernel) h)

private def cut21Pairs : Fin 5 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (2, 4), (5, 8), (6, 11)]
private theorem cut21 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut21Pairs i) → sep x (cut21Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut21Pairs (by decide +kernel) h)

private theorem branch0 : safe 3 [6342, 9192, 31, 992, 31744, 1057, 2114, 4228, 8456, 16912] := by
  intro z hz
  have h := (choice_iff _ _).2 hz
  rw [show choices [6342, 9192, 31, 992, 31744, 1057, 2114, 4228, 8456, 16912] = [0, 32767, 6342, 192, 15342, 6, 6367, 7142, 6144, 31942, 7399, 2114, 4228, 14798, 23254, 9192, 8, 9215, 992, 8192, 32744, 32, 10217, 64, 11242, 128, 13292, 8456, 512, 25592, 31, 1023, 31775, 1, 1087, 2, 2143, 4, 4255, 8479, 16, 16927, 32736, 2017, 3042, 5092, 256, 17392, 31744, 1024, 31777, 2048, 31810, 4096, 31876, 32008, 16384, 32272, 1057, 3171, 5285, 9513, 17969, 10570, 19026, 12684, 21140, 25368, 16912] by decide +kernel] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))

private def cut22Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (6, 11), (7, 8)]
private theorem cut22 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut22Pairs i) → sep x (cut22Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut22Pairs (by decide +kernel) h)

private theorem branch1 : safe 4 [9192, 31, 992, 31744, 1057, 2114, 4228, 8456, 16912] := by
  intro z hz
  have h := (choice_iff _ _).2 hz
  rw [show choices [9192, 31, 992, 31744, 1057, 2114, 4228, 8456, 16912] = [0, 32767, 9192, 8, 9215, 992, 8192, 32744, 32, 10217, 64, 11242, 128, 13292, 8456, 512, 25592, 31, 1023, 31775, 1, 1087, 2, 2143, 4, 4255, 8479, 16, 16927, 32736, 2017, 3042, 5092, 256, 17392, 31744, 1024, 31777, 2048, 31810, 4096, 31876, 32008, 16384, 32272, 1057, 3171, 5285, 9513, 17969, 2114, 6342, 10570, 19026, 4228, 12684, 21140, 25368, 16912] by decide +kernel] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut10 (by decide +kernel)
  · exact cut11 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut10 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut12 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut13 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut14 (by decide +kernel)
  · exact cut10 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut11 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut12 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut15 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut17 (by decide +kernel)
  · exact cut11 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut12 (by decide +kernel)
  · exact cut18 (by decide +kernel)
  · exact cut16 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut19 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut10 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut19 (by decide +kernel)
  · exact cut20 (by decide +kernel)
  · exact cut21 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact branch0
  · exact cut13 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut22 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)
  · exact cut9 (by decide +kernel)

private def cut23Pairs : Fin 6 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (2, 4), (3, 4), (6, 11), (10, 11)]
private theorem cut23 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut23Pairs i) → sep x (cut23Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut23Pairs (by decide +kernel) h)

private def cut24Pairs : Fin 6 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (2, 4), (3, 4), (6, 11), (10, 12)]
private theorem cut24 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut24Pairs i) → sep x (cut24Pairs j) → i = j)) = true) : safe 4 w :=
  infeasible_safe _ _ (packing cut24Pairs (by decide +kernel) h)

private def cut25Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (3, 4), (6, 11)]
private theorem cut25 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut25Pairs i) → sep x (cut25Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut25Pairs (by decide +kernel) h)

private def cut26Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (3, 4), (3, 8), (6, 8), (6, 11)]
private theorem cut26 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut26Pairs i) → sep x (cut26Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut26Pairs (by decide +kernel) h)

private def cut27Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 11), (3, 4), (6, 8), (6, 11)]
private theorem cut27 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut27Pairs i) → sep x (cut27Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut27Pairs (by decide +kernel) h)

private def cut28Pairs : Fin 5 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (3, 4), (6, 11), (10, 11)]
private theorem cut28 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut28Pairs i) → sep x (cut28Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut28Pairs (by decide +kernel) h)

private def cut29Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 11), (2, 4), (3, 4), (6, 11)]
private theorem cut29 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut29Pairs i) → sep x (cut29Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut29Pairs (by decide +kernel) h)

private def cut30Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (3, 4), (3, 8), (6, 11)]
private theorem cut30 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut30Pairs i) → sep x (cut30Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut30Pairs (by decide +kernel) h)

private def cut31Pairs : Fin 5 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (3, 4), (5, 8), (6, 11)]
private theorem cut31 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut31Pairs i) → sep x (cut31Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut31Pairs (by decide +kernel) h)

private def cut32Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (2, 4), (2, 12), (3, 4), (6, 11)]
private theorem cut32 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut32Pairs i) → sep x (cut32Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut32Pairs (by decide +kernel) h)

private def cut33Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (2, 12), (3, 4), (6, 11)]
private theorem cut33 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut33Pairs i) → sep x (cut33Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut33Pairs (by decide +kernel) h)

private def cut34Pairs : Fin 5 → Fin 15 × Fin 15 := ![(0, 4), (1, 4), (1, 11), (3, 4), (7, 12)]
private theorem cut34 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut34Pairs i) → sep x (cut34Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut34Pairs (by decide +kernel) h)

private theorem branch2 : safe 3 [9192, 6342, 31, 992, 31744, 1057, 2114, 4228, 8456, 16912] := by
  intro z hz
  have h := (choice_iff _ _).2 hz
  rw [show choices [9192, 6342, 31, 992, 31744, 1057, 2114, 4228, 8456, 16912] = [0, 32767, 9192, 192, 15342, 8, 9215, 992, 8192, 32744, 32, 10217, 64, 11242, 128, 13292, 8456, 512, 25592, 6342, 6, 6367, 7142, 6144, 31942, 7399, 2114, 4228, 14798, 23254, 31, 1023, 31775, 1, 1087, 2, 2143, 4, 4255, 8479, 16, 16927, 32736, 2017, 3042, 5092, 256, 17392, 31744, 1024, 31777, 2048, 31810, 4096, 31876, 32008, 16384, 32272, 1057, 3171, 5285, 9513, 17969, 10570, 19026, 12684, 21140, 25368, 16912] by decide +kernel] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))
  · exact lastTwo_safe (fast_implies_last (by decide +kernel))

private def cut35Pairs : Fin 5 → Fin 15 × Fin 15 := ![(1, 11), (2, 4), (3, 4), (6, 11), (10, 11)]
private theorem cut35 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut35Pairs i) → sep x (cut35Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut35Pairs (by decide +kernel) h)

private def cut36Pairs : Fin 5 → Fin 15 × Fin 15 := ![(1, 4), (1, 11), (3, 4), (6, 11), (10, 12)]
private theorem cut36 {w : List T} (h : w.all (fun x => decide (∀ i j, sep x (cut36Pairs i) → sep x (cut36Pairs j) → i = j)) = true) : safe 3 w :=
  infeasible_safe _ _ (packing cut36Pairs (by decide +kernel) h)

private theorem branch3 : safe 4 [6342, 31, 992, 31744, 1057, 2114, 4228, 8456, 16912] := by
  intro z hz
  have h := (choice_iff _ _).2 hz
  rw [show choices [6342, 31, 992, 31744, 1057, 2114, 4228, 8456, 16912] = [0, 32767, 6342, 6, 6367, 192, 7142, 6144, 31942, 7399, 2114, 4228, 14798, 23254, 31, 1023, 31775, 1, 1087, 2, 2143, 4, 4255, 8, 8479, 16, 16927, 992, 32736, 32, 2017, 64, 3042, 128, 5092, 256, 9192, 512, 17392, 31744, 1024, 31777, 2048, 31810, 4096, 31876, 8192, 32008, 16384, 32272, 1057, 3171, 5285, 9513, 17969, 10570, 19026, 12684, 21140, 8456, 25368, 16912] by decide +kernel] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut26 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut27 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut28 (by decide +kernel)
  · exact cut29 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut27 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut30 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut31 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut32 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut33 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut30 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut31 (by decide +kernel)
  · exact cut34 (by decide +kernel)
  · exact cut29 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut34 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact branch2
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut28 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut29 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut35 (by decide +kernel)
  · exact cut36 (by decide +kernel)
  · exact cut31 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut29 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)
  · exact cut25 (by decide +kernel)

private theorem branch4 : safe 5 [31, 992, 31744, 1057, 2114, 4228, 8456, 16912] := by
  intro z hz
  have h := (choice_iff _ _).2 hz
  rw [show choices [31, 992, 31744, 1057, 2114, 4228, 8456, 16912] = [0, 32767, 31, 1023, 31775, 1, 1087, 2, 2143, 4, 4255, 8, 8479, 16, 16927, 992, 32736, 32, 2017, 64, 3042, 128, 5092, 256, 9192, 512, 17392, 31744, 1024, 31777, 2048, 31810, 4096, 31876, 8192, 32008, 16384, 32272, 1057, 3171, 5285, 9513, 17969, 2114, 6342, 10570, 19026, 4228, 12684, 21140, 8456, 25368, 16912] by decide +kernel] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut1 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut2 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut3 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut4 (by decide +kernel)
  · exact cut5 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut1 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut2 (by decide +kernel)
  · exact cut6 (by decide +kernel)
  · exact cut7 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut8 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact branch1
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut23 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut23 (by decide +kernel)
  · exact cut24 (by decide +kernel)
  · exact cut2 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact branch3
  · exact cut7 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut4 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)
  · exact cut0 (by decide +kernel)

def graph (u : Fin 3) (v : Fin 5) := (1263 : Nat).testBit (5 * u.val + v.val)
def row (i : Fin 15) : Fin 3 := ⟨i.val / 5, by have := i.isLt; omega⟩
def col (i : Fin 15) : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
def inputs (i : Fin 15) := PEqualNP.Represents.oneEach (row i) (col i)

theorem exactLower : ¬ PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 3) (v : Fin 5) => (1263 : ℕ).testBit (5 * u.val + v.val)) 5 := by
  rintro ⟨C, hg, hsize, he⟩
  apply exclude C.gates C.output (fun g hm => hg g hm) ins ins (fun ⦃_⦄ h => h) 5 hsize branch4
  intro k
  have hi : ∀ i : Fin 15, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 15, graph (row i) (col i) = bit i target := by decide +kernel
  have heval : C.eval (inputs k) = graph (row k) (col k) := he (row k) (col k)
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using heval

#print axioms exactLower
end Mask1263
