import PEqualNP.Defs.Represents

-- The gate semantics and safety induction adapt the Apache-2.0 proof credited in Mask53Exact.lean.
-- Lewis Watson and Nico Habets developed the earlier gate enumeration.
-- The fifteen inputs and support certificates below apply to graph 266311.
namespace Graph266311

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 15
private def ins : List T := [31, 482, 3652, 13448, 26896]
private def target : T := 4647
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => (z == u || z == ~~~u) ||
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

private def fullLegal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem tableFull (w ws : List T) (hw : w ⊆ ws) (g : Gate) (hg : fullLegal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  by_cases hn : g.op = .not
  · obtain ⟨op,args⟩ := g
    change op = .not at hn
    subst op
    cases args with
    | nil =>
      exact ⟨-1, by simp [possible], by intro k; simp [step,GateOp.eval,bit]; revert k; decide +kernel⟩
    | cons i rest =>
      refine ⟨~~~(w.getD i 0), ?_, ?_⟩
      · rcases read_wire w i with h | h
        · rw [h]; simp [possible]
        · simp only [possible,Bool.or_eq_true,List.any_eq_true,beq_iff_eq]
          exact .inr ⟨_,hw h,.inl (.inr rfl)⟩
      · intro k
        simp only [step,List.map_cons,List.map_nil,read_bit,List.map_append]
        simp [GateOp.eval,bit]
  · apply gate_table w ws hw g
    obtain ⟨ho,ha⟩ := hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at ho
    exact ⟨ho.elim Or.inl (fun h => Or.inr (h.resolve_right hn)),ha⟩

private def safe : ℕ → List T → Prop
  | 0, ws => ws.contains target = false
  | n + 1, ws => ∀ z, possible ws z → safe n (z :: ws)

private theorem absent {n : ℕ} {ws : List T} (h : safe n ws) : target ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, fullLegal g)
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
      obtain ⟨z, hz, hstep⟩ := tableFull w ws hw g (hg g (by simp))
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
  (0 :: -1 :: ws.flatMap (fun x => x :: (~~~x) :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff (ws : List T) (z : T) : z ∈ choices ws ↔ possible ws z := by
  simp [choices, possible, List.any_eq_true]
  grind

private def lastTwo (w : List T) : Bool :=
  let above := w.filter (fun x => (x &&& target) == target)
  let below := w.filter (fun x => (x ||| target) == target)
  (choices w).all fun z => !(z == target || ~~~z == target ||
    above.any (fun x => (x &&& z) == target) || below.any (fun x => (x ||| z) == target))

private theorem terminal {w : List T} (h : lastTwo w) : safe 2 w := by
  intro z hz v hv
  have avoid (u : T) (hu : possible w u) : u ≠ target ∧ ~~~u ≠ target ∧
      (∀ x ∈ w, x &&& u ≠ target) ∧ (∀ x ∈ w, x ||| u ≠ target) := by
    have hh := (List.all_eq_true.mp h) u ((choice_iff _ _).2 hu)
    simp at hh
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := hh
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx e
      apply h3 x hx _ e
      rw [← e, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx e
      apply h4 x hx _ e
      rw [← e, ← BitVec.or_assoc, BitVec.or_self]
  have base (x : T) (hx : x ∈ w) := avoid x (atom (.inr hx))
  have H := avoid z hz
  have unary (x : T) (hx : x ∈ z :: w) : x ≠ target ∧ ~~~x ≠ target := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1,H.2.1⟩
    · exact ⟨(base x hx).1,(base x hx).2.1⟩
  have binary (x y : T) (hx : x ∈ z :: w) (hy : y ∈ z :: w) :
      x &&& y ≠ target ∧ x ||| y ≠ target := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe,hye] using H.1
    · simpa [hxe,BitVec.and_comm,BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm,(base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target := by
    simp only [possible,Bool.or_eq_true,List.any_eq_true,beq_iff_eq] at hv
    rcases hv with ((e | e) | ⟨x,hx,((e | e) | ⟨y,hy,e | e⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: w).contains target = false
  suffices target ∉ v :: z :: w by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with e | hm
  · exact hv' e.symm
  · exact (unary target hm).1 rfl

private def masked (ws : List T) (mask want : T) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    (x == want || (~~~x &&& mask) == want) ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo (ws : List T) : Bool :=
  !(masked ws (-1) target || masked ws (-1) (~~~target) ||
    ws.any fun x =>
      ((x &&& target) == target && masked ws x target) ||
      ((x ||| target) == target && masked ws (~~~x) (target &&& ~~~x)))

private theorem masked_of_possible {ws : List T} {u : T} (hu : possible ws u) (m : T) :
    masked ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases x[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last {ws : List T} (hf : fastTwo ws) : lastTwo ws := by
  simp [fastTwo] at hf
  obtain ⟨⟨hn, hi⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible hz' (-1)
    rw [show z &&& (-1 : T) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible hz' (-1)
    have eq : z = ~~~target := by rw [← he]; simp
    rw [show z &&& (-1 : T) = z from BitVec.and_allOnes, eq] at hh
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

private def three (w : List T) : Bool :=
  (choices w).all (fun z => fastTwo (z :: w))

private theorem three_safe {w : List T} (h : three w) : safe 3 w := by
  intro z hz
  exact terminal (fast_implies_last ((List.all_eq_true.mp h) z ((choice_iff _ _).2 hz)))

private def rename (p : Fin 15 → Fin 15) (x : T) : T :=
  (BitVec.ofBoolListLE (List.ofFn fun i => x[(p i).val])).cast (by simp)

private theorem digit (p : Fin 15 → Fin 15) (x : T) (i : Fin 15) :
    (rename p x)[i.val] = x[(p i).val] := by
  rw [← BitVec.getLsbD_eq_getElem i.isLt]
  unfold rename
  rw [BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

private theorem mapAnd (p) (x y : T) : rename p (x &&& y) = rename p x &&& rename p y := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_and,digit p _ ⟨i,hi⟩,digit p x ⟨i,hi⟩,digit p y ⟨i,hi⟩]; simp
private theorem mapOr (p) (x y : T) : rename p (x ||| y) = rename p x ||| rename p y := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_or,digit p _ ⟨i,hi⟩,digit p x ⟨i,hi⟩,digit p y ⟨i,hi⟩]; simp
private theorem mapNot (p) (x : T) : rename p (~~~x) = ~~~(rename p x) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_not,digit p _ ⟨i,hi⟩,digit p x ⟨i,hi⟩]
  simp

private theorem transport (p : Fin 15 → Fin 15) (fixed : rename p target = target)
    (zero : rename p 0 = 0) (full : rename p (-1) = -1)
    {n ws us} (h : safe n us) (hsub : ∀ x ∈ ws, rename p x ∈ us) : safe n ws := by
  induction n generalizing ws us with
  | zero =>
    have ht := absent h
    change ws.contains target = false
    suffices target ∉ ws by simpa using this
    intro hm
    exact ht (fixed ▸ hsub _ hm)
  | succ n ih =>
    intro z hz
    have hz' : possible us (rename p z) := by
      simp only [possible,Bool.or_eq_true,List.any_eq_true,beq_iff_eq] at hz ⊢
      rcases hz with ((e | e) | ⟨x,hx,((e | e) | ⟨y,hy,e | e⟩)⟩) <;> subst z
      · exact .inl (.inl zero)
      · exact .inl (.inr full)
      · exact .inr ⟨_,hsub _ hx,.inl (.inl rfl)⟩
      · exact .inr ⟨_,hsub _ hx,.inl (.inr (mapNot p x))⟩
      · exact .inr ⟨_,hsub _ hx,.inr ⟨_,hsub _ hy,.inl (mapAnd p x y)⟩⟩
      · exact .inr ⟨_,hsub _ hx,.inr ⟨_,hsub _ hy,.inr (mapOr p x y)⟩⟩
    apply ih (h (rename p z) hz')
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · exact List.mem_cons_of_mem _ (hsub _ hx)
namespace Mono
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || w.any (fun v => z == (u &&& v) || z == (u ||| v)))
private def safe : ℕ → List T → Prop
  | 0, ws => ws.contains target = false
  | n+1, ws => ∀ z, possible ws z → safe n (z::ws)
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

end Mono

namespace Abs
private def sep (x : T) (pq : Fin 15 × Fin 15) : Prop :=
  bit pq.1 x ≠ bit pq.2 x

private def covers (s : Finset T) : Prop :=
  ∀ pq, sep target pq → ∃ x ∈ s, sep x pq

private def feasible (w : List T) (b : ℕ) : Prop :=
  ∃ s : Finset T, (∀ x ∈ s, x ∈ w) ∧ s.card ≤ b ∧ covers s

-- A difference across a gate is witnessed by an operand, in either direction.
private theorem factors {w : List T} {z : T} (h : possible w z) :
    ∃ a : Finset T, (∀ x ∈ a, x ∈ w) ∧ a.card ≤ 2 ∧
      ∀ pq, sep z pq → ∃ x ∈ a, sep x pq := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst z
  · refine ⟨∅, by simp, by simp, ?_⟩
    simp [sep, bit]
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro pq hs
    have ha : ∀ i : Fin 15, bit i (-1) = true := by decide +kernel
    exact False.elim (hs ((ha _).trans (ha _).symm))
  · exact ⟨{x}, by simpa using hx, by simp, fun pq hs => ⟨x, by simp, hs⟩⟩
  · refine ⟨{x}, by simpa using hx, by simp, fun pq hs => ⟨x, by simp, ?_⟩⟩
    intro he
    apply hs
    simpa only [bit,BitVec.getElem_not] using congrArg Bool.not he
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

private theorem pullCore {z : T} {w : List T} {b k : ℕ}
    (f : ∃ a : Finset T, (∀ x ∈ a, x ∈ w) ∧ a.card ≤ k+1 ∧ ∀ pq, sep z pq → ∃ x ∈ a, sep x pq)
    (hf : feasible (z :: w) b) : feasible w (b + k) := by
  obtain ⟨s, sub, lim, cov⟩ := hf
  by_cases hs : z ∈ s
  · obtain ⟨a, ha, ca, fac⟩ := f
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

private theorem pull {z w b} (hz : possible w z) (hf : feasible (z :: w) b) : feasible w (b+1) :=
  pullCore (k:=1) (factors hz) hf

private theorem pullNot {x w b} (hx : x ∈ w) (hf : feasible (~~~x :: w) b) : feasible w b := by
  apply pullCore (k:=0) _ hf
  refine ⟨{x}, by simpa using hx, by simp, fun pq hs => ⟨x,by simp,?_⟩⟩
  intro he
  apply hs
  simpa only [bit,BitVec.getElem_not] using congrArg Bool.not he

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
  inferInstanceAs (Decidable (_ ≠ _))

-- Pairwise incompatible differences give a lower bound on the required support.
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

end Abs

private theorem pureOrNot {w : List T} {z : T} (hz : possible w z) :
    Mono.possible w z ∨ ∃ x ∈ w, z = ~~~x := by
  simp only [possible,Mono.possible,Bool.or_eq_true,List.any_eq_true,beq_iff_eq] at *
  grind

private theorem mixed {n w} (ha : ¬ Abs.feasible w n) (hm : Mono.safe n w) : safe n w := by
  induction n generalizing w with
  | zero => exact hm
  | succ n ih =>
    intro z hz
    rcases pureOrNot hz with hp | ⟨x,hx,rfl⟩
    · exact ih (fun hf => ha (Abs.pull hz hf)) (hm z hp)
    · exact Abs.infeasible_safe n _ (fun hf => ha (Abs.pullNot hx hf))

private def symm : Fin 2 → Fin 15 → Fin 15 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 2, 1, 3, 4, 9, 6, 10, 11, 5, 7, 8, 12, 13, 14]]
private theorem symmFacts : ∀ p, rename (symm p) target = target ∧ rename (symm p) 0 = 0 ∧ rename (symm p) (-1) = -1 := by decide +kernel
private def routeOK (w : List T) (next : List (List T)) :
    List T → List (Fin 2 × Nat) → Bool
  | [], [] => true
  | z :: zs, (p,j) :: rest =>
      decide (j < next.length) &&
      (z :: w).all (fun x => (next.getD j []).contains (rename (symm p) x)) &&
      routeOK w next zs rest
  | _, _ => false

private theorem routeSound {w : List T} {next : List (List T)} {n : Nat}
    (good : ∀ u ∈ next, safe n u) (zs : List T) (plan : List (Fin 2 × Nat))
    (h : routeOK w next zs plan = true) :
    ∀ z ∈ zs, safe n (z :: w) := by
  induction zs generalizing plan with
  | nil => simp
  | cons z zs ih =>
    cases plan with
    | nil => simp [routeOK] at h
    | cons item plan =>
      obtain ⟨p,j⟩ := item
      simp only [routeOK,Bool.and_eq_true,decide_eq_true_eq] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hu : next.getD j [] ∈ next := by
          rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h.1.1]
          exact List.getElem_mem _
        apply transport (symm p) (symmFacts p).1 (symmFacts p).2.1 (symmFacts p).2.2 (good _ hu)
        intro v hv
        simpa only [List.contains_iff_mem] using (List.all_eq_true.mp h.1.2) v hv
      · exact ih plan h.2 x hx

private theorem stage {n w next} (good : ∀ u ∈ next, safe n u)
    (plan : List (Fin 2 × Nat)) (h : routeOK w next (choices w) plan = true) : safe (n+1) w := by
  intro z hz
  exact routeSound good _ plan h z ((choice_iff _ _).2 hz)

private def eligibleA {n : Nat} (p : Fin n → Fin 15 × Fin 15) (w : List T) : Bool :=
  w.all (fun x => decide (∀ i j, Abs.sep x (p i) → Abs.sep x (p j) → i = j))
private def eligibleM {n : Nat} (p : Fin n → Fin 15 × Fin 15) (w : List T) : Bool :=
  w.all (fun x => decide (∀ i j, Mono.sep x (p i) → Mono.sep x (p j) → i = j))

private theorem mixedGroup {n : Nat} (ws : List (List T)) (p : Fin (n+2) → Fin 15 × Fin 15) (q : Fin (n+1) → Fin 15 × Fin 15)
    (hp : ∀ i, Mono.sep target (p i)) (hq : ∀ i, Abs.sep target (q i))
    (ht : ws.all (fun w => eligibleM p w && eligibleA q w) = true) :
    ∀ w ∈ ws, safe n w := by
  intro w hw
  have both : (eligibleM p w && eligibleA q w) = true := (List.all_eq_true.mp ht) w hw
  obtain ⟨hm,ha⟩ : eligibleM p w = true ∧ eligibleA q w = true := by simpa using both
  exact mixed (Abs.packing q hq ha) (Mono.infeasible_safe n w (Mono.packing p hp hm))

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def g3_0 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 128, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 256, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 13450],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 3679, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 159, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 159, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 26911, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 130, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 130, 3679, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 159, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 287, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 287, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 26911, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 258, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 258, 3679, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 258, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 258, 26911, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 287, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 480, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 480, 3679, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5856, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 8223],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13440, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 19296],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26880, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115, 29119],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32736, 32738],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32736, 32740],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5856, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27135, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27135, 28671],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27135, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27135, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27135, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27135, 32736]]
private theorem ok3_0 : ∀ w ∈ g3_0, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (5, 6), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_1 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1032, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 10, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 256, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 256, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 256, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 4078],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 8192, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 8200, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26904, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26904, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26904, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8200, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32736, 32744],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8200, 26911, 27135]]
private theorem ok3_1 : ∀ w ∈ g3_1, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 6), (5, 7), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_2 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 256, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 32256]]
private theorem ok3_2 : ∀ w ∈ g3_2, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (2, 6), (5, 6), (5, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_3 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 128, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 13464],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 32751],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 6127],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135, 28671]]
private theorem ok3_3 : ∀ w ∈ g3_3, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (2, 6), (5, 6), (5, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_4 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2064, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 18, 3679, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8208, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32736, 32752],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135, 32736]]
private theorem ok3_4 : ∀ w ∈ g3_4, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (5, 8), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_5 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 64, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 128, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 256, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 13512],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 26960],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 32703],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32349]]
private theorem ok3_5 : ∀ w ∈ g3_5, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_6 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 64, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 66, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 66, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 256, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 320, 26911, 28500]]
private theorem ok3_6 : ∀ w ∈ g3_6, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_7 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 68, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 418, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 443, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115, 30139],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32324]]
private theorem ok3_7 : ∀ w ∈ g3_7, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (2, 6), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_8 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 128, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 256, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 1024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 3654],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 13450],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 256, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 1024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 3780],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 27024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 32639],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 3908],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 13704],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 32511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 486, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 1152, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 1160, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 2304, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 16383],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 28671],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 28672],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5256, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5632, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 5887],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 6143],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 8703],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 11844],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 24575],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13312, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 16383],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 18944],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 32255],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26624, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 28671],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 32255],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115, 29183],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115, 31163],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32287],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32738]]
private theorem ok3_8 : ∀ w ∈ g3_8, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (2, 6), (5, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_9 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 136, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 128, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 136, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 136, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 256, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 490, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 3788],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 27032],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8328, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 12424, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32392]]
private theorem ok3_9 : ∀ w ∈ g3_9, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (2, 6), (5, 6), (9, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_10 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 256, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 239, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 3924],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 13720],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 32495],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4267, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 7919],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8464, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 9216, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 24848, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 28671],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32528]]
private theorem ok3_10 : ∀ w ∈ g3_10, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (2, 6), (5, 6), (9, 11)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_11 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 490, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8448, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13320, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8200, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 26911, 27122]]
private theorem ok3_11 : ∀ w ∈ g3_11, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 6), (5, 7), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_12 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 136, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 204, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 10240, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 16383],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 32256]]
private theorem ok3_12 : ∀ w ∈ g3_12, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (2, 6), (9, 10), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_13 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 19327],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 19455],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 27511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 32256]]
private theorem ok3_13 : ∀ w ∈ g3_13, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (0, 4), (2, 6), (5, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_14 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 498, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 18, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 18, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 498, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5645, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8320, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26640, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8320, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135, 32255],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135, 32285]]
private theorem ok3_14 : ∀ w ∈ g3_14, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (5, 8), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_15 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 384, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 2320, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 14063],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32152, 32255],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32152, 32256]]
private theorem ok3_15 : ∀ w ∈ g3_15, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (2, 6), (5, 6), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_16 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 226, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 258, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 8674],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115, 29179],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32287],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32413],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32541],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5856, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8320, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 32736]]
private theorem ok3_16 : ∀ w ∈ g3_16, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (5, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_17 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 128, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 3780],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 26911, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 3908],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 26911, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 258, 26911, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 418, 3679, 29115]]
private theorem ok3_17 : ∀ w ∈ g3_17, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_18 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13802, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 3679, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 26911, 28511]]
private theorem ok3_18 : ∀ w ∈ g3_18, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 6), (5, 7), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_19 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 192, 3679, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 16076]]
private theorem ok3_19 : ∀ w ∈ g3_19, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (9, 6), (9, 10), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_20 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 26911, 27135]]
private theorem ok3_20 : ∀ w ∈ g3_20, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (0, 4), (5, 6), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_21 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 28500, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 28500, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4267, 28500, 28511]]
private theorem ok3_21 : ∀ w ∈ g3_21, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (9, 6), (9, 11), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_22 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 29088],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 128, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 256, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 1032, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 2048, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 3807],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 27024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 29088],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 32639],
  [0, 32767, 31, 482, 3652, 13448, 26896, 194, 3679, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 226, 3679, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 3935],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 13704],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 29088],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 32511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 416, 3679, 29088],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 29088],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4256, 26911, 28511]]
private theorem ok3_22 : ∀ w ∈ g3_22, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (1, 6), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_23 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32152, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32152, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 32152, 32736]]
private theorem ok3_23 : ∀ w ∈ g3_23, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (9, 6), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_24 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 18, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 18, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 28500, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 28500, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 258, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 384, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 384, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 384, 28500, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4267, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4267, 28500, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5856, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8320, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8320, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 29115, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 32152, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27024, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 28500, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 28500, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 28500, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 28662, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 29115, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 32152, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 32152, 32736]]
private theorem ok3_24 : ∀ w ∈ g3_24, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_25 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 24, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 27130],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26904, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26904, 27130]]
private theorem ok3_25 : ∀ w ∈ g3_25, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (5, 8), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_26 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 27122, 27135]]
private theorem ok3_26 : ∀ w ∈ g3_26, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(2, 6), (5, 6), (5, 7), (5, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_27 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 26904]]
private theorem ok3_27 : ∀ w ∈ g3_27, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 7), (12, 7), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_28 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 66, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 1032, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 13802]]
private theorem ok3_28 : ∀ w ∈ g3_28, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (1, 6), (5, 7), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_29 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 128, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 128, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 128, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 136, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 159, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8328, 26911, 27135]]
private theorem ok3_29 : ∀ w ∈ g3_29, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 6), (9, 6), (9, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_30 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 128, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 3679]]
private theorem ok3_30 : ∀ w ∈ g3_30, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (1, 6), (9, 6), (9, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_31 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 256, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 3679]]
private theorem ok3_31 : ∀ w ∈ g3_31, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (1, 6), (5, 7), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_32 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 28500]]
private theorem ok3_32 : ∀ w ∈ g3_32, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(2, 6), (5, 6), (5, 7), (9, 11)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_33 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471, 26904]]
private theorem ok3_33 : ∀ w ∈ g3_33, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (1, 7), (5, 6), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_34 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 32736]]
private theorem ok3_34 : ∀ w ∈ g3_34, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (9, 6), (9, 10), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_35 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 32277],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26904, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 23, 511, 19319]]
private theorem ok3_35 : ∀ w ∈ g3_35, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 4), (5, 6), (5, 7), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_36 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 28500]]
private theorem ok3_36 : ∀ w ∈ g3_36, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (9, 6), (9, 11)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_37 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26904, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 26911, 32152]]
private theorem ok3_37 : ∀ w ∈ g3_37, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (9, 6), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_38 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 19447]]
private theorem ok3_38 : ∀ w ∈ g3_38, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 4), (2, 6), (5, 6), (5, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_39 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 511, 32152]]
private theorem ok3_39 : ∀ w ∈ g3_39, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(2, 6), (5, 6), (5, 7), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_40 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5863, 26904]]
private theorem ok3_40 : ∀ w ∈ g3_40, safe 3 w := by
  exact mixedGroup _ ![(5, 6), (5, 6), (5, 6), (5, 6), (5, 6)] ![(0, 4), (5, 6), (5, 7), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_41 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8200, 26911, 32152]]
private theorem ok3_41 : ∀ w ∈ g3_41, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 6), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_42 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26904, 26911, 32152]]
private theorem ok3_42 : ∀ w ∈ g3_42, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_43 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 64, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 27122, 27135]]
private theorem ok3_43 : ∀ w ∈ g3_43, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 8), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_44 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 66, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 2064, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 27122]]
private theorem ok3_44 : ∀ w ∈ g3_44, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (1, 6), (5, 8), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_45 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 128, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 498, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 2064, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 27122]]
private theorem ok3_45 : ∀ w ∈ g3_45, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (1, 6), (5, 8), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_46 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 136, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8328, 27122, 27135]]
private theorem ok3_46 : ∀ w ∈ g3_46, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(2, 6), (5, 6), (5, 8), (9, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_47 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 256, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4256, 28500, 28511]]
private theorem ok3_47 : ∀ w ∈ g3_47, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (1, 6), (9, 6), (9, 11)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_48 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 32250],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122, 32250],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135, 32250]]
private theorem ok3_48 : ∀ w ∈ g3_48, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (5, 8), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_49 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 16076]]
private theorem ok3_49 : ∀ w ∈ g3_49, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(2, 6), (5, 8), (9, 10), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_50 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511, 19319]]
private theorem ok3_50 : ∀ w ∈ g3_50, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (2, 6), (5, 6), (5, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_51 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 28511]]
private theorem ok3_51 : ∀ w ∈ g3_51, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (1, 8), (5, 6), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_52 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 18, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26898, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 28662]]
private theorem ok3_52 : ∀ w ∈ g3_52, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (1, 4), (5, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_53 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 95, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 322, 26911, 28511]]
private theorem ok3_53 : ∀ w ∈ g3_53, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (12, 7), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_54 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 320, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 320, 27122, 28500]]
private theorem ok3_54 : ∀ w ∈ g3_54, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (9, 11), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_55 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 16076]]
private theorem ok3_55 : ∀ w ∈ g3_55, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 7), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_56 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 192, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 32285]]
private theorem ok3_56 : ∀ w ∈ g3_56, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (9, 10), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_57 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 19319]]
private theorem ok3_57 : ∀ w ∈ g3_57, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (0, 4), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_58 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511, 32152]]
private theorem ok3_58 : ∀ w ∈ g3_58, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (12, 3), (12, 10), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_59 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 320, 28500, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26960, 27122, 28500]]
private theorem ok3_59 : ∀ w ∈ g3_59, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (12, 3), (12, 7), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_60 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 27122, 28500]]
private theorem ok3_60 : ∀ w ∈ g3_60, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 8), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_61 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 95, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 256, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 1024, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 2048, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3654, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 13514],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 26962],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 29088],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 32701],
  [0, 32767, 31, 482, 3652, 13448, 26896, 95, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 322, 3679, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 13823]]
private theorem ok3_61 : ∀ w ∈ g3_61, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (1, 6), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_62 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 16076]]
private theorem ok3_62 : ∀ w ∈ g3_62, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (9, 10), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_63 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 354, 3679, 19319]]
private theorem ok3_63 : ∀ w ∈ g3_63, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (0, 4), (1, 6), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_64 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 320, 3679, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 320, 28500, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 322, 28500, 28511]]
private theorem ok3_64 : ∀ w ∈ g3_64, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (9, 11), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_65 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679, 32152]]
private theorem ok3_65 : ∀ w ∈ g3_65, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (1, 6), (12, 7), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_66 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 19319]]
private theorem ok3_66 : ∀ w ∈ g3_66, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (0, 4), (1, 6), (9, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_67 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 2064, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 384, 3679, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 32152]]
private theorem ok3_67 : ∀ w ∈ g3_67, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (1, 6), (9, 6), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_68 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 28500]]
private theorem ok3_68 : ∀ w ∈ g3_68, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(2, 6), (5, 6), (9, 10), (9, 11)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_69 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 32631],
  [0, 32767, 31, 482, 3652, 13448, 26896, 375, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 20343]]
private theorem ok3_69 : ∀ w ∈ g3_69, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 4), (2, 6), (5, 6), (9, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_70 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 408, 511, 32152]]
private theorem ok3_70 : ∀ w ∈ g3_70, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(2, 6), (5, 6), (9, 10), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_71 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 287, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 32736]]
private theorem ok3_71 : ∀ w ∈ g3_71, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (9, 6), (9, 11)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_72 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 498, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 32285]]
private theorem ok3_72 : ∀ w ∈ g3_72, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (9, 11), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_73 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 27122, 28500]]
private theorem ok3_73 : ∀ w ∈ g3_73, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (9, 11), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_74 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 32732],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 32732]]
private theorem ok3_74 : ∀ w ∈ g3_74, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(2, 6), (9, 10), (9, 11), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_75 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 28500]]
private theorem ok3_75 : ∀ w ∈ g3_75, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (2, 6), (5, 6), (9, 11)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_76 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 340, 511, 28500]]
private theorem ok3_76 : ∀ w ∈ g3_76, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (2, 6), (9, 11), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_77 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 354, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 26911, 27122]]
private theorem ok3_77 : ∀ w ∈ g3_77, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (0, 4), (5, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_78 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 615, 32152]]
private theorem ok3_78 : ∀ w ∈ g3_78, safe 3 w := by
  exact mixedGroup _ ![(5, 6), (5, 6), (5, 6), (5, 6), (5, 6)] ![(0, 3), (2, 6), (5, 6), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_79 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 19319]]
private theorem ok3_79 : ∀ w ∈ g3_79, safe 3 w := by
  exact mixedGroup _ ![(5, 6), (5, 6), (5, 6), (5, 6), (5, 6)] ![(0, 3), (0, 4), (2, 6), (5, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_80 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471, 16095]]
private theorem ok3_80 : ∀ w ∈ g3_80, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (9, 6), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_81 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 18965],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 19319]]
private theorem ok3_81 : ∀ w ∈ g3_81, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 4), (5, 6), (5, 7), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_82 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32152, 32250]]
private theorem ok3_82 : ∀ w ∈ g3_82, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (12, 3), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_83 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27135, 32255]]
private theorem ok3_83 : ∀ w ∈ g3_83, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (5, 6), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_84 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 16691],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 19319]]
private theorem ok3_84 : ∀ w ∈ g3_84, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 4), (2, 6), (9, 10), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_85 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 27122]]
private theorem ok3_85 : ∀ w ∈ g3_85, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 8), (9, 10), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_86 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32152, 32732]]
private theorem ok3_86 : ∀ w ∈ g3_86, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(2, 6), (9, 10), (12, 10), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_87 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 18704, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 32152]]
private theorem ok3_87 : ∀ w ∈ g3_87, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (2, 6), (5, 6), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_88 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 27122, 27135]]
private theorem ok3_88 : ∀ w ∈ g3_88, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (5, 6), (5, 8), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_89 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32152, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 32152, 32285]]
private theorem ok3_89 : ∀ w ∈ g3_89, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (12, 3), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_90 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27135, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135, 32152]]
private theorem ok3_90 : ∀ w ∈ g3_90, safe 3 w := by
  intro w hu
  simp only [g3_90,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  all_goals (apply three_safe; decide +kernel)
private def g3_91 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 615, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 615, 27122, 32152]]
private theorem ok3_91 : ∀ w ∈ g3_91, safe 3 w := by
  exact mixedGroup _ ![(5, 6), (5, 6), (5, 6), (5, 6), (5, 6)] ![(0, 3), (5, 6), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_92 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 4267, 26911, 28500]]
private theorem ok3_92 : ∀ w ∈ g3_92, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (2, 4), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_93 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 26911, 28500]]
private theorem ok3_93 : ∀ w ∈ g3_93, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 7), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_94 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 26911, 32152]]
private theorem ok3_94 : ∀ w ∈ g3_94, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 6), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_95 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 27122, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 28500, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 32152, 32250],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 28500, 32250],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 32152, 32250]]
private theorem ok3_95 : ∀ w ∈ g3_95, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_96 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 28500, 28511]]
private theorem ok3_96 : ∀ w ∈ g3_96, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 7), (9, 11), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_97 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 26911, 32152]]
private theorem ok3_97 : ∀ w ∈ g3_97, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 4), (5, 6), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_98 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 27122, 28500]]
private theorem ok3_98 : ∀ w ∈ g3_98, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (5, 6), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_99 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 27122, 32152]]
private theorem ok3_99 : ∀ w ∈ g3_99, safe 3 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(5, 6), (5, 8), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_100 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122, 32250]]
private theorem ok3_100 : ∀ w ∈ g3_100, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(1, 4), (5, 6), (5, 7), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_101 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 28500, 29115]]
private theorem ok3_101 : ∀ w ∈ g3_101, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 8), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g3_102 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 32152, 32732]]
private theorem ok3_102 : ∀ w ∈ g3_102, safe 3 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(9, 6), (9, 10), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def groups3 : List (List (List T)) := [g3_0, g3_1, g3_2, g3_3, g3_4, g3_5, g3_6, g3_7, g3_8, g3_9, g3_10, g3_11, g3_12, g3_13, g3_14, g3_15, g3_16, g3_17, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, g3_28, g3_29, g3_30, g3_31, g3_32, g3_33, g3_34, g3_35, g3_36, g3_37, g3_38, g3_39, g3_40, g3_41, g3_42, g3_43, g3_44, g3_45, g3_46, g3_47, g3_48, g3_49, g3_50, g3_51, g3_52, g3_53, g3_54, g3_55, g3_56, g3_57, g3_58, g3_59, g3_60, g3_61, g3_62, g3_63, g3_64, g3_65, g3_66, g3_67, g3_68, g3_69, g3_70, g3_71, g3_72, g3_73, g3_74, g3_75, g3_76, g3_77, g3_78, g3_79, g3_80, g3_81, g3_82, g3_83, g3_84, g3_85, g3_86, g3_87, g3_88, g3_89, g3_90, g3_91, g3_92, g3_93, g3_94, g3_95, g3_96, g3_97, g3_98, g3_99, g3_100, g3_101, g3_102]
private theorem good3 (w : List T) (hw : w ∈ groups3.flatten) : safe 3 w := by
  obtain ⟨g,hu,h⟩ := List.mem_flatten.mp hw
  simp only [groups3,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok3_0 _ h
  · exact ok3_1 _ h
  · exact ok3_2 _ h
  · exact ok3_3 _ h
  · exact ok3_4 _ h
  · exact ok3_5 _ h
  · exact ok3_6 _ h
  · exact ok3_7 _ h
  · exact ok3_8 _ h
  · exact ok3_9 _ h
  · exact ok3_10 _ h
  · exact ok3_11 _ h
  · exact ok3_12 _ h
  · exact ok3_13 _ h
  · exact ok3_14 _ h
  · exact ok3_15 _ h
  · exact ok3_16 _ h
  · exact ok3_17 _ h
  · exact ok3_18 _ h
  · exact ok3_19 _ h
  · exact ok3_20 _ h
  · exact ok3_21 _ h
  · exact ok3_22 _ h
  · exact ok3_23 _ h
  · exact ok3_24 _ h
  · exact ok3_25 _ h
  · exact ok3_26 _ h
  · exact ok3_27 _ h
  · exact ok3_28 _ h
  · exact ok3_29 _ h
  · exact ok3_30 _ h
  · exact ok3_31 _ h
  · exact ok3_32 _ h
  · exact ok3_33 _ h
  · exact ok3_34 _ h
  · exact ok3_35 _ h
  · exact ok3_36 _ h
  · exact ok3_37 _ h
  · exact ok3_38 _ h
  · exact ok3_39 _ h
  · exact ok3_40 _ h
  · exact ok3_41 _ h
  · exact ok3_42 _ h
  · exact ok3_43 _ h
  · exact ok3_44 _ h
  · exact ok3_45 _ h
  · exact ok3_46 _ h
  · exact ok3_47 _ h
  · exact ok3_48 _ h
  · exact ok3_49 _ h
  · exact ok3_50 _ h
  · exact ok3_51 _ h
  · exact ok3_52 _ h
  · exact ok3_53 _ h
  · exact ok3_54 _ h
  · exact ok3_55 _ h
  · exact ok3_56 _ h
  · exact ok3_57 _ h
  · exact ok3_58 _ h
  · exact ok3_59 _ h
  · exact ok3_60 _ h
  · exact ok3_61 _ h
  · exact ok3_62 _ h
  · exact ok3_63 _ h
  · exact ok3_64 _ h
  · exact ok3_65 _ h
  · exact ok3_66 _ h
  · exact ok3_67 _ h
  · exact ok3_68 _ h
  · exact ok3_69 _ h
  · exact ok3_70 _ h
  · exact ok3_71 _ h
  · exact ok3_72 _ h
  · exact ok3_73 _ h
  · exact ok3_74 _ h
  · exact ok3_75 _ h
  · exact ok3_76 _ h
  · exact ok3_77 _ h
  · exact ok3_78 _ h
  · exact ok3_79 _ h
  · exact ok3_80 _ h
  · exact ok3_81 _ h
  · exact ok3_82 _ h
  · exact ok3_83 _ h
  · exact ok3_84 _ h
  · exact ok3_85 _ h
  · exact ok3_86 _ h
  · exact ok3_87 _ h
  · exact ok3_88 _ h
  · exact ok3_89 _ h
  · exact ok3_90 _ h
  · exact ok3_91 _ h
  · exact ok3_92 _ h
  · exact ok3_93 _ h
  · exact ok3_94 _ h
  · exact ok3_95 _ h
  · exact ok3_96 _ h
  · exact ok3_97 _ h
  · exact ok3_98 _ h
  · exact ok3_99 _ h
  · exact ok3_100 _ h
  · exact ok3_101 _ h
  · exact ok3_102 _ h
private def g2_0 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 128],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 13450],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 1024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3780],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 27024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 32639],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 130, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 226, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 287],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3908],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 13704],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 32511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 258, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 480, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 1152, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2304, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5256, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5856, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 8223],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 8674],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 24575],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13440, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 19296],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26880, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 29115, 29119],
  [0, 32767, 31, 482, 3652, 13448, 26896, 29115, 31163],
  [0, 32767, 31, 482, 3652, 13448, 26896, 29115, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 29115, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 32736, 32738]]
private theorem ok2_0 : ∀ w ∈ g2_0, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (5, 6), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_1 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8200, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 32736, 32744]]
private theorem ok2_1 : ∀ w ∈ g2_1, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 6), (5, 7), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_2 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 128],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 498],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 13464],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 32751],
  [0, 32767, 31, 482, 3652, 13448, 26896, 18, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 6127],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8208, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8320, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 32736, 32752]]
private theorem ok2_2 : ∀ w ∈ g2_2, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (5, 8), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_3 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 64],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 95],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 13512],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 26960],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 32703],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 32736]]
private theorem ok2_3 : ∀ w ∈ g2_3, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (12, 3), (12, 7), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_4 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 66, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 136, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 32152]]
private theorem ok2_4 : ∀ w ∈ g2_4, safe 4 w := by
  intro w hu
  simp only [g2_4,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply stage good3 [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,5), (0,0), (0,216), (0,135), (0,3), (0,153), (0,4), (0,474), (0,182), (0,217), (0,211), (0,381), (0,212), (0,425), (0,225), (0,213), (0,396), (0,214), (0,344), (0,215), (0,203), (0,218), (0,412), (0,220), (0,457), (0,221), (0,321), (0,222), (0,219), (0,223), (0,343), (0,224), (0,227), (0,226)]
    decide +kernel
  · apply stage good3 [(0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,17), (0,216), (1,0), (0,105), (0,13), (0,171), (0,15), (0,16), (0,196), (0,8), (0,1), (0,524), (0,2), (0,173), (0,197), (0,9), (0,513), (0,6), (0,534), (0,7), (0,543), (0,511), (0,538), (0,11), (0,592), (0,12), (0,107), (0,512), (0,10), (0,14), (0,172), (0,550), (0,18), (0,551)]
    decide +kernel
  · apply stage good3 [(0,103), (0,103), (0,103), (0,103), (0,103), (0,103), (0,103), (0,103), (0,103), (0,121), (0,103), (0,137), (1,104), (0,678), (0,682), (0,649), (0,118), (0,108), (0,120), (0,659), (0,113), (0,667), (0,525), (0,109), (0,652), (0,119), (1,668), (0,684), (1,110), (0,693), (0,112), (0,114), (0,687), (0,116), (0,694), (0,670), (0,115), (0,117), (0,653), (0,689), (0,688)]
    decide +kernel
  · apply stage good3 [(0,22), (0,22), (0,22), (0,22), (0,22), (0,22), (0,22), (0,22), (0,22), (0,123), (0,135), (1,105), (0,679), (0,22), (0,656), (0,122), (0,147), (0,660), (0,138), (0,322), (0,526), (0,136), (0,657), (0,137), (0,145), (1,675), (0,397), (1,677), (0,681), (1,678), (1,662), (0,139), (0,697), (0,141), (0,700), (0,323), (0,142), (0,140), (0,143), (0,680), (0,144), (0,698), (0,146)]
    decide +kernel
  · apply stage good3 [(0,106), (0,106), (0,106), (0,106), (0,106), (0,106), (0,106), (0,106), (0,106), (0,130), (0,106), (0,143), (1,106), (1,143), (0,683), (0,650), (0,128), (0,651), (1,129), (0,661), (0,124), (0,669), (0,527), (0,111), (0,654), (0,117), (0,655), (0,129), (1,669), (1,527), (1,111), (1,654), (1,117), (1,655), (0,690), (0,126), (0,695), (0,127), (0,125), (0,691), (0,702)]
    decide +kernel
  · apply stage good3 [(0,23), (0,23), (0,23), (0,23), (0,23), (0,23), (0,23), (0,23), (0,23), (0,176), (0,153), (1,171), (0,717), (0,656), (0,175), (0,23), (0,429), (0,709), (0,155), (0,154), (0,728), (0,345), (0,428), (0,427), (0,162), (1,715), (0,734), (1,725), (0,347), (1,716), (1,712), (0,156), (0,735), (0,158), (0,458), (0,159), (0,722), (0,160), (0,157), (0,346), (0,161), (0,164), (0,163)]
    decide +kernel
  · apply stage good3 [(0,182), (0,182), (0,182), (0,182), (0,182), (0,182), (0,182), (0,182), (0,182), (0,744), (0,182), (1,196), (0,742), (0,660), (0,187), (0,709), (0,743), (0,741), (0,192), (0,476), (0,183), (0,753), (0,184), (0,710), (0,191), (1,515), (0,755), (1,199), (0,750), (1,198), (0,477), (0,758), (0,186), (0,759), (0,188), (0,398), (0,189), (0,185), (0,190), (0,749), (0,204), (0,193), (0,205)]
    decide +kernel
  · apply stage good3 [(0,197), (0,197), (0,197), (0,197), (0,197), (0,197), (0,197), (0,197), (0,197), (0,747), (0,197), (0,767), (1,203), (0,662), (0,200), (0,712), (0,746), (0,765), (0,778), (0,198), (0,553), (0,552), (0,664), (0,766), (0,714), (0,554), (0,201), (0,768), (0,784), (0,769), (0,787), (0,770), (0,785), (0,772), (0,791), (0,773), (0,663), (0,774), (0,771), (0,775), (0,713), (0,776), (0,779), (0,777)]
    decide +kernel
  · apply stage good3 [(0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,30), (0,211), (1,6), (0,556), (0,322), (0,28), (0,154), (0,29), (0,26), (0,479), (0,183), (0,233), (0,478), (0,229), (0,433), (0,240), (0,230), (0,399), (0,231), (0,349), (0,232), (1,768), (0,234), (0,413), (0,236), (0,459), (0,324), (0,237), (0,235), (0,238), (0,348), (0,239), (0,242), (0,241)]
    decide +kernel
  · apply stage good3 [(0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,33), (0,1), (0,556), (1,213), (0,675), (0,31), (0,715), (0,32), (0,27), (0,568), (0,515), (0,560), (0,781), (0,555), (0,719), (0,552), (0,561), (0,517), (1,230), (0,535), (0,558), (0,545), (0,516), (0,792), (0,563), (0,795), (0,557), (0,564), (0,562), (0,565), (0,718), (0,566), (0,569), (0,559), (0,567)]
    decide +kernel
  · apply stage good3 [(0,38), (0,38), (0,38), (0,38), (0,38), (0,38), (0,38), (0,38), (0,38), (0,673), (0,321), (1,107), (0,676), (0,323), (0,38), (0,722), (0,672), (0,671), (0,337), (0,398), (0,329), (0,324), (0,148), (0,325), (0,723), (0,326), (0,335), (1,557), (0,400), (0,327), (0,801), (0,328), (1,663), (0,330), (0,802), (0,332), (0,806), (0,243), (0,331), (0,333), (0,800), (0,334), (0,803), (0,336)]
    decide +kernel
  · apply stage good3 [(0,40), (0,40), (0,40), (0,40), (0,40), (0,40), (0,40), (0,40), (0,40), (0,44), (0,212), (1,7), (0,572), (0,136), (0,42), (0,345), (0,43), (0,40), (0,483), (0,184), (0,246), (0,229), (0,383), (0,482), (0,253), (1,558), (0,402), (0,244), (0,352), (0,245), (1,769), (0,247), (0,414), (0,249), (0,460), (0,250), (0,325), (0,251), (0,248), (0,351), (0,252), (0,255), (0,254)]
    decide +kernel
  · apply stage good3 [(0,2), (0,2), (0,2), (0,2), (0,2), (0,2), (0,2), (0,2), (0,2), (0,47), (0,2), (0,572), (1,214), (0,677), (0,45), (0,725), (0,46), (0,41), (0,582), (0,199), (0,574), (0,555), (0,665), (0,720), (0,766), (0,575), (0,520), (1,231), (0,537), (1,244), (0,547), (0,519), (0,793), (0,577), (0,797), (0,578), (1,327), (0,579), (0,576), (0,796), (0,580), (0,583), (0,573), (0,581)]
    decide +kernel
  · apply stage good3 [(0,54), (0,54), (0,54), (0,54), (0,54), (0,54), (0,54), (0,54), (0,54), (0,810), (0,343), (1,172), (0,726), (0,680), (0,809), (0,346), (0,54), (0,808), (0,815), (0,749), (0,354), (0,348), (0,818), (0,351), (0,435), (0,814), (0,361), (1,718), (0,821), (1,796), (0,360), (0,353), (1,713), (0,355), (0,825), (0,357), (0,461), (0,358), (0,800), (0,359), (0,356), (0,256), (0,363), (0,362)]
    decide +kernel
  · apply stage good3 [(0,58), (0,58), (0,58), (0,58), (0,58), (0,58), (0,58), (0,58), (0,58), (0,60), (0,216), (1,216), (0,679), (0,58), (0,717), (0,59), (1,261), (0,742), (0,585), (0,556), (0,666), (0,572), (0,721), (0,767), (0,586), (0,261), (1,556), (1,666), (1,572), (1,721), (1,767), (0,794), (0,588), (0,799), (0,676), (0,783), (1,676), (1,783), (0,587), (0,726), (0,589), (1,726), (1,589), (1,590), (0,780), (0,590)]
    decide +kernel
  · apply stage good3 [(0,21), (0,21), (0,21), (0,21), (0,21), (0,21), (0,21), (0,21), (0,21), (0,63), (0,217), (1,8), (0,585), (0,138), (0,61), (0,155), (0,62), (0,21), (0,262), (0,487), (0,476), (0,233), (0,385), (0,246), (0,437), (0,268), (1,560), (0,338), (1,574), (0,364), (1,553), (0,415), (0,264), (0,464), (0,329), (0,265), (0,258), (0,149), (0,263), (0,354), (0,266), (0,260), (0,165), (0,269), (0,257), (0,267)]
    decide +kernel
  · apply stage good3 [(0,64), (0,64), (0,64), (0,64), (0,64), (0,64), (0,64), (0,64), (0,64), (0,66), (0,218), (1,9), (0,586), (0,139), (0,64), (0,156), (0,65), (0,279), (0,477), (0,262), (0,234), (0,150), (0,247), (0,166), (0,277), (1,561), (0,339), (1,575), (0,365), (1,554), (0,416), (0,271), (0,465), (0,330), (0,272), (0,259), (0,273), (0,270), (0,355), (0,274), (0,463), (0,275), (0,278), (0,276)]
    decide +kernel
  · apply stage good3 [(0,68), (0,68), (0,68), (0,68), (0,68), (0,68), (0,68), (0,68), (0,68), (0,70), (0,219), (1,10), (0,587), (0,140), (0,68), (0,157), (0,69), (0,174), (0,282), (0,488), (0,185), (0,263), (0,235), (0,386), (0,248), (0,439), (0,481), (0,167), (0,287), (1,562), (0,403), (1,576), (0,368), (1,771), (0,270), (1,571), (0,367), (0,832), (0,284), (0,467), (0,331), (0,285), (0,280), (0,466), (0,356), (0,286), (0,288), (0,350), (0,283)]
    decide +kernel
  · apply stage good3 [(0,71), (0,71), (0,71), (0,71), (0,71), (0,71), (0,71), (0,71), (0,71), (0,74), (0,220), (1,11), (0,588), (0,141), (0,72), (0,158), (0,73), (0,71), (0,490), (0,186), (0,264), (0,236), (0,387), (0,249), (0,440), (0,489), (0,294), (1,563), (0,404), (1,577), (0,369), (1,772), (0,271), (0,290), (0,417), (0,468), (0,332), (0,291), (0,284), (0,357), (0,293), (0,295), (0,289), (0,292)]
    decide +kernel
  · apply stage good3 [(0,3), (0,3), (0,3), (0,3), (0,3), (0,3), (0,3), (0,3), (0,3), (0,80), (0,3), (1,13), (0,58), (0,22), (0,175), (0,77), (0,493), (0,187), (0,61), (0,28), (0,491), (0,42), (0,442), (0,36), (0,492), (0,78), (1,31), (0,833), (1,45), (0,811), (1,200), (0,64), (1,37), (0,834), (0,539), (0,72), (0,593), (0,38), (0,68), (0,809), (0,297), (0,178), (0,79), (0,298), (0,39), (0,76)]
    decide +kernel
  · apply stage good3 [(0,148), (0,148), (0,148), (0,148), (0,148), (0,148), (0,148), (0,148), (0,148), (0,531), (0,381), (1,534), (0,666), (0,526), (0,491), (0,728), (0,530), (0,528), (0,390), (0,393), (0,753), (0,385), (0,478), (0,383), (0,729), (0,392), (1,535), (0,754), (1,537), (0,819), (1,784), (0,150), (1,536), (0,391), (0,836), (0,387), (0,837), (0,148), (0,386), (0,818), (0,151), (0,388), (0,730), (0,152), (0,384), (0,835)]
    decide +kernel
  · apply stage good3 [(0,142), (0,142), (0,142), (0,142), (0,142), (0,142), (0,142), (0,142), (0,142), (0,840), (0,222), (1,512), (0,783), (0,142), (0,492), (0,160), (0,839), (0,494), (0,189), (0,265), (0,237), (0,390), (0,251), (0,443), (0,302), (1,564), (0,208), (1,579), (0,372), (1,774), (0,272), (1,570), (0,299), (0,418), (0,291), (0,469), (0,243), (0,285), (0,359), (0,301), (0,370), (0,303), (0,304), (0,300)]
    decide +kernel
  · apply stage good3 [(0,208), (0,208), (0,208), (0,208), (0,208), (0,208), (0,208), (0,208), (0,208), (0,686), (0,396), (1,524), (1,666), (0,397), (0,833), (0,734), (0,685), (1,529), (0,406), (0,757), (0,755), (0,338), (0,399), (0,754), (0,402), (0,844), (0,756), (0,407), (0,410), (1,781), (1,665), (0,822), (1,664), (0,339), (0,843), (0,404), (0,845), (0,400), (0,208), (0,403), (0,821), (0,409), (0,405), (0,823), (0,411), (0,401), (0,408), (0,842)]
    decide +kernel
  · apply stage good3 [(0,412), (0,412), (0,412), (0,412), (0,412), (0,412), (0,412), (0,412), (0,412), (0,541), (0,412), (1,538), (0,794), (0,697), (0,539), (0,735), (0,540), (0,692), (0,419), (0,829), (0,758), (0,415), (0,413), (0,836), (0,414), (0,849), (0,828), (0,699), (0,423), (1,792), (0,843), (1,793), (0,826), (1,785), (0,416), (1,786), (0,805), (0,417), (0,848), (0,802), (0,418), (0,832), (0,825), (0,421), (0,847), (0,422), (0,424), (0,804), (0,420)]
    decide +kernel
  · apply stage good3 [(0,4), (0,4), (0,4), (0,4), (0,4), (0,4), (0,4), (0,4), (0,4), (0,86), (0,4), (1,15), (0,59), (0,122), (0,77), (0,23), (0,85), (0,743), (0,62), (0,29), (0,530), (0,43), (0,495), (0,50), (0,306), (0,83), (1,32), (0,685), (1,46), (0,812), (1,746), (0,65), (1,51), (0,82), (0,540), (0,73), (0,594), (0,672), (0,839), (0,132), (0,84), (0,69), (0,54), (0,307), (0,55), (0,67)]
    decide +kernel
  · apply stage good3 [(0,166), (0,166), (0,166), (0,166), (0,166), (0,166), (0,166), (0,166), (0,166), (0,179), (0,425), (1,543), (0,721), (0,657), (0,442), (0,428), (0,495), (0,431), (0,168), (0,447), (0,710), (0,437), (0,433), (0,729), (0,482), (0,446), (1,545), (0,844), (1,547), (0,816), (1,787), (0,166), (1,788), (0,445), (0,849), (0,440), (0,851), (0,723), (0,443), (0,441), (0,731), (0,439), (0,435), (0,169), (0,436), (0,438)]
    decide +kernel
  · apply stage good3 [(0,144), (0,144), (0,144), (0,144), (0,144), (0,144), (0,144), (0,144), (0,144), (0,313), (0,224), (1,550), (0,589), (0,144), (0,297), (0,161), (0,306), (0,312), (0,204), (0,266), (0,239), (0,151), (0,252), (0,168), (0,309), (1,566), (0,409), (1,580), (0,374), (1,776), (0,274), (1,782), (0,308), (0,421), (0,293), (0,470), (0,334), (0,301), (0,340), (0,310), (0,286), (0,256), (0,311), (0,281)]
    decide +kernel
  · apply stage good3 [(0,344), (0,344), (0,344), (0,344), (0,344), (0,344), (0,344), (0,344), (0,344), (0,813), (0,344), (1,173), (1,721), (0,681), (0,811), (0,347), (0,812), (1,177), (0,375), (0,817), (0,750), (0,364), (0,349), (0,819), (0,352), (0,816), (0,751), (0,376), (0,378), (1,719), (0,822), (1,720), (1,714), (0,365), (0,826), (0,369), (0,854), (0,801), (0,372), (0,371), (0,824), (0,368), (0,360), (0,374), (0,379), (0,827), (0,377), (0,366)]
    decide +kernel
  · apply stage good3 [(0,78), (0,78), (0,78), (0,78), (0,78), (0,78), (0,78), (0,78), (0,78), (0,88), (0,225), (1,16), (0,261), (0,145), (0,78), (0,162), (0,83), (0,228), (0,87), (0,497), (0,191), (0,268), (0,240), (0,392), (0,253), (0,446), (0,206), (0,496), (1,568), (0,410), (1,582), (0,378), (1,778), (0,277), (0,423), (0,294), (0,471), (0,335), (0,302), (0,341), (0,209), (0,287), (0,361), (0,309), (0,373), (0,315), (0,316), (0,207), (0,314)]
    decide +kernel
  · apply stage good3 [(0,457), (0,457), (0,457), (0,457), (0,457), (0,457), (0,457), (0,457), (0,457), (0,596), (0,457), (1,592), (0,799), (0,700), (0,593), (0,458), (0,594), (0,701), (0,595), (0,852), (0,759), (0,464), (0,459), (0,837), (0,460), (0,851), (0,462), (0,838), (0,471), (1,795), (0,845), (1,797), (0,854), (1,791), (0,465), (1,798), (0,846), (0,848), (0,468), (0,806), (0,469), (0,467), (0,461), (0,470), (0,473), (0,807), (0,472), (0,831)]
    decide +kernel
  · apply stage good3 [(0,146), (0,146), (0,146), (0,146), (0,146), (0,146), (0,146), (0,146), (0,146), (0,319), (0,226), (1,551), (1,590), (0,146), (0,298), (0,163), (0,307), (0,318), (0,317), (0,205), (0,269), (0,241), (0,152), (0,254), (0,169), (0,320), (0,316), (1,567), (0,411), (1,581), (0,379), (1,777), (0,278), (1,584), (0,210), (0,424), (0,295), (0,473), (0,336), (0,304), (0,296), (0,342), (0,288), (0,362), (0,311), (0,305), (0,380)]
    decide +kernel
  · apply stage good3 [(0,85), (0,85), (0,85), (0,85), (0,85), (0,85), (0,85), (0,85), (0,85), (0,89), (0,474), (1,513), (1,261), (0,147), (0,493), (0,429), (0,85), (1,25), (0,498), (0,192), (0,487), (0,479), (0,393), (0,483), (0,447), (0,497), (1,517), (0,757), (1,520), (0,817), (1,201), (0,279), (1,523), (0,195), (0,829), (0,490), (0,852), (0,337), (0,494), (0,389), (0,499), (0,488), (0,815), (0,312), (0,444), (0,500), (0,317)]
    decide +kernel
  · apply stage good3 [(0,5), (0,5), (0,5), (0,5), (0,5), (0,5), (0,5), (0,5), (0,5), (0,5), (1,17), (0,60), (0,123), (0,80), (0,176), (0,86), (0,89), (0,744), (0,63), (0,30), (0,531), (0,44), (0,179), (0,56), (0,90), (0,88), (1,33), (0,686), (1,47), (0,813), (1,747), (0,66), (1,57), (0,91), (0,541), (0,74), (0,596), (0,673), (0,840), (0,75), (0,133), (0,70), (0,810), (0,313), (0,81), (0,180), (0,319)]
    decide +kernel
  · apply stage good3 [(0,194), (0,194), (0,194), (0,194), (0,194), (0,194), (0,194), (0,194), (0,194), (0,510), (0,475), (0,495), (1,514), (1,812), (0,382), (0,505), (0,736), (0,738), (0,506), (0,509), (0,194), (0,501), (0,480), (0,395), (0,484), (0,486), (0,507), (1,518), (1,861), (1,521), (0,637), (1,522), (0,737), (1,202), (0,740), (0,830), (0,503), (0,638), (0,394), (0,508), (0,504), (0,872), (0,625), (0,502), (0,739), (1,860)]
    decide +kernel
  · apply stage good3 [(0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,102), (0,19), (0,306), (1,20), (1,82), (0,131), (0,96), (0,24), (0,101), (0,745), (0,92), (0,34), (0,532), (0,48), (0,506), (0,52), (0,99), (1,35), (1,533), (1,49), (1,737), (1,53), (0,97), (1,748), (0,98), (0,542), (0,95), (0,855), (0,134), (0,100), (0,674), (0,841), (0,94), (0,93), (1,591)]
    decide +kernel
  · apply stage good3 [(0,594), (0,594), (0,594), (0,594), (0,594), (0,594), (0,594), (0,594), (0,594), (0,597), (0,598), (0,594), (1,598), (1,594), (0,703), (0,634), (0,602), (0,696), (0,640), (1,639), (0,760), (0,619), (0,607), (0,862), (0,611), (0,638), (0,615), (0,855), (0,616), (0,865), (0,639), (1,607), (1,862), (1,611), (1,638), (1,615), (1,855), (1,616), (1,865), (0,869), (0,629), (0,704), (0,626), (0,624), (0,708), (0,858)]
    decide +kernel
  · apply stage good3 [(0,168), (0,168), (0,168), (0,168), (0,168), (0,168), (0,168), (0,168), (0,168), (0,181), (0,426), (0,168), (1,544), (1,375), (0,658), (0,452), (0,430), (0,506), (0,432), (0,456), (0,711), (0,448), (0,434), (0,732), (0,485), (0,454), (1,546), (1,868), (1,548), (0,856), (1,789), (0,453), (1,790), (0,170), (0,850), (0,450), (0,857), (0,451), (0,733), (0,724), (0,455), (0,449), (1,549), (1,727)]
    decide +kernel
  · apply stage good3 [(0,599), (0,599), (0,599), (0,599), (0,599), (0,599), (0,599), (0,599), (0,599), (0,644), (0,599), (0,816), (1,599), (1,816), (0,705), (0,635), (0,603), (0,637), (0,605), (0,856), (1,605), (1,856), (1,873), (0,764), (0,620), (0,608), (0,820), (0,612), (0,752), (0,642), (0,873), (1,608), (1,820), (1,612), (1,752), (0,870), (0,630), (0,643), (0,632), (0,866), (1,632), (1,866), (0,627), (1,622), (0,763), (0,622)]
    decide +kernel
  · apply stage good3 [(0,600), (0,600), (0,600), (0,600), (0,600), (0,600), (0,600), (0,600), (0,600), (0,648), (0,600), (0,851), (1,601), (1,854), (0,706), (0,636), (0,604), (0,638), (0,606), (0,857), (0,707), (0,647), (0,853), (0,761), (0,621), (0,609), (0,863), (0,613), (0,617), (0,867), (0,646), (1,610), (1,864), (1,614), (0,643), (1,762), (0,645), (1,618), (0,874), (0,871), (0,631), (0,633), (0,628), (1,623), (0,641), (0,859)]
    decide +kernel
private def g2_5 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8448, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 32736]]
private theorem ok2_5 : ∀ w ∈ g2_5, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 6), (5, 7), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_6 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 192, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 16076]]
private theorem ok2_6 : ∀ w ∈ g2_6, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (9, 6), (9, 10), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_7 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 19327],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 27511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 32736]]
private theorem ok2_7 : ∀ w ∈ g2_7, safe 4 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (0, 4), (5, 6), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_8 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4267, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24848, 29115]]
private theorem ok2_8 : ∀ w ∈ g2_8, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (9, 6), (9, 11), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_9 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 384, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 14063],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 29115, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 32152, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 32152, 32736]]
private theorem ok2_9 : ∀ w ∈ g2_9, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 6), (9, 6), (12, 3), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_10 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 27122]]
private theorem ok2_10 : ∀ w ∈ g2_10, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (5, 8), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_11 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 16076]]
private theorem ok2_11 : ∀ w ∈ g2_11, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 7), (12, 3), (12, 7), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_12 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 128],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12424, 29115]]
private theorem ok2_12 : ∀ w ∈ g2_12, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 4), (5, 6), (9, 6), (9, 10), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_13 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 23, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 19447]]
private theorem ok2_13 : ∀ w ∈ g2_13, safe 4 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 4), (5, 6), (5, 7), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_14 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 32152]]
private theorem ok2_14 : ∀ w ∈ g2_14, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (9, 6), (12, 3), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_15 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 64],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 27122]]
private theorem ok2_15 : ∀ w ∈ g2_15, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (5, 8), (12, 3), (12, 7), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_16 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 32250],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122, 32250]]
private theorem ok2_16 : ∀ w ∈ g2_16, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (5, 8), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_17 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 16, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 27122]]
private theorem ok2_17 : ∀ w ∈ g2_17, safe 4 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (5, 6), (5, 8), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_18 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 128],
  [0, 32767, 31, 482, 3652, 13448, 26896, 418, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 29115, 30139]]
private theorem ok2_18 : ∀ w ∈ g2_18, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (9, 6), (12, 3), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_19 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 29115, 29179]]
private theorem ok2_19 : ∀ w ∈ g2_19, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (0, 4), (5, 6), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_20 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 19319]]
private theorem ok2_20 : ∀ w ∈ g2_20, safe 4 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (0, 4), (12, 3), (12, 7), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_21 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 64, 32152]]
private theorem ok2_21 : ∀ w ∈ g2_21, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (12, 3), (12, 7), (12, 10), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_22 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 320, 28500]]
private theorem ok2_22 : ∀ w ∈ g2_22, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(0, 3), (9, 11), (12, 3), (12, 7), (12, 10)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_23 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 354, 19319]]
private theorem ok2_23 : ∀ w ∈ g2_23, safe 4 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (0, 4), (5, 6), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_24 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 615, 32152]]
private theorem ok2_24 : ∀ w ∈ g2_24, safe 4 w := by
  exact mixedGroup _ ![(5, 6), (5, 6), (5, 6), (5, 6), (5, 6), (5, 6)] ![(0, 3), (5, 6), (9, 6), (12, 3), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_25 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 19319]]
private theorem ok2_25 : ∀ w ∈ g2_25, safe 4 w := by
  exact mixedGroup _ ![(5, 6), (5, 6), (5, 6), (5, 6), (5, 6), (5, 6)] ![(0, 3), (0, 4), (5, 6), (9, 6), (12, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_26 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 18965],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 19319]]
private theorem ok2_26 : ∀ w ∈ g2_26, safe 4 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 4), (5, 6), (5, 7), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_27 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 28500]]
private theorem ok2_27 : ∀ w ∈ g2_27, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (9, 11), (12, 3), (12, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_28 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 32152, 32250]]
private theorem ok2_28 : ∀ w ∈ g2_28, safe 4 w := by
  exact mixedGroup _ ![(0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3)] ![(5, 6), (5, 7), (12, 3), (12, 7), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def g2_29 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 18704, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319, 32152]]
private theorem ok2_29 : ∀ w ∈ g2_29, safe 4 w := by
  exact mixedGroup _ ![(0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4)] ![(0, 3), (5, 6), (9, 6), (12, 3), (12, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def groups2 : List (List (List T)) := [g2_0, g2_1, g2_2, g2_3, g2_4, g2_5, g2_6, g2_7, g2_8, g2_9, g2_10, g2_11, g2_12, g2_13, g2_14, g2_15, g2_16, g2_17, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, g2_28, g2_29]
private theorem good2 (w : List T) (hw : w ∈ groups2.flatten) : safe 4 w := by
  obtain ⟨g,hu,h⟩ := List.mem_flatten.mp hw
  simp only [groups2,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok2_0 _ h
  · exact ok2_1 _ h
  · exact ok2_2 _ h
  · exact ok2_3 _ h
  · exact ok2_4 _ h
  · exact ok2_5 _ h
  · exact ok2_6 _ h
  · exact ok2_7 _ h
  · exact ok2_8 _ h
  · exact ok2_9 _ h
  · exact ok2_10 _ h
  · exact ok2_11 _ h
  · exact ok2_12 _ h
  · exact ok2_13 _ h
  · exact ok2_14 _ h
  · exact ok2_15 _ h
  · exact ok2_16 _ h
  · exact ok2_17 _ h
  · exact ok2_18 _ h
  · exact ok2_19 _ h
  · exact ok2_20 _ h
  · exact ok2_21 _ h
  · exact ok2_22 _ h
  · exact ok2_23 _ h
  · exact ok2_24 _ h
  · exact ok2_25 _ h
  · exact ok2_26 _ h
  · exact ok2_27 _ h
  · exact ok2_28 _ h
  · exact ok2_29 _ h
private def g1_0 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8],
  [0, 32767, 31, 482, 3652, 13448, 26896, 16],
  [0, 32767, 31, 482, 3652, 13448, 26896, 64],
  [0, 32767, 31, 482, 3652, 13448, 26896, 128],
  [0, 32767, 31, 482, 3652, 13448, 26896, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 32736]]
private theorem ok1_0 : ∀ w ∈ g1_0, safe 5 w := by
  intro w hu
  simp only [g1_0,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply stage good2 [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,15), (0,147), (0,0), (0,148), (0,92), (0,10), (0,105), (0,12), (0,14), (0,135), (0,6), (0,1), (0,186), (0,2), (0,106), (0,13), (0,3), (0,199), (0,4), (0,214), (0,5), (0,203), (0,8), (0,220), (0,9), (0,7), (0,11), (0,16)]
    decide +kernel
  · apply stage good2 [(0,92), (0,92), (0,92), (0,92), (0,92), (0,92), (0,92), (0,92), (0,100), (0,92), (0,150), (1,92), (1,150), (0,97), (0,233), (0,98), (1,99), (0,235), (0,94), (0,238), (0,187), (0,93), (0,234), (0,149), (0,99), (1,238), (1,187), (1,93), (1,234), (1,149), (0,240), (0,96), (0,244), (0,95), (0,151), (0,241)]
    decide +kernel
  · apply stage good2 [(0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (0,117), (0,105), (0,152), (1,105), (1,152), (0,233), (0,114), (0,18), (1,116), (0,246), (0,110), (0,108), (0,248), (0,215), (0,115), (0,109), (0,116), (1,108), (1,248), (1,215), (1,115), (1,109), (0,252), (0,112), (0,221), (0,113), (0,111), (0,118)]
    decide +kernel
  · apply stage good2 [(0,135), (0,135), (0,135), (0,135), (0,135), (0,135), (0,135), (0,135), (0,146), (0,135), (0,153), (1,135), (1,153), (0,235), (0,140), (0,246), (0,142), (0,136), (1,144), (0,257), (0,254), (0,236), (0,137), (0,247), (0,144), (1,254), (1,236), (1,137), (1,247), (0,262), (0,139), (0,263), (0,141), (0,138), (0,143), (0,145)]
    decide +kernel
  · apply stage good2 [(0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,34), (0,1), (0,155), (1,3), (0,156), (0,238), (0,28), (0,108), (0,29), (0,20), (0,32), (0,254), (0,25), (0,258), (0,21), (0,120), (0,31), (0,22), (0,200), (0,23), (0,216), (0,24), (0,204), (0,27), (0,222), (0,26), (0,30), (0,33)]
    decide +kernel
  · apply stage good2 [(0,2), (0,2), (0,2), (0,2), (0,2), (0,2), (0,2), (0,2), (0,49), (0,2), (0,158), (1,4), (0,159), (0,93), (0,43), (0,215), (0,45), (0,37), (0,47), (0,137), (0,40), (0,21), (0,189), (0,121), (0,46), (1,23), (0,202), (0,38), (0,217), (0,39), (0,205), (0,42), (0,223), (0,44), (0,41), (0,48)]
    decide +kernel
  · apply stage good2 [(0,147), (0,147), (0,147), (0,147), (0,147), (0,147), (0,147), (0,147), (0,179), (0,147), (1,148), (0,161), (0,150), (0,166), (0,152), (0,171), (0,178), (0,153), (0,162), (0,155), (0,167), (0,158), (0,172), (0,175), (1,156), (0,169), (1,159), (0,174), (1,154), (0,163), (0,170), (0,165), (0,176), (0,157), (0,168), (0,164), (0,160), (0,173), (0,177)]
    decide +kernel
  · apply stage good2 [(0,6), (0,6), (0,6), (0,6), (0,6), (0,6), (0,6), (0,6), (0,61), (0,6), (0,162), (1,6), (1,162), (0,94), (0,57), (0,110), (0,58), (0,17), (0,54), (1,60), (0,257), (0,25), (0,101), (0,40), (0,122), (0,60), (1,25), (1,101), (1,40), (1,122), (0,206), (0,56), (0,225), (0,52), (0,102), (0,55), (0,53), (0,123), (0,59)]
    decide +kernel
  · apply stage good2 [(0,7), (0,7), (0,7), (0,7), (0,7), (0,7), (0,7), (0,7), (0,69), (0,7), (0,164), (1,7), (1,164), (0,95), (0,66), (0,111), (0,67), (0,107), (0,64), (1,68), (0,138), (0,55), (0,26), (0,190), (0,41), (0,125), (0,36), (0,124), (0,68), (1,26), (1,190), (1,41), (1,125), (1,36), (1,124), (0,267), (0,65), (0,227), (0,62), (0,226)]
    decide +kernel
  · apply stage good2 [(0,8), (0,8), (0,8), (0,8), (0,8), (0,8), (0,8), (0,8), (0,76), (0,8), (0,165), (1,8), (1,165), (0,96), (0,72), (0,112), (0,74), (0,70), (1,75), (0,139), (0,56), (0,27), (0,191), (0,42), (0,126), (0,71), (0,75), (1,27), (1,191), (1,42), (1,126), (1,71), (0,207), (0,228), (0,65), (0,73)]
    decide +kernel
  · apply stage good2 [(0,10), (0,10), (0,10), (0,10), (0,10), (0,10), (0,10), (0,10), (0,82), (0,10), (0,166), (1,10), (1,166), (0,97), (0,114), (0,79), (1,80), (0,140), (0,57), (0,28), (0,259), (0,43), (0,129), (0,35), (0,260), (0,80), (1,28), (1,259), (1,43), (1,129), (1,35), (1,260), (0,208), (0,72), (0,229), (0,66), (0,127), (0,81), (0,78)]
    decide +kernel
  · apply stage good2 [(0,101), (0,101), (0,101), (0,101), (0,101), (0,101), (0,101), (0,101), (0,198), (0,186), (0,167), (1,199), (1,169), (0,187), (0,259), (0,248), (0,195), (0,188), (0,193), (0,197), (0,236), (0,101), (0,258), (0,189), (0,249), (0,196), (1,200), (0,237), (1,202), (0,270), (1,201), (0,194), (0,269), (0,191), (0,271), (0,190), (0,192), (0,250), (0,268)]
    decide +kernel
  · apply stage good2 [(0,170), (0,170), (0,170), (0,170), (0,170), (0,170), (0,170), (0,170), (0,213), (0,203), (0,170), (1,203), (1,170), (0,240), (0,208), (0,252), (0,210), (0,242), (0,209), (1,212), (0,262), (0,206), (0,204), (0,269), (0,205), (0,253), (0,265), (0,243), (0,212), (1,204), (1,269), (1,205), (1,253), (1,265), (1,243), (0,207), (0,274), (0,267), (0,273), (0,211)]
    decide +kernel
  · apply stage good2 [(0,12), (0,12), (0,12), (0,12), (0,12), (0,12), (0,12), (0,12), (0,86), (0,12), (0,171), (1,12), (1,171), (0,98), (0,79), (0,18), (1,84), (0,142), (0,58), (0,29), (0,195), (0,45), (0,180), (0,50), (0,181), (0,84), (1,29), (1,195), (1,45), (1,180), (1,50), (1,181), (0,210), (0,74), (0,182), (0,103), (0,85), (0,67), (0,63)]
    decide +kernel
  · apply stage good2 [(0,106), (0,106), (0,106), (0,106), (0,106), (0,106), (0,106), (0,106), (0,133), (0,106), (0,172), (1,214), (1,174), (0,234), (0,129), (0,115), (0,180), (0,119), (0,183), (0,132), (0,247), (0,122), (0,120), (0,249), (0,121), (0,131), (1,216), (1,270), (1,217), (0,184), (1,264), (0,130), (0,253), (0,126), (0,185), (0,128), (0,251), (0,125), (1,218)]
    decide +kernel
  · apply stage good2 [(0,13), (0,13), (0,13), (0,13), (0,13), (0,13), (0,13), (0,13), (0,90), (0,13), (0,175), (1,14), (1,178), (0,99), (0,80), (0,116), (0,84), (0,19), (0,87), (0,89), (0,144), (0,60), (0,31), (0,196), (0,46), (0,131), (0,255), (0,261), (1,32), (1,197), (1,47), (1,132), (0,212), (0,75), (0,230), (0,239), (0,256), (0,68), (0,219), (0,88)]
    decide +kernel
  · apply stage good2 [(0,176), (0,176), (0,176), (0,176), (0,176), (0,176), (0,176), (0,176), (0,232), (0,220), (0,176), (1,220), (1,176), (0,244), (0,229), (0,221), (0,182), (0,245), (0,231), (1,230), (0,263), (0,225), (0,222), (0,271), (0,223), (0,185), (0,224), (0,272), (0,230), (1,222), (1,271), (1,223), (1,185), (1,224), (1,272), (0,274), (0,228), (0,227), (0,266)]
    decide +kernel
  · apply stage good2 [(0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,179), (1,15), (1,179), (0,100), (0,82), (0,117), (0,86), (1,90), (0,146), (0,61), (0,34), (0,198), (0,49), (0,133), (0,51), (0,91), (0,90), (1,34), (1,198), (1,49), (1,133), (1,51), (1,91), (0,213), (0,76), (0,232), (0,77), (0,104), (0,69), (0,83), (0,134)]
    decide +kernel
private def groups1 : List (List (List T)) := [g1_0]
private theorem good1 (w : List T) (hw : w ∈ groups1.flatten) : safe 5 w := by
  obtain ⟨g,hu,h⟩ := List.mem_flatten.mp hw
  simp only [groups1,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl
  · exact ok1_0 _ h
private def g0_0 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896]]
private theorem ok0_0 : ∀ w ∈ g0_0, safe 6 w := by
  intro w hu
  simp only [g0_0,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl
  · apply stage good1 [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,17), (0,0), (0,6), (1,0), (1,6), (0,1), (0,10), (0,2), (0,13), (1,15), (0,3), (0,7), (0,4), (0,11), (0,5), (0,14), (0,15), (1,4), (1,11), (1,5), (1,14), (0,12), (0,9), (0,16), (0,8)]
    decide +kernel
private def groups0 : List (List (List T)) := [g0_0]
private theorem good0 (w : List T) (hw : w ∈ groups0.flatten) : safe 6 w := by
  obtain ⟨g,hu,h⟩ := List.mem_flatten.mp hw
  simp only [groups0,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl
  · exact ok0_0 _ h
private theorem s0_0 : safe 6 [0, 32767, 31, 482, 3652, 13448, 26896] := good0 _ (by decide +kernel)
private def samples : Fin 15 → Fin 5 × Fin 5 := ![(0,0), (0,1), (0,2), (0,3), (0,4), (1,1), (1,2), (1,3), (1,4), (2,2), (2,3), (2,4), (3,3), (3,4), (4,4)]
private def inputs (i : Fin 15) :=
  List.ofFn fun k : Fin 5 => decide (k = (samples i).1 ∨ k = (samples i).2)

private theorem tables (C : Circuit)
    (he : ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
      (266311 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :
    ∀ k, (C.gates.foldl step (ins.map (bit k))).getD C.output false = bit k target := by
  intro k
  have hi : ∀ i : Fin 15, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 15, (266311 : Nat).testBit
      (5 * min (samples i).1.val (samples i).2.val + max (samples i).1.val (samples i).2.val) = bit i target := by decide +kernel
  have h := he (samples k).1 (samples k).2
  change C.eval (inputs k) = _ at h
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using h

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5,
    C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
    (266311 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hg,hs,he⟩
  apply exclude C.gates C.output (fun g hm => hg g hm) ins [0,32767,31,482,3652,13448,26896] _ 6 hs s0_0 (tables C he)
  intro x hx
  simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  tauto

#print axioms generalLower

-- A seventh gate suffices on all 25 ordered pairs of pins.
def circuit : Circuit :=
  { gates := [⟨.or,[0,1]⟩, ⟨.and,[1,2]⟩, ⟨.or,[5,2]⟩, ⟨.or,[6,3]⟩,
              ⟨.and,[7,8]⟩, ⟨.or,[9,4]⟩, ⟨.not,[10]⟩], output := 11 }

theorem seven : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5,
    C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
    (266311 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms seven
end Graph266311
