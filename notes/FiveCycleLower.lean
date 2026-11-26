import PEqualNP.Defs.Represents

-- The gate semantics and safety induction adapt the Apache-2.0 proof credited in Mask53Exact.lean.
-- Lewis Watson and Nico Habets developed the earlier gate enumeration.
-- Here the fifteen inputs, cycle symmetries and support certificates apply to the five-cycle.
namespace FiveCycleLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 15
private def ins : List T := [31, 482, 3652, 13448, 26896, 0]
private def target : T := 1368
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

private def symm : Fin 10 → Fin 15 → Fin 15 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 2, 1, 4, 3, 9, 6, 11, 10, 5, 8, 7, 14, 13, 12], ![5, 1, 7, 6, 8, 0, 3, 2, 4, 12, 10, 13, 9, 11, 14], ![9, 2, 11, 6, 10, 0, 4, 1, 3, 14, 8, 13, 5, 7, 12], ![5, 7, 1, 8, 6, 12, 3, 13, 10, 0, 4, 2, 14, 11, 9], ![9, 11, 2, 10, 6, 14, 4, 13, 8, 0, 3, 1, 12, 7, 5], ![12, 7, 13, 3, 10, 5, 8, 1, 6, 14, 4, 11, 0, 2, 9], ![14, 11, 13, 4, 8, 9, 10, 2, 6, 12, 3, 7, 0, 1, 5], ![12, 13, 7, 10, 3, 14, 8, 11, 4, 5, 6, 1, 9, 2, 0], ![14, 13, 11, 8, 4, 12, 10, 7, 3, 9, 6, 2, 5, 1, 0]]
private theorem symmFacts : ∀ p, rename (symm p) target = target ∧ rename (symm p) 0 = 0 ∧ rename (symm p) (-1) = -1 := by decide +kernel
private def routeOK (w : List T) (next : List (List T)) :
    List T → List (Fin 10 × Nat) → Bool
  | [], [] => true
  | z :: zs, (p,j) :: rest =>
      decide (j < next.length) &&
      (z :: w).all (fun x => (next.getD j []).contains (rename (symm p) x)) &&
      routeOK w next zs rest
  | _, _ => false

private theorem routeSound {w : List T} {next : List (List T)} {n : Nat}
    (good : ∀ u ∈ next, safe n u) (zs : List T) (plan : List (Fin 10 × Nat))
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
    (plan : List (Fin 10 × Nat)) (h : routeOK w next (choices w) plan = true) : safe (n+1) w := by
  intro z hz
  exact routeSound good _ plan h z ((choice_iff _ _).2 hz)

private def eligibleA {n : Nat} (p : Fin n → Fin 15 × Fin 15) (w : List T) : Bool :=
  w.all (fun x => decide (∀ i j, Abs.sep x (p i) → Abs.sep x (p j) → i = j))
private def eligibleM {n : Nat} (p : Fin n → Fin 15 × Fin 15) (w : List T) : Bool :=
  w.all (fun x => decide (∀ i j, Mono.sep x (p i) → Mono.sep x (p j) → i = j))

private theorem absoluteGroup (ws : List (List T)) (p : Fin 5 → Fin 15 × Fin 15)
    (hp : ∀ i, Abs.sep target (p i)) (ht : ws.all (eligibleA p) = true) :
    ∀ w ∈ ws, safe 3 w := by
  intro w hw
  exact Abs.infeasible_safe 3 w (Abs.packing p hp ((List.all_eq_true.mp ht) w hw))

private theorem mixedGroup (ws : List (List T)) (p : Fin 5 → Fin 15 × Fin 15) (q : Fin 4 → Fin 15 × Fin 15)
    (hp : ∀ i, Mono.sep target (p i)) (hq : ∀ i, Abs.sep target (q i))
    (ht : ws.all (fun w => eligibleM p w && eligibleA q w) = true) :
    ∀ w ∈ ws, safe 3 w := by
  intro w hw
  have both : (eligibleM p w && eligibleA q w) = true := (List.all_eq_true.mp ht) w hw
  obtain ⟨hm,ha⟩ : eligibleM p w = true ∧ eligibleA q w = true := by simpa using both
  exact mixed (Abs.packing q hq ha) (Mono.infeasible_safe 3 w (Mono.packing p hp hm))

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def group0 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 6],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 128],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 486],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 13450],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 13452],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 32763],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 6, 3654],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 6, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 27, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 29, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 29, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 1026],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 1055],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 3654],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 27920],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 31743],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1028, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1604, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 2050],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 2079],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 2530],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 13450],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 30719],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2304, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3648, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 13450],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 29113],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5869, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871, 5887],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871, 7919],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 18704, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 19447],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 27511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26898, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26898, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32285, 32287],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32285, 32413],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32285, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32285, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 256, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 486, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 1152, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 13454],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 32761],
  [0, 32767, 31, 482, 3652, 13448, 26896, 25, 4070, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 4070, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 5871, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 13467, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 13471, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 19319, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 24848, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115, 29119],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115, 31163],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115, 32740],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 32736, 32740],
  [0, 32767, 31, 482, 3652, 13448, 26896, 608, 13471, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 1158, 4070, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 1766, 4070, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4064, 4070, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095, 16383],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 5887],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 7919],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 14063],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13471, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13471, 16383],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13471, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13471, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 28697, 28703],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 28697, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 28697, 29179],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 28697, 29849],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 28697, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 29115, 29119],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 29115, 29179],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 29115, 30139],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 29115, 31163],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 29115, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 29115, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 32736, 32738],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 32736, 32742],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 6127],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 6143],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 7919],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 7935],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 14063],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 14079],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919, 7935],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919, 14063],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919, 16111],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 19319, 24575],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 19319, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 19319, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 32285, 32511]]
private theorem proved0 : ∀ w ∈ group0, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (3, 12), (4, 0), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel)
private def group1 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 8],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 10],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 3654],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 13450],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 10, 13450],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 8, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 10, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 12, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 23, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 27, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 29, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 354, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 4078],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 32277],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 1604, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3648, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 4078],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 29107],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 4078],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5856, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 7919],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 14063],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319, 19447],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319, 20343],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319, 27511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32285, 32287],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32285, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 4070, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 14, 4070, 16366]]
private theorem proved1 : ∀ w ∈ group1, safe 3 w := by
  exact absoluteGroup _ ![(4, 0), (4, 14), (6, 5), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel)
private def group2 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 64]]
private theorem proved2 : ∀ w ∈ group2, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (3, 12), (4, 0), (8, 14), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group3 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 1024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 3654],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 159, 511, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 239, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 16383],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 28671],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5632, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 5887],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 6143],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 7919],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 19455],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 27511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 28671],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32287],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32528]]
private theorem proved3 : ∀ w ∈ group3, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (3, 7), (4, 0), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group4 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 13802, 29115]]
private theorem proved4 : ∀ w ∈ group4, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (3, 7), (4, 0), (6, 1), (8, 13)] ![(3, 0), (3, 12), (4, 0), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group5 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 16078],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 10240, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 16078],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 16691],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 32732],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 13471, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 16076, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 35, 16076, 32732],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16076, 16095]]
private theorem proved5 : ∀ w ∈ group5, safe 3 w := by
  exact absoluteGroup _ ![(3, 12), (4, 0), (6, 9), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group6 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3072, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115, 32152]]
private theorem proved6 : ∀ w ∈ group6, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 1), (6, 2), (8, 7), (10, 11)] ![(3, 0), (3, 12), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group7 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 16],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 24],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 498],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 13464],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 32751],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366, 32766]]
private theorem proved7 : ∀ w ∈ group7, safe 3 w := by
  exact absoluteGroup _ ![(3, 12), (6, 5), (6, 9), (8, 5), (10, 9)] (by decide +kernel) (by decide +kernel)
private def group8 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 64],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 72],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 95],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 32703],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 192, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 192, 16076]]
private theorem proved8 : ∀ w ∈ group8, safe 3 w := by
  exact absoluteGroup _ ![(4, 0), (4, 14), (8, 14), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group9 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32759]]
private theorem proved9 : ∀ w ∈ group9, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 0), (6, 1), (6, 2), (10, 2)] ![(4, 0), (4, 14), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group10 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 1024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2052, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 19327],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26898, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 1028, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471, 19296],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319, 19327],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 26907, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 26911, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5856, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 26911]]
private theorem proved10 : ∀ w ∈ group10, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (4, 0), (4, 14), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel)
private def group11 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 32759]]
private theorem proved11 : ∀ w ∈ group11, safe 3 w := by
  exact mixedGroup _ ![(4, 0), (4, 11), (6, 1), (6, 2), (10, 2)] ![(4, 0), (4, 11), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group12 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 10, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 10, 13802]]
private theorem proved12 : ∀ w ∈ group12, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 11), (6, 1), (8, 13)] ![(4, 0), (4, 14), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group13 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 12, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 12, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076, 32732],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32285, 32349],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 494, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 3660, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 5871, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 13452, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 16691],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 26908],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 32732],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 32755],
  [0, 32767, 31, 482, 3652, 13448, 26896, 14, 16076, 16366]]
private theorem proved13 : ∀ w ∈ group13, safe 3 w := by
  exact absoluteGroup _ ![(4, 0), (4, 14), (6, 9), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group14 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 27122]]
private theorem proved14 : ∀ w ∈ group14, safe 3 w := by
  exact absoluteGroup _ ![(4, 14), (6, 5), (8, 5), (8, 14), (10, 9)] (by decide +kernel) (by decide +kernel)
private def group15 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 320, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 28508],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 28500, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 28500, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 28500, 32759]]
private theorem proved15 : ∀ w ∈ group15, safe 3 w := by
  exact mixedGroup _ ![(4, 2), (4, 11), (6, 2), (10, 2), (10, 13)] ![(4, 0), (4, 14), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group16 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 32152]]
private theorem proved16 : ∀ w ∈ group16, safe 3 w := by
  exact mixedGroup _ ![(4, 11), (6, 1), (6, 2), (8, 7), (10, 11)] ![(4, 0), (4, 14), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group17 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 15, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 495, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 1604, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 3663, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 4070, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5256, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 6127],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 7919],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 13455],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 14063],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 32752],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 32736, 32752]]
private theorem proved17 : ∀ w ∈ group17, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (4, 14), (6, 5), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel)
private def group18 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 18],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 498],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 1024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 3654],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 3668],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 8192],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 13450],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 13464],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 32751],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 18, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26640, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 5887],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2530, 4070, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 6127],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 8175],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13471, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919, 8175]]
private theorem proved18 : ∀ w ∈ group18, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (3, 12), (6, 5), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel)
private def group19 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 511]]
private theorem proved19 : ∀ w ∈ group19, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (6, 1), (6, 2), (8, 1)] ![(3, 0), (3, 7), (6, 5), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group20 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 3679]]
private theorem proved20 : ∀ w ∈ group20, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (6, 1), (6, 2), (8, 1)] ![(3, 0), (3, 12), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group21 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 13802]]
private theorem proved21 : ∀ w ∈ group21, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (3, 7), (6, 1), (8, 1), (8, 13)] ![(3, 0), (3, 12), (6, 5), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group22 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 16076]]
private theorem proved22 : ∀ w ∈ group22, safe 3 w := by
  exact absoluteGroup _ ![(3, 12), (6, 9), (8, 5), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group23 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 18, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5645, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 27122, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5645, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5645, 5871, 32285]]
private theorem proved23 : ∀ w ∈ group23, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (3, 12), (6, 5), (8, 5), (8, 14)] (by decide +kernel) (by decide +kernel)
private def group24 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16, 28500]]
private theorem proved24 : ∀ w ∈ group24, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 2), (6, 2), (10, 13)] ![(3, 0), (3, 12), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group25 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 20, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 28502],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 28662]]
private theorem proved25 : ∀ w ∈ group25, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 2), (6, 2), (10, 13)] ![(3, 0), (3, 12), (4, 2), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group26 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 23, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 20343],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 23, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 5887],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16076, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16076, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366, 16383],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 32736, 32744]]
private theorem proved26 : ∀ w ∈ group26, safe 3 w := by
  exact absoluteGroup _ ![(3, 12), (4, 0), (6, 5), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel)
private def group27 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 24, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 4070, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 13464, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 29115, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 32152, 32743]]
private theorem proved27 : ∀ w ∈ group27, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 1), (6, 2), (8, 7), (10, 11)] ![(3, 12), (6, 5), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group28 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 68, 511]]
private theorem proved28 : ∀ w ∈ group28, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 2), (10, 7)] ![(3, 0), (3, 7), (4, 0), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group29 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 511, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 32256]]
private theorem proved29 : ∀ w ∈ group29, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (4, 0), (6, 2), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group30 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 19447],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32413]]
private theorem proved30 : ∀ w ∈ group30, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (3, 12), (4, 0), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group31 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 204, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 16383],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 16691],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 32256]]
private theorem proved31 : ∀ w ∈ group31, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 0), (6, 2), (6, 7)] ![(3, 7), (4, 0), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group32 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 26898]]
private theorem proved32 : ∀ w ∈ group32, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 1), (6, 1), (6, 2)] ![(3, 0), (3, 7), (4, 0), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group33 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 19327],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32159],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 32285]]
private theorem proved33 : ∀ w ∈ group33, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (4, 0), (4, 14), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group34 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 3679, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 506, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 511, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 340, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 615, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500, 28671]]
private theorem proved34 : ∀ w ∈ group34, safe 3 w := by
  intro w hu
  simp only [group34,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (apply three_safe; decide +kernel)
private def group35 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511, 32765]]
private theorem proved35 : ∀ w ∈ group35, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 2), (6, 5)] ![(3, 0), (3, 7), (4, 0), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group36 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 615, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 7, 615, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 615, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 32152, 32159]]
private theorem proved36 : ∀ w ∈ group36, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 1), (6, 2), (8, 7), (10, 11)] ![(3, 12), (6, 5), (6, 9), (8, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group37 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 32765]]
private theorem proved37 : ∀ w ∈ group37, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 0), (4, 11), (6, 1), (6, 2)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group38 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2628, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32285, 32349],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115, 30139],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13471, 16076]]
private theorem proved38 : ∀ w ∈ group38, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (3, 12), (4, 0), (6, 9), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group39 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070, 28500]]
private theorem proved39 : ∀ w ∈ group39, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 2), (6, 1), (6, 2)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group40 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1032, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 29088]]
private theorem proved40 : ∀ w ∈ group40, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 0), (4, 11), (6, 1), (6, 2)] ![(3, 0), (4, 0), (4, 11), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group41 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2064, 3679]]
private theorem proved41 : ∀ w ∈ group41, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 11), (6, 1), (6, 2), (8, 1)] ![(3, 0), (3, 12), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group42 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2112, 27122]]
private theorem proved42 : ∀ w ∈ group42, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (3, 12), (8, 5), (8, 14), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group43 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3588, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32285, 32541],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 64, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115, 29179]]
private theorem proved43 : ∀ w ∈ group43, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (3, 12), (4, 0), (6, 5), (8, 14)] (by decide +kernel) (by decide +kernel)
private def group44 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654, 28502]]
private theorem proved44 : ∀ w ∈ group44, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 1), (6, 1), (6, 2)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group45 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 3679, 29115]]
private theorem proved45 : ∀ w ∈ group45, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group46 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 16076]]
private theorem proved46 : ∀ w ∈ group46, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (4, 0), (4, 11), (6, 1), (6, 2)] ![(3, 12), (4, 0), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group47 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 26898]]
private theorem proved47 : ∀ w ∈ group47, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 1), (4, 11), (6, 1), (6, 2)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group48 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 27122]]
private theorem proved48 : ∀ w ∈ group48, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 1), (4, 11), (6, 1), (6, 11)] ![(3, 0), (3, 12), (8, 5), (8, 14)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group49 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 28500]]
private theorem proved49 : ∀ w ∈ group49, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 2), (4, 11), (6, 1), (6, 2)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group50 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679, 32736]]
private theorem proved50 : ∀ w ∈ group50, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 0), (4, 11), (6, 1), (6, 9)] ![(3, 0), (4, 0), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group51 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871, 28500]]
private theorem proved51 : ∀ w ∈ group51, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 2), (6, 1), (6, 2)] ![(3, 0), (3, 12), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group52 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076, 28500]]
private theorem proved52 : ∀ w ∈ group52, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 2), (6, 2), (10, 13)] ![(3, 12), (4, 0), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group53 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 32765]]
private theorem proved53 : ∀ w ∈ group53, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 2), (6, 2), (10, 13)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group54 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319, 32152]]
private theorem proved54 : ∀ w ∈ group54, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 0), (6, 1), (6, 2), (10, 11)] ![(3, 12), (4, 0), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group55 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26898, 28500]]
private theorem proved55 : ∀ w ∈ group55, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 1), (6, 2), (10, 13)] ![(3, 0), (3, 12), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group56 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26898, 28502]]
private theorem proved56 : ∀ w ∈ group56, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 1), (6, 1), (6, 2)] ![(3, 0), (3, 12), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group57 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 226, 5871]]
private theorem proved57 : ∀ w ∈ group57, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (4, 0), (4, 14), (6, 5), (8, 14)] (by decide +kernel) (by decide +kernel)
private def group58 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 28511]]
private theorem proved58 : ∀ w ∈ group58, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 13), (4, 2), (6, 2), (10, 13)] ![(3, 0), (4, 0), (4, 14), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group59 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911, 32152]]
private theorem proved59 : ∀ w ∈ group59, safe 3 w := by
  exact mixedGroup _ ![(3, 13), (4, 0), (6, 1), (6, 2), (10, 11)] ![(3, 0), (4, 14), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group60 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 32152]]
private theorem proved60 : ∀ w ∈ group60, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 2), (6, 2), (10, 11), (10, 13)] ![(3, 0), (3, 12), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group61 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 32285]]
private theorem proved61 : ∀ w ∈ group61, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 12), (4, 2), (6, 2), (10, 13)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group62 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 32732],
  [0, 32767, 31, 482, 3652, 13448, 26896, 35, 28500, 32732]]
private theorem proved62 : ∀ w ∈ group62, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 2), (6, 2), (10, 13)] ![(3, 12), (4, 2), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group63 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500, 32736]]
private theorem proved63 : ∀ w ∈ group63, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 2), (6, 9), (10, 13)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group64 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070, 13802]]
private theorem proved64 : ∀ w ∈ group64, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (3, 12), (4, 0), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group65 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 15, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 24, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 6127]]
private theorem proved65 : ∀ w ∈ group65, safe 3 w := by
  exact absoluteGroup _ ![(4, 14), (6, 5), (6, 9), (8, 5), (10, 9)] (by decide +kernel) (by decide +kernel)
private def group66 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 64]]
private theorem proved66 : ∀ w ∈ group66, safe 3 w := by
  exact absoluteGroup _ ![(3, 12), (8, 5), (8, 14), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group67 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 511]]
private theorem proved67 : ∀ w ∈ group67, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 1), (6, 2), (8, 1), (10, 2)] ![(6, 2), (6, 5), (8, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group68 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16, 13802]]
private theorem proved68 : ∀ w ∈ group68, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 11), (6, 1), (8, 1), (8, 13)] ![(3, 12), (6, 5), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group69 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 18, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26, 27122, 32250]]
private theorem proved69 : ∀ w ∈ group69, safe 3 w := by
  exact absoluteGroup _ ![(3, 12), (6, 5), (8, 5), (8, 14), (10, 9)] (by decide +kernel) (by decide +kernel)
private def group70 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 20, 28500]]
private theorem proved70 : ∀ w ∈ group70, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 2), (6, 2), (10, 2), (10, 13)] ![(3, 12), (4, 2), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group71 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 24, 32152]]
private theorem proved71 : ∀ w ∈ group71, safe 3 w := by
  exact mixedGroup _ ![(4, 11), (6, 1), (6, 2), (8, 7), (10, 11)] ![(4, 14), (6, 5), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group72 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 68, 511]]
private theorem proved72 : ∀ w ∈ group72, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 0), (6, 2), (10, 2), (10, 7)] ![(4, 0), (4, 14), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group73 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 66, 3679]]
private theorem proved73 : ∀ w ∈ group73, safe 3 w := by
  exact mixedGroup _ ![(4, 0), (4, 11), (6, 1), (8, 11), (10, 2)] ![(4, 0), (4, 11), (8, 14), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group74 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 226, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3588, 32285]]
private theorem proved74 : ∀ w ∈ group74, safe 3 w := by
  exact absoluteGroup _ ![(4, 0), (4, 14), (6, 5), (8, 14), (10, 9)] (by decide +kernel) (by decide +kernel)
private def group75 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64, 28500]]
private theorem proved75 : ∀ w ∈ group75, safe 3 w := by
  exact mixedGroup _ ![(4, 2), (4, 11), (8, 11), (10, 2), (10, 13)] ![(4, 0), (4, 14), (8, 14), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group76 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 272, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 4095]]
private theorem proved76 : ∀ w ∈ group76, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 0), (6, 1), (6, 2), (10, 2)] ![(4, 0), (6, 2), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group77 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 13471]]
private theorem proved77 : ∀ w ∈ group77, safe 3 w := by
  exact mixedGroup _ ![(4, 0), (4, 13), (6, 1), (6, 2), (10, 2)] ![(4, 0), (4, 13), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group78 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 26904],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32285]]
private theorem proved78 : ∀ w ∈ group78, safe 3 w := by
  exact mixedGroup _ ![(4, 0), (4, 11), (6, 1), (6, 2), (10, 2)] ![(4, 0), (4, 14), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group79 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 3679]]
private theorem proved79 : ∀ w ∈ group79, safe 3 w := by
  exact mixedGroup _ ![(4, 0), (4, 11), (6, 1), (6, 2), (10, 2)] ![(4, 0), (6, 1), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group80 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 13471]]
private theorem proved80 : ∀ w ∈ group80, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 0), (6, 1), (6, 2), (10, 2)] ![(3, 0), (4, 0), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group81 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 13802]]
private theorem proved81 : ∀ w ∈ group81, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 11), (6, 1), (6, 2)] ![(4, 0), (4, 14), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group82 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 13823]]
private theorem proved82 : ∀ w ∈ group82, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 0), (6, 1), (6, 2), (10, 2)] ![(3, 0), (4, 0), (6, 2), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group83 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 16076]]
private theorem proved83 : ∀ w ∈ group83, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 0), (6, 2), (6, 7), (10, 2)] ![(4, 0), (4, 14), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group84 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 27122]]
private theorem proved84 : ∀ w ∈ group84, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 1), (6, 1), (6, 2), (10, 2)] ![(4, 14), (6, 5), (8, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group85 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32256]]
private theorem proved85 : ∀ w ∈ group85, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 0), (6, 1), (6, 2), (10, 9)] ![(4, 0), (6, 2), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group86 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511, 32736]]
private theorem proved86 : ∀ w ∈ group86, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (4, 0), (6, 2), (6, 5), (10, 9)] ![(4, 0), (6, 5), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group87 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 615, 32152]]
private theorem proved87 : ∀ w ∈ group87, safe 3 w := by
  exact mixedGroup _ ![(4, 11), (6, 1), (6, 2), (8, 7), (10, 11)] ![(4, 14), (6, 5), (6, 9), (8, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group88 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 2064, 3679]]
private theorem proved88 : ∀ w ∈ group88, safe 3 w := by
  exact mixedGroup _ ![(4, 11), (6, 1), (6, 2), (8, 1), (10, 2)] ![(4, 11), (6, 9), (8, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group89 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 2112, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 27122]]
private theorem proved89 : ∀ w ∈ group89, safe 3 w := by
  exact absoluteGroup _ ![(4, 14), (8, 5), (8, 14), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group90 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 2628, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471, 16095]]
private theorem proved90 : ∀ w ∈ group90, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (4, 0), (4, 14), (6, 9), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group91 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 29115]]
private theorem proved91 : ∀ w ∈ group91, safe 3 w := by
  exact mixedGroup _ ![(4, 0), (4, 11), (6, 1), (6, 2), (10, 2)] ![(4, 0), (4, 14), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group92 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 13471]]
private theorem proved92 : ∀ w ∈ group92, safe 3 w := by
  exact mixedGroup _ ![(4, 0), (4, 11), (6, 1), (6, 2), (10, 2)] ![(3, 0), (4, 0), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group93 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 27122]]
private theorem proved93 : ∀ w ∈ group93, safe 3 w := by
  exact mixedGroup _ ![(4, 1), (4, 11), (6, 1), (6, 11), (10, 2)] ![(4, 11), (8, 5), (8, 14), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group94 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 28500]]
private theorem proved94 : ∀ w ∈ group94, safe 3 w := by
  exact mixedGroup _ ![(4, 2), (4, 11), (6, 1), (6, 2), (10, 2)] ![(4, 0), (4, 11), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group95 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679, 32736]]
private theorem proved95 : ∀ w ∈ group95, safe 3 w := by
  exact mixedGroup _ ![(4, 0), (4, 11), (6, 1), (6, 9), (10, 9)] ![(4, 0), (6, 5), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group96 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070, 28500]]
private theorem proved96 : ∀ w ∈ group96, safe 3 w := by
  exact mixedGroup _ ![(4, 2), (4, 11), (6, 1), (6, 2), (10, 2)] ![(4, 0), (4, 14), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group97 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4267, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 28500, 28508],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 28500, 28662]]
private theorem proved97 : ∀ w ∈ group97, safe 3 w := by
  exact mixedGroup _ ![(4, 2), (4, 11), (6, 2), (10, 2), (10, 13)] ![(4, 2), (4, 14), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group98 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871, 28500]]
private theorem proved98 : ∀ w ∈ group98, safe 3 w := by
  exact mixedGroup _ ![(4, 2), (4, 11), (6, 1), (6, 2), (10, 2)] ![(4, 14), (6, 5), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group99 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471, 13823]]
private theorem proved99 : ∀ w ∈ group99, safe 3 w := by
  exact mixedGroup _ ![(4, 0), (4, 13), (6, 1), (6, 2), (10, 2)] ![(3, 0), (4, 0), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group100 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471, 28500]]
private theorem proved100 : ∀ w ∈ group100, safe 3 w := by
  exact mixedGroup _ ![(4, 2), (4, 13), (6, 2), (10, 2), (10, 13)] ![(3, 0), (4, 0), (4, 14), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group101 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 490, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 1088, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 3662, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 5871, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 8448, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13450, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 18965],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 14, 13802, 16366]]
private theorem proved101 : ∀ w ∈ group101, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 11), (6, 1), (8, 13)] ![(3, 1), (4, 0), (4, 14), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group102 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 511, 13802]]
private theorem proved102 : ∀ w ∈ group102, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 1), (4, 0), (4, 14), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group103 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 4070, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 19319]]
private theorem proved103 : ∀ w ∈ group103, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 11), (6, 1), (6, 2)] ![(4, 0), (4, 14), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group104 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13471, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 13823]]
private theorem proved104 : ∀ w ∈ group104, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 13), (6, 1), (8, 13)] ![(3, 1), (3, 12), (4, 0), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group105 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 16076]]
private theorem proved105 : ∀ w ∈ group105, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 11), (6, 7), (8, 13)] ![(4, 0), (4, 14), (6, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group106 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 26906]]
private theorem proved106 : ∀ w ∈ group106, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 1), (4, 11), (6, 1), (8, 13)] ![(3, 1), (4, 0), (4, 14), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group107 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 27122]]
private theorem proved107 : ∀ w ∈ group107, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 1), (4, 11), (6, 1), (8, 13)] ![(4, 14), (6, 5), (8, 5), (8, 13)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group108 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 29115]]
private theorem proved108 : ∀ w ∈ group108, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 13), (6, 1), (8, 13)] ![(3, 1), (4, 0), (4, 14), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group109 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 32152]]
private theorem proved109 : ∀ w ∈ group109, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 11), (6, 1), (8, 7), (8, 13)] ![(4, 0), (4, 14), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group110 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 32250]]
private theorem proved110 : ∀ w ∈ group110, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 1), (4, 11), (6, 1), (8, 13)] ![(3, 1), (4, 14), (6, 5), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group111 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 32285]]
private theorem proved111 : ∀ w ∈ group111, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 11), (6, 1), (8, 13)] ![(4, 0), (4, 14), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group112 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802, 32757]]
private theorem proved112 : ∀ w ∈ group112, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 11), (6, 5), (8, 13)] ![(3, 1), (4, 0), (4, 14), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group113 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 11, 4267, 28500]]
private theorem proved113 : ∀ w ∈ group113, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 2), (4, 11), (6, 2), (10, 13)] ![(3, 0), (4, 2), (4, 14), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group114 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 26911]]
private theorem proved114 : ∀ w ∈ group114, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 0), (6, 2), (6, 7)] ![(4, 0), (4, 14), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group115 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 3679, 16076]]
private theorem proved115 : ∀ w ∈ group115, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (4, 0), (4, 11), (6, 1), (6, 2)] ![(4, 0), (4, 14), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group116 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 13802, 16076]]
private theorem proved116 : ∀ w ∈ group116, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (4, 0), (4, 11), (6, 7), (8, 13)] ![(4, 0), (4, 14), (6, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group117 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 28500]]
private theorem proved117 : ∀ w ∈ group117, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (4, 2), (4, 11), (6, 2), (10, 13)] ![(4, 0), (4, 14), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group118 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076, 32152]]
private theorem proved118 : ∀ w ∈ group118, safe 3 w := by
  exact mixedGroup _ ![(4, 11), (6, 2), (6, 7), (8, 7), (10, 11)] ![(4, 0), (4, 14), (6, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group119 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 13, 5645, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 27122]]
private theorem proved119 : ∀ w ∈ group119, safe 3 w := by
  exact absoluteGroup _ ![(3, 0), (4, 14), (6, 5), (8, 5), (8, 14)] (by decide +kernel) (by decide +kernel)
private def group120 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 511, 5871]]
private theorem proved120 : ∀ w ∈ group120, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (4, 14), (6, 5), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group121 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 3679, 5871]]
private theorem proved121 : ∀ w ∈ group121, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 0), (4, 11), (6, 1), (6, 2)] ![(3, 0), (4, 11), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group122 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 13802]]
private theorem proved122 : ∀ w ∈ group122, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (4, 0), (4, 11), (6, 1), (8, 13)] ![(3, 0), (4, 14), (6, 5), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group123 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 16076]]
private theorem proved123 : ∀ w ∈ group123, safe 3 w := by
  exact absoluteGroup _ ![(4, 14), (6, 9), (8, 5), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel)
private def group124 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 28500]]
private theorem proved124 : ∀ w ∈ group124, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 2), (4, 11), (6, 1), (6, 2)] ![(3, 0), (4, 14), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group125 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871, 32152]]
private theorem proved125 : ∀ w ∈ group125, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (4, 11), (6, 1), (6, 2), (8, 7)] ![(3, 0), (4, 14), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group126 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 5871, 32152]]
private theorem proved126 : ∀ w ∈ group126, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 1), (6, 2), (8, 7), (10, 2)] ![(3, 12), (6, 5), (6, 9), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group127 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 13471, 32152]]
private theorem proved127 : ∀ w ∈ group127, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 1), (6, 2), (8, 7), (10, 2)] ![(3, 12), (6, 5), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group128 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 13802, 32152]]
private theorem proved128 : ∀ w ∈ group128, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 1), (8, 7), (8, 13), (10, 11)] ![(3, 12), (6, 5), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group129 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 16076, 32152]]
private theorem proved129 : ∀ w ∈ group129, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 2), (6, 7), (8, 7), (10, 11)] ![(3, 12), (6, 9), (8, 5), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group130 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 32152, 32250],
  [0, 32767, 31, 482, 3652, 13448, 26896, 26, 32152, 32250]]
private theorem proved130 : ∀ w ∈ group130, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 1), (6, 11), (8, 7), (10, 11)] ![(3, 12), (6, 5), (8, 5), (8, 14)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group131 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 32152, 32736]]
private theorem proved131 : ∀ w ∈ group131, safe 3 w := by
  exact mixedGroup _ ![(3, 7), (6, 5), (6, 9), (8, 7), (10, 11)] ![(3, 12), (6, 5), (6, 9), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group132 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 26, 13802, 32250]]
private theorem proved132 : ∀ w ∈ group132, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (3, 7), (4, 1), (6, 1), (8, 13)] ![(3, 1), (3, 12), (6, 5), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group133 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 507, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 287, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 26911]]
private theorem proved133 : ∀ w ∈ group133, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (4, 0), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group134 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 28500, 29115]]
private theorem proved134 : ∀ w ∈ group134, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 2), (10, 13)] ![(3, 0), (3, 12), (4, 0), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group135 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 95, 511, 3679]]
private theorem proved135 : ∀ w ∈ group135, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (4, 0), (6, 1), (8, 14)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group136 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 375, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 20343]]
private theorem proved136 : ∀ w ∈ group136, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 7), (4, 0), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group137 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 13823],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 16095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 29088]]
private theorem proved137 : ∀ w ∈ group137, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (4, 0), (6, 1), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group138 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 16076]]
private theorem proved138 : ∀ w ∈ group138, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 0), (6, 1), (6, 2)] ![(4, 0), (6, 2), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group139 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679, 32736]]
private theorem proved139 : ∀ w ∈ group139, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 9)] ![(3, 0), (4, 0), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group140 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 16076]]
private theorem proved140 : ∀ w ∈ group140, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 0), (6, 2), (6, 7)] ![(3, 12), (4, 0), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group141 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 16366]]
private theorem proved141 : ∀ w ∈ group141, safe 3 w := by
  exact mixedGroup _ ![(3, 1), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 12), (4, 0), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group142 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 28662],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5645, 27122],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 27122]]
private theorem proved142 : ∀ w ∈ group142, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 1), (6, 1), (6, 2)] ![(3, 0), (3, 12), (6, 5), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group143 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32736]]
private theorem proved143 : ∀ w ∈ group143, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 2), (6, 5)] ![(3, 0), (4, 0), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group144 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 16076]]
private theorem proved144 : ∀ w ∈ group144, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 0), (6, 2), (6, 7)] ![(3, 7), (4, 0), (6, 5), (10, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group145 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095, 27122]]
private theorem proved145 : ∀ w ∈ group145, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 1), (6, 1), (6, 2)] ![(3, 0), (3, 7), (6, 5), (8, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group146 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 19319]]
private theorem proved146 : ∀ w ∈ group146, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 0), (6, 2), (10, 7)] ![(3, 7), (4, 0), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group147 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 32285]]
private theorem proved147 : ∀ w ∈ group147, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 0), (6, 2), (6, 7)] ![(3, 12), (4, 0), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group148 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076, 32732]]
private theorem proved148 : ∀ w ∈ group148, safe 3 w := by
  exact mixedGroup _ ![(3, 2), (3, 7), (4, 2), (6, 2), (6, 7)] ![(3, 7), (4, 0), (10, 9), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group149 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 27122]]
private theorem proved149 : ∀ w ∈ group149, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 1), (6, 1), (6, 2)] ![(3, 0), (4, 0), (4, 14), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group150 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 28511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911, 32285]]
private theorem proved150 : ∀ w ∈ group150, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 13), (4, 0), (6, 1), (6, 2)] ![(3, 0), (4, 0), (4, 14), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group151 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256, 32324]]
private theorem proved151 : ∀ w ∈ group151, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 2), (10, 12)] ![(3, 0), (3, 7), (4, 0), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group152 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32287],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32541]]
private theorem proved152 : ∀ w ∈ group152, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 12), (4, 0), (6, 1), (6, 2)] ![(3, 0), (3, 12), (4, 0), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group153 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32349]]
private theorem proved153 : ∀ w ∈ group153, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 12), (4, 0), (6, 2), (10, 12)] ![(3, 0), (3, 12), (4, 0), (10, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group154 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285, 32736]]
private theorem proved154 : ∀ w ∈ group154, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 2), (6, 5)] ![(3, 0), (3, 12), (4, 0), (6, 5)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def group155 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 615, 5871, 19319]]
private theorem proved155 : ∀ w ∈ group155, safe 3 w := by
  exact mixedGroup _ ![(3, 0), (3, 7), (4, 0), (6, 1), (6, 2)] ![(3, 0), (3, 12), (6, 5), (6, 9)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def groups : List (List (List T)) := [group0, group1, group2, group3, group4, group5, group6, group7, group8, group9, group10, group11, group12, group13, group14, group15, group16, group17, group18, group19, group20, group21, group22, group23, group24, group25, group26, group27, group28, group29, group30, group31, group32, group33, group34, group35, group36, group37, group38, group39, group40, group41, group42, group43, group44, group45, group46, group47, group48, group49, group50, group51, group52, group53, group54, group55, group56, group57, group58, group59, group60, group61, group62, group63, group64, group65, group66, group67, group68, group69, group70, group71, group72, group73, group74, group75, group76, group77, group78, group79, group80, group81, group82, group83, group84, group85, group86, group87, group88, group89, group90, group91, group92, group93, group94, group95, group96, group97, group98, group99, group100, group101, group102, group103, group104, group105, group106, group107, group108, group109, group110, group111, group112, group113, group114, group115, group116, group117, group118, group119, group120, group121, group122, group123, group124, group125, group126, group127, group128, group129, group130, group131, group132, group133, group134, group135, group136, group137, group138, group139, group140, group141, group142, group143, group144, group145, group146, group147, group148, group149, group150, group151, group152, group153, group154, group155]
private def states3 := groups.flatten
private theorem good3 (w : List T) (hw : w ∈ states3) : safe 3 w := by
  obtain ⟨g,hu,h⟩ := List.mem_flatten.mp hw
  simp only [groups,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact proved0 _ h
  · exact proved1 _ h
  · exact proved2 _ h
  · exact proved3 _ h
  · exact proved4 _ h
  · exact proved5 _ h
  · exact proved6 _ h
  · exact proved7 _ h
  · exact proved8 _ h
  · exact proved9 _ h
  · exact proved10 _ h
  · exact proved11 _ h
  · exact proved12 _ h
  · exact proved13 _ h
  · exact proved14 _ h
  · exact proved15 _ h
  · exact proved16 _ h
  · exact proved17 _ h
  · exact proved18 _ h
  · exact proved19 _ h
  · exact proved20 _ h
  · exact proved21 _ h
  · exact proved22 _ h
  · exact proved23 _ h
  · exact proved24 _ h
  · exact proved25 _ h
  · exact proved26 _ h
  · exact proved27 _ h
  · exact proved28 _ h
  · exact proved29 _ h
  · exact proved30 _ h
  · exact proved31 _ h
  · exact proved32 _ h
  · exact proved33 _ h
  · exact proved34 _ h
  · exact proved35 _ h
  · exact proved36 _ h
  · exact proved37 _ h
  · exact proved38 _ h
  · exact proved39 _ h
  · exact proved40 _ h
  · exact proved41 _ h
  · exact proved42 _ h
  · exact proved43 _ h
  · exact proved44 _ h
  · exact proved45 _ h
  · exact proved46 _ h
  · exact proved47 _ h
  · exact proved48 _ h
  · exact proved49 _ h
  · exact proved50 _ h
  · exact proved51 _ h
  · exact proved52 _ h
  · exact proved53 _ h
  · exact proved54 _ h
  · exact proved55 _ h
  · exact proved56 _ h
  · exact proved57 _ h
  · exact proved58 _ h
  · exact proved59 _ h
  · exact proved60 _ h
  · exact proved61 _ h
  · exact proved62 _ h
  · exact proved63 _ h
  · exact proved64 _ h
  · exact proved65 _ h
  · exact proved66 _ h
  · exact proved67 _ h
  · exact proved68 _ h
  · exact proved69 _ h
  · exact proved70 _ h
  · exact proved71 _ h
  · exact proved72 _ h
  · exact proved73 _ h
  · exact proved74 _ h
  · exact proved75 _ h
  · exact proved76 _ h
  · exact proved77 _ h
  · exact proved78 _ h
  · exact proved79 _ h
  · exact proved80 _ h
  · exact proved81 _ h
  · exact proved82 _ h
  · exact proved83 _ h
  · exact proved84 _ h
  · exact proved85 _ h
  · exact proved86 _ h
  · exact proved87 _ h
  · exact proved88 _ h
  · exact proved89 _ h
  · exact proved90 _ h
  · exact proved91 _ h
  · exact proved92 _ h
  · exact proved93 _ h
  · exact proved94 _ h
  · exact proved95 _ h
  · exact proved96 _ h
  · exact proved97 _ h
  · exact proved98 _ h
  · exact proved99 _ h
  · exact proved100 _ h
  · exact proved101 _ h
  · exact proved102 _ h
  · exact proved103 _ h
  · exact proved104 _ h
  · exact proved105 _ h
  · exact proved106 _ h
  · exact proved107 _ h
  · exact proved108 _ h
  · exact proved109 _ h
  · exact proved110 _ h
  · exact proved111 _ h
  · exact proved112 _ h
  · exact proved113 _ h
  · exact proved114 _ h
  · exact proved115 _ h
  · exact proved116 _ h
  · exact proved117 _ h
  · exact proved118 _ h
  · exact proved119 _ h
  · exact proved120 _ h
  · exact proved121 _ h
  · exact proved122 _ h
  · exact proved123 _ h
  · exact proved124 _ h
  · exact proved125 _ h
  · exact proved126 _ h
  · exact proved127 _ h
  · exact proved128 _ h
  · exact proved129 _ h
  · exact proved130 _ h
  · exact proved131 _ h
  · exact proved132 _ h
  · exact proved133 _ h
  · exact proved134 _ h
  · exact proved135 _ h
  · exact proved136 _ h
  · exact proved137 _ h
  · exact proved138 _ h
  · exact proved139 _ h
  · exact proved140 _ h
  · exact proved141 _ h
  · exact proved142 _ h
  · exact proved143 _ h
  · exact proved144 _ h
  · exact proved145 _ h
  · exact proved146 _ h
  · exact proved147 _ h
  · exact proved148 _ h
  · exact proved149 _ h
  · exact proved150 _ h
  · exact proved151 _ h
  · exact proved152 _ h
  · exact proved153 _ h
  · exact proved154 _ h
  · exact proved155 _ h
private def states1 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871]
]
private def states2 : List (List T) := [
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26898],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32765],
  [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32759],
  [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802],
  [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 24, 32152],
  [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256],
  [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13471],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16076],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 28697],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 29115],
  [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 32736],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 19319],
  [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 32285]
]
private theorem s2_0 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4] := by
  apply stage good3 [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,11), (0,249), (1,249), (0,168), (0,9), (1,168), (1,9), (1,10), (0,248), (0,4), (0,1), (0,288), (0,2), (1,292), (0,3), (0,10), (1,2), (0,292), (1,1), (1,288), (1,3), (1,5), (0,6), (0,312), (0,7), (0,8), (0,5), (1,8), (1,7), (1,12), (0,0), (0,12)]
  decide +kernel
private theorem s2_1 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 8] := by
  apply stage good3 [(0,168), (0,168), (0,168), (0,168), (0,168), (0,168), (0,168), (0,168), (0,168), (0,185), (0,343), (0,168), (0,378), (0,352), (0,319), (0,182), (0,184), (0,330), (0,175), (2,248), (0,388), (0,170), (0,421), (0,171), (0,183), (0,351), (0,391), (0,172), (0,423), (0,173), (0,174), (0,179), (0,177), (0,433), (0,178), (0,176), (0,180), (0,181), (0,187), (0,169), (0,186)]
  decide +kernel
private theorem s2_2 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16] := by
  apply stage good3 [(0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,467), (0,483), (1,168), (0,484), (0,319), (0,462), (0,16), (0,466), (2,170), (0,457), (2,2), (0,485), (0,15), (0,488), (0,453), (0,465), (0,454), (0,486), (7,177), (0,497), (0,455), (0,456), (0,463), (0,459), (0,313), (0,460), (0,461), (0,458), (0,464), (0,469), (0,452), (0,468)]
  decide +kernel
private theorem s2_3 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 511] := by
  apply stage good3 [(0,249), (0,249), (0,249), (0,249), (0,249), (0,249), (0,249), (0,249), (0,249), (2,536), (0,249), (0,530), (0,343), (2,535), (0,483), (0,558), (0,536), (2,343), (0,535), (2,249), (2,530), (2,483), (2,558), (2,256), (0,251), (0,549), (0,252), (0,567), (0,253), (0,529), (0,254), (0,256), (2,252), (2,567), (2,253), (2,529), (2,254), (0,255), (0,557), (0,250), (0,257), (0,591), (0,258)]
  decide +kernel
private theorem s2_4 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 1024] := by
  apply stage good3 [(0,20), (0,20), (0,20), (0,20), (0,20), (0,20), (0,20), (0,20), (0,20), (2,29), (0,251), (1,2), (0,596), (0,351), (2,23), (0,454), (0,353), (0,21), (0,29), (2,351), (0,23), (4,2), (2,596), (2,454), (2,353), (2,21), (2,25), (0,605), (5,172), (0,610), (0,22), (0,25), (8,172), (2,610), (2,22), (0,24), (0,26), (0,27), (0,30), (0,20), (0,28)]
  decide +kernel
private theorem s2_5 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 2048] := by
  apply stage good3 [(0,33), (0,33), (0,33), (0,33), (0,33), (0,33), (0,33), (0,33), (0,33), (5,41), (0,252), (1,1), (0,597), (0,172), (0,39), (7,177), (5,36), (0,34), (5,37), (2,177), (0,36), (2,6), (0,289), (2,459), (0,490), (0,35), (0,41), (5,172), (5,39), (5,252), (5,34), (0,40), (7,6), (5,289), (0,38), (5,38), (0,37), (5,35), (5,42), (0,33), (0,42)]
  decide +kernel
private theorem s2_6 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3654] := by
  apply stage good3 [(0,13), (0,13), (0,13), (0,13), (0,13), (0,13), (0,13), (0,13), (0,13), (0,54), (0,253), (1,3), (0,598), (0,173), (0,48), (0,455), (0,355), (0,13), (0,53), (2,178), (0,45), (2,7), (0,290), (2,460), (0,491), (2,188), (0,52), (0,22), (0,293), (5,34), (0,611), (0,49), (2,38), (0,315), (0,47), (0,294), (0,46), (0,50), (0,624), (0,55), (0,51)]
  decide +kernel
private theorem s2_7 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 3679] := by
  apply stage good3 [(0,378), (0,378), (0,378), (0,378), (0,378), (0,378), (0,378), (0,378), (0,378), (0,632), (0,530), (1,249), (0,378), (0,625), (0,484), (0,615), (0,603), (2,388), (0,599), (2,288), (0,568), (2,485), (0,630), (2,389), (0,614), (0,626), (0,596), (0,628), (0,597), (0,631), (0,598), (0,602), (2,289), (0,569), (2,290), (0,613), (0,601), (0,600), (0,629), (0,618), (0,616), (0,604), (0,617)]
  decide +kernel
private theorem s2_8 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 4070] := by
  apply stage good3 [(0,4), (0,4), (0,4), (0,4), (0,4), (0,4), (0,4), (0,4), (0,4), (0,64), (0,535), (0,4), (0,599), (0,175), (0,58), (0,457), (0,356), (0,14), (0,56), (0,63), (2,352), (2,9), (2,625), (2,462), (0,471), (0,62), (0,23), (0,502), (0,36), (0,612), (0,45), (0,59), (2,39), (0,316), (2,48), (2,31), (0,503), (0,57), (0,60), (0,43), (0,472), (0,65), (0,61)]
  decide +kernel
private theorem s2_9 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 5871] := by
  apply stage good3 [(0,5), (0,5), (0,5), (0,5), (0,5), (0,5), (0,5), (0,5), (0,5), (2,71), (0,255), (0,5), (0,600), (0,176), (2,57), (0,458), (0,357), (0,435), (0,67), (0,71), (2,176), (0,57), (2,5), (2,600), (2,458), (2,357), (2,435), (2,67), (2,69), (0,24), (0,295), (0,37), (0,633), (0,46), (0,32), (0,68), (0,69), (2,37), (2,633), (2,46), (2,32), (2,68), (0,70), (0,72)]
  decide +kernel
private theorem s2_10 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 16076] := by
  apply stage good3 [(0,292), (0,292), (0,292), (0,292), (0,292), (0,292), (0,292), (0,292), (0,292), (2,302), (0,549), (0,292), (0,628), (0,391), (2,502), (0,486), (0,393), (0,392), (0,298), (0,302), (2,391), (0,502), (2,292), (2,628), (2,486), (2,393), (2,392), (2,298), (2,300), (0,605), (5,39), (0,634), (0,293), (0,300), (8,39), (2,634), (2,293), (0,295), (0,301), (0,296), (0,303), (0,304), (0,297), (0,299)]
  decide +kernel
private theorem s2_11 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 19319] := by
  apply stage good3 [(0,25), (0,25), (0,25), (0,25), (0,25), (0,25), (0,25), (0,25), (0,25), (0,79), (0,256), (1,5), (0,602), (0,179), (2,62), (0,463), (0,359), (0,501), (0,358), (0,78), (2,183), (0,59), (2,10), (2,626), (2,465), (0,493), (2,17), (0,74), (0,77), (0,25), (0,300), (0,40), (0,635), (0,49), (0,606), (0,504), (2,41), (0,637), (2,52), (0,69), (0,75), (0,73), (0,76), (0,80)]
  decide +kernel
private theorem s2_12 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26898] := by
  apply stage good3 [(0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (2,81), (0,557), (1,8), (0,629), (0,180), (2,60), (0,464), (0,360), (0,470), (0,81), (2,180), (0,60), (4,8), (2,629), (2,464), (2,360), (2,470), (2,75), (0,26), (0,301), (5,35), (0,638), (0,50), (0,639), (0,75), (8,35), (2,638), (2,50), (2,639), (0,70), (0,82), (0,66)]
  decide +kernel
private theorem s2_13 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 26911] := by
  apply stage good3 [(0,16), (0,16), (0,16), (0,16), (0,16), (0,16), (0,16), (0,16), (0,16), (0,364), (0,558), (1,9), (0,615), (0,182), (2,471), (0,16), (0,363), (2,421), (0,356), (4,292), (2,630), (2,488), (0,640), (2,489), (0,641), (2,493), (0,353), (0,393), (5,36), (0,643), (0,355), (0,354), (0,361), (0,359), (2,490), (0,645), (2,491), (2,619), (0,362), (0,357), (0,360), (0,365), (2,492)]
  decide +kernel
private theorem s2_14 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 28500] := by
  apply stage good3 [(0,423), (0,423), (0,423), (0,423), (0,423), (0,423), (0,423), (0,423), (0,423), (0,650), (0,567), (1,288), (0,631), (0,423), (2,316), (0,497), (0,643), (0,498), (0,644), (0,647), (2,433), (0,612), (2,312), (2,569), (2,313), (2,645), (2,523), (0,500), (2,637), (0,610), (0,634), (5,252), (0,611), (0,635), (8,289), (0,646), (2,315), (2,314), (0,648), (0,633), (0,638), (0,636), (0,499), (2,592)]
  decide +kernel
private theorem s2_15 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32285] := by
  apply stage good3 [(0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (0,85), (0,536), (1,10), (0,603), (0,184), (2,64), (0,466), (0,363), (0,18), (0,83), (2,185), (0,63), (2,11), (2,632), (2,467), (2,364), (2,79), (0,29), (0,302), (5,37), (0,647), (0,53), (0,620), (0,607), (0,78), (8,41), (2,650), (2,54), (2,44), (0,84), (0,71), (0,81), (0,473), (0,621), (0,86)]
  decide +kernel
private theorem s2_16 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 2, 32765] := by
  apply stage good3 [(0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (2,86), (0,591), (1,12), (0,604), (0,187), (2,65), (0,469), (0,365), (0,19), (0,86), (2,187), (0,65), (4,12), (2,604), (2,469), (2,365), (2,19), (2,80), (0,30), (0,304), (5,42), (0,636), (0,55), (0,80), (8,42), (2,636), (2,55), (0,72), (0,82)]
  decide +kernel
private theorem s2_17 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 6, 4070] := by
  apply stage good3 [(0,14), (0,14), (0,14), (0,14), (0,14), (0,14), (0,14), (0,14), (0,14), (0,96), (0,14), (0,537), (1,14), (1,537), (0,189), (0,93), (1,189), (1,93), (0,90), (1,95), (0,622), (4,354), (0,651), (0,87), (1,505), (0,88), (0,95), (1,87), (0,505), (5,354), (1,651), (1,88), (1,91), (8,296), (0,317), (0,92), (0,89), (0,506), (0,91), (1,92), (1,89), (1,506), (0,97), (0,94)]
  decide +kernel
private theorem s2_18 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16] := by
  apply stage good3 [(0,319), (0,319), (0,319), (0,319), (0,319), (0,319), (0,319), (0,319), (0,319), (0,326), (0,319), (0,659), (1,319), (1,659), (0,436), (1,436), (1,325), (0,658), (0,322), (6,351), (0,660), (0,507), (1,487), (0,653), (0,321), (0,325), (1,507), (0,487), (7,351), (1,660), (1,321), (1,653), (1,323), (8,15), (0,524), (0,324), (0,323), (1,324), (1,327), (0,320), (0,327)]
  decide +kernel
private theorem s2_19 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 64] := by
  apply stage good3 [(0,330), (0,330), (0,330), (0,330), (0,330), (0,330), (0,330), (0,330), (0,330), (2,339), (0,330), (0,665), (3,170), (0,667), (2,669), (0,658), (0,338), (0,332), (0,339), (0,669), (6,170), (2,667), (2,658), (2,338), (2,332), (2,336), (3,507), (0,335), (5,454), (0,672), (0,333), (0,336), (8,454), (2,672), (2,333), (0,334), (0,337), (2,337), (2,340), (0,331), (0,340)]
  decide +kernel
private theorem s2_20 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 490] := by
  apply stage good3 [(0,171), (0,171), (0,171), (0,171), (0,171), (0,171), (0,171), (0,171), (0,171), (6,200), (0,171), (0,344), (1,456), (0,379), (0,675), (0,653), (6,395), (0,190), (0,202), (2,332), (0,197), (6,171), (6,344), (4,332), (6,197), (6,199), (6,653), (0,395), (5,27), (0,425), (0,196), (0,198), (0,200), (8,456), (6,379), (6,190), (0,199), (6,196), (6,198), (0,203), (0,201)]
  decide +kernel
private theorem s2_21 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 511] := by
  apply stage good3 [(0,343), (0,343), (0,343), (0,343), (0,343), (0,343), (0,343), (0,343), (0,343), (0,688), (0,343), (1,484), (0,681), (0,682), (0,659), (0,679), (0,680), (0,665), (0,345), (6,388), (0,683), (4,667), (0,686), (0,344), (0,349), (6,660), (0,685), (5,610), (0,570), (0,677), (0,666), (0,674), (0,347), (8,497), (0,571), (6,390), (0,684), (0,346), (0,678), (0,673), (0,348), (0,350), (0,687)]
  decide +kernel
private theorem s2_22 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3660] := by
  apply stage good3 [(0,174), (0,174), (0,174), (0,174), (0,174), (0,174), (0,174), (0,174), (0,174), (0,215), (0,174), (0,677), (1,453), (0,695), (0,676), (1,321), (0,211), (0,191), (0,214), (0,333), (0,206), (6,181), (6,678), (6,337), (0,422), (0,196), (0,207), (0,213), (8,324), (0,396), (5,21), (0,426), (0,209), (8,461), (0,434), (6,654), (0,208), (0,210), (0,427), (0,216), (0,212)]
  decide +kernel
private theorem s2_23 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 3679] := by
  apply stage good3 [(0,378), (0,378), (0,378), (0,378), (0,378), (0,378), (0,378), (0,378), (0,378), (0,702), (0,378), (0,681), (1,483), (0,699), (1,659), (0,384), (0,386), (0,667), (0,696), (6,433), (6,571), (4,672), (0,700), (0,379), (0,668), (0,380), (0,698), (6,524), (0,697), (5,596), (0,701), (0,695), (0,383), (8,313), (0,572), (6,664), (0,382), (0,381), (6,434), (0,690), (0,385), (0,387), (6,689)]
  decide +kernel
private theorem s2_24 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 4070] := by
  apply stage good3 [(0,175), (0,175), (0,175), (0,175), (0,175), (0,175), (0,175), (0,175), (0,175), (0,227), (0,175), (0,345), (1,457), (0,696), (0,367), (0,322), (0,223), (0,189), (0,218), (0,226), (0,669), (6,421), (6,686), (4,338), (0,655), (0,197), (0,225), (8,487), (0,220), (5,353), (0,703), (0,206), (0,222), (8,486), (6,700), (6,661), (0,221), (0,219), (6,422), (6,691), (0,656), (0,228), (0,217), (0,224)]
  decide +kernel
private theorem s2_25 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 5871] := by
  apply stage good3 [(0,176), (0,176), (0,176), (0,176), (0,176), (0,176), (0,176), (0,176), (0,176), (0,236), (0,176), (0,346), (1,463), (0,381), (0,368), (0,323), (0,233), (0,652), (0,509), (0,235), (0,334), (0,219), (6,183), (6,349), (4,336), (6,225), (0,199), (0,670), (0,657), (0,234), (6,325), (0,397), (5,29), (0,707), (0,208), (0,204), (0,230), (0,232), (8,466), (6,698), (6,193), (0,231), (6,213), (0,237)]
  decide +kernel
private theorem s2_26 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 13471] := by
  apply stage good3 [(0,305), (0,305), (0,305), (0,305), (0,305), (0,305), (0,305), (0,305), (0,305), (6,510), (0,352), (0,682), (1,16), (0,699), (0,436), (6,305), (0,370), (2,669), (0,367), (6,352), (6,682), (4,669), (6,367), (0,675), (2,622), (0,708), (6,368), (6,436), (0,305), (5,605), (0,709), (0,676), (0,366), (0,694), (0,510), (8,16), (6,699), (0,368), (6,676), (6,366), (6,694), (0,371), (0,369)]
  decide +kernel
private theorem s2_27 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 16076] := by
  apply stage good3 [(0,220), (0,220), (0,220), (0,220), (0,220), (0,220), (0,220), (0,220), (0,220), (0,403), (0,391), (0,685), (1,488), (0,697), (0,305), (0,487), (0,400), (0,394), (0,306), (0,401), (0,335), (0,220), (6,182), (6,679), (6,338), (6,223), (0,395), (0,341), (0,398), (6,233), (8,436), (7,23), (0,428), (0,396), (0,399), (8,462), (6,384), (0,397), (6,211), (9,87), (0,402), (0,404), (6,229)]
  decide +kernel
private theorem s2_28 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 19319] := by
  apply stage good3 [(0,179), (0,179), (0,179), (0,179), (0,179), (0,179), (0,179), (0,179), (0,179), (0,242), (0,179), (0,347), (1,458), (0,383), (0,510), (1,323), (6,403), (0,508), (0,372), (0,241), (0,336), (0,222), (6,185), (6,688), (4,339), (6,227), (0,200), (0,195), (0,238), (6,236), (6,326), (0,399), (5,25), (0,429), (0,209), (0,693), (0,239), (8,467), (6,702), (0,232), (6,215), (6,205), (0,240), (0,243)]
  decide +kernel
private theorem s2_29 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 28500] := by
  apply stage good3 [(0,423), (0,423), (0,423), (0,423), (0,423), (0,423), (0,423), (0,423), (0,423), (6,429), (0,423), (0,570), (1,485), (0,701), (0,709), (1,660), (6,428), (0,663), (0,430), (0,431), (0,672), (0,703), (6,423), (6,570), (6,672), (6,703), (0,425), (0,424), (0,706), (6,707), (8,660), (0,428), (5,251), (0,426), (0,429), (8,485), (6,701), (6,663), (6,430), (0,707), (6,426), (0,432), (0,705), (0,704)]
  decide +kernel
private theorem s2_30 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32285] := by
  apply stage good3 [(0,184), (0,184), (0,184), (0,184), (0,184), (0,184), (0,184), (0,184), (0,184), (6,241), (0,184), (0,680), (1,465), (0,386), (0,370), (1,325), (6,401), (0,194), (0,244), (0,339), (0,226), (6,184), (6,680), (6,339), (6,226), (0,202), (6,235), (8,325), (0,401), (5,24), (0,431), (0,214), (0,671), (0,405), (0,241), (8,465), (6,386), (6,194), (6,244), (0,235), (6,214), (6,671), (6,405), (0,245)]
  decide +kernel
private theorem s2_31 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 8, 32759] := by
  apply stage good3 [(0,186), (0,186), (0,186), (0,186), (0,186), (0,186), (0,186), (0,186), (0,186), (6,243), (0,186), (0,350), (1,468), (0,387), (0,371), (1,327), (6,404), (0,192), (0,245), (2,340), (0,228), (6,186), (6,350), (4,340), (6,228), (0,203), (6,237), (8,327), (0,404), (5,28), (0,432), (0,216), (0,243), (8,468), (6,387), (6,192), (0,237), (6,216)]
  decide +kernel
private theorem s2_32 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 10, 13802] := by
  apply stage good3 [(0,389), (0,389), (0,389), (0,389), (0,389), (0,389), (0,389), (0,389), (0,389), (0,732), (0,389), (0,720), (1,498), (0,573), (0,390), (0,723), (1,663), (0,718), (0,724), (0,731), (2,668), (0,721), (4,529), (4,666), (0,727), (0,710), (0,728), (8,690), (0,725), (5,314), (0,574), (0,712), (0,711), (0,716), (0,722), (8,618), (0,729), (0,715), (0,713), (0,726), (0,714), (0,730), (0,733), (0,717)]
  decide +kernel
private theorem s2_33 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 12, 16076] := by
  apply stage good3 [(0,246), (0,246), (0,246), (0,246), (0,246), (0,246), (0,246), (0,246), (0,246), (0,418), (0,392), (0,735), (1,489), (0,737), (0,394), (0,307), (1,661), (0,414), (0,308), (0,416), (2,341), (0,246), (4,619), (0,738), (4,691), (0,692), (0,406), (0,342), (0,410), (0,415), (5,366), (5,31), (0,739), (0,407), (0,412), (9,43), (0,740), (0,409), (0,408), (0,413), (7,89), (0,417), (0,419), (0,411)]
  decide +kernel
private theorem s2_34 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 15, 5871] := by
  apply stage good3 [(0,373), (0,373), (0,373), (0,373), (0,373), (0,373), (0,373), (0,373), (0,373), (0,449), (0,435), (0,743), (1,501), (0,744), (0,652), (0,475), (1,508), (0,373), (0,474), (0,448), (2,670), (0,440), (4,606), (0,745), (4,693), (0,742), (0,437), (0,642), (0,442), (0,447), (5,671), (0,746), (5,620), (0,747), (0,439), (0,438), (0,443), (0,446), (8,473), (0,748), (0,444), (0,441), (0,445), (0,450)]
  decide +kernel
private theorem s2_35 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 24, 32152] := by
  apply stage good3 [(0,523), (0,523), (0,523), (0,523), (0,523), (0,523), (0,523), (0,523), (0,523), (0,755), (0,523), (0,576), (1,523), (1,576), (0,664), (0,750), (1,664), (1,750), (0,595), (1,527), (2,424), (0,525), (6,613), (0,751), (9,673), (1,752), (0,575), (4,711), (0,753), (0,527), (8,673), (0,752), (7,613), (1,751), (1,575), (5,711), (1,753), (1,749), (8,250), (0,526), (0,749), (1,526), (0,528), (0,594)]
  decide +kernel
private theorem s2_36 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 27, 29115] := by
  apply stage good3 [(0,17), (0,17), (0,17), (0,17), (0,17), (0,17), (0,17), (0,17), (0,17), (0,108), (0,17), (0,531), (1,18), (0,627), (0,193), (0,102), (1,194), (0,375), (0,105), (0,107), (2,195), (0,99), (4,32), (0,291), (4,204), (0,494), (0,757), (4,438), (0,623), (5,205), (0,309), (5,44), (0,761), (0,103), (8,73), (0,318), (0,101), (6,441), (0,608), (0,100), (0,374), (0,104), (0,106), (0,109)]
  decide +kernel
private theorem s2_37 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 3679] := by
  apply stage good3 [(0,530), (0,530), (0,530), (0,530), (0,530), (0,530), (0,530), (0,530), (0,530), (0,772), (0,530), (1,530), (0,681), (0,759), (1,681), (1,759), (1,532), (2,683), (0,765), (4,631), (0,579), (4,701), (1,771), (2,720), (0,766), (0,532), (5,701), (0,771), (5,631), (1,579), (3,720), (1,767), (8,646), (0,580), (6,729), (0,768), (6,751), (0,769), (0,767), (7,751), (1,769), (7,729), (1,768), (1,770), (0,762), (0,770)]
  decide +kernel
private theorem s2_38 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4070] := by
  apply stage good3 [(0,345), (0,345), (0,345), (0,345), (0,345), (0,345), (0,345), (0,345), (0,345), (0,779), (0,535), (1,599), (0,765), (0,345), (0,539), (1,696), (0,559), (0,537), (0,533), (0,544), (2,682), (4,615), (2,759), (4,384), (0,775), (0,543), (8,428), (0,773), (5,643), (0,581), (3,723), (0,541), (8,634), (0,582), (6,727), (0,540), (8,739), (0,774), (0,538), (9,752), (0,560), (9,740), (0,776), (0,534), (2,259), (0,542)]
  decide +kernel
private theorem s2_39 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 4095] := by
  apply stage good3 [(0,254), (0,254), (0,254), (0,254), (0,254), (0,254), (0,254), (0,254), (0,254), (0,780), (0,254), (1,614), (0,766), (0,674), (2,540), (1,380), (0,760), (0,269), (2,684), (0,533), (4,616), (2,768), (4,385), (0,784), (0,267), (5,430), (0,783), (5,644), (0,583), (3,724), (0,264), (8,648), (0,584), (6,730), (0,262), (6,756), (0,263), (0,261), (7,753), (0,265), (7,754), (0,266), (0,268), (8,649)]
  decide +kernel
private theorem s2_40 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 5871] := by
  apply stage good3 [(0,255), (0,255), (0,255), (0,255), (0,255), (0,255), (0,255), (0,255), (0,255), (2,545), (0,255), (1,602), (0,767), (0,346), (2,538), (1,383), (0,561), (0,743), (0,271), (0,545), (2,346), (0,538), (4,602), (2,767), (4,383), (2,561), (2,743), (2,271), (2,274), (5,431), (0,551), (5,647), (0,585), (3,728), (0,261), (3,291), (0,273), (0,274), (8,647), (2,585), (6,728), (2,261), (6,291), (2,273), (7,755), (0,275), (0,276), (0,260), (0,272)]
  decide +kernel
private theorem s2_41 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 16076] := by
  apply stage good3 [(0,549), (0,549), (0,549), (0,549), (0,549), (0,549), (0,549), (0,549), (0,549), (2,786), (0,549), (1,630), (0,771), (0,685), (2,773), (1,700), (0,736), (0,735), (0,552), (0,786), (2,685), (0,773), (4,630), (2,771), (4,700), (2,736), (2,735), (2,552), (2,785), (5,709), (7,316), (7,582), (3,718), (0,783), (0,785), (9,316), (9,582), (6,718), (2,783), (0,551), (7,525), (0,555), (7,317), (0,787), (0,556), (0,550), (0,553), (0,554)]
  decide +kernel
private theorem s2_42 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 19319] := by
  apply stage good3 [(0,256), (0,256), (0,256), (0,256), (0,256), (0,256), (0,256), (0,256), (0,256), (0,781), (0,256), (1,600), (1,767), (0,347), (2,543), (1,381), (0,563), (1,744), (0,562), (0,547), (2,349), (0,541), (4,603), (2,532), (4,386), (0,778), (2,531), (0,546), (0,280), (5,429), (0,785), (5,635), (0,586), (3,713), (0,264), (3,745), (0,764), (8,650), (0,587), (6,732), (2,267), (0,274), (7,527), (0,278), (7,318), (0,279), (0,281), (0,763), (0,277)]
  decide +kernel
private theorem s2_43 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 26911] := by
  apply stage good3 [(0,282), (0,282), (0,282), (0,282), (0,282), (0,282), (0,282), (0,282), (0,282), (0,782), (0,558), (1,625), (1,759), (0,679), (2,775), (1,699), (0,790), (2,686), (0,559), (4,628), (4,771), (4,697), (0,788), (4,737), (0,564), (2,778), (5,703), (0,736), (5,612), (5,581), (3,721), (0,760), (3,651), (0,789), (0,563), (9,645), (0,588), (6,725), (2,784), (6,738), (0,565), (0,561), (7,750), (0,282), (0,758), (2,777)]
  decide +kernel
private theorem s2_44 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 27135] := by
  apply stage good3 [(0,257), (0,257), (0,257), (0,257), (0,257), (0,257), (0,257), (0,257), (0,257), (2,566), (0,257), (1,601), (1,769), (0,348), (2,560), (1,382), (0,564), (0,566), (2,348), (0,560), (4,601), (4,769), (4,382), (2,564), (2,278), (5,706), (0,555), (5,500), (0,589), (3,716), (0,265), (3,719), (0,283), (0,278), (8,500), (2,589), (6,716), (2,265), (6,719), (2,283), (0,275), (7,595), (0,284), (0,270)]
  decide +kernel
private theorem s2_45 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 28500] := by
  apply stage good3 [(0,567), (0,567), (0,567), (0,567), (0,567), (0,567), (0,567), (0,567), (0,567), (7,587), (0,567), (1,568), (1,579), (0,570), (2,582), (7,571), (5,581), (1,573), (5,583), (5,585), (2,571), (0,581), (4,569), (2,580), (4,572), (2,588), (2,576), (5,589), (2,587), (5,570), (7,582), (5,567), (3,573), (0,583), (0,586), (9,569), (7,580), (6,574), (2,584), (8,574), (7,584), (0,585), (7,576), (0,589), (7,578), (0,577), (0,590), (2,578)]
  decide +kernel
private theorem s2_46 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32256] := by
  apply stage good3 [(0,258), (0,258), (0,258), (0,258), (0,258), (0,258), (0,258), (0,258), (0,258), (2,285), (0,258), (1,617), (1,770), (0,687), (2,534), (7,689), (0,282), (0,286), (0,285), (2,687), (0,534), (4,617), (4,770), (9,689), (2,282), (2,286), (2,281), (5,704), (0,556), (7,592), (7,578), (3,717), (0,268), (5,734), (0,791), (0,281), (9,592), (9,578), (6,717), (2,268), (8,734), (2,791), (0,276), (7,594), (0,284), (7,593), (0,287)]
  decide +kernel
private theorem s2_47 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 511, 32285] := by
  apply stage good3 [(0,269), (0,269), (0,269), (0,269), (0,269), (0,269), (0,269), (0,269), (0,269), (0,795), (0,536), (1,626), (1,532), (0,680), (2,779), (1,698), (0,790), (1,627), (0,792), (2,688), (0,544), (4,632), (2,772), (4,702), (2,782), (2,781), (5,707), (0,786), (5,633), (5,585), (3,722), (0,269), (5,747), (0,794), (0,547), (9,637), (9,587), (6,731), (2,780), (8,761), (0,548), (0,545), (7,749), (0,566), (7,748), (0,793), (0,285)]
  decide +kernel
private theorem s2_48 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 4095] := by
  apply stage good3 [(0,56), (0,56), (0,56), (0,56), (0,56), (0,56), (0,56), (0,56), (0,56), (0,120), (0,56), (0,533), (1,56), (1,533), (0,218), (0,116), (1,218), (1,116), (0,90), (1,119), (2,708), (4,361), (4,789), (9,402), (1,511), (0,119), (8,402), (0,511), (5,361), (5,789), (1,115), (8,303), (8,787), (8,417), (0,512), (6,662), (0,117), (0,115), (9,417), (1,512), (7,662), (1,117), (0,118), (8,310)]
  decide +kernel
private theorem s2_49 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 5871] := by
  apply stage good3 [(0,57), (0,57), (0,57), (0,57), (0,57), (0,57), (0,57), (0,57), (0,57), (0,129), (0,57), (0,538), (1,59), (1,541), (0,219), (0,123), (1,222), (0,377), (0,91), (0,115), (0,440), (0,121), (0,128), (2,368), (4,359), (4,563), (9,403), (0,479), (2,475), (0,477), (0,127), (8,401), (0,513), (5,363), (5,790), (3,102), (0,122), (0,125), (8,302), (8,786), (8,416), (0,514), (6,494), (0,124), (9,418), (0,480), (0,126), (0,113), (0,478)]
  decide +kernel
private theorem s2_50 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 13471] := by
  apply stage good3 [(0,58), (0,58), (0,58), (0,58), (0,58), (0,58), (0,58), (0,58), (0,58), (2,133), (0,58), (0,539), (1,356), (1,559), (0,367), (1,223), (0,132), (0,93), (0,116), (0,133), (2,367), (4,356), (4,559), (4,223), (2,132), (2,93), (2,116), (4,377), (5,400), (0,609), (5,393), (5,736), (5,414), (0,130), (1,377), (8,393), (8,736), (8,414), (2,130), (0,123), (9,692), (0,481), (7,692), (2,481), (4,376), (0,112), (0,131), (1,376)]
  decide +kernel
private theorem s2_51 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16076] := by
  apply stage good3 [(0,220), (0,220), (0,220), (0,220), (0,220), (0,220), (0,220), (0,220), (0,220), (9,513), (0,502), (0,773), (1,471), (1,775), (0,220), (0,609), (1,655), (3,132), (0,505), (0,511), (0,246), (0,311), (7,479), (2,305), (4,640), (4,788), (9,220), (8,609), (2,307), (0,515), (0,516), (8,305), (7,471), (7,775), (1,479), (9,502), (9,773), (8,307), (0,513), (9,246), (9,311), (9,505), (9,511), (7,495), (1,476), (1,495)]
  decide +kernel
private theorem s2_52 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 16366] := by
  apply stage good3 [(0,221), (0,221), (0,221), (0,221), (0,221), (0,221), (0,221), (0,221), (0,221), (0,521), (0,503), (0,774), (1,472), (1,776), (0,221), (2,130), (1,656), (1,481), (0,506), (0,512), (0,247), (0,517), (0,520), (2,694), (4,641), (4,564), (9,398), (8,311), (0,519), (8,306), (0,515), (5,362), (5,565), (1,480), (8,298), (8,552), (8,308), (0,514), (9,410), (0,328), (9,420), (0,329), (0,518), (3,111)]
  decide +kernel
private theorem s2_53 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 28697] := by
  apply stage good3 [(0,61), (0,61), (0,61), (0,61), (0,61), (0,61), (0,61), (0,61), (0,61), (0,138), (0,61), (0,542), (1,61), (1,542), (0,224), (4,376), (1,224), (5,376), (0,94), (0,118), (0,98), (0,134), (1,135), (2,369), (6,492), (6,777), (4,229), (6,495), (0,136), (0,135), (5,229), (7,495), (7,492), (7,777), (1,136), (1,126), (8,299), (8,554), (8,411), (0,518), (6,741), (0,137), (0,126), (9,411), (1,518), (7,741), (1,137)]
  decide +kernel
private theorem s2_54 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 29115] := by
  apply stage good3 [(0,62), (0,62), (0,62), (0,62), (0,62), (0,62), (0,62), (0,62), (0,62), (0,144), (0,62), (0,543), (1,63), (1,544), (0,225), (4,377), (1,226), (1,133), (0,95), (0,119), (0,99), (0,139), (0,143), (2,510), (4,357), (4,561), (4,233), (6,479), (4,373), (0,140), (8,399), (0,516), (5,364), (5,782), (1,128), (8,300), (8,785), (8,412), (0,519), (6,742), (0,141), (0,127), (9,415), (1,520), (9,309), (0,142), (0,135)]
  decide +kernel
private theorem s2_55 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 4070, 32736] := by
  apply stage good3 [(0,64), (0,64), (0,64), (0,64), (0,64), (0,64), (0,64), (0,64), (0,64), (0,64), (0,779), (1,64), (1,779), (0,227), (2,133), (1,227), (3,133), (0,96), (0,120), (1,144), (2,370), (6,493), (6,778), (9,397), (8,513), (4,375), (0,145), (0,144), (8,397), (9,513), (7,493), (7,778), (5,375), (1,145), (1,129), (8,295), (8,551), (8,408), (0,521), (8,746), (0,522), (0,129), (9,408), (1,521), (9,746), (1,522), (0,138), (0,114), (0,146)]
  decide +kernel
private theorem s2_56 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 5887] := by
  apply stage good3 [(0,67), (0,67), (0,67), (0,67), (0,67), (0,67), (0,67), (0,67), (0,67), (0,156), (0,67), (0,271), (1,358), (1,562), (0,509), (2,477), (1,372), (3,140), (0,474), (0,155), (2,657), (0,121), (4,504), (4,764), (4,239), (6,141), (2,442), (0,147), (0,148), (0,154), (5,405), (7,522), (5,607), (5,794), (3,623), (0,149), (0,150), (0,153), (8,621), (8,793), (6,608), (0,151), (0,152), (9,451)]
  decide +kernel
private theorem s2_57 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 7919] := by
  apply stage good3 [(0,68), (0,68), (0,68), (0,68), (0,68), (0,68), (0,68), (0,68), (0,68), (0,163), (0,68), (0,273), (1,74), (1,546), (0,230), (2,124), (1,238), (3,139), (0,443), (0,149), (0,157), (0,162), (2,231), (0,122), (4,76), (4,279), (4,240), (6,142), (2,445), (2,151), (0,482), (0,161), (5,244), (7,145), (5,83), (5,792), (3,105), (0,160), (8,84), (8,548), (6,106), (0,158), (0,159), (9,110)]
  decide +kernel
private theorem s2_58 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 19319] := by
  apply stage good3 [(0,69), (0,69), (0,69), (0,69), (0,69), (0,69), (0,69), (0,69), (0,69), (0,166), (0,69), (0,274), (1,69), (1,274), (0,232), (2,127), (1,232), (3,127), (0,446), (0,153), (1,446), (1,153), (1,165), (2,234), (0,125), (4,78), (4,547), (4,241), (6,144), (2,447), (2,154), (2,100), (1,160), (0,165), (5,241), (7,144), (5,78), (5,547), (3,100), (0,160), (3,447), (3,154), (8,85), (8,795), (6,108), (2,161), (7,108), (3,161), (0,796), (0,164)]
  decide +kernel
private theorem s2_59 : safe 4 [0, 32767, 31, 482, 3652, 13448, 26896, 5871, 32285] := by
  apply stage good3 [(0,71), (0,71), (0,71), (0,71), (0,71), (0,71), (0,71), (0,71), (0,71), (7,166), (0,71), (0,545), (1,77), (1,280), (0,235), (2,129), (7,236), (5,128), (0,448), (0,155), (1,103), (5,162), (2,236), (0,128), (4,79), (4,781), (4,242), (6,143), (2,449), (2,156), (2,166), (5,235), (7,129), (5,71), (5,545), (3,103), (0,162), (5,448), (5,155), (1,165), (9,79), (9,781), (6,107), (2,163), (8,107), (7,163), (7,449), (7,156), (0,496), (0,167)]
  decide +kernel
private theorem good2 (u : List T) (hu : u ∈ states2) : safe 4 u := by
  simp only [states2,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s2_0
  · exact s2_1
  · exact s2_2
  · exact s2_3
  · exact s2_4
  · exact s2_5
  · exact s2_6
  · exact s2_7
  · exact s2_8
  · exact s2_9
  · exact s2_10
  · exact s2_11
  · exact s2_12
  · exact s2_13
  · exact s2_14
  · exact s2_15
  · exact s2_16
  · exact s2_17
  · exact s2_18
  · exact s2_19
  · exact s2_20
  · exact s2_21
  · exact s2_22
  · exact s2_23
  · exact s2_24
  · exact s2_25
  · exact s2_26
  · exact s2_27
  · exact s2_28
  · exact s2_29
  · exact s2_30
  · exact s2_31
  · exact s2_32
  · exact s2_33
  · exact s2_34
  · exact s2_35
  · exact s2_36
  · exact s2_37
  · exact s2_38
  · exact s2_39
  · exact s2_40
  · exact s2_41
  · exact s2_42
  · exact s2_43
  · exact s2_44
  · exact s2_45
  · exact s2_46
  · exact s2_47
  · exact s2_48
  · exact s2_49
  · exact s2_50
  · exact s2_51
  · exact s2_52
  · exact s2_53
  · exact s2_54
  · exact s2_55
  · exact s2_56
  · exact s2_57
  · exact s2_58
  · exact s2_59
private theorem s1_0 : safe 5 [0, 32767, 31, 482, 3652, 13448, 26896, 2] := by
  apply stage good2 [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (2,15), (0,3), (0,0), (0,7), (0,1), (2,8), (0,2), (0,13), (0,15), (2,1), (0,8), (2,0), (2,7), (2,2), (2,13), (2,11), (0,4), (0,10), (0,5), (0,14), (0,6), (0,11), (2,5), (2,14), (2,6), (0,9), (0,12), (0,16)]
  decide +kernel
private theorem s1_1 : safe 5 [0, 32767, 31, 482, 3652, 13448, 26896, 8] := by
  apply stage good2 [(0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (6,28), (0,1), (0,21), (1,2), (0,23), (0,26), (0,18), (6,27), (0,30), (0,19), (0,24), (6,1), (6,21), (4,19), (6,24), (0,20), (6,25), (6,18), (0,27), (5,4), (0,29), (0,22), (0,28), (8,2), (6,23), (0,25), (6,22), (0,31)]
  decide +kernel
private theorem s1_2 : safe 5 [0, 32767, 31, 482, 3652, 13448, 26896, 511] := by
  apply stage good2 [(0,3), (0,3), (0,3), (0,3), (0,3), (0,3), (0,3), (0,3), (2,47), (0,3), (1,7), (0,37), (0,21), (2,38), (1,23), (0,43), (0,47), (2,21), (0,38), (4,7), (2,37), (4,23), (2,43), (2,42), (5,29), (0,41), (5,14), (0,45), (3,32), (0,39), (0,42), (8,14), (2,45), (6,32), (2,39), (0,40), (7,35), (0,44), (0,46)]
  decide +kernel
private theorem s1_3 : safe 5 [0, 32767, 31, 482, 3652, 13448, 26896, 4070] := by
  apply stage good2 [(0,8), (0,8), (0,8), (0,8), (0,8), (0,8), (0,8), (0,8), (0,55), (0,8), (0,38), (1,8), (1,38), (0,24), (0,50), (1,24), (1,50), (0,17), (0,48), (1,54), (2,26), (4,13), (4,43), (9,27), (1,51), (0,54), (8,27), (0,51), (5,13), (5,43), (1,49), (8,10), (8,41), (8,33), (0,52), (0,49), (9,33), (1,52), (0,53)]
  decide +kernel
private theorem s1_4 : safe 5 [0, 32767, 31, 482, 3652, 13448, 26896, 5871] := by
  apply stage good2 [(0,9), (0,9), (0,9), (0,9), (0,9), (0,9), (0,9), (0,9), (2,59), (0,9), (0,40), (1,11), (1,42), (0,25), (2,49), (1,28), (3,54), (0,34), (0,56), (0,59), (2,25), (0,49), (4,11), (4,42), (4,28), (6,54), (2,34), (2,56), (2,58), (5,30), (7,55), (5,15), (5,47), (3,36), (0,57), (0,58), (8,15), (8,47), (6,36), (2,57)]
  decide +kernel
private theorem good1 (u : List T) (hu : u ∈ states1) : safe 5 u := by
  simp only [states1,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl
  · exact s1_0
  · exact s1_1
  · exact s1_2
  · exact s1_3
  · exact s1_4
private theorem s0_0 : safe 6 [0, 32767, 31, 482, 3652, 13448, 26896] := by
  apply stage good1 [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (8,4), (0,0), (0,2), (1,0), (1,2), (0,1), (2,3), (1,1), (3,3), (5,4), (2,1), (0,3), (4,0), (4,2), (4,1), (6,3), (4,4), (5,1), (7,3), (5,0), (5,2), (1,4), (8,0), (8,2), (0,4)]
  decide +kernel
private def samples : Fin 15 → Fin 6 × Fin 6 := ![(0,0), (0,1), (0,2), (0,3), (0,4), (1,1), (1,2), (1,3), (1,4), (2,2), (2,3), (2,4), (3,3), (3,4), (4,4)]
private def inputs (i : Fin 15) :=
  List.ofFn fun k : Fin 6 => decide (k = (samples i).1 ∨ k = (samples i).2)

private theorem tables (C : Circuit)
    (he : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (34072 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :
    ∀ k, (C.gates.foldl step (ins.map (bit k))).getD C.output false = bit k target := by
  intro k
  have hi : ∀ i : Fin 15, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 15, (34072 : Nat).testBit
      (6 * min (samples i).1.val (samples i).2.val + max (samples i).1.val (samples i).2.val) = bit i target := by decide +kernel
  have h := he (samples k).1 (samples k).2
  change C.eval (inputs k) = _ at h
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using h

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34072 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hg,hs,he⟩
  apply exclude C.gates C.output (fun g hm => hg g hm) ins [0,32767,31,482,3652,13448,26896] _ 6 hs s0_0 (tables C he)
  intro x hx
  simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  tauto

theorem monotoneLower : ¬ (∃ C : Circuit, Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34072 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hm,hs,he⟩
  apply generalLower
  refine ⟨C,?_,hs,he⟩
  intro g hg
  obtain ⟨ho,ha⟩ := hm g hg
  change g.op = .and ∨ g.op = .or at ho
  exact ⟨ho.imp_right Or.inl,ha⟩

#print axioms generalLower
#print axioms monotoneLower
-- The positive catalogue claims use the same explicit six-input circuit.
def circuit : Circuit :=
  { gates := [⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.and,[1,2]⟩, ⟨.or,[8,3]⟩,
              ⟨.and,[6,4]⟩, ⟨.and,[7,9]⟩, ⟨.or,[10,11]⟩], output := 12 }

theorem catalogue21916 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34072 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

theorem catalogue22480 : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34072 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  obtain ⟨C,hm,hs,he⟩ := catalogue21916
  refine ⟨C,?_,hs,he⟩
  intro g hg
  obtain ⟨ho,ha⟩ := hm g hg
  change g.op = .and ∨ g.op = .or at ho
  exact ⟨ho.imp_right Or.inl,ha⟩

#print axioms catalogue21916
#print axioms catalogue22480
end FiveCycleLower
