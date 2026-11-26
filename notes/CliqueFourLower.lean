import PEqualNP.Defs.Represents

-- The gate semantics and safety induction adapt the Apache-2.0 proof credited in Mask53Exact.lean.
-- Lewis Watson and Nico Habets developed the earlier gate enumeration.
-- Here the ten inputs, use of NOT, vertex symmetry and terminal checks are specific to K4.
namespace CliqueFourLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 10
private def ins : List T := [15, 114, 420, 840, 0, 0]
private def target : T := 366
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => (z == u || z == ~~~u) ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 10) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin 10) :
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

private def rename (p : Fin 10 → Fin 10) (x : T) : T :=
  (BitVec.ofBoolListLE (List.ofFn fun i => x[(p i).val])).cast (by simp)

private theorem digit (p : Fin 10 → Fin 10) (x : T) (i : Fin 10) :
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

private theorem transport (p : Fin 10 → Fin 10) (fixed : rename p target = target)
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

private def symm : Fin 24 → Fin 10 → Fin 10 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 3, 2, 4, 6, 5, 9, 8, 7], ![0, 2, 1, 3, 7, 5, 8, 4, 6, 9], ![0, 3, 1, 2, 9, 6, 8, 4, 5, 7], ![0, 2, 3, 1, 7, 8, 5, 9, 6, 4], ![0, 3, 2, 1, 9, 8, 6, 7, 5, 4], ![4, 1, 5, 6, 0, 2, 3, 7, 8, 9], ![4, 1, 6, 5, 0, 3, 2, 9, 8, 7], ![7, 2, 5, 8, 0, 1, 3, 4, 6, 9], ![9, 3, 6, 8, 0, 1, 2, 4, 5, 7], ![7, 2, 8, 5, 0, 3, 1, 9, 6, 4], ![9, 3, 8, 6, 0, 2, 1, 7, 5, 4], ![4, 5, 1, 6, 7, 2, 8, 0, 3, 9], ![4, 6, 1, 5, 9, 3, 8, 0, 2, 7], ![7, 5, 2, 8, 4, 1, 6, 0, 3, 9], ![9, 6, 3, 8, 4, 1, 5, 0, 2, 7], ![7, 8, 2, 5, 9, 3, 6, 0, 1, 4], ![9, 8, 3, 6, 7, 2, 5, 0, 1, 4], ![4, 5, 6, 1, 7, 8, 2, 9, 3, 0], ![4, 6, 5, 1, 9, 8, 3, 7, 2, 0], ![7, 5, 8, 2, 4, 6, 1, 9, 3, 0], ![9, 6, 8, 3, 4, 5, 1, 7, 2, 0], ![7, 8, 5, 2, 9, 6, 3, 4, 1, 0], ![9, 8, 6, 3, 7, 5, 2, 4, 1, 0]]
private theorem symmFacts : ∀ p, rename (symm p) target = target ∧ rename (symm p) 0 = 0 ∧ rename (symm p) (-1) = -1 := by decide +kernel
private def routeOK (w : List T) (next : List (List T)) :
    List T → List (Fin 24 × Nat) → Bool
  | [], [] => true
  | z :: zs, (p,j) :: rest =>
      decide (j < next.length) &&
      (z :: w).all (fun x => (next.getD j []).contains (rename (symm p) x)) &&
      routeOK w next zs rest
  | _, _ => false

private theorem routeSound {w : List T} {next : List (List T)} {n : Nat}
    (good : ∀ u ∈ next, safe n u) (zs : List T) (plan : List (Fin 24 × Nat))
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
    (plan : List (Fin 24 × Nat)) (h : routeOK w next (choices w) plan = true) : safe (n+1) w := by
  intro z hz
  exact routeSound good _ plan h z ((choice_iff _ _).2 hz)

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def states1 : List (List T) := [
  [0, 1023, 15, 114, 420, 840, 2],
  [0, 1023, 15, 114, 420, 840, 127],
  [0, 1023, 15, 114, 420, 840, 183]
]
private def states2 : List (List T) := [
  [0, 1023, 15, 114, 420, 840, 2, 4],
  [0, 1023, 15, 114, 420, 840, 2, 127],
  [0, 1023, 15, 114, 420, 840, 2, 183],
  [0, 1023, 15, 114, 420, 840, 2, 256],
  [0, 1023, 15, 114, 420, 840, 2, 422],
  [0, 1023, 15, 114, 420, 840, 2, 431],
  [0, 1023, 15, 114, 420, 840, 2, 909],
  [0, 1023, 15, 114, 420, 840, 2, 1004],
  [0, 1023, 15, 114, 420, 840, 2, 1021],
  [0, 1023, 15, 114, 420, 840, 6, 502],
  [0, 1023, 15, 114, 420, 840, 7, 183],
  [0, 1023, 15, 114, 420, 840, 19, 1004],
  [0, 1023, 15, 114, 420, 840, 127, 183],
  [0, 1023, 15, 114, 420, 840, 127, 431],
  [0, 1023, 15, 114, 420, 840, 127, 511],
  [0, 1023, 15, 114, 420, 840, 127, 909],
  [0, 1023, 15, 114, 420, 840, 127, 1004],
  [0, 1023, 15, 114, 420, 840, 183, 191],
  [0, 1023, 15, 114, 420, 840, 183, 603]
]
private def states3 : List (List T) := [
  [0, 1023, 15, 114, 420, 840, 1, 502, 1022],
  [0, 1023, 15, 114, 420, 840, 2, 4, 6],
  [0, 1023, 15, 114, 420, 840, 2, 4, 8],
  [0, 1023, 15, 114, 420, 840, 2, 4, 32],
  [0, 1023, 15, 114, 420, 840, 2, 4, 64],
  [0, 1023, 15, 114, 420, 840, 2, 4, 118],
  [0, 1023, 15, 114, 420, 840, 2, 4, 127],
  [0, 1023, 15, 114, 420, 840, 2, 4, 183],
  [0, 1023, 15, 114, 420, 840, 2, 4, 502],
  [0, 1023, 15, 114, 420, 840, 2, 4, 603],
  [0, 1023, 15, 114, 420, 840, 2, 4, 842],
  [0, 1023, 15, 114, 420, 840, 2, 4, 847],
  [0, 1023, 15, 114, 420, 840, 2, 4, 890],
  [0, 1023, 15, 114, 420, 840, 2, 4, 1008],
  [0, 1023, 15, 114, 420, 840, 2, 4, 1019],
  [0, 1023, 15, 114, 420, 840, 2, 6, 422],
  [0, 1023, 15, 114, 420, 840, 2, 6, 502],
  [0, 1023, 15, 114, 420, 840, 2, 7, 183],
  [0, 1023, 15, 114, 420, 840, 2, 12, 1004],
  [0, 1023, 15, 114, 420, 840, 2, 13, 909],
  [0, 1023, 15, 114, 420, 840, 2, 13, 1021],
  [0, 1023, 15, 114, 420, 840, 2, 19, 1004],
  [0, 1023, 15, 114, 420, 840, 2, 36, 127],
  [0, 1023, 15, 114, 420, 840, 2, 127, 183],
  [0, 1023, 15, 114, 420, 840, 2, 127, 256],
  [0, 1023, 15, 114, 420, 840, 2, 127, 422],
  [0, 1023, 15, 114, 420, 840, 2, 127, 431],
  [0, 1023, 15, 114, 420, 840, 2, 127, 511],
  [0, 1023, 15, 114, 420, 840, 2, 127, 896],
  [0, 1023, 15, 114, 420, 840, 2, 127, 909],
  [0, 1023, 15, 114, 420, 840, 2, 127, 1004],
  [0, 1023, 15, 114, 420, 840, 2, 127, 1021],
  [0, 1023, 15, 114, 420, 840, 2, 133, 890],
  [0, 1023, 15, 114, 420, 840, 2, 164, 183],
  [0, 1023, 15, 114, 420, 840, 2, 181, 842],
  [0, 1023, 15, 114, 420, 840, 2, 183, 191],
  [0, 1023, 15, 114, 420, 840, 2, 183, 256],
  [0, 1023, 15, 114, 420, 840, 2, 183, 422],
  [0, 1023, 15, 114, 420, 840, 2, 183, 431],
  [0, 1023, 15, 114, 420, 840, 2, 183, 439],
  [0, 1023, 15, 114, 420, 840, 2, 183, 603],
  [0, 1023, 15, 114, 420, 840, 2, 183, 842],
  [0, 1023, 15, 114, 420, 840, 2, 183, 847],
  [0, 1023, 15, 114, 420, 840, 2, 183, 909],
  [0, 1023, 15, 114, 420, 840, 2, 183, 1004],
  [0, 1023, 15, 114, 420, 840, 2, 183, 1021],
  [0, 1023, 15, 114, 420, 840, 2, 256, 258],
  [0, 1023, 15, 114, 420, 840, 2, 256, 271],
  [0, 1023, 15, 114, 420, 840, 2, 256, 431],
  [0, 1023, 15, 114, 420, 840, 2, 256, 767],
  [0, 1023, 15, 114, 420, 840, 2, 260, 847],
  [0, 1023, 15, 114, 420, 840, 2, 388, 909],
  [0, 1023, 15, 114, 420, 840, 2, 422, 431],
  [0, 1023, 15, 114, 420, 840, 2, 422, 842],
  [0, 1023, 15, 114, 420, 840, 2, 422, 847],
  [0, 1023, 15, 114, 420, 840, 2, 422, 909],
  [0, 1023, 15, 114, 420, 840, 2, 422, 1004],
  [0, 1023, 15, 114, 420, 840, 2, 422, 1006],
  [0, 1023, 15, 114, 420, 840, 2, 422, 1021],
  [0, 1023, 15, 114, 420, 840, 2, 431, 502],
  [0, 1023, 15, 114, 420, 840, 2, 431, 511],
  [0, 1023, 15, 114, 420, 840, 2, 431, 847],
  [0, 1023, 15, 114, 420, 840, 2, 431, 890],
  [0, 1023, 15, 114, 420, 840, 2, 431, 909],
  [0, 1023, 15, 114, 420, 840, 2, 431, 1004],
  [0, 1023, 15, 114, 420, 840, 2, 431, 1007],
  [0, 1023, 15, 114, 420, 840, 2, 431, 1008],
  [0, 1023, 15, 114, 420, 840, 2, 431, 1021],
  [0, 1023, 15, 114, 420, 840, 2, 909, 911],
  [0, 1023, 15, 114, 420, 840, 2, 909, 941],
  [0, 1023, 15, 114, 420, 840, 2, 909, 1004],
  [0, 1023, 15, 114, 420, 840, 2, 909, 1008],
  [0, 1023, 15, 114, 420, 840, 2, 909, 1021],
  [0, 1023, 15, 114, 420, 840, 2, 1004, 1006],
  [0, 1023, 15, 114, 420, 840, 2, 1004, 1007],
  [0, 1023, 15, 114, 420, 840, 2, 1004, 1021],
  [0, 1023, 15, 114, 420, 840, 3, 19, 1004],
  [0, 1023, 15, 114, 420, 840, 6, 118, 502],
  [0, 1023, 15, 114, 420, 840, 6, 127, 502],
  [0, 1023, 15, 114, 420, 840, 6, 183, 502],
  [0, 1023, 15, 114, 420, 840, 6, 320, 502],
  [0, 1023, 15, 114, 420, 840, 6, 502, 511],
  [0, 1023, 15, 114, 420, 840, 6, 502, 521],
  [0, 1023, 15, 114, 420, 840, 6, 502, 603],
  [0, 1023, 15, 114, 420, 840, 6, 502, 846],
  [0, 1023, 15, 114, 420, 840, 6, 502, 847],
  [0, 1023, 15, 114, 420, 840, 6, 502, 890],
  [0, 1023, 15, 114, 420, 840, 6, 502, 1008],
  [0, 1023, 15, 114, 420, 840, 6, 502, 1017],
  [0, 1023, 15, 114, 420, 840, 6, 502, 1022],
  [0, 1023, 15, 114, 420, 840, 7, 50, 183],
  [0, 1023, 15, 114, 420, 840, 7, 119, 183],
  [0, 1023, 15, 114, 420, 840, 7, 127, 183],
  [0, 1023, 15, 114, 420, 840, 7, 183, 191],
  [0, 1023, 15, 114, 420, 840, 7, 183, 247],
  [0, 1023, 15, 114, 420, 840, 7, 183, 502],
  [0, 1023, 15, 114, 420, 840, 7, 183, 603],
  [0, 1023, 15, 114, 420, 840, 7, 183, 847],
  [0, 1023, 15, 114, 420, 840, 7, 183, 890],
  [0, 1023, 15, 114, 420, 840, 7, 183, 1008],
  [0, 1023, 15, 114, 420, 840, 7, 183, 1016],
  [0, 1023, 15, 114, 420, 840, 7, 1008, 1016],
  [0, 1023, 15, 114, 420, 840, 14, 502, 1022],
  [0, 1023, 15, 114, 420, 840, 19, 31, 1004],
  [0, 1023, 15, 114, 420, 840, 19, 127, 1004],
  [0, 1023, 15, 114, 420, 840, 19, 183, 603],
  [0, 1023, 15, 114, 420, 840, 19, 183, 1004],
  [0, 1023, 15, 114, 420, 840, 19, 431, 1004],
  [0, 1023, 15, 114, 420, 840, 19, 439, 1004],
  [0, 1023, 15, 114, 420, 840, 19, 909, 1004],
  [0, 1023, 15, 114, 420, 840, 19, 1004, 1007],
  [0, 1023, 15, 114, 420, 840, 47, 127, 431],
  [0, 1023, 15, 114, 420, 840, 55, 127, 183],
  [0, 1023, 15, 114, 420, 840, 108, 127, 1004],
  [0, 1023, 15, 114, 420, 840, 127, 183, 191],
  [0, 1023, 15, 114, 420, 840, 127, 183, 255],
  [0, 1023, 15, 114, 420, 840, 127, 183, 431],
  [0, 1023, 15, 114, 420, 840, 127, 183, 439],
  [0, 1023, 15, 114, 420, 840, 127, 183, 511],
  [0, 1023, 15, 114, 420, 840, 127, 183, 603],
  [0, 1023, 15, 114, 420, 840, 127, 183, 847],
  [0, 1023, 15, 114, 420, 840, 127, 183, 895],
  [0, 1023, 15, 114, 420, 840, 127, 183, 909],
  [0, 1023, 15, 114, 420, 840, 127, 183, 1004],
  [0, 1023, 15, 114, 420, 840, 127, 431, 502],
  [0, 1023, 15, 114, 420, 840, 127, 431, 511],
  [0, 1023, 15, 114, 420, 840, 127, 431, 847],
  [0, 1023, 15, 114, 420, 840, 127, 431, 890],
  [0, 1023, 15, 114, 420, 840, 127, 431, 895],
  [0, 1023, 15, 114, 420, 840, 127, 431, 1008],
  [0, 1023, 15, 114, 420, 840, 127, 511, 895],
  [0, 1023, 15, 114, 420, 840, 127, 511, 909],
  [0, 1023, 15, 114, 420, 840, 127, 511, 1004],
  [0, 1023, 15, 114, 420, 840, 127, 909, 911],
  [0, 1023, 15, 114, 420, 840, 127, 909, 941],
  [0, 1023, 15, 114, 420, 840, 127, 909, 1008],
  [0, 1023, 15, 114, 420, 840, 183, 191, 247],
  [0, 1023, 15, 114, 420, 840, 183, 191, 255],
  [0, 1023, 15, 114, 420, 840, 183, 191, 603],
  [0, 1023, 15, 114, 420, 840, 183, 191, 1008],
  [0, 1023, 15, 114, 420, 840, 183, 603, 767],
  [0, 1023, 15, 114, 420, 840, 183, 603, 909]
]
private theorem s3_0 : safe 3 [0, 1023, 15, 114, 420, 840, 1, 502, 1022] := by
  apply three_safe
  decide +kernel
#print axioms s3_0
private theorem s3_1 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 6] := by
  apply three_safe
  decide +kernel
private theorem s3_2 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 8] := by
  apply three_safe
  decide +kernel
private theorem s3_3 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 32] := by
  apply three_safe
  decide +kernel
private theorem s3_4 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 64] := by
  apply three_safe
  decide +kernel
private theorem s3_5 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 118] := by
  apply three_safe
  decide +kernel
private theorem s3_6 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 127] := by
  apply three_safe
  decide +kernel
private theorem s3_7 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 183] := by
  apply three_safe
  decide +kernel
private theorem s3_8 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 502] := by
  apply three_safe
  decide +kernel
private theorem s3_9 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 603] := by
  apply three_safe
  decide +kernel
private theorem s3_10 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 842] := by
  apply three_safe
  decide +kernel
private theorem s3_11 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 847] := by
  apply three_safe
  decide +kernel
private theorem s3_12 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 890] := by
  apply three_safe
  decide +kernel
private theorem s3_13 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 1008] := by
  apply three_safe
  decide +kernel
private theorem s3_14 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 4, 1019] := by
  apply three_safe
  decide +kernel
private theorem s3_15 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 6, 422] := by
  apply three_safe
  decide +kernel
private theorem s3_16 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 6, 502] := by
  apply three_safe
  decide +kernel
private theorem s3_17 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 7, 183] := by
  apply three_safe
  decide +kernel
private theorem s3_18 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 12, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_19 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 13, 909] := by
  apply three_safe
  decide +kernel
private theorem s3_20 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 13, 1021] := by
  apply three_safe
  decide +kernel
private theorem s3_21 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 19, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_22 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 36, 127] := by
  apply three_safe
  decide +kernel
private theorem s3_23 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 127, 183] := by
  apply three_safe
  decide +kernel
private theorem s3_24 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 127, 256] := by
  apply three_safe
  decide +kernel
private theorem s3_25 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 127, 422] := by
  apply three_safe
  decide +kernel
private theorem s3_26 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 127, 431] := by
  apply three_safe
  decide +kernel
private theorem s3_27 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 127, 511] := by
  apply three_safe
  decide +kernel
private theorem s3_28 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 127, 896] := by
  apply three_safe
  decide +kernel
private theorem s3_29 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 127, 909] := by
  apply three_safe
  decide +kernel
private theorem s3_30 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 127, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_31 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 127, 1021] := by
  apply three_safe
  decide +kernel
private theorem s3_32 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 133, 890] := by
  apply three_safe
  decide +kernel
private theorem s3_33 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 164, 183] := by
  apply three_safe
  decide +kernel
private theorem s3_34 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 181, 842] := by
  apply three_safe
  decide +kernel
private theorem s3_35 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 191] := by
  apply three_safe
  decide +kernel
private theorem s3_36 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 256] := by
  apply three_safe
  decide +kernel
private theorem s3_37 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 422] := by
  apply three_safe
  decide +kernel
private theorem s3_38 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 431] := by
  apply three_safe
  decide +kernel
private theorem s3_39 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 439] := by
  apply three_safe
  decide +kernel
private theorem s3_40 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 603] := by
  apply three_safe
  decide +kernel
private theorem s3_41 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 842] := by
  apply three_safe
  decide +kernel
private theorem s3_42 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 847] := by
  apply three_safe
  decide +kernel
private theorem s3_43 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 909] := by
  apply three_safe
  decide +kernel
private theorem s3_44 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_45 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 183, 1021] := by
  apply three_safe
  decide +kernel
private theorem s3_46 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 256, 258] := by
  apply three_safe
  decide +kernel
private theorem s3_47 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 256, 271] := by
  apply three_safe
  decide +kernel
#print axioms s3_47
private theorem s3_48 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 256, 431] := by
  apply three_safe
  decide +kernel
private theorem s3_49 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 256, 767] := by
  apply three_safe
  decide +kernel
private theorem s3_50 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 260, 847] := by
  apply three_safe
  decide +kernel
private theorem s3_51 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 388, 909] := by
  apply three_safe
  decide +kernel
private theorem s3_52 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 422, 431] := by
  apply three_safe
  decide +kernel
private theorem s3_53 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 422, 842] := by
  apply three_safe
  decide +kernel
private theorem s3_54 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 422, 847] := by
  apply three_safe
  decide +kernel
private theorem s3_55 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 422, 909] := by
  apply three_safe
  decide +kernel
private theorem s3_56 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 422, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_57 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 422, 1006] := by
  apply three_safe
  decide +kernel
private theorem s3_58 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 422, 1021] := by
  apply three_safe
  decide +kernel
private theorem s3_59 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 431, 502] := by
  apply three_safe
  decide +kernel
private theorem s3_60 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 431, 511] := by
  apply three_safe
  decide +kernel
private theorem s3_61 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 431, 847] := by
  apply three_safe
  decide +kernel
private theorem s3_62 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 431, 890] := by
  apply three_safe
  decide +kernel
private theorem s3_63 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 431, 909] := by
  apply three_safe
  decide +kernel
private theorem s3_64 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 431, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_65 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 431, 1007] := by
  apply three_safe
  decide +kernel
private theorem s3_66 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 431, 1008] := by
  apply three_safe
  decide +kernel
private theorem s3_67 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 431, 1021] := by
  apply three_safe
  decide +kernel
private theorem s3_68 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 909, 911] := by
  apply three_safe
  decide +kernel
private theorem s3_69 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 909, 941] := by
  apply three_safe
  decide +kernel
private theorem s3_70 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 909, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_71 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 909, 1008] := by
  apply three_safe
  decide +kernel
private theorem s3_72 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 909, 1021] := by
  apply three_safe
  decide +kernel
private theorem s3_73 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 1004, 1006] := by
  apply three_safe
  decide +kernel
private theorem s3_74 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 1004, 1007] := by
  apply three_safe
  decide +kernel
private theorem s3_75 : safe 3 [0, 1023, 15, 114, 420, 840, 2, 1004, 1021] := by
  apply three_safe
  decide +kernel
private theorem s3_76 : safe 3 [0, 1023, 15, 114, 420, 840, 3, 19, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_77 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 118, 502] := by
  apply three_safe
  decide +kernel
private theorem s3_78 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 127, 502] := by
  apply three_safe
  decide +kernel
private theorem s3_79 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 183, 502] := by
  apply three_safe
  decide +kernel
private theorem s3_80 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 320, 502] := by
  apply three_safe
  decide +kernel
private theorem s3_81 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 502, 511] := by
  apply three_safe
  decide +kernel
private theorem s3_82 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 502, 521] := by
  apply three_safe
  decide +kernel
private theorem s3_83 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 502, 603] := by
  apply three_safe
  decide +kernel
private theorem s3_84 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 502, 846] := by
  apply three_safe
  decide +kernel
private theorem s3_85 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 502, 847] := by
  apply three_safe
  decide +kernel
private theorem s3_86 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 502, 890] := by
  apply three_safe
  decide +kernel
private theorem s3_87 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 502, 1008] := by
  apply three_safe
  decide +kernel
private theorem s3_88 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 502, 1017] := by
  apply three_safe
  decide +kernel
private theorem s3_89 : safe 3 [0, 1023, 15, 114, 420, 840, 6, 502, 1022] := by
  apply three_safe
  decide +kernel
private theorem s3_90 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 50, 183] := by
  apply three_safe
  decide +kernel
private theorem s3_91 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 119, 183] := by
  apply three_safe
  decide +kernel
private theorem s3_92 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 127, 183] := by
  apply three_safe
  decide +kernel
private theorem s3_93 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 183, 191] := by
  apply three_safe
  decide +kernel
private theorem s3_94 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 183, 247] := by
  apply three_safe
  decide +kernel
private theorem s3_95 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 183, 502] := by
  apply three_safe
  decide +kernel
#print axioms s3_95
private theorem s3_96 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 183, 603] := by
  apply three_safe
  decide +kernel
private theorem s3_97 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 183, 847] := by
  apply three_safe
  decide +kernel
private theorem s3_98 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 183, 890] := by
  apply three_safe
  decide +kernel
private theorem s3_99 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 183, 1008] := by
  apply three_safe
  decide +kernel
private theorem s3_100 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 183, 1016] := by
  apply three_safe
  decide +kernel
private theorem s3_101 : safe 3 [0, 1023, 15, 114, 420, 840, 7, 1008, 1016] := by
  apply three_safe
  decide +kernel
private theorem s3_102 : safe 3 [0, 1023, 15, 114, 420, 840, 14, 502, 1022] := by
  apply three_safe
  decide +kernel
private theorem s3_103 : safe 3 [0, 1023, 15, 114, 420, 840, 19, 31, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_104 : safe 3 [0, 1023, 15, 114, 420, 840, 19, 127, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_105 : safe 3 [0, 1023, 15, 114, 420, 840, 19, 183, 603] := by
  apply three_safe
  decide +kernel
private theorem s3_106 : safe 3 [0, 1023, 15, 114, 420, 840, 19, 183, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_107 : safe 3 [0, 1023, 15, 114, 420, 840, 19, 431, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_108 : safe 3 [0, 1023, 15, 114, 420, 840, 19, 439, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_109 : safe 3 [0, 1023, 15, 114, 420, 840, 19, 909, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_110 : safe 3 [0, 1023, 15, 114, 420, 840, 19, 1004, 1007] := by
  apply three_safe
  decide +kernel
private theorem s3_111 : safe 3 [0, 1023, 15, 114, 420, 840, 47, 127, 431] := by
  apply three_safe
  decide +kernel
private theorem s3_112 : safe 3 [0, 1023, 15, 114, 420, 840, 55, 127, 183] := by
  apply three_safe
  decide +kernel
private theorem s3_113 : safe 3 [0, 1023, 15, 114, 420, 840, 108, 127, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_114 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 191] := by
  apply three_safe
  decide +kernel
private theorem s3_115 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 255] := by
  apply three_safe
  decide +kernel
private theorem s3_116 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 431] := by
  apply three_safe
  decide +kernel
private theorem s3_117 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 439] := by
  apply three_safe
  decide +kernel
private theorem s3_118 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 511] := by
  apply three_safe
  decide +kernel
private theorem s3_119 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 603] := by
  apply three_safe
  decide +kernel
private theorem s3_120 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 847] := by
  apply three_safe
  decide +kernel
private theorem s3_121 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 895] := by
  apply three_safe
  decide +kernel
private theorem s3_122 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 909] := by
  apply three_safe
  decide +kernel
private theorem s3_123 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 183, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_124 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 431, 502] := by
  apply three_safe
  decide +kernel
private theorem s3_125 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 431, 511] := by
  apply three_safe
  decide +kernel
private theorem s3_126 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 431, 847] := by
  apply three_safe
  decide +kernel
private theorem s3_127 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 431, 890] := by
  apply three_safe
  decide +kernel
private theorem s3_128 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 431, 895] := by
  apply three_safe
  decide +kernel
private theorem s3_129 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 431, 1008] := by
  apply three_safe
  decide +kernel
private theorem s3_130 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 511, 895] := by
  apply three_safe
  decide +kernel
private theorem s3_131 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 511, 909] := by
  apply three_safe
  decide +kernel
private theorem s3_132 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 511, 1004] := by
  apply three_safe
  decide +kernel
private theorem s3_133 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 909, 911] := by
  apply three_safe
  decide +kernel
private theorem s3_134 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 909, 941] := by
  apply three_safe
  decide +kernel
private theorem s3_135 : safe 3 [0, 1023, 15, 114, 420, 840, 127, 909, 1008] := by
  apply three_safe
  decide +kernel
private theorem s3_136 : safe 3 [0, 1023, 15, 114, 420, 840, 183, 191, 247] := by
  apply three_safe
  decide +kernel
private theorem s3_137 : safe 3 [0, 1023, 15, 114, 420, 840, 183, 191, 255] := by
  apply three_safe
  decide +kernel
private theorem s3_138 : safe 3 [0, 1023, 15, 114, 420, 840, 183, 191, 603] := by
  apply three_safe
  decide +kernel
private theorem s3_139 : safe 3 [0, 1023, 15, 114, 420, 840, 183, 191, 1008] := by
  apply three_safe
  decide +kernel
private theorem s3_140 : safe 3 [0, 1023, 15, 114, 420, 840, 183, 603, 767] := by
  apply three_safe
  decide +kernel
private theorem s3_141 : safe 3 [0, 1023, 15, 114, 420, 840, 183, 603, 909] := by
  apply three_safe
  decide +kernel
#print axioms s3_141
private theorem good3 (u : List T) (hu : u ∈ states3) : safe 3 u := by
  simp only [states3,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_0
  · exact s3_1
  · exact s3_2
  · exact s3_3
  · exact s3_4
  · exact s3_5
  · exact s3_6
  · exact s3_7
  · exact s3_8
  · exact s3_9
  · exact s3_10
  · exact s3_11
  · exact s3_12
  · exact s3_13
  · exact s3_14
  · exact s3_15
  · exact s3_16
  · exact s3_17
  · exact s3_18
  · exact s3_19
  · exact s3_20
  · exact s3_21
  · exact s3_22
  · exact s3_23
  · exact s3_24
  · exact s3_25
  · exact s3_26
  · exact s3_27
  · exact s3_28
  · exact s3_29
  · exact s3_30
  · exact s3_31
  · exact s3_32
  · exact s3_33
  · exact s3_34
  · exact s3_35
  · exact s3_36
  · exact s3_37
  · exact s3_38
  · exact s3_39
  · exact s3_40
  · exact s3_41
  · exact s3_42
  · exact s3_43
  · exact s3_44
  · exact s3_45
  · exact s3_46
  · exact s3_47
  · exact s3_48
  · exact s3_49
  · exact s3_50
  · exact s3_51
  · exact s3_52
  · exact s3_53
  · exact s3_54
  · exact s3_55
  · exact s3_56
  · exact s3_57
  · exact s3_58
  · exact s3_59
  · exact s3_60
  · exact s3_61
  · exact s3_62
  · exact s3_63
  · exact s3_64
  · exact s3_65
  · exact s3_66
  · exact s3_67
  · exact s3_68
  · exact s3_69
  · exact s3_70
  · exact s3_71
  · exact s3_72
  · exact s3_73
  · exact s3_74
  · exact s3_75
  · exact s3_76
  · exact s3_77
  · exact s3_78
  · exact s3_79
  · exact s3_80
  · exact s3_81
  · exact s3_82
  · exact s3_83
  · exact s3_84
  · exact s3_85
  · exact s3_86
  · exact s3_87
  · exact s3_88
  · exact s3_89
  · exact s3_90
  · exact s3_91
  · exact s3_92
  · exact s3_93
  · exact s3_94
  · exact s3_95
  · exact s3_96
  · exact s3_97
  · exact s3_98
  · exact s3_99
  · exact s3_100
  · exact s3_101
  · exact s3_102
  · exact s3_103
  · exact s3_104
  · exact s3_105
  · exact s3_106
  · exact s3_107
  · exact s3_108
  · exact s3_109
  · exact s3_110
  · exact s3_111
  · exact s3_112
  · exact s3_113
  · exact s3_114
  · exact s3_115
  · exact s3_116
  · exact s3_117
  · exact s3_118
  · exact s3_119
  · exact s3_120
  · exact s3_121
  · exact s3_122
  · exact s3_123
  · exact s3_124
  · exact s3_125
  · exact s3_126
  · exact s3_127
  · exact s3_128
  · exact s3_129
  · exact s3_130
  · exact s3_131
  · exact s3_132
  · exact s3_133
  · exact s3_134
  · exact s3_135
  · exact s3_136
  · exact s3_137
  · exact s3_138
  · exact s3_139
  · exact s3_140
  · exact s3_141
private theorem s2_0 : safe 4 [0, 1023, 15, 114, 420, 840, 2, 4] := by
  apply stage good3 [(0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,13), (0,6), (2,6), (0,2), (0,11), (2,9), (0,3), (0,8), (0,4), (0,12), (0,5), (0,9), (2,4), (2,12), (2,5), (0,7), (0,10), (2,10), (2,14), (0,1), (0,14)]
  decide +kernel
private theorem s2_1 : safe 4 [0, 1023, 15, 114, 420, 840, 2, 127] := by
  apply stage good3 [(0,6), (0,6), (0,6), (0,6), (0,6), (0,6), (0,6), (0,6), (6,29), (0,6), (0,26), (1,6), (1,26), (0,29), (6,6), (6,26), (7,6), (7,26), (1,23), (0,24), (0,30), (0,25), (0,22), (0,27), (0,23), (1,25), (1,22), (1,27), (0,31), (0,28)]
  decide +kernel
private theorem s2_2 : safe 4 [0, 1023, 15, 114, 420, 840, 2, 183] := by
  apply stage good3 [(0,7), (0,7), (0,7), (0,7), (0,7), (0,7), (0,7), (0,7), (6,43), (0,23), (0,7), (0,38), (1,9), (0,42), (0,17), (0,35), (0,43), (6,7), (6,38), (7,9), (6,42), (6,17), (6,35), (0,40), (0,36), (0,44), (0,37), (0,33), (0,39), (0,41), (0,45)]
  decide +kernel
private theorem s2_3 : safe 4 [0, 1023, 15, 114, 420, 840, 2, 256] := by
  apply stage good3 [(0,24), (0,24), (0,24), (0,24), (0,24), (0,24), (0,24), (0,24), (22,36), (0,24), (2,4), (0,48), (3,4), (1,48), (0,47), (16,36), (12,4), (6,48), (13,4), (7,48), (6,47), (1,36), (16,24), (16,47), (0,36), (17,47), (16,49), (0,46), (0,49)]
  decide +kernel
private theorem s2_4 : safe 4 [0, 1023, 15, 114, 420, 840, 2, 422] := by
  apply stage good3 [(0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (0,15), (6,55), (0,25), (2,5), (0,52), (1,10), (0,54), (0,15), (0,55), (12,5), (6,52), (7,10), (6,54), (6,15), (1,41), (16,47), (0,56), (0,37), (0,53), (0,57), (0,58), (1,34)]
  decide +kernel
private theorem s2_5 : safe 4 [0, 1023, 15, 114, 420, 840, 2, 431] := by
  apply stage good3 [(0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,66), (0,26), (2,6), (1,11), (0,61), (0,63), (6,8), (0,59), (7,12), (0,62), (6,16), (0,60), (1,42), (0,48), (0,64), (0,52), (0,38), (1,54), (1,50), (0,65), (0,67), (7,32)]
  decide +kernel
private theorem s2_6 : safe 4 [0, 1023, 15, 114, 420, 840, 2, 909] := by
  apply stage good3 [(0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,19), (0,71), (0,29), (2,9), (0,63), (3,9), (1,63), (0,19), (0,68), (6,13), (6,66), (7,13), (7,66), (1,43), (16,36), (0,70), (0,55), (0,51), (0,69), (0,43), (1,55), (1,51), (1,69), (0,72)]
  decide +kernel
private theorem s2_7 : safe 4 [0, 1023, 15, 114, 420, 840, 2, 1004] := by
  apply stage good3 [(0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (0,18), (6,70), (0,30), (2,12), (0,64), (3,12), (1,64), (0,18), (0,74), (0,70), (12,12), (6,64), (13,12), (7,64), (6,18), (6,74), (1,44), (16,24), (0,56), (0,44), (1,56), (0,75), (0,73), (0,21)]
  decide +kernel
private theorem s2_8 : safe 4 [0, 1023, 15, 114, 420, 840, 2, 1021] := by
  apply stage good3 [(0,20), (0,20), (0,20), (0,20), (0,20), (0,20), (0,20), (0,20), (6,72), (0,31), (2,14), (0,67), (3,14), (1,67), (0,20), (0,72), (12,14), (6,67), (13,14), (7,67), (6,20), (1,45), (16,49), (0,75), (0,58), (0,45), (1,58)]
  decide +kernel
private theorem s2_9 : safe 4 [0, 1023, 15, 114, 420, 840, 6, 502] := by
  apply stage good3 [(0,16), (0,16), (0,16), (0,16), (0,16), (0,16), (0,16), (0,16), (0,87), (0,16), (0,78), (2,16), (2,78), (3,18), (0,85), (0,81), (2,83), (12,22), (13,50), (0,86), (0,77), (0,83), (16,50), (2,86), (2,77), (0,79), (0,84), (0,80), (0,89), (0,88), (0,82)]
  decide +kernel
private theorem s2_10 : safe 4 [0, 1023, 15, 114, 420, 840, 7, 183] := by
  apply stage good3 [(0,17), (0,17), (0,17), (0,17), (0,17), (0,17), (0,17), (0,17), (0,99), (0,17), (0,92), (2,17), (2,92), (3,19), (0,97), (0,93), (2,96), (12,33), (0,95), (13,51), (0,98), (0,91), (0,90), (0,94), (0,96), (16,51), (2,98), (2,91), (2,90), (2,94), (0,100)]
  decide +kernel
private theorem s2_11 : safe 4 [0, 1023, 15, 114, 420, 840, 19, 1004] := by
  apply stage good3 [(0,21), (0,21), (0,21), (0,21), (0,21), (0,21), (0,21), (0,21), (6,109), (0,21), (0,104), (2,32), (0,107), (3,32), (1,107), (0,76), (0,103), (4,82), (0,110), (0,109), (12,32), (6,107), (13,32), (7,107), (6,76), (6,103), (18,82), (6,110), (1,106), (16,28), (0,108), (0,106), (1,108)]
  decide +kernel
private theorem s2_12 : safe 4 [0, 1023, 15, 114, 420, 840, 127, 183] := by
  apply stage good3 [(0,23), (0,23), (0,23), (0,23), (0,23), (0,23), (0,23), (0,23), (6,122), (0,23), (2,38), (0,116), (3,63), (0,120), (0,92), (0,114), (0,122), (12,38), (6,116), (13,63), (6,120), (6,92), (6,114), (0,119), (16,70), (0,123), (8,79), (0,118), (8,95), (0,117), (9,87), (0,121), (16,109), (0,112), (0,115)]
  decide +kernel
private theorem s2_13 : safe 4 [0, 1023, 15, 114, 420, 840, 127, 431] := by
  apply stage good3 [(0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,26), (0,129), (0,26), (2,26), (3,61), (0,126), (4,120), (12,59), (0,124), (13,64), (0,127), (6,78), (0,125), (1,120), (16,64), (2,127), (8,78), (0,116), (9,86), (0,128), (11,86), (2,128), (16,107), (0,111), (13,107)]
  decide +kernel
private theorem s2_14 : safe 4 [0, 1023, 15, 114, 420, 840, 127, 511] := by
  apply stage good3 [(0,27), (0,27), (0,27), (0,27), (0,27), (0,27), (0,27), (0,27), (6,131), (0,27), (2,60), (0,125), (3,65), (1,128), (0,131), (12,60), (6,125), (13,65), (7,128), (1,121), (16,74), (0,132), (8,81), (0,118), (9,89), (0,130), (9,102), (16,110), (9,0)]
  decide +kernel
private theorem s2_15 : safe 4 [0, 1023, 15, 114, 420, 840, 127, 909] := by
  apply stage good3 [(0,29), (0,29), (0,29), (0,29), (0,29), (0,29), (0,29), (0,29), (0,135), (0,29), (4,42), (4,120), (5,42), (5,120), (4,97), (0,133), (12,66), (6,129), (13,66), (7,129), (1,122), (16,44), (16,123), (8,83), (0,131), (10,98), (0,134), (0,122), (9,83), (1,131), (11,98), (1,134), (16,106)]
  decide +kernel
private theorem s2_16 : safe 4 [0, 1023, 15, 114, 420, 840, 127, 1004] := by
  apply stage good3 [(0,30), (0,30), (0,30), (0,30), (0,30), (0,30), (0,30), (0,30), (22,123), (0,30), (2,62), (2,127), (3,62), (3,127), (4,85), (16,132), (16,123), (12,62), (12,127), (13,62), (13,127), (18,85), (22,132), (1,123), (16,30), (8,85), (0,132), (0,123), (9,85), (1,132), (16,104), (0,113), (0,104)]
  decide +kernel
private theorem s2_17 : safe 4 [0, 1023, 15, 114, 420, 840, 183, 191] := by
  apply stage good3 [(0,35), (0,35), (0,35), (0,35), (0,35), (0,35), (0,35), (0,35), (0,139), (0,35), (0,114), (2,35), (2,114), (3,68), (3,133), (0,93), (2,138), (12,39), (12,117), (13,69), (13,134), (6,94), (0,136), (0,137), (0,138), (16,69), (16,134), (8,94), (2,136), (2,137), (21,101)]
  decide +kernel
private theorem s2_18 : safe 4 [0, 1023, 15, 114, 420, 840, 183, 603] := by
  apply stage good3 [(0,40), (0,40), (0,40), (0,40), (0,40), (0,40), (0,40), (0,40), (6,141), (0,40), (0,119), (2,43), (2,122), (3,43), (3,122), (0,96), (0,138), (1,96), (1,138), (0,141), (12,43), (12,122), (13,43), (13,122), (6,96), (6,138), (7,96), (7,138), (16,71), (16,135), (8,99), (8,139), (9,99), (9,139), (0,105), (0,140)]
  decide +kernel
private theorem good2 (u : List T) (hu : u ∈ states2) : safe 4 u := by
  simp only [states2,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
private theorem s1_0 : safe 5 [0, 1023, 15, 114, 420, 840, 2] := by
  apply stage good2 [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (6,6), (0,1), (0,0), (0,5), (1,0), (1,5), (0,6), (6,0), (6,5), (7,0), (7,5), (1,2), (0,3), (0,7), (0,4), (0,2), (1,4), (0,8)]
  decide +kernel
private theorem s1_1 : safe 5 [0, 1023, 15, 114, 420, 840, 127] := by
  apply stage good2 [(0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (6,15), (0,1), (2,5), (0,13), (3,5), (1,13), (0,15), (12,5), (6,13), (13,5), (7,13), (1,12), (16,7), (0,16), (8,9), (0,14), (0,12), (9,9), (1,14), (16,11)]
  decide +kernel
private theorem s1_2 : safe 5 [0, 1023, 15, 114, 420, 840, 183] := by
  apply stage good2 [(0,2), (0,2), (0,2), (0,2), (0,2), (0,2), (0,2), (12,18), (0,2), (0,12), (2,2), (2,12), (3,6), (3,15), (0,10), (0,17), (2,18), (12,2), (12,12), (13,6), (13,15), (6,10), (6,17), (0,18), (16,6), (16,15), (8,10), (8,17)]
  decide +kernel
private theorem good1 (u : List T) (hu : u ∈ states1) : safe 5 u := by
  simp only [states1,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact s1_0
  · exact s1_1
  · exact s1_2
private theorem s0_0 : safe 6 [0, 1023, 15, 114, 420, 840] := by
  apply stage good1 [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (18,2), (0,0), (0,1), (2,0), (2,1), (3,0), (3,1), (4,2), (12,0), (12,1), (13,0), (13,1), (1,2), (16,0), (16,1), (0,2)]
  decide +kernel
private def samples : Fin 10 → Fin 6 × Fin 6 := ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]
private def inputs (i : Fin 10) :=
  List.ofFn fun k : Fin 6 => decide (k = (samples i).1 ∨ k = (samples i).2)

private theorem tables (C : Circuit)
    (he : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (33550 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :
    ∀ k, (C.gates.foldl step (ins.map (bit k))).getD C.output false = bit k target := by
  intro k
  have hi : ∀ i : Fin 10, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 10, (33550 : Nat).testBit
      (6 * min (samples i).1.val (samples i).2.val + max (samples i).1.val (samples i).2.val) = bit i target := by decide +kernel
  have h := he (samples k).1 (samples k).2
  change C.eval (inputs k) = _ at h
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using h

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (33550 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hg,hs,he⟩
  apply exclude C.gates C.output (fun g hm => hg g hm) ins [0,1023,15,114,420,840] _ 6 hs s0_0 (tables C he)
  intro x hx
  simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  tauto

theorem monotoneLower : ¬ (∃ C : Circuit, Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (33550 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hm,hs,he⟩
  apply generalLower
  refine ⟨C,?_,hs,he⟩
  intro g hg
  obtain ⟨ho,ha⟩ := hm g hg
  change g.op = .and ∨ g.op = .or at ho
  exact ⟨ho.imp_right Or.inl,ha⟩

#print axioms generalLower
#print axioms monotoneLower
end CliqueFourLower
