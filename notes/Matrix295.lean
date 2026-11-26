import PEqualNP.Defs.Represents

-- Search soundness adapted from Nico Habets and Lewis Watson, as credited in Mask53Exact.lean.
-- Original source: https://github.com/open-goat/pequalnp-proofs/blob/62a08312807b6a9ea0e9f8319897c74bf63e8be2/lean/PEqualNP/Outside/L_meta_5601.lean
-- For graph 1223 the support argument, separation certificates, input tables and theorem are new.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Matrix295

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 12
private def ins : List T := [15, 240, 3840, 273, 546, 1092, 2184]
private def target : T := 295
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 12) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin 12) :
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

private inductive Op
  | zero | ones | wire (x : T) | meet (x y : T) | join (x y : T)
  deriving DecidableEq

private def Op.args : Op → List T
  | .zero | .ones => []
  | .wire x => [x]
  | .meet x y | .join x y => [x,y]

private def Op.out : Op → T
  | .zero => 0
  | .ones => -1
  | .wire x => x
  | .meet x y => x &&& y
  | .join x y => x ||| y

private theorem origin {w z} (hz : possible w z) :
    ∃ g : Op, g.out = z ∧ g.args ⊆ w := by
  simp only [possible,Bool.or_eq_true,List.any_eq_true,beq_iff_eq] at hz
  rcases hz with ((h | h) | ⟨x,hx,(h | ⟨y,hy,h | h⟩)⟩) <;> subst z
  · exact ⟨.zero,rfl,by simp [Op.args]⟩
  · exact ⟨.ones,rfl,by simp [Op.args]⟩
  · exact ⟨.wire x,rfl,by simpa [Op.args] using hx⟩
  · exact ⟨.meet x y,rfl,by simpa [Op.args] using And.intro hx hy⟩
  · exact ⟨.join x y,rfl,by simpa [Op.args] using And.intro hx hy⟩

-- Trace the exact set of wire values required by the output cone backwards.
private inductive Need : Nat → Finset T → Prop
  | output : Need 0 {target}
  | skip {n s} : Need n s → Need (n+1) s
  | step {n s} (g : Op) : g.out ∈ s → Need n s →
      Need (n+1) (s.erase g.out ∪ g.args.toFinset)

private theorem extract {n w} (h : ¬ safe n w) :
    ∃ s ⊆ w.toFinset, Need n s := by
  classical
  induction n generalizing w with
  | zero =>
    have ht : target ∈ w := by simpa [safe] using h
    exact ⟨{target}, by simpa using ht, .output⟩
  | succ k ih =>
    change ¬ ∀ z, possible w z → safe k (z :: w) at h
    push Not at h
    obtain ⟨z,hz,hn⟩ := h
    obtain ⟨g,rfl,ha⟩ := origin hz
    obtain ⟨s,hs,hn⟩ := ih hn
    by_cases hm : g.out ∈ s
    · refine ⟨_,?_,.step g hm hn⟩
      intro x hx
      rcases Finset.mem_union.mp hx with he | he
      · obtain ⟨hne,hx⟩ := Finset.mem_erase.mp he
        have hx' : x = g.out ∨ x ∈ w := by simpa using hs hx
        exact List.mem_toFinset.mpr (hx'.resolve_left hne)
      · exact List.mem_toFinset.mpr (ha (List.mem_toFinset.mp he))
    · refine ⟨s,?_,.skip hn⟩
      intro x hx
      have hx' : x = g.out ∨ x ∈ w := by simpa using hs hx
      exact List.mem_toFinset.mpr (hx'.resolve_left (fun h => hm (h ▸ hx)))

private def down (x : T) (p q : Fin 12) : Prop := bit p x = true ∧ bit q x = false
private def covers (r : T → Fin 12 → Fin 12 → Prop) (s : Finset T) :=
  ∀ p q, down target p q → ∃ x ∈ s, r x p q

private theorem transfer {r s} {g : Op}
    (hs : covers r s) (hg : ∀ p q, r g.out p q → ∃ x ∈ g.args, r x p q) :
    covers r (s.erase g.out ∪ g.args.toFinset) := by
  intro p q ht
  obtain ⟨x,hx,hr⟩ := hs p q ht
  by_cases he : x = g.out
  · subst x
    obtain ⟨y,hy,hh⟩ := hg p q hr
    exact ⟨y,Finset.mem_union_right _ (List.mem_toFinset.mpr hy),hh⟩
  · exact ⟨x,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hx⟩),hr⟩


private theorem downFactors (g : Op) (p q) (h : down g.out p q) :
    ∃ x ∈ g.args, down x p q := by
  cases g
  case ones =>
    have ho : ∀ i : Fin 12, bit i (-1) = true := by decide +kernel
    exact False.elim (Bool.noConfusion ((ho q).symm.trans h.2))
  all_goals simp [Op.out,Op.args,down,bit] at *
  all_goals grind

private theorem bound {n s} (h : Need n s) : s.card ≤ n+1 ∧ covers down s := by
  induction h with
  | output =>
    refine ⟨by simp,?_⟩
    intro p q ht
    exact ⟨target,by simp,ht⟩
  | skip _ ih => exact ⟨by omega,ih.2⟩
  | @step n s g hm _ ih =>
    have hc := ih.1
    have hp := Finset.card_pos.mpr ⟨g.out,hm⟩
    have he := Finset.card_erase_of_mem hm
    have hu := Finset.card_union_le (s.erase g.out) g.args.toFinset
    have hlen : g.args.toFinset.card ≤ 2 := by
      calc
        _ ≤ g.args.length := List.toFinset_card_le _
        _ ≤ 2 := by cases g <;> simp [Op.args]
    exact ⟨by omega,transfer ih.2 (downFactors g)⟩

private def viable (n : Nat) (w : List T) : Bool :=
  decide (w.toFinset.card ≤ n+1) && (List.finRange 12).all (fun p =>
    (List.finRange 12).all (fun q => !(bit p target && !(bit q target)) ||
      w.any (fun x => bit p x && !(bit q x))))

private theorem fits {n w} (h : Need n w.toFinset) : viable n w = true := by
  obtain ⟨hc,hd⟩ := bound h
  simp only [viable, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨hc,?_⟩
  intro p _ q _
  by_cases ht : down target p q
  · obtain ⟨x,hx,hp,hq⟩ := hd p q ht
    rw [Bool.or_eq_true]
    exact .inr (List.any_eq_true.mpr ⟨x,List.mem_toFinset.mp hx,by simp [hp,hq]⟩)
  · rw [Bool.or_eq_true]
    left
    unfold down at ht
    cases hp : bit p target <;> cases hq : bit q target <;> simp_all

private def ops (w : List T) : List Op :=
  .zero :: .ones :: w.flatMap (fun x => .wire x ::
    w.flatMap (fun y => [.meet x y,.join x y]))

private theorem mem_ops {g : Op} {w : List T} (h : g.args ⊆ w) : g ∈ ops w := by
  cases g <;> simp [Op.args,ops,List.mem_flatMap] at * <;> grind

private def kids (w : List T) : List (List T) :=
  w :: (ops w).flatMap (fun g => g.args.sublists.map (fun drop =>
    g.out :: w.filter (fun x => !(drop.contains x))))

private theorem child {w : List T} {s : Finset T} {g : Op} (hg : g.out ∈ s)
    (he : s.erase g.out ∪ g.args.toFinset = w.toFinset) : ∃ v ∈ kids w, v.toFinset = s := by
  classical
  let rest := s.erase g.out
  let drop := g.args.filter (fun x => decide (x ∉ rest))
  have hargs : g.args ⊆ w := by
    intro x hx
    apply List.mem_toFinset.mp
    rw [← he]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr hx)
  have hdrop : drop ∈ g.args.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  let v := g.out :: w.filter (fun x => !(drop.contains x))
  refine ⟨v,List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g,mem_ops hargs,
    List.mem_map.mpr ⟨drop,hdrop,rfl⟩⟩),?_⟩
  ext x
  have hx : x ∈ w ↔ x ∈ rest ∨ x ∈ g.args := by
    rw [← List.mem_toFinset,← he]
    simp [rest]
  have hd0 : drop.contains x = false ↔ x ∉ drop := by simp
  simp only [v,List.mem_toFinset,List.mem_cons,List.mem_filter,Bool.not_eq_true',hd0]
  have hd : x ∈ drop ↔ x ∈ g.args ∧ x ∉ rest := by simp [drop]
  have hr : x ∈ rest ↔ x ≠ g.out ∧ x ∈ s := Finset.mem_erase
  grind

private def locate (v : List T) (pool : List (List T)) : Bool :=
  pool.any (fun u => v.all (fun x => u.contains x) && u.all (fun x => v.contains x))

private theorem located {v pool} (h : locate v pool = true) : ∃ u ∈ pool, u.toFinset = v.toFinset := by
  obtain ⟨u,hu,hb⟩ := List.any_eq_true.mp h
  change (v.all (fun x => u.contains x) && u.all (fun x => v.contains x)) = true at hb
  simp only [Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem] at hb
  refine ⟨u,hu,?_⟩
  ext x
  simp only [List.mem_toFinset]
  exact ⟨hb.2 x,hb.1 x⟩

private def routes (n : Nat) (next : List (List T)) (w : List T) : Bool :=
  (kids w).all fun v => !viable n v || locate v next

private theorem route_sound {n w next}
    (hh : ∀ v ∈ next, ¬ Need n v.toFinset) (hr : routes n next w = true) :
    ¬ Need (n+1) w.toFinset := by
  intro h
  have ban (v : List T) (hv : v ∈ kids w) (hn : Need n v.toFinset) : False := by
    have hnext := (List.all_eq_true.mp hr) v hv
    have found : locate v next = true := by simpa [fits hn] using hnext
    obtain ⟨u,hu,he⟩ := located found
    exact hh _ hu (he ▸ hn)
  generalize he : w.toFinset = s at h
  cases h with
  | skip h => exact ban w (by simp [kids]) (he ▸ h)
  | step g hm hn =>
    obtain ⟨v,hv,hs⟩ := child hm he.symm
    exact ban v hv (hs ▸ hn)

private theorem initial {n : Nat} {w : List T} {next : List (List T)} (hh : ∀ v ∈ next, ¬ Need n v.toFinset)
    (hr : w.sublists.all (fun v => !viable n v || locate v next) = true) : safe n w := by
  classical
  by_contra h
  obtain ⟨s,hs,hn⟩ := extract h
  let v := w.filter (fun x => decide (x ∈ s))
  have hv : v ∈ w.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have he : v.toFinset = s := by
    ext x; simp [v]; exact fun hx => List.mem_toFinset.mp (hs hx)
  have hf := fits (he ▸ hn : Need n v.toFinset)
  have hx := (List.all_eq_true.mp hr) v hv
  have found : locate v next = true := by simpa [hf] using hx
  obtain ⟨u,hu,he'⟩ := located found
  exact hh _ hu (he'.trans he ▸ hn)
private def wire4 : T := 4
private def wire15 : T := 15
private def wire32 : T := 32
private def wire34 : T := 34
private def wire47 : T := 47
private def wire240 : T := 240
private def wire244 : T := 244
private def wire255 : T := 255
private def wire256 : T := 256
private def wire257 : T := 257
private def wire271 : T := 271
private def wire273 : T := 273
private def wire277 : T := 277
private def wire305 : T := 305
private def wire497 : T := 497
private def wire501 : T := 501
private def wire546 : T := 546
private def wire550 : T := 550
private def wire802 : T := 802
private def wire1092 : T := 1092
private def wire1124 : T := 1124
private def wire1268 : T := 1268
private def wire1348 : T := 1348
private def wire1365 : T := 1365
private def wire1525 : T := 1525
private def wire1638 : T := 1638
private def wire2184 : T := 2184
private def wire2191 : T := 2191
private def wire2296 : T := 2296
private def wire3840 : T := 3840
private def wire3844 : T := 3844
private def wire3855 : T := 3855
private def wire3874 : T := 3874
private def wire3878 : T := 3878
private def wire3908 : T := 3908
private def wire3942 : T := 3942
private def wire3976 : T := 3976

-- Every listed set is checked against every possible next output and every reuse of its inputs.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def layer1 : List (List T) := []
private theorem good1 (w : List T) (h : w ∈ layer1) : ¬ Need 1 w.toFinset := by simp [layer1] at h
private def chunk2_0 : List (List T) := [[wire15,wire305,wire3942],
  [wire15,wire497,wire3878],
  [wire15,wire501,wire3874],
  [wire15,wire802,wire1525]]
private def pool2_0 : List (List (List T)) := []
private theorem checked2_0 : ∀ w ∈ chunk2_0, ¬ Need 2 w.toFinset := by
  have h : chunk2_0.all (routes 1 pool2_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool2_0] at hv
private def chunk2_1 : List (List T) := [[wire47,wire273,wire3942],
  [wire271,wire546,wire1525]]
private def pool2_1 : List (List (List T)) := []
private theorem checked2_1 : ∀ w ∈ chunk2_1, ¬ Need 2 w.toFinset := by
  have h : chunk2_1.all (routes 1 pool2_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool2_1] at hv
#print axioms checked2_1
private def chunk3_0 : List (List T) := [[wire4,wire15,wire497,wire3874],
  [wire15,wire32,wire273,wire3942],
  [wire15,wire34,wire273,wire3908],
  [wire15,wire240,wire273,wire3878]]
private def pool3_0 : List (List (List T)) := [chunk2_0, chunk2_1]
private theorem checked3_0 : ∀ w ∈ chunk3_0, ¬ Need 3 w.toFinset := by
  have h : chunk3_0.all (routes 2 pool3_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked2_0 _ hm
  · exact checked2_1 _ hm
private def chunk3_1 : List (List T) := [[wire15,wire240,wire277,wire3874],
  [wire15,wire240,wire802,wire1365],
  [wire15,wire244,wire273,wire3874],
  [wire15,wire256,wire546,wire1525]]
private def pool3_1 : List (List (List T)) := [chunk2_0, chunk2_1]
private theorem checked3_1 : ∀ w ∈ chunk3_1, ¬ Need 3 w.toFinset := by
  have h : chunk3_1.all (routes 2 pool3_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked2_0 _ hm
  · exact checked2_1 _ hm
private def chunk3_2 : List (List T) := [[wire15,wire257,wire546,wire1268],
  [wire15,wire273,wire802,wire1268],
  [wire15,wire305,wire546,wire3908],
  [wire15,wire305,wire1092,wire3874]]
private def pool3_2 : List (List (List T)) := [chunk2_0]
private theorem checked3_2 : ∀ w ∈ chunk3_2, ¬ Need 3 w.toFinset := by
  have h : chunk3_2.all (routes 2 pool3_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
private def chunk3_3 : List (List T) := [[wire15,wire305,wire1638,wire3840],
  [wire15,wire497,wire546,wire3844],
  [wire15,wire497,wire550,wire3840],
  [wire15,wire497,wire802,wire1092]]
private def pool3_3 : List (List (List T)) := [chunk2_0]
private theorem checked3_3 : ∀ w ∈ chunk3_3, ¬ Need 3 w.toFinset := by
  have h : chunk3_3.all (routes 2 pool3_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
private def chunk3_4 : List (List T) := [[wire15,wire497,wire1092,wire3874],
  [wire15,wire497,wire1268,wire3874],
  [wire15,wire497,wire1365,wire3874],
  [wire15,wire497,wire1525,wire3874]]
private def pool3_4 : List (List (List T)) := []
private theorem checked3_4 : ∀ w ∈ chunk3_4, ¬ Need 3 w.toFinset := by
  have h : chunk3_4.all (routes 2 pool3_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_4] at hv
private def chunk3_5 : List (List T) := [[wire15,wire497,wire1638,wire3874],
  [wire15,wire497,wire3874,wire3908],
  [wire15,wire497,wire3874,wire3942],
  [wire15,wire501,wire546,wire3840]]
private def pool3_5 : List (List (List T)) := [chunk2_0]
private theorem checked3_5 : ∀ w ∈ chunk3_5, ¬ Need 3 w.toFinset := by
  have h : chunk3_5.all (routes 2 pool3_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
private def chunk3_6 : List (List T) := [[wire47,wire273,wire546,wire3908],
  [wire47,wire273,wire1092,wire3874],
  [wire47,wire273,wire1638,wire3840],
  [wire240,wire271,wire546,wire1365]]
private def pool3_6 : List (List (List T)) := [chunk2_1]
private theorem checked3_6 : ∀ w ∈ chunk3_6, ¬ Need 3 w.toFinset := by
  have h : chunk3_6.all (routes 2 pool3_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
private def chunk3_7 : List (List T) := [[wire271,wire273,wire546,wire1268],
  [wire271,wire497,wire546,wire1092]]
private def pool3_7 : List (List (List T)) := [chunk2_1]
private theorem checked3_7 : ∀ w ∈ chunk3_7, ¬ Need 3 w.toFinset := by
  have h : chunk3_7.all (routes 2 pool3_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
#print axioms checked3_7
private def chunk4_0 : List (List T) := [[wire4,wire15,wire240,wire273,wire3874],
  [wire4,wire15,wire497,wire546,wire3840],
  [wire15,wire32,wire273,wire546,wire3908],
  [wire15,wire32,wire273,wire1092,wire3874]]
private def pool4_0 : List (List (List T)) := [chunk3_0, chunk3_1, chunk3_2, chunk3_3, chunk3_5, chunk3_6]
private theorem checked4_0 : ∀ w ∈ chunk4_0, ¬ Need 4 w.toFinset := by
  have h : chunk4_0.all (routes 3 pool4_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_1 _ hm
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
private def chunk4_1 : List (List T) := [[wire15,wire32,wire273,wire1638,wire3840],
  [wire15,wire34,wire273,wire1092,wire3840],
  [wire15,wire240,wire256,wire546,wire1365],
  [wire15,wire240,wire257,wire546,wire1092]]
private def pool4_1 : List (List (List T)) := [chunk3_0, chunk3_1, chunk3_2, chunk3_3, chunk3_6]
private theorem checked4_1 : ∀ w ∈ chunk4_1, ¬ Need 4 w.toFinset := by
  have h : chunk4_1.all (routes 3 pool4_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_1 _ hm
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
  · exact checked3_6 _ hm
private def chunk4_2 : List (List T) := [[wire15,wire240,wire273,wire546,wire1348],
  [wire15,wire240,wire273,wire546,wire3844],
  [wire15,wire240,wire273,wire546,wire3908],
  [wire15,wire240,wire273,wire546,wire3942]]
private def pool4_2 : List (List (List T)) := [chunk3_0, chunk3_3]
private theorem checked4_2 : ∀ w ∈ chunk4_2, ¬ Need 4 w.toFinset := by
  have h : chunk4_2.all (routes 3 pool4_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_3 _ hm
private def chunk4_3 : List (List T) := [[wire15,wire240,wire273,wire550,wire3840],
  [wire15,wire240,wire273,wire802,wire1092],
  [wire15,wire240,wire273,wire1092,wire3874],
  [wire15,wire240,wire273,wire1268,wire3874]]
private def pool4_3 : List (List (List T)) := [chunk3_0, chunk3_1, chunk3_2, chunk3_3, chunk3_4]
private theorem checked4_3 : ∀ w ∈ chunk4_3, ¬ Need 4 w.toFinset := by
  have h : chunk4_3.all (routes 3 pool4_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_1 _ hm
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
  · exact checked3_4 _ hm
private def chunk4_4 : List (List T) := [[wire15,wire240,wire273,wire1365,wire3874],
  [wire15,wire240,wire273,wire1638,wire3874],
  [wire15,wire240,wire273,wire3874,wire3908],
  [wire15,wire240,wire273,wire3874,wire3942]]
private def pool4_4 : List (List (List T)) := [chunk3_0, chunk3_4, chunk3_5]
private theorem checked4_4 : ∀ w ∈ chunk4_4, ¬ Need 4 w.toFinset := by
  have h : chunk4_4.all (routes 3 pool4_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
private def chunk4_5 : List (List T) := [[wire15,wire240,wire277,wire546,wire3840],
  [wire15,wire240,wire497,wire1092,wire3874],
  [wire15,wire244,wire273,wire546,wire3840],
  [wire15,wire255,wire273,wire546,wire3908]]
private def pool4_5 : List (List (List T)) := [chunk3_0, chunk3_1, chunk3_4, chunk3_5]
private theorem checked4_5 : ∀ w ∈ chunk4_5, ¬ Need 4 w.toFinset := by
  have h : chunk4_5.all (routes 3 pool4_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_1 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
private def chunk4_6 : List (List T) := [[wire15,wire255,wire273,wire1092,wire3874],
  [wire15,wire256,wire273,wire546,wire1268],
  [wire15,wire256,wire497,wire546,wire1092],
  [wire15,wire273,wire497,wire546,wire3908]]
private def pool4_6 : List (List (List T)) := [chunk3_1, chunk3_2, chunk3_3, chunk3_7]
private theorem checked4_6 : ∀ w ∈ chunk4_6, ¬ Need 4 w.toFinset := by
  have h : chunk4_6.all (routes 3 pool4_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_1 _ hm
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
  · exact checked3_7 _ hm
private def chunk4_7 : List (List T) := [[wire15,wire273,wire497,wire1092,wire3874],
  [wire15,wire273,wire546,wire1124,wire3840],
  [wire15,wire273,wire546,wire1268,wire3840],
  [wire15,wire273,wire546,wire1268,wire3855]]
private def pool4_7 : List (List (List T)) := [chunk3_2, chunk3_4]
private theorem checked4_7 : ∀ w ∈ chunk4_7, ¬ Need 4 w.toFinset := by
  have h : chunk4_7.all (routes 3 pool4_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_4 _ hm
private def chunk4_8 : List (List T) := [[wire15,wire273,wire546,wire1268,wire3874],
  [wire15,wire273,wire546,wire1268,wire3908],
  [wire15,wire273,wire546,wire1268,wire3976],
  [wire15,wire273,wire546,wire1525,wire3840]]
private def pool4_8 : List (List (List T)) := [chunk3_1]
private theorem checked4_8 : ∀ w ∈ chunk4_8, ¬ Need 4 w.toFinset := by
  have h : chunk4_8.all (routes 3 pool4_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_1 _ hm
private def chunk4_9 : List (List T) := [[wire15,wire273,wire546,wire2296,wire3908],
  [wire15,wire305,wire546,wire1092,wire3840],
  [wire15,wire497,wire546,wire1092,wire3840],
  [wire15,wire497,wire546,wire1092,wire3855]]
private def pool4_9 : List (List (List T)) := [chunk3_2, chunk3_3, chunk3_4]
private theorem checked4_9 : ∀ w ∈ chunk4_9, ¬ Need 4 w.toFinset := by
  have h : chunk4_9.all (routes 3 pool4_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
  · exact checked3_4 _ hm
private def chunk4_10 : List (List T) := [[wire15,wire497,wire546,wire1092,wire3874],
  [wire15,wire497,wire546,wire1268,wire3840],
  [wire15,wire497,wire546,wire1365,wire3840],
  [wire15,wire497,wire546,wire1525,wire3840]]
private def pool4_10 : List (List (List T)) := [chunk3_1, chunk3_4, chunk3_5]
private theorem checked4_10 : ∀ w ∈ chunk4_10, ¬ Need 4 w.toFinset := by
  have h : chunk4_10.all (routes 3 pool4_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_1 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
private def chunk4_11 : List (List T) := [[wire15,wire497,wire546,wire1638,wire3840],
  [wire15,wire497,wire546,wire3840,wire3908],
  [wire15,wire497,wire1092,wire2184,wire3874],
  [wire15,wire497,wire1092,wire3840,wire3874]]
private def pool4_11 : List (List (List T)) := [chunk3_4, chunk3_5]
private theorem checked4_11 : ∀ w ∈ chunk4_11, ¬ Need 4 w.toFinset := by
  have h : chunk4_11.all (routes 3 pool4_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
private def chunk4_12 : List (List T) := [[wire15,wire497,wire1092,wire3874],
  [wire47,wire273,wire546,wire1092,wire3840],
  [wire240,wire271,wire273,wire546,wire1092],
  [wire255,wire273,wire546,wire1092,wire3855]]
private def pool4_12 : List (List (List T)) := [chunk3_0, chunk3_4, chunk3_5, chunk3_6, chunk3_7]
private theorem checked4_12 : ∀ w ∈ chunk4_12, ¬ Need 4 w.toFinset := by
  have h : chunk4_12.all (routes 3 pool4_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
#print axioms checked4_12
private def chunk5_0 : List (List T) := [[wire4,wire15,wire240,wire273,wire546,wire3840],
  [wire15,wire32,wire273,wire546,wire1092,wire3840],
  [wire15,wire240,wire256,wire273,wire546,wire1092],
  [wire15,wire240,wire273,wire546,wire1092,wire3840]]
private def pool5_0 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_2, chunk4_3, chunk4_5, chunk4_6, chunk4_7, chunk4_9, chunk4_12]
private theorem checked5_0 : ∀ w ∈ chunk5_0, ¬ Need 5 w.toFinset := by
  have h : chunk5_0.all (routes 4 pool5_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_9 _ hm
  · exact checked4_12 _ hm
private def chunk5_1 : List (List T) := [[wire15,wire240,wire273,wire546,wire1092,wire3855],
  [wire15,wire240,wire273,wire546,wire1092,wire3874],
  [wire15,wire240,wire273,wire546,wire1092,wire3908],
  [wire15,wire240,wire273,wire546,wire1092,wire3976]]
private def pool5_1 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_2, chunk4_3, chunk4_4, chunk4_7, chunk4_8, chunk4_9, chunk4_10, chunk4_12]
private theorem checked5_1 : ∀ w ∈ chunk5_1, ¬ Need 5 w.toFinset := by
  have h : chunk5_1.all (routes 4 pool5_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
private def chunk5_2 : List (List T) := [[wire15,wire240,wire273,wire546,wire1268,wire3840],
  [wire15,wire240,wire273,wire546,wire1365,wire3840],
  [wire15,wire240,wire273,wire546,wire1638,wire3840],
  [wire15,wire240,wire273,wire546,wire2184,wire3908]]
private def pool5_2 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_3, chunk4_4, chunk4_7, chunk4_8, chunk4_9, chunk4_10, chunk4_11]
private theorem checked5_2 : ∀ w ∈ chunk5_2, ¬ Need 5 w.toFinset := by
  have h : chunk5_2.all (routes 4 pool5_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
private def chunk5_3 : List (List T) := [[wire15,wire240,wire273,wire546,wire3840,wire3908],
  [wire15,wire240,wire273,wire546,wire3908],
  [wire15,wire240,wire273,wire1092,wire2184,wire3874],
  [wire15,wire240,wire273,wire1092,wire3840,wire3874]]
private def pool5_3 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_3, chunk4_4, chunk4_5, chunk4_6, chunk4_11]
private theorem checked5_3 : ∀ w ∈ chunk5_3, ¬ Need 5 w.toFinset := by
  have h : chunk5_3.all (routes 4 pool5_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_11 _ hm
private def chunk5_4 : List (List T) := [[wire15,wire240,wire273,wire1092,wire3874],
  [wire15,wire240,wire497,wire546,wire1092,wire3840],
  [wire15,wire255,wire273,wire546,wire1092,wire3840],
  [wire15,wire273,wire497,wire546,wire1092,wire3840]]
private def pool5_4 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_3, chunk4_4, chunk4_5, chunk4_6, chunk4_7, chunk4_8, chunk4_9, chunk4_10, chunk4_12]
private theorem checked5_4 : ∀ w ∈ chunk5_4, ¬ Need 5 w.toFinset := by
  have h : chunk5_4.all (routes 4 pool5_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
private def chunk5_5 : List (List T) := [[wire15,wire273,wire546,wire1092,wire1268,wire3840],
  [wire15,wire273,wire546,wire1092,wire2296,wire3840],
  [wire15,wire273,wire546,wire1268,wire2184,wire3840],
  [wire15,wire273,wire546,wire1268,wire3840]]
private def pool5_5 : List (List (List T)) := [chunk4_6, chunk4_7, chunk4_8, chunk4_9]
private theorem checked5_5 : ∀ w ∈ chunk5_5, ¬ Need 5 w.toFinset := by
  have h : chunk5_5.all (routes 4 pool5_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
private def chunk5_6 : List (List T) := [[wire15,wire497,wire546,wire1092,wire2184,wire3840],
  [wire15,wire497,wire546,wire1092,wire3840],
  [wire240,wire273,wire546,wire1092,wire2191,wire3840]]
private def pool5_6 : List (List (List T)) := [chunk4_0, chunk4_6, chunk4_9, chunk4_10, chunk4_11, chunk4_12]
private theorem checked5_6 : ∀ w ∈ chunk5_6, ¬ Need 5 w.toFinset := by
  have h : chunk5_6.all (routes 4 pool5_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_6 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
#print axioms checked5_6
private def chunk6_0 : List (List T) := [[wire15,wire240,wire273,wire546,wire1092,wire2184,wire3840],
  [wire15,wire240,wire273,wire546,wire1092,wire3840]]
private def pool6_0 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_2, chunk5_3, chunk5_4, chunk5_5, chunk5_6]
private theorem checked6_0 : ∀ w ∈ chunk6_0, ¬ Need 6 w.toFinset := by
  have h : chunk6_0.all (routes 5 pool6_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
#print axioms checked6_0
private theorem root : safe 6 ins := initial checked6_0 (by decide +kernel)
def graph (u : Fin 3) (v : Fin 4) := (295 : Nat).testBit (4 * u.val + v.val)
def row (i : Fin 12) : Fin 3 := ⟨i.val / 4, by have := i.isLt; omega⟩
def col (i : Fin 12) : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
def inputs (i : Fin 12) := PEqualNP.Represents.oneEach (row i) (col i)

theorem exactLower : ¬ PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 3) (v : Fin 4) => (295 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  rintro ⟨C, hg, hsize, he⟩
  apply exclude C.gates C.output (fun g hm => hg g hm) ins ins (fun ⦃_⦄ h => h) 6 hsize root
  intro k
  have hi : ∀ i : Fin 12, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 12, graph (row i) (col i) = bit i target := by decide +kernel
  have heval : C.eval (inputs k) = graph (row k) (col k) := he (row k) (col k)
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using heval

#print axioms exactLower


def circuit : Circuit :=
  { gates := [⟨.and,[0,5]⟩, ⟨.or,[0,1]⟩, ⟨.and,[8,4]⟩, ⟨.or,[0,2]⟩,
              ⟨.and,[10,3]⟩, ⟨.or,[7,9]⟩, ⟨.or,[12,11]⟩], output := 13 }
theorem upper : PEqualNP.Represents.RepSizeAtMost graph 7 := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
#print axioms upper
end Matrix295
