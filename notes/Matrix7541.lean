import PEqualNP.Defs.Represents

-- Search soundness adapted from Nico Habets and Lewis Watson, as credited in Mask53Exact.lean.
-- Original source: https://github.com/open-goat/pequalnp-proofs/blob/62a08312807b6a9ea0e9f8319897c74bf63e8be2/lean/PEqualNP/Outside/L_meta_5601.lean
-- For graph 1223 the support argument, separation certificates, input tables and theorem are new.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Matrix7541

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 15
private def ins : List T := [31, 992, 31744, 1057, 2114, 4228, 8456, 16912]
private def target : T := 7541
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

private def down (x : T) (p q : Fin 15) : Prop := bit p x = true ∧ bit q x = false
private def covers (r : T → Fin 15 → Fin 15 → Prop) (s : Finset T) :=
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
    have ho : ∀ i : Fin 15, bit i (-1) = true := by decide +kernel
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
  decide (w.toFinset.card ≤ n+1) && (List.finRange 15).all (fun p =>
    (List.finRange 15).all (fun q => !(bit p target && !(bit q target)) ||
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
private def wire16 : T := 16
private def wire20 : T := 20
private def wire31 : T := 31
private def wire256 : T := 256
private def wire276 : T := 276
private def wire287 : T := 287
private def wire320 : T := 320
private def wire336 : T := 336
private def wire992 : T := 992
private def wire1008 : T := 1008
private def wire1057 : T := 1057
private def wire1073 : T := 1073
private def wire1077 : T := 1077
private def wire1087 : T := 1087
private def wire1313 : T := 1313
private def wire1333 : T := 1333
private def wire1377 : T := 1377
private def wire1393 : T := 1393
private def wire2017 : T := 2017
private def wire2114 : T := 2114
private def wire2143 : T := 2143
private def wire2370 : T := 2370
private def wire2399 : T := 2399
private def wire3171 : T := 3171
private def wire3199 : T := 3199
private def wire4228 : T := 4228
private def wire4244 : T := 4244
private def wire5092 : T := 5092
private def wire5108 : T := 5108
private def wire5285 : T := 5285
private def wire6117 : T := 6117
private def wire8456 : T := 8456
private def wire8479 : T := 8479
private def wire9513 : T := 9513
private def wire9535 : T := 9535
private def wire10570 : T := 10570
private def wire10591 : T := 10591
private def wire16912 : T := 16912
private def wire17392 : T := 17392
private def wire17969 : T := 17969
private def wire18417 : T := 18417
private def wire21140 : T := 21140
private def wire21492 : T := 21492
private def wire31744 : T := 31744
private def wire31760 : T := 31760
private def wire31777 : T := 31777
private def wire32000 : T := 32000
private def wire32008 : T := 32008
private def wire32041 : T := 32041
private def wire32272 : T := 32272
private def wire32305 : T := 32305

-- Every listed set is checked against every possible next output and every reuse of its inputs.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def layer2 : List (List T) := []
private theorem good2 (w : List T) (h : w ∈ layer2) : ¬ Need 2 w.toFinset := by simp [layer2] at h
private def chunk3_0 : List (List T) := [[wire1077,wire2114,wire5092,wire32008],
  [wire1333,wire2114,wire5092,wire31744],
  [wire1377,wire2143,wire4228,wire32272],
  [wire1393,wire2143,wire4228,wire31744]]
private def pool3_0 : List (List (List T)) := []
private theorem checked3_0 : ∀ w ∈ chunk3_0, ¬ Need 3 w.toFinset := by
  have h : chunk3_0.all (routes 2 pool3_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_0] at hv
#print axioms checked3_0
private def chunk4_0 : List (List T) := [[wire20,wire1057,wire2114,wire5092,wire32008],
  [wire31,wire1057,wire2114,wire5108,wire32008],
  [wire31,wire1073,wire2114,wire5092,wire32008],
  [wire31,wire1377,wire2114,wire4228,wire32272]]
private def pool4_0 : List (List (List T)) := [chunk3_0]
private theorem checked4_0 : ∀ w ∈ chunk4_0, ¬ Need 4 w.toFinset := by
  have h : chunk4_0.all (routes 3 pool4_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_1 : List (List T) := [[wire31,wire2114,wire6117,wire16912,wire32041],
  [wire31,wire3171,wire5092,wire16912,wire32041],
  [wire31,wire3171,wire5092,wire17969,wire32008],
  [wire31,wire3171,wire6117,wire16912,wire32008]]
private def pool4_1 : List (List (List T)) := []
private theorem checked4_1 : ∀ w ∈ chunk4_1, ¬ Need 4 w.toFinset := by
  have h : chunk4_1.all (routes 3 pool4_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_1] at hv
private def chunk4_2 : List (List T) := [[wire276,wire1057,wire2114,wire5092,wire31744],
  [wire320,wire1057,wire2143,wire4228,wire32272],
  [wire336,wire1057,wire2143,wire4228,wire31744],
  [wire992,wire1057,wire2399,wire4228,wire32272]]
private def pool4_2 : List (List (List T)) := [chunk3_0]
private theorem checked4_2 : ∀ w ∈ chunk4_2, ¬ Need 4 w.toFinset := by
  have h : chunk4_2.all (routes 3 pool4_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_3 : List (List T) := [[wire992,wire1077,wire2114,wire4228,wire32008],
  [wire992,wire1313,wire2143,wire4228,wire32272],
  [wire992,wire2143,wire5285,wire8456,wire32305],
  [wire992,wire2143,wire5285,wire9513,wire32272]]
private def pool4_3 : List (List (List T)) := [chunk3_0]
private theorem checked4_3 : ∀ w ∈ chunk4_3, ¬ Need 4 w.toFinset := by
  have h : chunk4_3.all (routes 3 pool4_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_4 : List (List T) := [[wire992,wire3199,wire4228,wire8456,wire32305],
  [wire992,wire3199,wire5285,wire8456,wire32272],
  [wire1057,wire2114,wire5108,wire8479,wire31744],
  [wire1057,wire2143,wire5092,wire8456,wire31760]]
private def pool4_4 : List (List (List T)) := []
private theorem checked4_4 : ∀ w ∈ chunk4_4, ¬ Need 4 w.toFinset := by
  have h : chunk4_4.all (routes 3 pool4_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_4] at hv
private def chunk4_5 : List (List T) := [[wire1057,wire2143,wire5092,wire16912,wire32000],
  [wire1057,wire2143,wire5092,wire32008,wire32272],
  [wire1057,wire2143,wire5108,wire8456,wire31744],
  [wire1057,wire2399,wire4228,wire17392,wire31744]]
private def pool4_5 : List (List (List T)) := []
private theorem checked4_5 : ∀ w ∈ chunk4_5, ¬ Need 4 w.toFinset := by
  have h : chunk4_5.all (routes 3 pool4_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_5] at hv
private def chunk4_6 : List (List T) := [[wire1057,wire2399,wire5092,wire16912,wire31744],
  [wire1073,wire2114,wire5092,wire8479,wire31744],
  [wire1073,wire2143,wire5092,wire8456,wire31744],
  [wire1077,wire2114,wire5092,wire8456,wire31744]]
private def pool4_6 : List (List (List T)) := [chunk3_0]
private theorem checked4_6 : ∀ w ∈ chunk4_6, ¬ Need 4 w.toFinset := by
  have h : chunk4_6.all (routes 3 pool4_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_7 : List (List T) := [[wire1087,wire2114,wire5092,wire17969,wire32008],
  [wire1087,wire2114,wire6117,wire16912,wire32008],
  [wire1313,wire2143,wire4228,wire17392,wire31744],
  [wire1313,wire2143,wire5092,wire16912,wire31744]]
private def pool4_7 : List (List (List T)) := []
private theorem checked4_7 : ∀ w ∈ chunk4_7, ¬ Need 4 w.toFinset := by
  have h : chunk4_7.all (routes 3 pool4_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_7] at hv
private def chunk4_8 : List (List T) := [[wire1377,wire2143,wire4228,wire16912,wire31744],
  [wire2017,wire2143,wire4228,wire9513,wire32272],
  [wire2017,wire3199,wire4228,wire8456,wire32272],
  [wire2114,wire4228,wire9535,wire18417,wire31744]]
private def pool4_8 : List (List (List T)) := [chunk3_0]
private theorem checked4_8 : ∀ w ∈ chunk4_8, ¬ Need 4 w.toFinset := by
  have h : chunk4_8.all (routes 3 pool4_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_9 : List (List T) := [[wire2114,wire5092,wire9535,wire17969,wire31744],
  [wire2114,wire5285,wire8479,wire17392,wire31777],
  [wire2114,wire5285,wire9535,wire17392,wire31744],
  [wire2114,wire6117,wire8479,wire16912,wire31777]]
private def pool4_9 : List (List (List T)) := []
private theorem checked4_9 : ∀ w ∈ chunk4_9, ¬ Need 4 w.toFinset := by
  have h : chunk4_9.all (routes 3 pool4_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_9] at hv
private def chunk4_10 : List (List T) := [[wire2114,wire6117,wire9535,wire16912,wire31744],
  [wire2143,wire4228,wire9513,wire18417,wire31744],
  [wire2143,wire5092,wire9513,wire17969,wire31744],
  [wire2143,wire5285,wire8456,wire17392,wire31777]]
private def pool4_10 : List (List (List T)) := []
private theorem checked4_10 : ∀ w ∈ chunk4_10, ¬ Need 4 w.toFinset := by
  have h : chunk4_10.all (routes 3 pool4_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_10] at hv
private def chunk4_11 : List (List T) := [[wire2143,wire5285,wire9513,wire17392,wire31744],
  [wire2143,wire6117,wire8456,wire16912,wire31777],
  [wire2143,wire6117,wire9513,wire16912,wire31744],
  [wire3171,wire4228,wire8479,wire17392,wire31777]]
private def pool4_11 : List (List (List T)) := []
private theorem checked4_11 : ∀ w ∈ chunk4_11, ¬ Need 4 w.toFinset := by
  have h : chunk4_11.all (routes 3 pool4_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_11] at hv
private def chunk4_12 : List (List T) := [[wire3171,wire4228,wire8479,wire18417,wire31744],
  [wire3171,wire5092,wire8479,wire16912,wire31777],
  [wire3171,wire5092,wire8479,wire17969,wire31744],
  [wire3171,wire5285,wire8479,wire17392,wire31744]]
private def pool4_12 : List (List (List T)) := []
private theorem checked4_12 : ∀ w ∈ chunk4_12, ¬ Need 4 w.toFinset := by
  have h : chunk4_12.all (routes 3 pool4_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_12] at hv
private def chunk4_13 : List (List T) := [[wire3171,wire6117,wire8479,wire16912,wire31744],
  [wire3199,wire4228,wire8456,wire17392,wire31777],
  [wire3199,wire4228,wire8456,wire18417,wire31744],
  [wire3199,wire5092,wire8456,wire16912,wire31777]]
private def pool4_13 : List (List (List T)) := []
private theorem checked4_13 : ∀ w ∈ chunk4_13, ¬ Need 4 w.toFinset := by
  have h : chunk4_13.all (routes 3 pool4_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_13] at hv
private def chunk4_14 : List (List T) := [[wire3199,wire5092,wire8456,wire17969,wire31744],
  [wire3199,wire5285,wire8456,wire17392,wire31744],
  [wire3199,wire6117,wire8456,wire16912,wire31744]]
private def pool4_14 : List (List (List T)) := []
private theorem checked4_14 : ∀ w ∈ chunk4_14, ¬ Need 4 w.toFinset := by
  have h : chunk4_14.all (routes 3 pool4_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_14] at hv
#print axioms checked4_14
private def chunk5_0 : List (List T) := [[wire16,wire31,wire1057,wire2114,wire5092,wire32008],
  [wire16,wire1057,wire2114,wire5092,wire8479,wire31744],
  [wire16,wire1057,wire2143,wire5092,wire8456,wire31744],
  [wire20,wire992,wire1057,wire2114,wire4228,wire32008]]
private def pool5_0 : List (List (List T)) := [chunk4_0, chunk4_3, chunk4_4, chunk4_5, chunk4_6]
private theorem checked5_0 : ∀ w ∈ chunk5_0, ¬ Need 5 w.toFinset := by
  have h : chunk5_0.all (routes 4 pool5_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
private def chunk5_1 : List (List T) := [[wire20,wire1057,wire2114,wire5092,wire8456,wire31744],
  [wire31,wire320,wire1057,wire2114,wire4228,wire32272],
  [wire31,wire992,wire1057,wire2114,wire4244,wire32008],
  [wire31,wire992,wire1057,wire2370,wire4228,wire32272]]
private def pool5_1 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_6]
private theorem checked5_1 : ∀ w ∈ chunk5_1, ¬ Need 5 w.toFinset := by
  have h : chunk5_1.all (routes 4 pool5_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_6 _ hm
private def chunk5_2 : List (List T) := [[wire31,wire992,wire1073,wire2114,wire4228,wire32008],
  [wire31,wire992,wire1313,wire2114,wire4228,wire32272],
  [wire31,wire992,wire2114,wire5285,wire8456,wire32305],
  [wire31,wire992,wire2114,wire5285,wire9513,wire32272]]
private def pool5_2 : List (List (List T)) := [chunk4_0, chunk4_3]
private theorem checked5_2 : ∀ w ∈ chunk5_2, ¬ Need 5 w.toFinset := by
  have h : chunk5_2.all (routes 4 pool5_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_3 _ hm
private def chunk5_3 : List (List T) := [[wire31,wire992,wire2114,wire5285,wire16912,wire32041],
  [wire31,wire992,wire2114,wire5285,wire17969,wire32008],
  [wire31,wire992,wire3171,wire4228,wire8456,wire32305],
  [wire31,wire992,wire3171,wire4228,wire9513,wire32272]]
private def pool5_3 : List (List (List T)) := [chunk4_1, chunk4_4]
private theorem checked5_3 : ∀ w ∈ chunk5_3, ¬ Need 5 w.toFinset := by
  have h : chunk5_3.all (routes 4 pool5_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_4 _ hm
private def chunk5_4 : List (List T) := [[wire31,wire992,wire3171,wire4228,wire16912,wire32041],
  [wire31,wire992,wire3171,wire4228,wire17969,wire32008],
  [wire31,wire992,wire3171,wire5285,wire8456,wire32272],
  [wire31,wire992,wire3171,wire5285,wire16912,wire32008]]
private def pool5_4 : List (List (List T)) := [chunk4_1, chunk4_4]
private theorem checked5_4 : ∀ w ∈ chunk5_4, ¬ Need 5 w.toFinset := by
  have h : chunk5_4.all (routes 4 pool5_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_4 _ hm
private def chunk5_5 : List (List T) := [[wire31,wire1008,wire1057,wire2114,wire4228,wire32008],
  [wire31,wire1057,wire2114,wire5092,wire8456,wire31760],
  [wire31,wire1057,wire2114,wire5092,wire16912,wire32000],
  [wire31,wire1057,wire2114,wire5092,wire16912,wire32008]]
private def pool5_5 : List (List (List T)) := [chunk4_0, chunk4_4, chunk4_5]
private theorem checked5_5 : ∀ w ∈ chunk5_5, ¬ Need 5 w.toFinset := by
  have h : chunk5_5.all (routes 4 pool5_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
private def chunk5_6 : List (List T) := [[wire31,wire1057,wire2114,wire5092,wire16912,wire32041],
  [wire31,wire1057,wire2114,wire5092,wire17392,wire32008],
  [wire31,wire1057,wire2114,wire5092,wire17969,wire32008],
  [wire31,wire1057,wire2114,wire5092,wire21140,wire32008]]
private def pool5_6 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_7]
private theorem checked5_6 : ∀ w ∈ chunk5_6, ¬ Need 5 w.toFinset := by
  have h : chunk5_6.all (routes 4 pool5_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_7 _ hm
private def chunk5_7 : List (List T) := [[wire31,wire1057,wire2114,wire5092,wire21492,wire32008],
  [wire31,wire1057,wire2114,wire5092,wire32008,wire32272],
  [wire31,wire1057,wire2114,wire5108,wire8456,wire31744],
  [wire31,wire1057,wire2114,wire6117,wire16912,wire32008]]
private def pool5_7 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_4, chunk4_5, chunk4_7]
private theorem checked5_7 : ∀ w ∈ chunk5_7, ¬ Need 5 w.toFinset := by
  have h : chunk5_7.all (routes 4 pool5_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_7 _ hm
private def chunk5_8 : List (List T) := [[wire31,wire1057,wire2370,wire4228,wire17392,wire31744],
  [wire31,wire1057,wire2370,wire5092,wire16912,wire31744],
  [wire31,wire1057,wire3171,wire5092,wire16912,wire32008],
  [wire31,wire1073,wire2114,wire5092,wire8456,wire31744]]
private def pool5_8 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_5, chunk4_6]
private theorem checked5_8 : ∀ w ∈ chunk5_8, ¬ Need 5 w.toFinset := by
  have h : chunk5_8.all (routes 4 pool5_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
private def chunk5_9 : List (List T) := [[wire31,wire1313,wire2114,wire4228,wire17392,wire31744],
  [wire31,wire1313,wire2114,wire5092,wire16912,wire31744],
  [wire31,wire1377,wire2114,wire4228,wire16912,wire31744],
  [wire31,wire2017,wire2114,wire4228,wire9513,wire32272]]
private def pool5_9 : List (List (List T)) := [chunk4_0, chunk4_7, chunk4_8]
private theorem checked5_9 : ∀ w ∈ chunk5_9, ¬ Need 5 w.toFinset := by
  have h : chunk5_9.all (routes 4 pool5_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
private def chunk5_10 : List (List T) := [[wire31,wire2017,wire2114,wire4228,wire16912,wire32041],
  [wire31,wire2017,wire3171,wire4228,wire8456,wire32272],
  [wire31,wire2017,wire3171,wire4228,wire16912,wire32008],
  [wire31,wire2114,wire4228,wire9513,wire18417,wire31744]]
private def pool5_10 : List (List (List T)) := [chunk4_1, chunk4_8, chunk4_10]
private theorem checked5_10 : ∀ w ∈ chunk5_10, ¬ Need 5 w.toFinset := by
  have h : chunk5_10.all (routes 4 pool5_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_8 _ hm
  · exact checked4_10 _ hm
private def chunk5_11 : List (List T) := [[wire31,wire2114,wire5092,wire9513,wire17969,wire31744],
  [wire31,wire2114,wire5285,wire8456,wire17392,wire31777],
  [wire31,wire2114,wire5285,wire9513,wire17392,wire31744],
  [wire31,wire2114,wire6117,wire8456,wire16912,wire31777]]
private def pool5_11 : List (List (List T)) := [chunk4_1, chunk4_9, chunk4_10, chunk4_11]
private theorem checked5_11 : ∀ w ∈ chunk5_11, ¬ Need 5 w.toFinset := by
  have h : chunk5_11.all (routes 4 pool5_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
private def chunk5_12 : List (List T) := [[wire31,wire2114,wire6117,wire9513,wire16912,wire31744],
  [wire31,wire3171,wire4228,wire8456,wire17392,wire31777],
  [wire31,wire3171,wire4228,wire8456,wire18417,wire31744],
  [wire31,wire3171,wire4228,wire9513,wire17392,wire31744]]
private def pool5_12 : List (List (List T)) := [chunk4_1, chunk4_10, chunk4_11, chunk4_12, chunk4_13]
private theorem checked5_12 : ∀ w ∈ chunk5_12, ¬ Need 5 w.toFinset := by
  have h : chunk5_12.all (routes 4 pool5_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
private def chunk5_13 : List (List T) := [[wire31,wire3171,wire5092,wire8456,wire16912,wire31777],
  [wire31,wire3171,wire5092,wire8456,wire17969,wire31744],
  [wire31,wire3171,wire5092,wire9513,wire16912,wire31744],
  [wire31,wire3171,wire5285,wire8456,wire17392,wire31744]]
private def pool5_13 : List (List (List T)) := [chunk4_1, chunk4_12, chunk4_13, chunk4_14]
private theorem checked5_13 : ∀ w ∈ chunk5_13, ¬ Need 5 w.toFinset := by
  have h : chunk5_13.all (routes 4 pool5_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_14 : List (List T) := [[wire31,wire3171,wire6117,wire8456,wire16912,wire31744],
  [wire256,wire992,wire1057,wire2143,wire4228,wire32272],
  [wire256,wire1057,wire2143,wire4228,wire17392,wire31744],
  [wire256,wire1057,wire2143,wire5092,wire16912,wire31744]]
private def pool5_14 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_3, chunk4_5, chunk4_6, chunk4_7, chunk4_13, chunk4_14]
private theorem checked5_14 : ∀ w ∈ chunk5_14, ¬ Need 5 w.toFinset := by
  have h : chunk5_14.all (routes 4 pool5_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_15 : List (List T) := [[wire287,wire992,wire1057,wire2114,wire4228,wire32272],
  [wire287,wire1057,wire2114,wire4228,wire17392,wire31744],
  [wire287,wire1057,wire2114,wire5092,wire16912,wire31744],
  [wire320,wire1057,wire2143,wire4228,wire16912,wire31744]]
private def pool5_15 : List (List (List T)) := [chunk4_2, chunk4_5, chunk4_6, chunk4_8]
private theorem checked5_15 : ∀ w ∈ chunk5_15, ¬ Need 5 w.toFinset := by
  have h : chunk5_15.all (routes 4 pool5_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_8 _ hm
private def chunk5_16 : List (List T) := [[wire992,wire1057,wire2114,wire4244,wire8479,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire31760],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire32272],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire32305]]
private def pool5_16 : List (List (List T)) := [chunk4_3, chunk4_4]
private theorem checked5_16 : ∀ w ∈ chunk5_16, ¬ Need 5 w.toFinset := by
  have h : chunk5_16.all (routes 4 pool5_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
private def chunk5_17 : List (List T) := [[wire992,wire1057,wire2143,wire4228,wire8479,wire32272],
  [wire992,wire1057,wire2143,wire4228,wire9513,wire32272],
  [wire992,wire1057,wire2143,wire4228,wire10570,wire32272],
  [wire992,wire1057,wire2143,wire4228,wire10591,wire32272]]
private def pool5_17 : List (List (List T)) := [chunk4_2, chunk4_3, chunk4_8]
private theorem checked5_17 : ∀ w ∈ chunk5_17, ¬ Need 5 w.toFinset := by
  have h : chunk5_17.all (routes 4 pool5_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_8 _ hm
private def chunk5_18 : List (List T) := [[wire992,wire1057,wire2143,wire4228,wire16912,wire32000],
  [wire992,wire1057,wire2143,wire4228,wire32008,wire32272],
  [wire992,wire1057,wire2143,wire4244,wire8456,wire31744],
  [wire992,wire1057,wire2143,wire5285,wire8456,wire32272]]
private def pool5_18 : List (List (List T)) := [chunk4_3, chunk4_4, chunk4_5]
private theorem checked5_18 : ∀ w ∈ chunk5_18, ¬ Need 5 w.toFinset := by
  have h : chunk5_18.all (routes 4 pool5_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
private def chunk5_19 : List (List T) := [[wire992,wire1057,wire2399,wire4228,wire16912,wire31744],
  [wire992,wire1057,wire3199,wire4228,wire8456,wire32272],
  [wire992,wire1073,wire2114,wire4228,wire8479,wire31744],
  [wire992,wire1073,wire2143,wire4228,wire8456,wire31744]]
private def pool5_19 : List (List (List T)) := [chunk4_2, chunk4_4, chunk4_5, chunk4_6, chunk4_8]
private theorem checked5_19 : ∀ w ∈ chunk5_19, ¬ Need 5 w.toFinset := by
  have h : chunk5_19.all (routes 4 pool5_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_8 _ hm
private def chunk5_20 : List (List T) := [[wire992,wire1077,wire2114,wire4228,wire8456,wire31744],
  [wire992,wire1087,wire2114,wire4228,wire8456,wire32305],
  [wire992,wire1087,wire2114,wire4228,wire17969,wire32008],
  [wire992,wire1087,wire2114,wire5285,wire8456,wire32272]]
private def pool5_20 : List (List (List T)) := [chunk4_3, chunk4_4, chunk4_6, chunk4_7]
private theorem checked5_20 : ∀ w ∈ chunk5_20, ¬ Need 5 w.toFinset := by
  have h : chunk5_20.all (routes 4 pool5_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
private def chunk5_21 : List (List T) := [[wire992,wire1087,wire2114,wire5285,wire16912,wire32008],
  [wire992,wire1313,wire2143,wire4228,wire16912,wire31744],
  [wire992,wire2114,wire4228,wire9535,wire17969,wire31744],
  [wire992,wire2114,wire5285,wire8479,wire16912,wire31777]]
private def pool5_21 : List (List (List T)) := [chunk4_3, chunk4_7, chunk4_8, chunk4_9]
private theorem checked5_21 : ∀ w ∈ chunk5_21, ¬ Need 5 w.toFinset := by
  have h : chunk5_21.all (routes 4 pool5_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
private def chunk5_22 : List (List T) := [[wire992,wire2114,wire5285,wire8479,wire17969,wire31744],
  [wire992,wire2114,wire5285,wire9535,wire16912,wire31744],
  [wire992,wire2143,wire4228,wire9513,wire17969,wire31744],
  [wire992,wire2143,wire5285,wire8456,wire16912,wire31777]]
private def pool5_22 : List (List (List T)) := [chunk4_3, chunk4_9, chunk4_10, chunk4_11]
private theorem checked5_22 : ∀ w ∈ chunk5_22, ¬ Need 5 w.toFinset := by
  have h : chunk5_22.all (routes 4 pool5_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
private def chunk5_23 : List (List T) := [[wire992,wire2143,wire5285,wire8456,wire17969,wire31744],
  [wire992,wire2143,wire5285,wire9513,wire16912,wire31744],
  [wire992,wire3171,wire4228,wire8479,wire16912,wire31777],
  [wire992,wire3171,wire4228,wire8479,wire17969,wire31744]]
private def pool5_23 : List (List (List T)) := [chunk4_3, chunk4_11, chunk4_12]
private theorem checked5_23 : ∀ w ∈ chunk5_23, ¬ Need 5 w.toFinset := by
  have h : chunk5_23.all (routes 4 pool5_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
private def chunk5_24 : List (List T) := [[wire992,wire3171,wire5285,wire8479,wire16912,wire31744],
  [wire992,wire3199,wire4228,wire8456,wire16912,wire31777],
  [wire992,wire3199,wire4228,wire8456,wire17969,wire31744],
  [wire992,wire3199,wire5285,wire8456,wire16912,wire31744]]
private def pool5_24 : List (List (List T)) := [chunk4_4, chunk4_12, chunk4_13, chunk4_14]
private theorem checked5_24 : ∀ w ∈ chunk5_24, ¬ Need 5 w.toFinset := by
  have h : chunk5_24.all (routes 4 pool5_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_25 : List (List T) := [[wire1008,wire1057,wire2114,wire4228,wire8479,wire31744],
  [wire1008,wire1057,wire2143,wire4228,wire8456,wire31744],
  [wire1057,wire1087,wire2114,wire5092,wire16912,wire32008],
  [wire1057,wire2017,wire2143,wire4228,wire8456,wire32272]]
private def pool5_25 : List (List (List T)) := [chunk4_4, chunk4_5, chunk4_7, chunk4_8]
private theorem checked5_25 : ∀ w ∈ chunk5_25, ¬ Need 5 w.toFinset := by
  have h : chunk5_25.all (routes 4 pool5_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
private def chunk5_26 : List (List T) := [[wire1057,wire2114,wire2143,wire5092,wire16912,wire32008],
  [wire1057,wire2114,wire4228,wire8479,wire17392,wire31744],
  [wire1057,wire2114,wire4228,wire8479,wire17392,wire31777],
  [wire1057,wire2114,wire4228,wire8479,wire17392,wire32008]]
private def pool5_26 : List (List (List T)) := [chunk4_9, chunk4_11]
private theorem checked5_26 : ∀ w ∈ chunk5_26, ¬ Need 5 w.toFinset := by
  have h : chunk5_26.all (routes 4 pool5_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_11 _ hm
private def chunk5_27 : List (List T) := [[wire1057,wire2114,wire4228,wire8479,wire17392,wire32272],
  [wire1057,wire2114,wire4228,wire8479,wire18417,wire31744],
  [wire1057,wire2114,wire4228,wire8479,wire21492,wire31744],
  [wire1057,wire2114,wire4228,wire9535,wire17392,wire31744]]
private def pool5_27 : List (List (List T)) := [chunk4_8, chunk4_9, chunk4_12]
private theorem checked5_27 : ∀ w ∈ chunk5_27, ¬ Need 5 w.toFinset := by
  have h : chunk5_27.all (routes 4 pool5_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_12 _ hm
private def chunk5_28 : List (List T) := [[wire1057,wire2114,wire4228,wire10591,wire17392,wire31744],
  [wire1057,wire2114,wire5092,wire8479,wire16912,wire31744],
  [wire1057,wire2114,wire5092,wire8479,wire16912,wire31777],
  [wire1057,wire2114,wire5092,wire8479,wire16912,wire32008]]
private def pool5_28 : List (List (List T)) := [chunk4_9, chunk4_12]
private theorem checked5_28 : ∀ w ∈ chunk5_28, ¬ Need 5 w.toFinset := by
  have h : chunk5_28.all (routes 4 pool5_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_12 _ hm
private def chunk5_29 : List (List T) := [[wire1057,wire2114,wire5092,wire8479,wire17392,wire31744],
  [wire1057,wire2114,wire5092,wire8479,wire17969,wire31744],
  [wire1057,wire2114,wire5092,wire8479,wire21140,wire31744],
  [wire1057,wire2114,wire5092,wire8479,wire21492,wire31744]]
private def pool5_29 : List (List (List T)) := [chunk4_2, chunk4_9, chunk4_12]
private theorem checked5_29 : ∀ w ∈ chunk5_29, ¬ Need 5 w.toFinset := by
  have h : chunk5_29.all (routes 4 pool5_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_9 _ hm
  · exact checked4_12 _ hm
private def chunk5_30 : List (List T) := [[wire1057,wire2114,wire5092,wire9535,wire16912,wire31744],
  [wire1057,wire2114,wire5092,wire10591,wire16912,wire31744],
  [wire1057,wire2114,wire5285,wire8479,wire17392,wire31744],
  [wire1057,wire2114,wire6117,wire8479,wire16912,wire31744]]
private def pool5_30 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_12, chunk4_13]
private theorem checked5_30 : ∀ w ∈ chunk5_30, ¬ Need 5 w.toFinset := by
  have h : chunk5_30.all (routes 4 pool5_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
private def chunk5_31 : List (List T) := [[wire1057,wire2143,wire4228,wire5092,wire8456,wire32272],
  [wire1057,wire2143,wire4228,wire8456,wire17392,wire31744],
  [wire1057,wire2143,wire4228,wire8456,wire17392,wire31777],
  [wire1057,wire2143,wire4228,wire8456,wire17392,wire32272]]
private def pool5_31 : List (List (List T)) := [chunk4_10, chunk4_13]
private theorem checked5_31 : ∀ w ∈ chunk5_31, ¬ Need 5 w.toFinset := by
  have h : chunk5_31.all (routes 4 pool5_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_13 _ hm
private def chunk5_32 : List (List T) := [[wire1057,wire2143,wire4228,wire8456,wire18417,wire31744],
  [wire1057,wire2143,wire4228,wire8456,wire21492,wire31744],
  [wire1057,wire2143,wire4228,wire8479,wire17392,wire31744],
  [wire1057,wire2143,wire4228,wire9513,wire17392,wire31744]]
private def pool5_32 : List (List (List T)) := [chunk4_10, chunk4_11, chunk4_13]
private theorem checked5_32 : ∀ w ∈ chunk5_32, ¬ Need 5 w.toFinset := by
  have h : chunk5_32.all (routes 4 pool5_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_13 _ hm
private def chunk5_33 : List (List T) := [[wire1057,wire2143,wire4228,wire10570,wire17392,wire31744],
  [wire1057,wire2143,wire4228,wire10591,wire17392,wire31744],
  [wire1057,wire2143,wire5092,wire8456,wire16912,wire31744],
  [wire1057,wire2143,wire5092,wire8456,wire16912,wire31777]]
private def pool5_33 : List (List (List T)) := [chunk4_2, chunk4_11, chunk4_13]
private theorem checked5_33 : ∀ w ∈ chunk5_33, ¬ Need 5 w.toFinset := by
  have h : chunk5_33.all (routes 4 pool5_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_11 _ hm
  · exact checked4_13 _ hm
private def chunk5_34 : List (List T) := [[wire1057,wire2143,wire5092,wire8456,wire17392,wire31744],
  [wire1057,wire2143,wire5092,wire8456,wire17969,wire31744],
  [wire1057,wire2143,wire5092,wire8456,wire21140,wire31744],
  [wire1057,wire2143,wire5092,wire8456,wire21492,wire31744]]
private def pool5_34 : List (List (List T)) := [chunk4_10, chunk4_14]
private theorem checked5_34 : ∀ w ∈ chunk5_34, ¬ Need 5 w.toFinset := by
  have h : chunk5_34.all (routes 4 pool5_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_14 _ hm
private def chunk5_35 : List (List T) := [[wire1057,wire2143,wire5092,wire8456,wire31744,wire32272],
  [wire1057,wire2143,wire5092,wire8479,wire16912,wire31744],
  [wire1057,wire2143,wire5092,wire9513,wire16912,wire31744],
  [wire1057,wire2143,wire5092,wire10570,wire16912,wire31744]]
private def pool5_35 : List (List (List T)) := [chunk4_5, chunk4_10, chunk4_11]
private theorem checked5_35 : ∀ w ∈ chunk5_35, ¬ Need 5 w.toFinset := by
  have h : chunk5_35.all (routes 4 pool5_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
private def chunk5_36 : List (List T) := [[wire1057,wire2143,wire5092,wire10591,wire16912,wire31744],
  [wire1057,wire2143,wire5092,wire16912,wire31744,wire32008],
  [wire1057,wire2143,wire5285,wire8456,wire17392,wire31744],
  [wire1057,wire2143,wire6117,wire8456,wire16912,wire31744]]
private def pool5_36 : List (List (List T)) := [chunk4_5, chunk4_10, chunk4_11, chunk4_14]
private theorem checked5_36 : ∀ w ∈ chunk5_36, ¬ Need 5 w.toFinset := by
  have h : chunk5_36.all (routes 4 pool5_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_36,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_14 _ hm
private def chunk5_37 : List (List T) := [[wire1057,wire3171,wire4228,wire8479,wire17392,wire31744],
  [wire1057,wire3171,wire5092,wire8479,wire16912,wire31744],
  [wire1057,wire3199,wire4228,wire8456,wire17392,wire31744],
  [wire1057,wire3199,wire5092,wire8456,wire16912,wire31744]]
private def pool5_37 : List (List (List T)) := [chunk4_11, chunk4_12, chunk4_13, chunk4_14]
private theorem checked5_37 : ∀ w ∈ chunk5_37, ¬ Need 5 w.toFinset := by
  have h : chunk5_37.all (routes 4 pool5_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_38 : List (List T) := [[wire1087,wire2017,wire2114,wire4228,wire8456,wire32272],
  [wire1087,wire2017,wire2114,wire4228,wire16912,wire32008],
  [wire1087,wire2114,wire4228,wire8456,wire17392,wire31777],
  [wire1087,wire2114,wire4228,wire8456,wire18417,wire31744]]
private def pool5_38 : List (List (List T)) := [chunk4_7, chunk4_8, chunk4_13]
private theorem checked5_38 : ∀ w ∈ chunk5_38, ¬ Need 5 w.toFinset := by
  have h : chunk5_38.all (routes 4 pool5_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_38,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_13 _ hm
private def chunk5_39 : List (List T) := [[wire1087,wire2114,wire5092,wire8456,wire16912,wire31777],
  [wire1087,wire2114,wire5092,wire8456,wire17969,wire31744],
  [wire1087,wire2114,wire5285,wire8456,wire17392,wire31744],
  [wire1087,wire2114,wire6117,wire8456,wire16912,wire31744]]
private def pool5_39 : List (List (List T)) := [chunk4_7, chunk4_9, chunk4_10, chunk4_13, chunk4_14]
private theorem checked5_39 : ∀ w ∈ chunk5_39, ¬ Need 5 w.toFinset := by
  have h : chunk5_39.all (routes 4 pool5_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_40 : List (List T) := [[wire2017,wire2114,wire4228,wire8479,wire16912,wire31777],
  [wire2017,wire2114,wire4228,wire9535,wire16912,wire31744],
  [wire2017,wire2143,wire4228,wire8456,wire16912,wire31777],
  [wire2017,wire2143,wire4228,wire9513,wire16912,wire31744]]
private def pool5_40 : List (List (List T)) := [chunk4_8, chunk4_9, chunk4_10, chunk4_11]
private theorem checked5_40 : ∀ w ∈ chunk5_40, ¬ Need 5 w.toFinset := by
  have h : chunk5_40.all (routes 4 pool5_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_40,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
private def chunk5_41 : List (List T) := [[wire2017,wire3171,wire4228,wire8479,wire16912,wire31744],
  [wire2017,wire3199,wire4228,wire8456,wire16912,wire31744]]
private def pool5_41 : List (List (List T)) := [chunk4_8, chunk4_12, chunk4_13, chunk4_14]
private theorem checked5_41 : ∀ w ∈ chunk5_41, ¬ Need 5 w.toFinset := by
  have h : chunk5_41.all (routes 4 pool5_41.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_41,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
#print axioms checked5_41
private def chunk6_0 : List (List T) := [[wire16,wire31,wire992,wire1057,wire2114,wire4228,wire32008],
  [wire16,wire31,wire1057,wire2114,wire5092,wire8456,wire31744],
  [wire16,wire992,wire1057,wire2114,wire4228,wire8479,wire31744],
  [wire16,wire992,wire1057,wire2143,wire4228,wire8456,wire31744]]
private def pool6_0 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_2, chunk5_5, chunk5_7, chunk5_8, chunk5_16, chunk5_18, chunk5_19, chunk5_25]
private theorem checked6_0 : ∀ w ∈ chunk6_0, ¬ Need 6 w.toFinset := by
  have h : chunk6_0.all (routes 5 pool6_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_5 _ hm
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_16 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_25 _ hm
private def chunk6_1 : List (List T) := [[wire20,wire992,wire1057,wire2114,wire4228,wire8456,wire31744],
  [wire31,wire256,wire992,wire1057,wire2114,wire4228,wire32272],
  [wire31,wire256,wire1057,wire2114,wire4228,wire17392,wire31744],
  [wire31,wire256,wire1057,wire2114,wire5092,wire16912,wire31744]]
private def pool6_1 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_2, chunk5_5, chunk5_8, chunk5_9, chunk5_14, chunk5_15, chunk5_20]
private theorem checked6_1 : ∀ w ∈ chunk6_1, ¬ Need 6 w.toFinset := by
  have h : chunk6_1.all (routes 5 pool6_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_5 _ hm
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_20 _ hm
private def chunk6_2 : List (List T) := [[wire31,wire320,wire1057,wire2114,wire4228,wire16912,wire31744],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire31760],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire32272],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire32305]]
private def pool6_2 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_3, chunk5_5, chunk5_9, chunk5_15, chunk5_16, chunk5_20]
private theorem checked6_2 : ∀ w ∈ chunk6_2, ¬ Need 6 w.toFinset := by
  have h : chunk6_2.all (routes 5 pool6_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_5 _ hm
  · exact checked5_9 _ hm
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_20 _ hm
private def chunk6_3 : List (List T) := [[wire31,wire992,wire1057,wire2114,wire4228,wire8479,wire32272],
  [wire31,wire992,wire1057,wire2114,wire4228,wire9513,wire32272],
  [wire31,wire992,wire1057,wire2114,wire4228,wire10570,wire32272],
  [wire31,wire992,wire1057,wire2114,wire4228,wire16912,wire32000]]
private def pool6_3 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_3, chunk5_5, chunk5_9, chunk5_17, chunk5_18]
private theorem checked6_3 : ∀ w ∈ chunk6_3, ¬ Need 6 w.toFinset := by
  have h : chunk6_3.all (routes 5 pool6_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_5 _ hm
  · exact checked5_9 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
private def chunk6_4 : List (List T) := [[wire31,wire992,wire1057,wire2114,wire4228,wire16912,wire32008],
  [wire31,wire992,wire1057,wire2114,wire4228,wire16912,wire32041],
  [wire31,wire992,wire1057,wire2114,wire4228,wire17392,wire32008],
  [wire31,wire992,wire1057,wire2114,wire4228,wire17969,wire32008]]
private def pool6_4 : List (List (List T)) := [chunk5_3, chunk5_4, chunk5_5, chunk5_6, chunk5_10, chunk5_20]
private theorem checked6_4 : ∀ w ∈ chunk6_4, ¬ Need 6 w.toFinset := by
  have h : chunk6_4.all (routes 5 pool6_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_10 _ hm
  · exact checked5_20 _ hm
private def chunk6_5 : List (List T) := [[wire31,wire992,wire1057,wire2114,wire4228,wire21140,wire32008],
  [wire31,wire992,wire1057,wire2114,wire4228,wire32008,wire32272],
  [wire31,wire992,wire1057,wire2114,wire4244,wire8456,wire31744],
  [wire31,wire992,wire1057,wire2114,wire5092,wire16912,wire32008]]
private def pool6_5 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_5, chunk5_6, chunk5_7, chunk5_16, chunk5_18]
private theorem checked6_5 : ∀ w ∈ chunk6_5, ¬ Need 6 w.toFinset := by
  have h : chunk6_5.all (routes 5 pool6_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_16 _ hm
  · exact checked5_18 _ hm
private def chunk6_6 : List (List T) := [[wire31,wire992,wire1057,wire2114,wire5285,wire8456,wire32272],
  [wire31,wire992,wire1057,wire2114,wire5285,wire16912,wire32008],
  [wire31,wire992,wire1057,wire2143,wire4228,wire8456,wire32272],
  [wire31,wire992,wire1057,wire2370,wire4228,wire16912,wire31744]]
private def pool6_6 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_3, chunk5_4, chunk5_7, chunk5_8, chunk5_16, chunk5_17, chunk5_18, chunk5_19, chunk5_20, chunk5_21]
private theorem checked6_6 : ∀ w ∈ chunk6_6, ¬ Need 6 w.toFinset := by
  have h : chunk6_6.all (routes 5 pool6_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
private def chunk6_7 : List (List T) := [[wire31,wire992,wire1057,wire3171,wire4228,wire8456,wire32272],
  [wire31,wire992,wire1057,wire3171,wire4228,wire16912,wire32008],
  [wire31,wire992,wire1073,wire2114,wire4228,wire8456,wire31744],
  [wire31,wire992,wire1313,wire2114,wire4228,wire16912,wire31744]]
private def pool6_7 : List (List (List T)) := [chunk5_2, chunk5_3, chunk5_4, chunk5_8, chunk5_9, chunk5_10, chunk5_19, chunk5_21]
private theorem checked6_7 : ∀ w ∈ chunk6_7, ¬ Need 6 w.toFinset := by
  have h : chunk6_7.all (routes 5 pool6_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_19 _ hm
  · exact checked5_21 _ hm
private def chunk6_8 : List (List T) := [[wire31,wire992,wire2114,wire4228,wire9513,wire17969,wire31744],
  [wire31,wire992,wire2114,wire5285,wire8456,wire16912,wire31777],
  [wire31,wire992,wire2114,wire5285,wire8456,wire17969,wire31744],
  [wire31,wire992,wire2114,wire5285,wire9513,wire16912,wire31744]]
private def pool6_8 : List (List (List T)) := [chunk5_2, chunk5_3, chunk5_10, chunk5_11, chunk5_12, chunk5_21, chunk5_22, chunk5_23]
private theorem checked6_8 : ∀ w ∈ chunk6_8, ¬ Need 6 w.toFinset := by
  have h : chunk6_8.all (routes 5 pool6_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_10 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
private def chunk6_9 : List (List T) := [[wire31,wire992,wire3171,wire4228,wire8456,wire16912,wire31777],
  [wire31,wire992,wire3171,wire4228,wire8456,wire17969,wire31744],
  [wire31,wire992,wire3171,wire4228,wire9513,wire16912,wire31744],
  [wire31,wire992,wire3171,wire5285,wire8456,wire16912,wire31744]]
private def pool6_9 : List (List (List T)) := [chunk5_3, chunk5_4, chunk5_12, chunk5_13, chunk5_14, chunk5_23, chunk5_24]
private theorem checked6_9 : ∀ w ∈ chunk6_9, ¬ Need 6 w.toFinset := by
  have h : chunk6_9.all (routes 5 pool6_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
private def chunk6_10 : List (List T) := [[wire31,wire1008,wire1057,wire2114,wire4228,wire8456,wire31744],
  [wire31,wire1057,wire2017,wire2114,wire4228,wire8456,wire32272],
  [wire31,wire1057,wire2017,wire2114,wire4228,wire16912,wire32008],
  [wire31,wire1057,wire2114,wire4228,wire5092,wire8456,wire32272]]
private def pool6_10 : List (List (List T)) := [chunk5_5, chunk5_7, chunk5_9, chunk5_10, chunk5_25, chunk5_31, chunk5_38]
private theorem checked6_10 : ∀ w ∈ chunk6_10, ¬ Need 6 w.toFinset := by
  have h : chunk6_10.all (routes 5 pool6_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_7 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_25 _ hm
  · exact checked5_31 _ hm
  · exact checked5_38 _ hm
private def chunk6_11 : List (List T) := [[wire31,wire1057,wire2114,wire4228,wire5092,wire16912,wire32008],
  [wire31,wire1057,wire2114,wire4228,wire8456,wire17392,wire31744],
  [wire31,wire1057,wire2114,wire4228,wire8456,wire17392,wire31777],
  [wire31,wire1057,wire2114,wire4228,wire8456,wire17392,wire32008]]
private def pool6_11 : List (List (List T)) := [chunk5_5, chunk5_6, chunk5_11, chunk5_12, chunk5_26, chunk5_31, chunk5_38]
private theorem checked6_11 : ∀ w ∈ chunk6_11, ¬ Need 6 w.toFinset := by
  have h : chunk6_11.all (routes 5 pool6_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_26 _ hm
  · exact checked5_31 _ hm
  · exact checked5_38 _ hm
private def chunk6_12 : List (List T) := [[wire31,wire1057,wire2114,wire4228,wire8456,wire17392,wire32272],
  [wire31,wire1057,wire2114,wire4228,wire8456,wire18417,wire31744],
  [wire31,wire1057,wire2114,wire4228,wire8456,wire21492,wire31744],
  [wire31,wire1057,wire2114,wire4228,wire8479,wire17392,wire31744]]
private def pool6_12 : List (List (List T)) := [chunk5_10, chunk5_12, chunk5_26, chunk5_27, chunk5_31, chunk5_32, chunk5_38]
private theorem checked6_12 : ∀ w ∈ chunk6_12, ¬ Need 6 w.toFinset := by
  have h : chunk6_12.all (routes 5 pool6_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_10 _ hm
  · exact checked5_12 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_38 _ hm
private def chunk6_13 : List (List T) := [[wire31,wire1057,wire2114,wire4228,wire9513,wire17392,wire31744],
  [wire31,wire1057,wire2114,wire4228,wire10570,wire17392,wire31744],
  [wire31,wire1057,wire2114,wire5092,wire8456,wire16912,wire31744],
  [wire31,wire1057,wire2114,wire5092,wire8456,wire16912,wire31777]]
private def pool6_13 : List (List (List T)) := [chunk5_5, chunk5_6, chunk5_10, chunk5_11, chunk5_12, chunk5_13, chunk5_27, chunk5_28, chunk5_32, chunk5_33, chunk5_39]
private theorem checked6_13 : ∀ w ∈ chunk6_13, ¬ Need 6 w.toFinset := by
  have h : chunk6_13.all (routes 5 pool6_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_10 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_39 _ hm
private def chunk6_14 : List (List T) := [[wire31,wire1057,wire2114,wire5092,wire8456,wire16912,wire32008],
  [wire31,wire1057,wire2114,wire5092,wire8456,wire17392,wire31744],
  [wire31,wire1057,wire2114,wire5092,wire8456,wire17969,wire31744],
  [wire31,wire1057,wire2114,wire5092,wire8456,wire21140,wire31744]]
private def pool6_14 : List (List (List T)) := [chunk5_1, chunk5_5, chunk5_6, chunk5_11, chunk5_13, chunk5_28, chunk5_29, chunk5_34, chunk5_39]
private theorem checked6_14 : ∀ w ∈ chunk6_14, ¬ Need 6 w.toFinset := by
  have h : chunk6_14.all (routes 5 pool6_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_11 _ hm
  · exact checked5_13 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_34 _ hm
  · exact checked5_39 _ hm
private def chunk6_15 : List (List T) := [[wire31,wire1057,wire2114,wire5092,wire8456,wire21492,wire31744],
  [wire31,wire1057,wire2114,wire5092,wire8456,wire31744,wire32272],
  [wire31,wire1057,wire2114,wire5092,wire8479,wire16912,wire31744],
  [wire31,wire1057,wire2114,wire5092,wire9513,wire16912,wire31744]]
private def pool6_15 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_6, chunk5_7, chunk5_11, chunk5_12, chunk5_13, chunk5_28, chunk5_29, chunk5_30, chunk5_34, chunk5_35]
private theorem checked6_15 : ∀ w ∈ chunk6_15, ¬ Need 6 w.toFinset := by
  have h : chunk6_15.all (routes 5 pool6_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_34 _ hm
  · exact checked5_35 _ hm
private def chunk6_16 : List (List T) := [[wire31,wire1057,wire2114,wire5092,wire10570,wire16912,wire31744],
  [wire31,wire1057,wire2114,wire5092,wire16912,wire31744,wire32008],
  [wire31,wire1057,wire2114,wire5092,wire16912,wire32008],
  [wire31,wire1057,wire2114,wire5285,wire8456,wire17392,wire31744]]
private def pool6_16 : List (List (List T)) := [chunk5_0, chunk5_5, chunk5_6, chunk5_7, chunk5_8, chunk5_11, chunk5_13, chunk5_25, chunk5_26, chunk5_30, chunk5_35, chunk5_36, chunk5_39]
private theorem checked6_16 : ∀ w ∈ chunk6_16, ¬ Need 6 w.toFinset := by
  have h : chunk6_16.all (routes 5 pool6_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_11 _ hm
  · exact checked5_13 _ hm
  · exact checked5_25 _ hm
  · exact checked5_26 _ hm
  · exact checked5_30 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_39 _ hm
private def chunk6_17 : List (List T) := [[wire31,wire1057,wire2114,wire6117,wire8456,wire16912,wire31744],
  [wire31,wire1057,wire2143,wire4228,wire8456,wire17392,wire31744],
  [wire31,wire1057,wire2143,wire5092,wire8456,wire16912,wire31744],
  [wire31,wire1057,wire3171,wire4228,wire8456,wire17392,wire31744]]
private def pool6_17 : List (List (List T)) := [chunk5_0, chunk5_7, chunk5_11, chunk5_12, chunk5_13, chunk5_14, chunk5_30, chunk5_31, chunk5_32, chunk5_33, chunk5_35, chunk5_36, chunk5_37, chunk5_39]
private theorem checked6_17 : ∀ w ∈ chunk6_17, ¬ Need 6 w.toFinset := by
  have h : chunk6_17.all (routes 5 pool6_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_7 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_39 _ hm
private def chunk6_18 : List (List T) := [[wire31,wire1057,wire3171,wire5092,wire8456,wire16912,wire31744],
  [wire31,wire2017,wire2114,wire4228,wire8456,wire16912,wire31777],
  [wire31,wire2017,wire2114,wire4228,wire9513,wire16912,wire31744],
  [wire31,wire2017,wire3171,wire4228,wire8456,wire16912,wire31744]]
private def pool6_18 : List (List (List T)) := [chunk5_8, chunk5_9, chunk5_10, chunk5_11, chunk5_12, chunk5_13, chunk5_14, chunk5_37, chunk5_40, chunk5_41]
private theorem checked6_18 : ∀ w ∈ chunk6_18, ¬ Need 6 w.toFinset := by
  have h : chunk6_18.all (routes 5 pool6_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_37 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
private def chunk6_19 : List (List T) := [[wire256,wire992,wire1057,wire2143,wire4228,wire16912,wire31744],
  [wire287,wire992,wire1057,wire2114,wire4228,wire16912,wire31744],
  [wire992,wire1057,wire1087,wire2114,wire4228,wire8456,wire32272],
  [wire992,wire1057,wire1087,wire2114,wire4228,wire16912,wire32008]]
private def pool6_19 : List (List (List T)) := [chunk5_14, chunk5_15, chunk5_18, chunk5_19, chunk5_20, chunk5_21, chunk5_25, chunk5_38]
private theorem checked6_19 : ∀ w ∈ chunk6_19, ¬ Need 6 w.toFinset := by
  have h : chunk6_19.all (routes 5 pool6_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_25 _ hm
  · exact checked5_38 _ hm
private def chunk6_20 : List (List T) := [[wire992,wire1057,wire2114,wire2143,wire4228,wire8456,wire32272],
  [wire992,wire1057,wire2114,wire2143,wire4228,wire16912,wire32008],
  [wire992,wire1057,wire2114,wire4228,wire8479,wire16912,wire31744],
  [wire992,wire1057,wire2114,wire4228,wire8479,wire16912,wire31777]]
private def pool6_20 : List (List (List T)) := [chunk5_16, chunk5_17, chunk5_21, chunk5_23, chunk5_26, chunk5_28, chunk5_40]
private theorem checked6_20 : ∀ w ∈ chunk6_20, ¬ Need 6 w.toFinset := by
  have h : chunk6_20.all (routes 5 pool6_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_21 _ hm
  · exact checked5_23 _ hm
  · exact checked5_26 _ hm
  · exact checked5_28 _ hm
  · exact checked5_40 _ hm
private def chunk6_21 : List (List T) := [[wire992,wire1057,wire2114,wire4228,wire8479,wire16912,wire32008],
  [wire992,wire1057,wire2114,wire4228,wire8479,wire16912,wire32272],
  [wire992,wire1057,wire2114,wire4228,wire8479,wire17392,wire31744],
  [wire992,wire1057,wire2114,wire4228,wire8479,wire17969,wire31744]]
private def pool6_21 : List (List (List T)) := [chunk5_21, chunk5_22, chunk5_23, chunk5_26, chunk5_27, chunk5_28, chunk5_29]
private theorem checked6_21 : ∀ w ∈ chunk6_21, ¬ Need 6 w.toFinset := by
  have h : chunk6_21.all (routes 5 pool6_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
private def chunk6_22 : List (List T) := [[wire992,wire1057,wire2114,wire4228,wire8479,wire21140,wire31744],
  [wire992,wire1057,wire2114,wire4228,wire9535,wire16912,wire31744],
  [wire992,wire1057,wire2114,wire4228,wire10591,wire16912,wire31744],
  [wire992,wire1057,wire2114,wire5092,wire8479,wire16912,wire31744]]
private def pool6_22 : List (List (List T)) := [chunk5_21, chunk5_22, chunk5_27, chunk5_28, chunk5_29, chunk5_30, chunk5_40]
private theorem checked6_22 : ∀ w ∈ chunk6_22, ¬ Need 6 w.toFinset := by
  have h : chunk6_22.all (routes 5 pool6_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_40 _ hm
private def chunk6_23 : List (List T) := [[wire992,wire1057,wire2114,wire5285,wire8479,wire16912,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire16912,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire16912,wire31777],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire16912,wire32272]]
private def pool6_23 : List (List (List T)) := [chunk5_16, chunk5_21, chunk5_22, chunk5_24, chunk5_30, chunk5_31, chunk5_33, chunk5_40]
private theorem checked6_23 : ∀ w ∈ chunk6_23, ¬ Need 6 w.toFinset := by
  have h : chunk6_23.all (routes 5 pool6_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_16 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_24 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_33 _ hm
  · exact checked5_40 _ hm
private def chunk6_24 : List (List T) := [[wire992,wire1057,wire2143,wire4228,wire8456,wire17392,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire17969,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire21140,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire31744,wire32272]]
private def pool6_24 : List (List (List T)) := [chunk5_14, chunk5_16, chunk5_18, chunk5_22, chunk5_23, chunk5_24, chunk5_31, chunk5_32, chunk5_34, chunk5_35]
private theorem checked6_24 : ∀ w ∈ chunk6_24, ¬ Need 6 w.toFinset := by
  have h : chunk6_24.all (routes 5 pool6_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_16 _ hm
  · exact checked5_18 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_34 _ hm
  · exact checked5_35 _ hm
private def chunk6_25 : List (List T) := [[wire992,wire1057,wire2143,wire4228,wire8456,wire32272],
  [wire992,wire1057,wire2143,wire4228,wire8479,wire16912,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire9513,wire16912,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire10570,wire16912,wire31744]]
private def pool6_25 : List (List (List T)) := [chunk5_14, chunk5_15, chunk5_16, chunk5_17, chunk5_18, chunk5_19, chunk5_22, chunk5_23, chunk5_25, chunk5_31, chunk5_32, chunk5_33, chunk5_35, chunk5_40]
private theorem checked6_25 : ∀ w ∈ chunk6_25, ¬ Need 6 w.toFinset := by
  have h : chunk6_25.all (routes 5 pool6_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_25 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_35 _ hm
  · exact checked5_40 _ hm
private def chunk6_26 : List (List T) := [[wire992,wire1057,wire2143,wire4228,wire10591,wire16912,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire16912,wire31744,wire32008],
  [wire992,wire1057,wire2143,wire5092,wire8456,wire16912,wire31744],
  [wire992,wire1057,wire2143,wire5285,wire8456,wire16912,wire31744]]
private def pool6_26 : List (List (List T)) := [chunk5_14, chunk5_15, chunk5_17, chunk5_18, chunk5_22, chunk5_23, chunk5_24, chunk5_33, chunk5_34, chunk5_36]
private theorem checked6_26 : ∀ w ∈ chunk6_26, ¬ Need 6 w.toFinset := by
  have h : chunk6_26.all (routes 5 pool6_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
  · exact checked5_36 _ hm
private def chunk6_27 : List (List T) := [[wire992,wire1057,wire3171,wire4228,wire8479,wire16912,wire31744],
  [wire992,wire1057,wire3199,wire4228,wire8456,wire16912,wire31744],
  [wire992,wire1087,wire2114,wire4228,wire8456,wire16912,wire31777],
  [wire992,wire1087,wire2114,wire4228,wire8456,wire17969,wire31744]]
private def pool6_27 : List (List (List T)) := [chunk5_19, chunk5_20, chunk5_21, chunk5_23, chunk5_24, chunk5_37, chunk5_38, chunk5_39, chunk5_41]
private theorem checked6_27 : ∀ w ∈ chunk6_27, ¬ Need 6 w.toFinset := by
  have h : chunk6_27.all (routes 5 pool6_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_37 _ hm
  · exact checked5_38 _ hm
  · exact checked5_39 _ hm
  · exact checked5_41 _ hm
private def chunk6_28 : List (List T) := [[wire992,wire1087,wire2114,wire5285,wire8456,wire16912,wire31744],
  [wire1057,wire1087,wire2114,wire4228,wire8456,wire17392,wire31744],
  [wire1057,wire1087,wire2114,wire5092,wire8456,wire16912,wire31744],
  [wire1057,wire2017,wire2114,wire4228,wire8479,wire16912,wire31744]]
private def pool6_28 : List (List (List T)) := [chunk5_20, chunk5_21, chunk5_22, chunk5_24, chunk5_25, chunk5_27, chunk5_30, chunk5_37, chunk5_38, chunk5_39, chunk5_40, chunk5_41]
private theorem checked6_28 : ∀ w ∈ chunk6_28, ¬ Need 6 w.toFinset := by
  have h : chunk6_28.all (routes 5 pool6_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_27 _ hm
  · exact checked5_30 _ hm
  · exact checked5_37 _ hm
  · exact checked5_38 _ hm
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
private def chunk6_29 : List (List T) := [[wire1057,wire2017,wire2143,wire4228,wire8456,wire16912,wire31744],
  [wire1057,wire2114,wire2143,wire4228,wire8456,wire17392,wire31744],
  [wire1057,wire2114,wire2143,wire5092,wire8456,wire16912,wire31744],
  [wire1057,wire2114,wire4228,wire5092,wire8479,wire16912,wire31744]]
private def pool6_29 : List (List (List T)) := [chunk5_25, chunk5_26, chunk5_27, chunk5_28, chunk5_29, chunk5_30, chunk5_31, chunk5_32, chunk5_33, chunk5_35, chunk5_36, chunk5_40, chunk5_41]
private theorem checked6_29 : ∀ w ∈ chunk6_29, ¬ Need 6 w.toFinset := by
  have h : chunk6_29.all (routes 5 pool6_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_25 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
private def chunk6_30 : List (List T) := [[wire1057,wire2114,wire4228,wire8456,wire8479,wire17392,wire31744],
  [wire1057,wire2114,wire4228,wire8479,wire16912,wire17392,wire31744],
  [wire1057,wire2114,wire4228,wire8479,wire17392,wire31744],
  [wire1057,wire2114,wire5092,wire8456,wire8479,wire16912,wire31744]]
private def pool6_30 : List (List (List T)) := [chunk5_26, chunk5_27, chunk5_28, chunk5_30, chunk5_37]
private theorem checked6_30 : ∀ w ∈ chunk6_30, ¬ Need 6 w.toFinset := by
  have h : chunk6_30.all (routes 5 pool6_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_30 _ hm
  · exact checked5_37 _ hm
private def chunk6_31 : List (List T) := [[wire1057,wire2114,wire5092,wire8479,wire16912,wire31744],
  [wire1057,wire2143,wire4228,wire5092,wire8456,wire16912,wire31744],
  [wire1057,wire2143,wire4228,wire8456,wire16912,wire17392,wire31744],
  [wire1057,wire2143,wire4228,wire8456,wire17392,wire31744]]
private def pool6_31 : List (List (List T)) := [chunk5_0, chunk5_14, chunk5_28, chunk5_29, chunk5_30, chunk5_31, chunk5_32, chunk5_33, chunk5_34, chunk5_36, chunk5_37]
private theorem checked6_31 : ∀ w ∈ chunk6_31, ¬ Need 6 w.toFinset := by
  have h : chunk6_31.all (routes 5 pool6_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_14 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
private def chunk6_32 : List (List T) := [[wire1057,wire2143,wire5092,wire8456,wire16912,wire31744],
  [wire1087,wire2017,wire2114,wire4228,wire8456,wire16912,wire31744]]
private def pool6_32 : List (List (List T)) := [chunk5_0, chunk5_14, chunk5_33, chunk5_34, chunk5_35, chunk5_36, chunk5_37, chunk5_38, chunk5_39, chunk5_40, chunk5_41]
private theorem checked6_32 : ∀ w ∈ chunk6_32, ¬ Need 6 w.toFinset := by
  have h : chunk6_32.all (routes 5 pool6_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_14 _ hm
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_38 _ hm
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
#print axioms checked6_32
private def chunk7_0 : List (List T) := [[wire16,wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire31744],
  [wire31,wire256,wire992,wire1057,wire2114,wire4228,wire16912,wire31744],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire16912,wire31744],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire16912,wire31777]]
private def pool7_0 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_3, chunk6_4, chunk6_5, chunk6_6, chunk6_7, chunk6_8, chunk6_9, chunk6_10, chunk6_11, chunk6_13, chunk6_18, chunk6_19, chunk6_20, chunk6_23, chunk6_27]
private theorem checked7_0 : ∀ w ∈ chunk7_0, ¬ Need 7 w.toFinset := by
  have h : chunk7_0.all (routes 6 pool7_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_5 _ hm
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_9 _ hm
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_13 _ hm
  · exact checked6_18 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_23 _ hm
  · exact checked6_27 _ hm
private def chunk7_1 : List (List T) := [[wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire16912,wire32008],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire16912,wire32272],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire17392,wire31744],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire17969,wire31744]]
private def pool7_1 : List (List (List T)) := [chunk6_1, chunk6_2, chunk6_4, chunk6_8, chunk6_9, chunk6_11, chunk6_12, chunk6_14, chunk6_21, chunk6_23, chunk6_24, chunk6_27]
private theorem checked7_1 : ∀ w ∈ chunk7_1, ¬ Need 7 w.toFinset := by
  have h : chunk7_1.all (routes 6 pool7_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_4 _ hm
  · exact checked6_8 _ hm
  · exact checked6_9 _ hm
  · exact checked6_11 _ hm
  · exact checked6_12 _ hm
  · exact checked6_14 _ hm
  · exact checked6_21 _ hm
  · exact checked6_23 _ hm
  · exact checked6_24 _ hm
  · exact checked6_27 _ hm
private def chunk7_2 : List (List T) := [[wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire21140,wire31744],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire31744,wire32272],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire32272],
  [wire31,wire992,wire1057,wire2114,wire4228,wire8479,wire16912,wire31744]]
private def pool7_2 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_3, chunk6_5, chunk6_6, chunk6_7, chunk6_10, chunk6_12, chunk6_14, chunk6_15, chunk6_19, chunk6_20, chunk6_22, chunk6_24, chunk6_25]
private theorem checked7_2 : ∀ w ∈ chunk7_2, ¬ Need 7 w.toFinset := by
  have h : chunk7_2.all (routes 6 pool7_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_5 _ hm
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
  · exact checked6_10 _ hm
  · exact checked6_12 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_22 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
private def chunk7_3 : List (List T) := [[wire31,wire992,wire1057,wire2114,wire4228,wire9513,wire16912,wire31744],
  [wire31,wire992,wire1057,wire2114,wire4228,wire10570,wire16912,wire31744],
  [wire31,wire992,wire1057,wire2114,wire4228,wire16912,wire31744,wire32008],
  [wire31,wire992,wire1057,wire2114,wire4228,wire16912,wire32008]]
private def pool7_3 : List (List (List T)) := [chunk6_0, chunk6_2, chunk6_3, chunk6_4, chunk6_5, chunk6_6, chunk6_7, chunk6_8, chunk6_9, chunk6_10, chunk6_11, chunk6_13, chunk6_15, chunk6_16, chunk6_18, chunk6_19, chunk6_20, chunk6_22, chunk6_25, chunk6_26]
private theorem checked7_3 : ∀ w ∈ chunk7_3, ¬ Need 7 w.toFinset := by
  have h : chunk7_3.all (routes 6 pool7_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_5 _ hm
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_9 _ hm
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_13 _ hm
  · exact checked6_15 _ hm
  · exact checked6_16 _ hm
  · exact checked6_18 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_22 _ hm
  · exact checked6_25 _ hm
  · exact checked6_26 _ hm
private def chunk7_4 : List (List T) := [[wire31,wire992,wire1057,wire2114,wire5092,wire8456,wire16912,wire31744],
  [wire31,wire992,wire1057,wire2114,wire5285,wire8456,wire16912,wire31744],
  [wire31,wire992,wire1057,wire2143,wire4228,wire8456,wire16912,wire31744],
  [wire31,wire992,wire1057,wire3171,wire4228,wire8456,wire16912,wire31744]]
private def pool7_4 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_5, chunk6_6, chunk6_7, chunk6_8, chunk6_9, chunk6_13, chunk6_14, chunk6_16, chunk6_17, chunk6_18, chunk6_22, chunk6_23, chunk6_25, chunk6_26, chunk6_27, chunk6_28]
private theorem checked7_4 : ∀ w ∈ chunk7_4, ¬ Need 7 w.toFinset := by
  have h : chunk7_4.all (routes 6 pool7_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_5 _ hm
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_9 _ hm
  · exact checked6_13 _ hm
  · exact checked6_14 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_18 _ hm
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_25 _ hm
  · exact checked6_26 _ hm
  · exact checked6_27 _ hm
  · exact checked6_28 _ hm
private def chunk7_5 : List (List T) := [[wire31,wire1057,wire2017,wire2114,wire4228,wire8456,wire16912,wire31744],
  [wire31,wire1057,wire2114,wire4228,wire5092,wire8456,wire16912,wire31744],
  [wire31,wire1057,wire2114,wire4228,wire8456,wire16912,wire17392,wire31744],
  [wire31,wire1057,wire2114,wire4228,wire8456,wire17392,wire31744]]
private def pool7_5 : List (List (List T)) := [chunk6_1, chunk6_10, chunk6_11, chunk6_12, chunk6_13, chunk6_14, chunk6_16, chunk6_17, chunk6_18, chunk6_28, chunk6_29, chunk6_30, chunk6_31, chunk6_32]
private theorem checked7_5 : ∀ w ∈ chunk7_5, ¬ Need 7 w.toFinset := by
  have h : chunk7_5.all (routes 6 pool7_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_12 _ hm
  · exact checked6_13 _ hm
  · exact checked6_14 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_18 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_30 _ hm
  · exact checked6_31 _ hm
  · exact checked6_32 _ hm
private def chunk7_6 : List (List T) := [[wire31,wire1057,wire2114,wire5092,wire8456,wire16912,wire31744],
  [wire992,wire1057,wire1087,wire2114,wire4228,wire8456,wire16912,wire31744],
  [wire992,wire1057,wire2114,wire2143,wire4228,wire8456,wire16912,wire31744],
  [wire992,wire1057,wire2114,wire4228,wire8456,wire8479,wire16912,wire31744]]
private def pool7_6 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_13, chunk6_14, chunk6_15, chunk6_16, chunk6_17, chunk6_18, chunk6_19, chunk6_20, chunk6_21, chunk6_22, chunk6_23, chunk6_25, chunk6_27, chunk6_28, chunk6_29, chunk6_30, chunk6_31, chunk6_32]
private theorem checked7_6 : ∀ w ∈ chunk7_6, ¬ Need 7 w.toFinset := by
  have h : chunk7_6.all (routes 6 pool7_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_13 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_18 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_21 _ hm
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_25 _ hm
  · exact checked6_27 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_30 _ hm
  · exact checked6_31 _ hm
  · exact checked6_32 _ hm
private def chunk7_7 : List (List T) := [[wire992,wire1057,wire2114,wire4228,wire8479,wire16912,wire31744],
  [wire992,wire1057,wire2143,wire4228,wire8456,wire16912,wire31744]]
private def pool7_7 : List (List (List T)) := [chunk6_0, chunk6_19, chunk6_20, chunk6_21, chunk6_22, chunk6_23, chunk6_24, chunk6_25, chunk6_26, chunk6_27, chunk6_28, chunk6_29, chunk6_30, chunk6_31, chunk6_32]
private theorem checked7_7 : ∀ w ∈ chunk7_7, ¬ Need 7 w.toFinset := by
  have h : chunk7_7.all (routes 6 pool7_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_21 _ hm
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_26 _ hm
  · exact checked6_27 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_30 _ hm
  · exact checked6_31 _ hm
  · exact checked6_32 _ hm
#print axioms checked7_7
private def chunk8_0 : List (List T) := [[wire31,wire992,wire1057,wire2114,wire4228,wire8456,wire16912,wire31744]]
private def pool8_0 : List (List (List T)) := [chunk7_0, chunk7_1, chunk7_2, chunk7_3, chunk7_4, chunk7_5, chunk7_6, chunk7_7]
private theorem checked8_0 : ∀ w ∈ chunk8_0, ¬ Need 8 w.toFinset := by
  have h : chunk8_0.all (routes 7 pool8_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_0 _ hm
  · exact checked7_1 _ hm
  · exact checked7_2 _ hm
  · exact checked7_3 _ hm
  · exact checked7_4 _ hm
  · exact checked7_5 _ hm
  · exact checked7_6 _ hm
  · exact checked7_7 _ hm
#print axioms checked8_0
private theorem root : safe 8 ins := initial checked8_0 (by decide +kernel)
def graph (u : Fin 3) (v : Fin 5) := (7541 : Nat).testBit (5 * u.val + v.val)
def row (i : Fin 15) : Fin 3 := ⟨i.val / 5, by have := i.isLt; omega⟩
def col (i : Fin 15) : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
def inputs (i : Fin 15) := PEqualNP.Represents.oneEach (row i) (col i)

theorem exactLower : ¬ PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 3) (v : Fin 5) => (7541 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  rintro ⟨C, hg, hsize, he⟩
  apply exclude C.gates C.output (fun g hm => hg g hm) ins ins (fun ⦃_⦄ h => h) 8 hsize root
  intro k
  have hi : ∀ i : Fin 15, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 15, graph (row i) (col i) = bit i target := by decide +kernel
  have heval : C.eval (inputs k) = graph (row k) (col k) := he (row k) (col k)
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using heval

#print axioms exactLower


def circuit : Circuit :=
  { gates := [⟨.or,[4,0]⟩, ⟨.or,[5,1]⟩, ⟨.or,[9,8]⟩, ⟨.or,[6,8]⟩,
              ⟨.or,[7,9]⟩, ⟨.and,[12,11]⟩, ⟨.or,[3,13]⟩, ⟨.and,[2,10]⟩,
              ⟨.or,[15,14]⟩], output := 16 }
theorem upper : PEqualNP.Represents.RepSizeAtMost graph 9 := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
#print axioms upper
end Matrix7541
