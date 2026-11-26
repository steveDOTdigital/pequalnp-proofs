import PEqualNP.Defs.Represents

-- Search soundness adapted from Nico Habets and Lewis Watson, as credited in Mask53Exact.lean.
-- Original source: https://github.com/open-goat/pequalnp-proofs/blob/62a08312807b6a9ea0e9f8319897c74bf63e8be2/lean/PEqualNP/Outside/L_meta_5601.lean
-- For graph 1223 the support argument, separation certificates, input tables and theorem are new.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Matrix104317

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 20
private def ins : List T := [31, 992, 31744, 1015808, 33825, 67650, 135300, 270600, 541200]
private def target : T := 104317
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 20) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin 20) :
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

private def down (x : T) (p q : Fin 20) : Prop := bit p x = true ∧ bit q x = false
private def covers (r : T → Fin 20 → Fin 20 → Prop) (s : Finset T) :=
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
    have ho : ∀ i : Fin 20, bit i (-1) = true := by decide +kernel
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
  decide (w.toFinset.card ≤ n+1) && (List.finRange 20).all (fun p =>
    (List.finRange 20).all (fun q => !(bit p target && !(bit q target)) ||
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
private def wire31 : T := 31
private def wire992 : T := 992
private def wire4096 : T := 4096
private def wire4100 : T := 4100
private def wire4127 : T := 4127
private def wire31744 : T := 31744
private def wire31775 : T := 31775
private def wire33825 : T := 33825
private def wire33855 : T := 33855
private def wire34785 : T := 34785
private def wire37921 : T := 37921
private def wire37925 : T := 37925
private def wire64545 : T := 64545
private def wire65536 : T := 65536
private def wire65600 : T := 65600
private def wire66528 : T := 66528
private def wire67650 : T := 67650
private def wire67679 : T := 67679
private def wire69636 : T := 69636
private def wire69696 : T := 69696
private def wire71746 : T := 71746
private def wire71775 : T := 71775
private def wire97346 : T := 97346
private def wire97375 : T := 97375
private def wire99361 : T := 99361
private def wire99425 : T := 99425
private def wire101475 : T := 101475
private def wire101503 : T := 101503
private def wire103461 : T := 103461
private def wire103521 : T := 103521
private def wire130147 : T := 130147
private def wire135300 : T := 135300
private def wire136164 : T := 136164
private def wire169125 : T := 169125
private def wire169957 : T := 169957
private def wire200836 : T := 200836
private def wire201700 : T := 201700
private def wire270600 : T := 270600
private def wire274696 : T := 274696
private def wire294152 : T := 294152
private def wire304425 : T := 304425
private def wire326953 : T := 326953
private def wire336136 : T := 336136
private def wire541200 : T := 541200
private def wire545296 : T := 545296
private def wire556560 : T := 556560
private def wire575025 : T := 575025
private def wire589361 : T := 589361
private def wire606736 : T := 606736
private def wire811800 : T := 811800
private def wire815896 : T := 815896
private def wire818968 : T := 818968
private def wire845625 : T := 845625
private def wire851769 : T := 851769
private def wire877336 : T := 877336
private def wire1015808 : T := 1015808
private def wire1016800 : T := 1016800
private def wire1016865 : T := 1016865
private def wire1020036 : T := 1020036
private def wire1020900 : T := 1020900
private def wire1021093 : T := 1021093
private def wire1024264 : T := 1024264
private def wire1025321 : T := 1025321
private def wire1032720 : T := 1032720
private def wire1033777 : T := 1033777
private def wire1041176 : T := 1041176
private def wire1042233 : T := 1042233

-- Every listed set is checked against every possible next output and every reuse of its inputs.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def layer2 : List (List T) := []
private theorem good2 (w : List T) (h : w ∈ layer2) : ¬ Need 2 w.toFinset := by simp [layer2] at h
private def chunk3_0 : List (List T) := [[wire31,wire99425,wire136164,wire818968],
  [wire31,wire103521,wire136164,wire811800],
  [wire992,wire37925,wire67679,wire1041176],
  [wire992,wire67679,wire103461,wire811800]]
private def pool3_0 : List (List (List T)) := []
private theorem checked3_0 : ∀ w ∈ chunk3_0, ¬ Need 3 w.toFinset := by
  have h : chunk3_0.all (routes 2 pool3_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_0] at hv
#print axioms checked3_0
private def chunk4_0 : List (List T) := [[wire31,wire992,wire37925,wire67650,wire1041176],
  [wire31,wire992,wire99425,wire135300,wire818968],
  [wire31,wire992,wire130147,wire811800,wire1021093],
  [wire31,wire31744,wire99425,wire136164,wire811800]]
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
private def chunk4_1 : List (List T) := [[wire31,wire33825,wire65600,wire136164,wire818968],
  [wire31,wire33825,wire67650,wire201700,wire818968],
  [wire31,wire33825,wire69696,wire136164,wire811800],
  [wire31,wire33825,wire97346,wire201700,wire811800]]
private def pool4_1 : List (List (List T)) := [chunk3_0]
private theorem checked4_1 : ∀ w ∈ chunk4_1, ¬ Need 4 w.toFinset := by
  have h : chunk4_1.all (routes 3 pool4_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_2 : List (List T) := [[wire31,wire34785,wire97346,wire845625,wire1020036],
  [wire31,wire34785,wire130147,wire811800,wire1020036],
  [wire31,wire67650,wire99361,wire136164,wire818968],
  [wire31,wire67650,wire169957,wire851769,wire1015808]]
private def pool4_2 : List (List (List T)) := []
private theorem checked4_2 : ∀ w ∈ chunk4_2, ¬ Need 4 w.toFinset := by
  have h : chunk4_2.all (routes 3 pool4_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_2] at hv
private def chunk4_3 : List (List T) := [[wire31,wire97346,wire99361,wire136164,wire811800],
  [wire31,wire97346,wire169957,wire845625,wire1015808],
  [wire31,wire99425,wire136164,wire270600,wire556560],
  [wire31,wire99425,wire136164,wire294152,wire541200]]
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
private def chunk4_4 : List (List T) := [[wire31,wire101475,wire136164,wire818968,wire1016865],
  [wire31,wire101475,wire169957,wire818968,wire1015808],
  [wire31,wire103521,wire136164,wire270600,wire541200],
  [wire31,wire130147,wire136164,wire811800,wire1016865]]
private def pool4_4 : List (List (List T)) := [chunk3_0]
private theorem checked4_4 : ∀ w ∈ chunk4_4, ¬ Need 4 w.toFinset := by
  have h : chunk4_4.all (routes 3 pool4_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_5 : List (List T) := [[wire31,wire130147,wire169957,wire811800,wire1015808],
  [wire992,wire4100,wire33825,wire67679,wire1041176],
  [wire992,wire31744,wire101503,wire135300,wire1042233],
  [wire992,wire31744,wire101503,wire169125,wire1041176]]
private def pool4_5 : List (List (List T)) := [chunk3_0]
private theorem checked4_5 : ∀ w ∈ chunk4_5, ¬ Need 4 w.toFinset := by
  have h : chunk4_5.all (routes 3 pool4_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_6 : List (List T) := [[wire992,wire31744,wire101503,wire811800,wire1021093],
  [wire992,wire31744,wire101503,wire845625,wire1020036],
  [wire992,wire33825,wire67679,wire69636,wire811800],
  [wire992,wire33825,wire71775,wire135300,wire1041176]]
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
private def chunk4_7 : List (List T) := [[wire992,wire33825,wire71775,wire811800,wire1020036],
  [wire992,wire33855,wire97346,wire811800,wire1021093],
  [wire992,wire33855,wire97346,wire845625,wire1020036],
  [wire992,wire37921,wire67679,wire135300,wire1041176]]
private def pool4_7 : List (List (List T)) := []
private theorem checked4_7 : ∀ w ∈ chunk4_7, ¬ Need 4 w.toFinset := by
  have h : chunk4_7.all (routes 3 pool4_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_7] at hv
private def chunk4_8 : List (List T) := [[wire992,wire37921,wire67679,wire811800,wire1020036],
  [wire992,wire37925,wire67679,wire270600,wire1032720],
  [wire992,wire37925,wire67679,wire541200,wire1024264],
  [wire992,wire37925,wire67679,wire811800,wire1015808]]
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
private def chunk4_9 : List (List T) := [[wire992,wire64545,wire67679,wire169125,wire1041176],
  [wire992,wire64545,wire67679,wire811800,wire1021093],
  [wire992,wire67679,wire103461,wire270600,wire541200],
  [wire31744,wire33825,wire67679,wire136164,wire877336]]
private def pool4_9 : List (List (List T)) := [chunk3_0]
private theorem checked4_9 : ∀ w ∈ chunk4_9, ¬ Need 4 w.toFinset := by
  have h : chunk4_9.all (routes 3 pool4_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_10 : List (List T) := [[wire31744,wire33825,wire67679,wire201700,wire811800],
  [wire31744,wire34785,wire67679,wire135300,wire1042233],
  [wire31744,wire34785,wire67679,wire845625,wire1020036],
  [wire31744,wire34785,wire101503,wire135300,wire1041176]]
private def pool4_10 : List (List (List T)) := []
private theorem checked4_10 : ∀ w ∈ chunk4_10, ¬ Need 4 w.toFinset := by
  have h : chunk4_10.all (routes 3 pool4_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_10] at hv
private def chunk4_11 : List (List T) := [[wire31744,wire34785,wire101503,wire811800,wire1020036],
  [wire31744,wire67679,wire99361,wire136164,wire811800],
  [wire31744,wire67679,wire169957,wire845625,wire1015808],
  [wire31744,wire101503,wire136164,wire811800,wire1016865]]
private def pool4_11 : List (List (List T)) := []
private theorem checked4_11 : ∀ w ∈ chunk4_11, ¬ Need 4 w.toFinset := by
  have h : chunk4_11.all (routes 3 pool4_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_11] at hv
private def chunk4_12 : List (List T) := [[wire31744,wire101503,wire136164,wire845625,wire1015808],
  [wire31744,wire101503,wire169957,wire811800,wire1015808],
  [wire33825,wire67679,wire136164,wire815896,wire1015808],
  [wire33825,wire67679,wire136164,wire818968,wire1041176]]
private def pool4_12 : List (List (List T)) := []
private theorem checked4_12 : ∀ w ∈ chunk4_12, ¬ Need 4 w.toFinset := by
  have h : chunk4_12.all (routes 3 pool4_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_12] at hv
private def chunk4_13 : List (List T) := [[wire33825,wire71775,wire136164,wire811800,wire1015808],
  [wire33855,wire34785,wire97346,wire811800,wire1020036],
  [wire33855,wire67650,wire136164,wire818968,wire1016865],
  [wire33855,wire67650,wire136164,wire851769,wire1015808]]
private def pool4_13 : List (List (List T)) := []
private theorem checked4_13 : ∀ w ∈ chunk4_13, ¬ Need 4 w.toFinset := by
  have h : chunk4_13.all (routes 3 pool4_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_13] at hv
private def chunk4_14 : List (List T) := [[wire33855,wire67650,wire169957,wire818968,wire1015808],
  [wire33855,wire97346,wire136164,wire811800,wire1016865],
  [wire33855,wire97346,wire136164,wire845625,wire1015808],
  [wire33855,wire97346,wire169957,wire811800,wire1015808]]
private def pool4_14 : List (List (List T)) := []
private theorem checked4_14 : ∀ w ∈ chunk4_14, ¬ Need 4 w.toFinset := by
  have h : chunk4_14.all (routes 3 pool4_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_14] at hv
private def chunk4_15 : List (List T) := [[wire34785,wire64545,wire67679,wire135300,wire1041176],
  [wire34785,wire64545,wire67679,wire811800,wire1020036],
  [wire37921,wire67679,wire136164,wire811800,wire1015808],
  [wire64545,wire67679,wire136164,wire811800,wire1016865]]
private def pool4_15 : List (List (List T)) := []
private theorem checked4_15 : ∀ w ∈ chunk4_15, ¬ Need 4 w.toFinset := by
  have h : chunk4_15.all (routes 3 pool4_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_15] at hv
private def chunk4_16 : List (List T) := [[wire64545,wire67679,wire169957,wire811800,wire1015808]]
private def pool4_16 : List (List (List T)) := []
private theorem checked4_16 : ∀ w ∈ chunk4_16, ¬ Need 4 w.toFinset := by
  have h : chunk4_16.all (routes 3 pool4_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_16] at hv
#print axioms checked4_16
private def chunk5_0 : List (List T) := [[wire31,wire992,wire4100,wire33825,wire67650,wire1041176],
  [wire31,wire992,wire31744,wire99425,wire135300,wire811800],
  [wire31,wire992,wire31744,wire101475,wire135300,wire1042233],
  [wire31,wire992,wire31744,wire101475,wire169125,wire1041176]]
private def pool5_0 : List (List (List T)) := [chunk4_0, chunk4_5]
private theorem checked5_0 : ∀ w ∈ chunk5_0, ¬ Need 5 w.toFinset := by
  have h : chunk5_0.all (routes 4 pool5_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_5 _ hm
private def chunk5_1 : List (List T) := [[wire31,wire992,wire31744,wire101475,wire811800,wire1021093],
  [wire31,wire992,wire31744,wire101475,wire845625,wire1020036],
  [wire31,wire992,wire33825,wire65600,wire135300,wire818968],
  [wire31,wire992,wire33825,wire67650,wire200836,wire818968]]
private def pool5_1 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_6]
private theorem checked5_1 : ∀ w ∈ chunk5_1, ¬ Need 5 w.toFinset := by
  have h : chunk5_1.all (routes 4 pool5_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_6 _ hm
private def chunk5_2 : List (List T) := [[wire31,wire992,wire33825,wire71746,wire135300,wire1041176],
  [wire31,wire992,wire33825,wire71746,wire811800,wire1020036],
  [wire31,wire992,wire33825,wire97346,wire200836,wire811800],
  [wire31,wire992,wire33825,wire97346,wire811800,wire1020036]]
private def pool5_2 : List (List (List T)) := [chunk4_1, chunk4_6, chunk4_7]
private theorem checked5_2 : ∀ w ∈ chunk5_2, ¬ Need 5 w.toFinset := by
  have h : chunk5_2.all (routes 4 pool5_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
private def chunk5_3 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire811800,wire1020900],
  [wire31,wire992,wire33825,wire97346,wire811800,wire1021093],
  [wire31,wire992,wire33825,wire97346,wire818968,wire1020036],
  [wire31,wire992,wire33825,wire97346,wire845625,wire1020036]]
private def pool5_3 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_7]
private theorem checked5_3 : ∀ w ∈ chunk5_3, ¬ Need 5 w.toFinset := by
  have h : chunk5_3.all (routes 4 pool5_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_7 _ hm
private def chunk5_4 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire1020036,wire1041176],
  [wire31,wire992,wire33825,wire97375,wire811800,wire1020036],
  [wire31,wire992,wire33825,wire130147,wire811800,wire1020036],
  [wire31,wire992,wire37921,wire67650,wire135300,wire1041176]]
private def pool5_4 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_7]
private theorem checked5_4 : ∀ w ∈ chunk5_4, ¬ Need 5 w.toFinset := by
  have h : chunk5_4.all (routes 4 pool5_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_7 _ hm
private def chunk5_5 : List (List T) := [[wire31,wire992,wire37921,wire67650,wire811800,wire1020036],
  [wire31,wire992,wire37925,wire67650,wire270600,wire1032720],
  [wire31,wire992,wire37925,wire67650,wire541200,wire1024264],
  [wire31,wire992,wire37925,wire67650,wire811800,wire1015808]]
private def pool5_5 : List (List (List T)) := [chunk4_0, chunk4_8]
private theorem checked5_5 : ∀ w ∈ chunk5_5, ¬ Need 5 w.toFinset := by
  have h : chunk5_5.all (routes 4 pool5_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_8 _ hm
private def chunk5_6 : List (List T) := [[wire31,wire992,wire64545,wire67650,wire169125,wire1041176],
  [wire31,wire992,wire64545,wire67650,wire811800,wire1021093],
  [wire31,wire992,wire67650,wire99361,wire135300,wire818968],
  [wire31,wire992,wire67650,wire169125,wire326953,wire1032720]]
private def pool5_6 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_9]
private theorem checked5_6 : ∀ w ∈ chunk5_6, ¬ Need 5 w.toFinset := by
  have h : chunk5_6.all (routes 4 pool5_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_9 _ hm
private def chunk5_7 : List (List T) := [[wire31,wire992,wire67650,wire169125,wire589361,wire1024264],
  [wire31,wire992,wire67650,wire169125,wire851769,wire1015808],
  [wire31,wire992,wire97346,wire99361,wire135300,wire811800],
  [wire31,wire992,wire97346,wire169125,wire845625,wire1015808]]
private def pool5_7 : List (List (List T)) := [chunk4_2, chunk4_3]
private theorem checked5_7 : ∀ w ∈ chunk5_7, ¬ Need 5 w.toFinset := by
  have h : chunk5_7.all (routes 4 pool5_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
private def chunk5_8 : List (List T) := [[wire31,wire992,wire97346,wire304425,wire575025,wire1020036],
  [wire31,wire992,wire99425,wire135300,wire270600,wire556560],
  [wire31,wire992,wire99425,wire135300,wire294152,wire541200],
  [wire31,wire992,wire101475,wire135300,wire294152,wire1033777]]
private def pool5_8 : List (List (List T)) := [chunk4_0, chunk4_3]
private theorem checked5_8 : ∀ w ∈ chunk5_8, ¬ Need 5 w.toFinset := by
  have h : chunk5_8.all (routes 4 pool5_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_3 _ hm
private def chunk5_9 : List (List T) := [[wire31,wire992,wire101475,wire135300,wire556560,wire1025321],
  [wire31,wire992,wire101475,wire135300,wire818968,wire1016865],
  [wire31,wire992,wire101475,wire169125,wire294152,wire1032720],
  [wire31,wire992,wire101475,wire169125,wire556560,wire1024264]]
private def pool5_9 : List (List (List T)) := [chunk4_4]
private theorem checked5_9 : ∀ w ∈ chunk5_9, ¬ Need 5 w.toFinset := by
  have h : chunk5_9.all (routes 4 pool5_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_4 _ hm
private def chunk5_10 : List (List T) := [[wire31,wire992,wire101475,wire169125,wire818968,wire1015808],
  [wire31,wire992,wire130147,wire135300,wire811800,wire1016865],
  [wire31,wire992,wire130147,wire169125,wire811800,wire1015808],
  [wire31,wire992,wire130147,wire270600,wire541200,wire1021093]]
private def pool5_10 : List (List (List T)) := [chunk4_0, chunk4_4, chunk4_5]
private theorem checked5_10 : ∀ w ∈ chunk5_10, ¬ Need 5 w.toFinset := by
  have h : chunk5_10.all (routes 4 pool5_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
private def chunk5_11 : List (List T) := [[wire31,wire31744,wire33825,wire65600,wire136164,wire811800],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire877336],
  [wire31,wire31744,wire33825,wire67650,wire201700,wire811800],
  [wire31,wire31744,wire34785,wire67650,wire135300,wire1042233]]
private def pool5_11 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_9, chunk4_10]
private theorem checked5_11 : ∀ w ∈ chunk5_11, ¬ Need 5 w.toFinset := by
  have h : chunk5_11.all (routes 4 pool5_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
private def chunk5_12 : List (List T) := [[wire31,wire31744,wire34785,wire67650,wire845625,wire1020036],
  [wire31,wire31744,wire34785,wire101475,wire135300,wire1041176],
  [wire31,wire31744,wire34785,wire101475,wire811800,wire1020036],
  [wire31,wire31744,wire67650,wire99361,wire136164,wire811800]]
private def pool5_12 : List (List (List T)) := [chunk4_2, chunk4_3, chunk4_10, chunk4_11]
private theorem checked5_12 : ∀ w ∈ chunk5_12, ¬ Need 5 w.toFinset := by
  have h : chunk5_12.all (routes 4 pool5_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
private def chunk5_13 : List (List T) := [[wire31,wire31744,wire67650,wire169957,wire845625,wire1015808],
  [wire31,wire31744,wire99425,wire136164,wire270600,wire541200],
  [wire31,wire31744,wire101475,wire136164,wire811800,wire1016865],
  [wire31,wire31744,wire101475,wire136164,wire845625,wire1015808]]
private def pool5_13 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_3, chunk4_4, chunk4_11, chunk4_12]
private theorem checked5_13 : ∀ w ∈ chunk5_13, ¬ Need 5 w.toFinset := by
  have h : chunk5_13.all (routes 4 pool5_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
private def chunk5_14 : List (List T) := [[wire31,wire31744,wire101475,wire169957,wire811800,wire1015808],
  [wire31,wire33825,wire34785,wire97346,wire811800,wire1020036],
  [wire31,wire33825,wire65536,wire67650,wire136164,wire818968],
  [wire31,wire33825,wire65536,wire97346,wire136164,wire811800]]
private def pool5_14 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_3, chunk4_4, chunk4_5, chunk4_12, chunk4_13]
private theorem checked5_14 : ∀ w ∈ chunk5_14, ¬ Need 5 w.toFinset := by
  have h : chunk5_14.all (routes 4 pool5_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
private def chunk5_15 : List (List T) := [[wire31,wire33825,wire65600,wire136164,wire270600,wire556560],
  [wire31,wire33825,wire65600,wire136164,wire294152,wire541200],
  [wire31,wire33825,wire66528,wire67650,wire135300,wire818968],
  [wire31,wire33825,wire66528,wire97346,wire135300,wire811800]]
private def pool5_15 : List (List (List T)) := [chunk4_1, chunk4_3]
private theorem checked5_15 : ∀ w ∈ chunk5_15, ¬ Need 5 w.toFinset := by
  have h : chunk5_15.all (routes 4 pool5_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_3 _ hm
private def chunk5_16 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire294152,wire606736],
  [wire31,wire33825,wire67650,wire136164,wire336136,wire556560],
  [wire31,wire33825,wire67650,wire136164,wire815896,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire818968,wire1015808]]
private def pool5_16 : List (List (List T)) := [chunk4_12]
private theorem checked5_16 : ∀ w ∈ chunk5_16, ¬ Need 5 w.toFinset := by
  have h : chunk5_16.all (routes 4 pool5_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_12 _ hm
private def chunk5_17 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire818968,wire1016800],
  [wire31,wire33825,wire67650,wire136164,wire818968,wire1016865],
  [wire31,wire33825,wire67650,wire136164,wire818968,wire1020036],
  [wire31,wire33825,wire67650,wire136164,wire818968,wire1020900]]
private def pool5_17 : List (List (List T)) := [chunk4_1, chunk4_4, chunk4_13]
private theorem checked5_17 : ∀ w ∈ chunk5_17, ¬ Need 5 w.toFinset := by
  have h : chunk5_17.all (routes 4 pool5_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_4 _ hm
  · exact checked4_13 _ hm
private def chunk5_18 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire818968,wire1024264],
  [wire31,wire33825,wire67650,wire136164,wire818968,wire1032720],
  [wire31,wire33825,wire67650,wire136164,wire818968,wire1041176],
  [wire31,wire33825,wire67650,wire136164,wire851769,wire1015808]]
private def pool5_18 : List (List (List T)) := [chunk4_2, chunk4_12, chunk4_13]
private theorem checked5_18 : ∀ w ∈ chunk5_18, ¬ Need 5 w.toFinset := by
  have h : chunk5_18.all (routes 4 pool5_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
private def chunk5_19 : List (List T) := [[wire31,wire33825,wire67650,wire169957,wire818968,wire1015808],
  [wire31,wire33825,wire67650,wire201700,wire270600,wire556560],
  [wire31,wire33825,wire67650,wire201700,wire294152,wire541200],
  [wire31,wire33825,wire67679,wire136164,wire818968,wire1015808]]
private def pool5_19 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_4, chunk4_14]
private theorem checked5_19 : ∀ w ∈ chunk5_19, ¬ Need 5 w.toFinset := by
  have h : chunk5_19.all (routes 4 pool5_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_4 _ hm
  · exact checked4_14 _ hm
private def chunk5_20 : List (List T) := [[wire31,wire33825,wire69696,wire136164,wire270600,wire541200],
  [wire31,wire33825,wire71746,wire136164,wire811800,wire1015808],
  [wire31,wire33825,wire97346,wire136164,wire811800,wire1015808],
  [wire31,wire33825,wire97346,wire136164,wire811800,wire1016800]]
private def pool5_20 : List (List (List T)) := [chunk4_1, chunk4_4, chunk4_13]
private theorem checked5_20 : ∀ w ∈ chunk5_20, ¬ Need 5 w.toFinset := by
  have h : chunk5_20.all (routes 4 pool5_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_4 _ hm
  · exact checked4_13 _ hm
private def chunk5_21 : List (List T) := [[wire31,wire33825,wire97346,wire136164,wire811800,wire1016865],
  [wire31,wire33825,wire97346,wire136164,wire811800,wire1020036],
  [wire31,wire33825,wire97346,wire136164,wire811800,wire1020900],
  [wire31,wire33825,wire97346,wire136164,wire818968,wire1015808]]
private def pool5_21 : List (List (List T)) := [chunk4_1, chunk4_4, chunk4_14]
private theorem checked5_21 : ∀ w ∈ chunk5_21, ¬ Need 5 w.toFinset := by
  have h : chunk5_21.all (routes 4 pool5_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_4 _ hm
  · exact checked4_14 _ hm
private def chunk5_22 : List (List T) := [[wire31,wire33825,wire97346,wire136164,wire845625,wire1015808],
  [wire31,wire33825,wire97346,wire169957,wire811800,wire1015808],
  [wire31,wire33825,wire97346,wire201700,wire270600,wire541200],
  [wire31,wire33825,wire97375,wire136164,wire811800,wire1015808]]
private def pool5_22 : List (List (List T)) := [chunk4_1, chunk4_3, chunk4_5, chunk4_14]
private theorem checked5_22 : ∀ w ∈ chunk5_22, ¬ Need 5 w.toFinset := by
  have h : chunk5_22.all (routes 4 pool5_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_3 _ hm
  · exact checked4_5 _ hm
  · exact checked4_14 _ hm
private def chunk5_23 : List (List T) := [[wire31,wire33825,wire101475,wire136164,wire818968,wire1015808],
  [wire31,wire33825,wire130147,wire136164,wire811800,wire1015808],
  [wire31,wire34785,wire64545,wire67650,wire135300,wire1041176],
  [wire31,wire34785,wire64545,wire67650,wire811800,wire1020036]]
private def pool5_23 : List (List (List T)) := [chunk4_2, chunk4_4, chunk4_5, chunk4_15]
private theorem checked5_23 : ∀ w ∈ chunk5_23, ¬ Need 5 w.toFinset := by
  have h : chunk5_23.all (routes 4 pool5_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_15 _ hm
private def chunk5_24 : List (List T) := [[wire31,wire34785,wire67650,wire135300,wire294152,wire1033777],
  [wire31,wire34785,wire67650,wire135300,wire326953,wire1032720],
  [wire31,wire34785,wire67650,wire135300,wire556560,wire1025321],
  [wire31,wire34785,wire67650,wire135300,wire589361,wire1024264]]
private def pool5_24 : List (List (List T)) := []
private theorem checked5_24 : ∀ w ∈ chunk5_24, ¬ Need 5 w.toFinset := by
  have h : chunk5_24.all (routes 4 pool5_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_24] at hv
private def chunk5_25 : List (List T) := [[wire31,wire34785,wire67650,wire135300,wire818968,wire1016865],
  [wire31,wire34785,wire67650,wire135300,wire851769,wire1015808],
  [wire31,wire34785,wire97346,wire135300,wire811800,wire1016865],
  [wire31,wire34785,wire97346,wire135300,wire845625,wire1015808]]
private def pool5_25 : List (List (List T)) := [chunk4_2, chunk4_3]
private theorem checked5_25 : ∀ w ∈ chunk5_25, ¬ Need 5 w.toFinset := by
  have h : chunk5_25.all (routes 4 pool5_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
private def chunk5_26 : List (List T) := [[wire31,wire34785,wire97346,wire270600,wire575025,wire1020036],
  [wire31,wire34785,wire97346,wire304425,wire541200,wire1020036],
  [wire31,wire34785,wire101475,wire135300,wire294152,wire1032720],
  [wire31,wire34785,wire101475,wire135300,wire556560,wire1024264]]
private def pool5_26 : List (List (List T)) := [chunk4_2]
private theorem checked5_26 : ∀ w ∈ chunk5_26, ¬ Need 5 w.toFinset := by
  have h : chunk5_26.all (routes 4 pool5_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_2 _ hm
private def chunk5_27 : List (List T) := [[wire31,wire34785,wire101475,wire135300,wire818968,wire1015808],
  [wire31,wire34785,wire130147,wire135300,wire811800,wire1015808],
  [wire31,wire34785,wire130147,wire270600,wire541200,wire1020036],
  [wire31,wire37921,wire67650,wire136164,wire811800,wire1015808]]
private def pool5_27 : List (List (List T)) := [chunk4_2, chunk4_4, chunk4_5, chunk4_15]
private theorem checked5_27 : ∀ w ∈ chunk5_27, ¬ Need 5 w.toFinset := by
  have h : chunk5_27.all (routes 4 pool5_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_15 _ hm
private def chunk5_28 : List (List T) := [[wire31,wire64545,wire67650,wire136164,wire811800,wire1016865],
  [wire31,wire64545,wire67650,wire169957,wire811800,wire1015808],
  [wire31,wire67650,wire99361,wire136164,wire270600,wire556560],
  [wire31,wire67650,wire99361,wire136164,wire294152,wire541200]]
private def pool5_28 : List (List (List T)) := [chunk4_2, chunk4_4, chunk4_5, chunk4_15, chunk4_16]
private theorem checked5_28 : ∀ w ∈ chunk5_28, ¬ Need 5 w.toFinset := by
  have h : chunk5_28.all (routes 4 pool5_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
private def chunk5_29 : List (List T) := [[wire31,wire67650,wire169957,wire270600,wire589361,wire1015808],
  [wire31,wire67650,wire169957,wire294152,wire575025,wire1015808],
  [wire31,wire67650,wire169957,wire304425,wire556560,wire1015808],
  [wire31,wire67650,wire169957,wire326953,wire541200,wire1015808]]
private def pool5_29 : List (List (List T)) := [chunk4_2]
private theorem checked5_29 : ∀ w ∈ chunk5_29, ¬ Need 5 w.toFinset := by
  have h : chunk5_29.all (routes 4 pool5_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_2 _ hm
private def chunk5_30 : List (List T) := [[wire31,wire97346,wire99361,wire136164,wire270600,wire541200],
  [wire31,wire97346,wire136164,wire304425,wire575025,wire1015808],
  [wire31,wire97346,wire169957,wire270600,wire575025,wire1015808],
  [wire31,wire97346,wire169957,wire304425,wire541200,wire1015808]]
private def pool5_30 : List (List (List T)) := [chunk4_3]
private theorem checked5_30 : ∀ w ∈ chunk5_30, ¬ Need 5 w.toFinset := by
  have h : chunk5_30.all (routes 4 pool5_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_3 _ hm
private def chunk5_31 : List (List T) := [[wire31,wire101475,wire136164,wire270600,wire556560,wire1016865],
  [wire31,wire101475,wire136164,wire294152,wire541200,wire1016865],
  [wire31,wire101475,wire136164,wire294152,wire575025,wire1015808],
  [wire31,wire101475,wire136164,wire304425,wire556560,wire1015808]]
private def pool5_31 : List (List (List T)) := [chunk4_4]
private theorem checked5_31 : ∀ w ∈ chunk5_31, ¬ Need 5 w.toFinset := by
  have h : chunk5_31.all (routes 4 pool5_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_4 _ hm
private def chunk5_32 : List (List T) := [[wire31,wire101475,wire169957,wire270600,wire556560,wire1015808],
  [wire31,wire101475,wire169957,wire294152,wire541200,wire1015808],
  [wire31,wire130147,wire136164,wire270600,wire541200,wire1016865],
  [wire31,wire130147,wire169957,wire270600,wire541200,wire1015808]]
private def pool5_32 : List (List (List T)) := [chunk4_4, chunk4_5]
private theorem checked5_32 : ∀ w ∈ chunk5_32, ¬ Need 5 w.toFinset := by
  have h : chunk5_32.all (routes 4 pool5_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
private def chunk5_33 : List (List T) := [[wire992,wire4096,wire33825,wire67679,wire135300,wire1041176],
  [wire992,wire4096,wire33825,wire67679,wire811800,wire1020036],
  [wire992,wire4100,wire33825,wire67679,wire270600,wire1032720],
  [wire992,wire4100,wire33825,wire67679,wire541200,wire1024264]]
private def pool5_33 : List (List (List T)) := [chunk4_5, chunk4_6, chunk4_7, chunk4_8]
private theorem checked5_33 : ∀ w ∈ chunk5_33, ¬ Need 5 w.toFinset := by
  have h : chunk5_33.all (routes 4 pool5_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
private def chunk5_34 : List (List T) := [[wire992,wire4100,wire33825,wire67679,wire811800,wire1015808],
  [wire992,wire4127,wire33825,wire67650,wire135300,wire1041176],
  [wire992,wire4127,wire33825,wire67650,wire811800,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire877336]]
private def pool5_34 : List (List (List T)) := [chunk4_5, chunk4_6, chunk4_7, chunk4_8, chunk4_9]
private theorem checked5_34 : ∀ w ∈ chunk5_34, ¬ Need 5 w.toFinset := by
  have h : chunk5_34.all (routes 4 pool5_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
private def chunk5_35 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire1041176],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire1042233],
  [wire992,wire31744,wire33825,wire67679,wire136164,wire1041176],
  [wire992,wire31744,wire33825,wire67679,wire169125,wire1041176]]
private def pool5_35 : List (List (List T)) := [chunk4_5, chunk4_9, chunk4_10]
private theorem checked5_35 : ∀ w ∈ chunk5_35, ¬ Need 5 w.toFinset := by
  have h : chunk5_35.all (routes 4 pool5_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
private def chunk5_36 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire200836,wire811800],
  [wire992,wire31744,wire33825,wire67679,wire811800,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire811800,wire1020900],
  [wire992,wire31744,wire33825,wire67679,wire811800,wire1021093]]
private def pool5_36 : List (List (List T)) := [chunk4_6, chunk4_9, chunk4_10]
private theorem checked5_36 : ∀ w ∈ chunk5_36, ¬ Need 5 w.toFinset := by
  have h : chunk5_36.all (routes 4 pool5_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_36,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
private def chunk5_37 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire845625,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire1020036,wire1041176],
  [wire992,wire31744,wire33825,wire101503,wire135300,wire1041176],
  [wire992,wire31744,wire33825,wire101503,wire811800,wire1020036]]
private def pool5_37 : List (List (List T)) := [chunk4_5, chunk4_6, chunk4_10, chunk4_11]
private theorem checked5_37 : ∀ w ∈ chunk5_37, ¬ Need 5 w.toFinset := by
  have h : chunk5_37.all (routes 4 pool5_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
private def chunk5_38 : List (List T) := [[wire992,wire31744,wire33855,wire67650,wire135300,wire1042233],
  [wire992,wire31744,wire33855,wire67650,wire169125,wire1041176],
  [wire992,wire31744,wire33855,wire67650,wire811800,wire1021093],
  [wire992,wire31744,wire33855,wire67650,wire845625,wire1020036]]
private def pool5_38 : List (List (List T)) := [chunk4_5, chunk4_6, chunk4_7]
private theorem checked5_38 : ∀ w ∈ chunk5_38, ¬ Need 5 w.toFinset := by
  have h : chunk5_38.all (routes 4 pool5_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_38,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
private def chunk5_39 : List (List T) := [[wire992,wire31744,wire67679,wire99361,wire135300,wire811800],
  [wire992,wire31744,wire67679,wire169125,wire304425,wire1032720],
  [wire992,wire31744,wire67679,wire169125,wire575025,wire1024264],
  [wire992,wire31744,wire67679,wire169125,wire845625,wire1015808]]
private def pool5_39 : List (List (List T)) := [chunk4_11]
private theorem checked5_39 : ∀ w ∈ chunk5_39, ¬ Need 5 w.toFinset := by
  have h : chunk5_39.all (routes 4 pool5_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_11 _ hm
private def chunk5_40 : List (List T) := [[wire992,wire31744,wire67679,wire304425,wire575025,wire1020036],
  [wire992,wire31744,wire101503,wire135300,wire270600,wire1033777],
  [wire992,wire31744,wire101503,wire135300,wire304425,wire1032720],
  [wire992,wire31744,wire101503,wire135300,wire541200,wire1025321]]
private def pool5_40 : List (List (List T)) := [chunk4_5]
private theorem checked5_40 : ∀ w ∈ chunk5_40, ¬ Need 5 w.toFinset := by
  have h : chunk5_40.all (routes 4 pool5_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_40,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_5 _ hm
private def chunk5_41 : List (List T) := [[wire992,wire31744,wire101503,wire135300,wire575025,wire1024264],
  [wire992,wire31744,wire101503,wire135300,wire811800,wire1016865],
  [wire992,wire31744,wire101503,wire135300,wire845625,wire1015808],
  [wire992,wire31744,wire101503,wire169125,wire270600,wire1032720]]
private def pool5_41 : List (List (List T)) := [chunk4_5, chunk4_6, chunk4_11, chunk4_12]
private theorem checked5_41 : ∀ w ∈ chunk5_41, ¬ Need 5 w.toFinset := by
  have h : chunk5_41.all (routes 4 pool5_41.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_41,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
private def chunk5_42 : List (List T) := [[wire992,wire31744,wire101503,wire169125,wire541200,wire1024264],
  [wire992,wire31744,wire101503,wire169125,wire811800,wire1015808],
  [wire992,wire31744,wire101503,wire270600,wire541200,wire1021093],
  [wire992,wire31744,wire101503,wire270600,wire575025,wire1020036]]
private def pool5_42 : List (List (List T)) := [chunk4_5, chunk4_6, chunk4_12]
private theorem checked5_42 : ∀ w ∈ chunk5_42, ¬ Need 5 w.toFinset := by
  have h : chunk5_42.all (routes 4 pool5_42.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_42,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_12 _ hm
private def chunk5_43 : List (List T) := [[wire992,wire31744,wire101503,wire304425,wire541200,wire1020036],
  [wire992,wire31775,wire33825,wire67679,wire135300,wire1041176],
  [wire992,wire31775,wire33825,wire67679,wire811800,wire1020036],
  [wire992,wire33825,wire33855,wire97346,wire811800,wire1020036]]
private def pool5_43 : List (List (List T)) := [chunk4_5, chunk4_6, chunk4_7, chunk4_13]
private theorem checked5_43 : ∀ w ∈ chunk5_43, ¬ Need 5 w.toFinset := by
  have h : chunk5_43.all (routes 4 pool5_43.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_43,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_13 _ hm
private def chunk5_44 : List (List T) := [[wire992,wire33825,wire64545,wire67679,wire135300,wire1041176],
  [wire992,wire33825,wire64545,wire67679,wire811800,wire1020036],
  [wire992,wire33825,wire67679,wire69636,wire270600,wire541200],
  [wire992,wire33825,wire67679,wire97346,wire135300,wire1041176]]
private def pool5_44 : List (List (List T)) := [chunk4_6, chunk4_9, chunk4_15]
private theorem checked5_44 : ∀ w ∈ chunk5_44, ¬ Need 5 w.toFinset := by
  have h : chunk5_44.all (routes 4 pool5_44.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_44,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_9 _ hm
  · exact checked4_15 _ hm
private def chunk5_45 : List (List T) := [[wire992,wire33825,wire67679,wire97346,wire811800,wire1020036],
  [wire992,wire33825,wire67679,wire97375,wire135300,wire1041176],
  [wire992,wire33825,wire67679,wire97375,wire811800,wire1020036],
  [wire992,wire33825,wire67679,wire135300,wire274696,wire1032720]]
private def pool5_45 : List (List (List T)) := [chunk4_5, chunk4_6]
private theorem checked5_45 : ∀ w ∈ chunk5_45, ¬ Need 5 w.toFinset := by
  have h : chunk5_45.all (routes 4 pool5_45.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_45,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
private def chunk5_46 : List (List T) := [[wire992,wire33825,wire67679,wire135300,wire294152,wire1041176],
  [wire992,wire33825,wire67679,wire135300,wire545296,wire1024264],
  [wire992,wire33825,wire67679,wire135300,wire556560,wire1041176],
  [wire992,wire33825,wire67679,wire135300,wire815896,wire1015808]]
private def pool5_46 : List (List (List T)) := [chunk4_12]
private theorem checked5_46 : ∀ w ∈ chunk5_46, ¬ Need 5 w.toFinset := by
  have h : chunk5_46.all (routes 4 pool5_46.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_46,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_12 _ hm
private def chunk5_47 : List (List T) := [[wire992,wire33825,wire67679,wire135300,wire818968,wire1041176],
  [wire992,wire33825,wire71775,wire135300,wire270600,wire1032720],
  [wire992,wire33825,wire71775,wire135300,wire541200,wire1024264],
  [wire992,wire33825,wire71775,wire135300,wire811800,wire1015808]]
private def pool5_47 : List (List (List T)) := [chunk4_6, chunk4_7, chunk4_12, chunk4_13]
private theorem checked5_47 : ∀ w ∈ chunk5_47, ¬ Need 5 w.toFinset := by
  have h : chunk5_47.all (routes 4 pool5_47.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_47,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
private def chunk5_48 : List (List T) := [[wire992,wire33825,wire71775,wire270600,wire541200,wire1020036],
  [wire992,wire33855,wire64545,wire67650,wire135300,wire1041176],
  [wire992,wire33855,wire64545,wire67650,wire811800,wire1020036],
  [wire992,wire33855,wire67650,wire135300,wire294152,wire1033777]]
private def pool5_48 : List (List (List T)) := [chunk4_7]
private theorem checked5_48 : ∀ w ∈ chunk5_48, ¬ Need 5 w.toFinset := by
  have h : chunk5_48.all (routes 4 pool5_48.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_48,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_7 _ hm
private def chunk5_49 : List (List T) := [[wire992,wire33855,wire67650,wire135300,wire326953,wire1032720],
  [wire992,wire33855,wire67650,wire135300,wire556560,wire1025321],
  [wire992,wire33855,wire67650,wire135300,wire589361,wire1024264],
  [wire992,wire33855,wire67650,wire135300,wire818968,wire1016865]]
private def pool5_49 : List (List (List T)) := [chunk4_13]
private theorem checked5_49 : ∀ w ∈ chunk5_49, ¬ Need 5 w.toFinset := by
  have h : chunk5_49.all (routes 4 pool5_49.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_49,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_13 _ hm
private def chunk5_50 : List (List T) := [[wire992,wire33855,wire67650,wire135300,wire851769,wire1015808],
  [wire992,wire33855,wire67650,wire169125,wire294152,wire1032720],
  [wire992,wire33855,wire67650,wire169125,wire556560,wire1024264],
  [wire992,wire33855,wire67650,wire169125,wire818968,wire1015808]]
private def pool5_50 : List (List (List T)) := [chunk4_13, chunk4_14]
private theorem checked5_50 : ∀ w ∈ chunk5_50, ¬ Need 5 w.toFinset := by
  have h : chunk5_50.all (routes 4 pool5_50.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_50,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_51 : List (List T) := [[wire992,wire33855,wire97346,wire135300,wire811800,wire1016865],
  [wire992,wire33855,wire97346,wire135300,wire845625,wire1015808],
  [wire992,wire33855,wire97346,wire169125,wire811800,wire1015808],
  [wire992,wire33855,wire97346,wire270600,wire541200,wire1021093]]
private def pool5_51 : List (List (List T)) := [chunk4_7, chunk4_14]
private theorem checked5_51 : ∀ w ∈ chunk5_51, ¬ Need 5 w.toFinset := by
  have h : chunk5_51.all (routes 4 pool5_51.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_51,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_14 _ hm
private def chunk5_52 : List (List T) := [[wire992,wire33855,wire97346,wire270600,wire575025,wire1020036],
  [wire992,wire33855,wire97346,wire304425,wire541200,wire1020036],
  [wire992,wire37921,wire67679,wire135300,wire270600,wire1032720],
  [wire992,wire37921,wire67679,wire135300,wire541200,wire1024264]]
private def pool5_52 : List (List (List T)) := [chunk4_7]
private theorem checked5_52 : ∀ w ∈ chunk5_52, ¬ Need 5 w.toFinset := by
  have h : chunk5_52.all (routes 4 pool5_52.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_52,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_7 _ hm
private def chunk5_53 : List (List T) := [[wire992,wire37921,wire67679,wire135300,wire811800,wire1015808],
  [wire992,wire37921,wire67679,wire270600,wire541200,wire1020036],
  [wire992,wire37925,wire67679,wire270600,wire541200,wire1015808],
  [wire992,wire64545,wire67679,wire135300,wire811800,wire1016865]]
private def pool5_53 : List (List (List T)) := [chunk4_7, chunk4_8, chunk4_9, chunk4_15]
private theorem checked5_53 : ∀ w ∈ chunk5_53, ¬ Need 5 w.toFinset := by
  have h : chunk5_53.all (routes 4 pool5_53.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_53,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_15 _ hm
private def chunk5_54 : List (List T) := [[wire992,wire64545,wire67679,wire169125,wire270600,wire1032720],
  [wire992,wire64545,wire67679,wire169125,wire541200,wire1024264],
  [wire992,wire64545,wire67679,wire169125,wire811800,wire1015808],
  [wire992,wire64545,wire67679,wire270600,wire541200,wire1021093]]
private def pool5_54 : List (List (List T)) := [chunk4_9, chunk4_16]
private theorem checked5_54 : ∀ w ∈ chunk5_54, ¬ Need 5 w.toFinset := by
  have h : chunk5_54.all (routes 4 pool5_54.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_54,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_16 _ hm
private def chunk5_55 : List (List T) := [[wire4096,wire33825,wire67679,wire136164,wire811800,wire1015808],
  [wire4127,wire33825,wire67650,wire136164,wire811800,wire1015808],
  [wire31744,wire33825,wire34785,wire67679,wire135300,wire1041176],
  [wire31744,wire33825,wire34785,wire67679,wire811800,wire1020036]]
private def pool5_55 : List (List (List T)) := [chunk4_10, chunk4_11, chunk4_12, chunk4_13, chunk4_15]
private theorem checked5_55 : ∀ w ∈ chunk5_55, ¬ Need 5 w.toFinset := by
  have h : chunk5_55.all (routes 4 pool5_55.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_55,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_15 _ hm
private def chunk5_56 : List (List T) := [[wire31744,wire33825,wire65536,wire67679,wire136164,wire811800],
  [wire31744,wire33825,wire66528,wire67679,wire135300,wire811800],
  [wire31744,wire33825,wire67679,wire136164,wire270600,wire606736],
  [wire31744,wire33825,wire67679,wire136164,wire336136,wire541200]]
private def pool5_56 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_11]
private theorem checked5_56 : ∀ w ∈ chunk5_56, ¬ Need 5 w.toFinset := by
  have h : chunk5_56.all (routes 4 pool5_56.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_56,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
private def chunk5_57 : List (List T) := [[wire31744,wire33825,wire67679,wire136164,wire811800,wire1015808],
  [wire31744,wire33825,wire67679,wire136164,wire811800,wire1016800],
  [wire31744,wire33825,wire67679,wire136164,wire811800,wire1016865],
  [wire31744,wire33825,wire67679,wire136164,wire811800,wire1020036]]
private def pool5_57 : List (List (List T)) := [chunk4_11, chunk4_15]
private theorem checked5_57 : ∀ w ∈ chunk5_57, ¬ Need 5 w.toFinset := by
  have h : chunk5_57.all (routes 4 pool5_57.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_57,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_15 _ hm
private def chunk5_58 : List (List T) := [[wire31744,wire33825,wire67679,wire136164,wire811800,wire1020900],
  [wire31744,wire33825,wire67679,wire136164,wire811800,wire1024264],
  [wire31744,wire33825,wire67679,wire136164,wire811800,wire1032720],
  [wire31744,wire33825,wire67679,wire136164,wire811800,wire1041176]]
private def pool5_58 : List (List (List T)) := [chunk4_12]
private theorem checked5_58 : ∀ w ∈ chunk5_58, ¬ Need 5 w.toFinset := by
  have h : chunk5_58.all (routes 4 pool5_58.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_58,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_12 _ hm
private def chunk5_59 : List (List T) := [[wire31744,wire33825,wire67679,wire136164,wire845625,wire1015808],
  [wire31744,wire33825,wire67679,wire169957,wire811800,wire1015808],
  [wire31744,wire33825,wire67679,wire201700,wire270600,wire541200],
  [wire31744,wire33825,wire101503,wire136164,wire811800,wire1015808]]
private def pool5_59 : List (List (List T)) := [chunk4_10, chunk4_11, chunk4_12, chunk4_16]
private theorem checked5_59 : ∀ w ∈ chunk5_59, ¬ Need 5 w.toFinset := by
  have h : chunk5_59.all (routes 4 pool5_59.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_59,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_16 _ hm
private def chunk5_60 : List (List T) := [[wire31744,wire33855,wire34785,wire67650,wire135300,wire1041176],
  [wire31744,wire33855,wire34785,wire67650,wire811800,wire1020036],
  [wire31744,wire33855,wire67650,wire136164,wire811800,wire1016865],
  [wire31744,wire33855,wire67650,wire136164,wire845625,wire1015808]]
private def pool5_60 : List (List (List T)) := [chunk4_10, chunk4_11, chunk4_12, chunk4_13, chunk4_14]
private theorem checked5_60 : ∀ w ∈ chunk5_60, ¬ Need 5 w.toFinset := by
  have h : chunk5_60.all (routes 4 pool5_60.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_60,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_61 : List (List T) := [[wire31744,wire33855,wire67650,wire169957,wire811800,wire1015808],
  [wire31744,wire34785,wire67679,wire135300,wire270600,wire1033777],
  [wire31744,wire34785,wire67679,wire135300,wire304425,wire1032720],
  [wire31744,wire34785,wire67679,wire135300,wire541200,wire1025321]]
private def pool5_61 : List (List (List T)) := [chunk4_10, chunk4_12, chunk4_14]
private theorem checked5_61 : ∀ w ∈ chunk5_61, ¬ Need 5 w.toFinset := by
  have h : chunk5_61.all (routes 4 pool5_61.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_61,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
  · exact checked4_14 _ hm
private def chunk5_62 : List (List T) := [[wire31744,wire34785,wire67679,wire135300,wire575025,wire1024264],
  [wire31744,wire34785,wire67679,wire135300,wire811800,wire1016865],
  [wire31744,wire34785,wire67679,wire135300,wire845625,wire1015808],
  [wire31744,wire34785,wire67679,wire270600,wire575025,wire1020036]]
private def pool5_62 : List (List (List T)) := [chunk4_10, chunk4_11]
private theorem checked5_62 : ∀ w ∈ chunk5_62, ¬ Need 5 w.toFinset := by
  have h : chunk5_62.all (routes 4 pool5_62.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_62,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
private def chunk5_63 : List (List T) := [[wire31744,wire34785,wire67679,wire304425,wire541200,wire1020036],
  [wire31744,wire34785,wire101503,wire135300,wire270600,wire1032720],
  [wire31744,wire34785,wire101503,wire135300,wire541200,wire1024264],
  [wire31744,wire34785,wire101503,wire135300,wire811800,wire1015808]]
private def pool5_63 : List (List (List T)) := [chunk4_10, chunk4_11, chunk4_12]
private theorem checked5_63 : ∀ w ∈ chunk5_63, ¬ Need 5 w.toFinset := by
  have h : chunk5_63.all (routes 4 pool5_63.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_63,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
private def chunk5_64 : List (List T) := [[wire31744,wire34785,wire101503,wire270600,wire541200,wire1020036],
  [wire31744,wire67679,wire99361,wire136164,wire270600,wire541200],
  [wire31744,wire67679,wire136164,wire304425,wire575025,wire1015808],
  [wire31744,wire67679,wire169957,wire270600,wire575025,wire1015808]]
private def pool5_64 : List (List (List T)) := [chunk4_11]
private theorem checked5_64 : ∀ w ∈ chunk5_64, ¬ Need 5 w.toFinset := by
  have h : chunk5_64.all (routes 4 pool5_64.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_64,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_11 _ hm
private def chunk5_65 : List (List T) := [[wire31744,wire67679,wire169957,wire304425,wire541200,wire1015808],
  [wire31744,wire101503,wire136164,wire270600,wire541200,wire1016865],
  [wire31744,wire101503,wire136164,wire270600,wire575025,wire1015808],
  [wire31744,wire101503,wire136164,wire304425,wire541200,wire1015808]]
private def pool5_65 : List (List (List T)) := [chunk4_11, chunk4_12]
private theorem checked5_65 : ∀ w ∈ chunk5_65, ¬ Need 5 w.toFinset := by
  have h : chunk5_65.all (routes 4 pool5_65.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_65,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
private def chunk5_66 : List (List T) := [[wire31744,wire101503,wire169957,wire270600,wire541200,wire1015808],
  [wire31775,wire33825,wire67679,wire136164,wire811800,wire1015808],
  [wire33825,wire33855,wire67650,wire136164,wire818968,wire1015808],
  [wire33825,wire33855,wire97346,wire136164,wire811800,wire1015808]]
private def pool5_66 : List (List (List T)) := [chunk4_12, chunk4_13, chunk4_14]
private theorem checked5_66 : ∀ w ∈ chunk5_66, ¬ Need 5 w.toFinset := by
  have h : chunk5_66.all (routes 4 pool5_66.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_66,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_67 : List (List T) := [[wire33825,wire64545,wire67679,wire136164,wire811800,wire1015808],
  [wire33825,wire67679,wire97346,wire136164,wire811800,wire1015808],
  [wire33825,wire67679,wire97375,wire136164,wire811800,wire1015808],
  [wire33825,wire67679,wire136164,wire270600,wire545296,wire1015808]]
private def pool5_67 : List (List (List T)) := [chunk4_12, chunk4_15, chunk4_16]
private theorem checked5_67 : ∀ w ∈ chunk5_67, ¬ Need 5 w.toFinset := by
  have h : chunk5_67.all (routes 4 pool5_67.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_67,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_12 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
private def chunk5_68 : List (List T) := [[wire33825,wire67679,wire136164,wire270600,wire556560,wire1032720],
  [wire33825,wire67679,wire136164,wire274696,wire541200,wire1015808],
  [wire33825,wire67679,wire136164,wire294152,wire541200,wire1024264],
  [wire33825,wire67679,wire136164,wire294152,wire811800,wire1015808]]
private def pool5_68 : List (List (List T)) := [chunk4_12]
private theorem checked5_68 : ∀ w ∈ chunk5_68, ¬ Need 5 w.toFinset := by
  have h : chunk5_68.all (routes 4 pool5_68.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_68,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_12 _ hm
private def chunk5_69 : List (List T) := [[wire33825,wire67679,wire136164,wire556560,wire811800,wire1015808],
  [wire33825,wire67679,wire136164,wire811800,wire818968,wire1015808],
  [wire33825,wire71775,wire136164,wire270600,wire541200,wire1015808],
  [wire33855,wire34785,wire67650,wire135300,wire294152,wire1032720]]
private def pool5_69 : List (List (List T)) := [chunk4_12, chunk4_13]
private theorem checked5_69 : ∀ w ∈ chunk5_69, ¬ Need 5 w.toFinset := by
  have h : chunk5_69.all (routes 4 pool5_69.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_69,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
private def chunk5_70 : List (List T) := [[wire33855,wire34785,wire67650,wire135300,wire556560,wire1024264],
  [wire33855,wire34785,wire67650,wire135300,wire818968,wire1015808],
  [wire33855,wire34785,wire97346,wire135300,wire811800,wire1015808],
  [wire33855,wire34785,wire97346,wire270600,wire541200,wire1020036]]
private def pool5_70 : List (List (List T)) := [chunk4_13, chunk4_14]
private theorem checked5_70 : ∀ w ∈ chunk5_70, ¬ Need 5 w.toFinset := by
  have h : chunk5_70.all (routes 4 pool5_70.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_70,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_71 : List (List T) := [[wire33855,wire64545,wire67650,wire136164,wire811800,wire1015808],
  [wire33855,wire67650,wire136164,wire270600,wire556560,wire1016865],
  [wire33855,wire67650,wire136164,wire270600,wire589361,wire1015808],
  [wire33855,wire67650,wire136164,wire294152,wire541200,wire1016865]]
private def pool5_71 : List (List (List T)) := [chunk4_13]
private theorem checked5_71 : ∀ w ∈ chunk5_71, ¬ Need 5 w.toFinset := by
  have h : chunk5_71.all (routes 4 pool5_71.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_71,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_13 _ hm
private def chunk5_72 : List (List T) := [[wire33855,wire67650,wire136164,wire294152,wire575025,wire1015808],
  [wire33855,wire67650,wire136164,wire304425,wire556560,wire1015808],
  [wire33855,wire67650,wire136164,wire326953,wire541200,wire1015808],
  [wire33855,wire67650,wire169957,wire270600,wire556560,wire1015808]]
private def pool5_72 : List (List (List T)) := [chunk4_13, chunk4_14]
private theorem checked5_72 : ∀ w ∈ chunk5_72, ¬ Need 5 w.toFinset := by
  have h : chunk5_72.all (routes 4 pool5_72.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_72,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_73 : List (List T) := [[wire33855,wire67650,wire169957,wire294152,wire541200,wire1015808],
  [wire33855,wire97346,wire136164,wire270600,wire541200,wire1016865],
  [wire33855,wire97346,wire136164,wire270600,wire575025,wire1015808],
  [wire33855,wire97346,wire136164,wire304425,wire541200,wire1015808]]
private def pool5_73 : List (List (List T)) := [chunk4_14]
private theorem checked5_73 : ∀ w ∈ chunk5_73, ¬ Need 5 w.toFinset := by
  have h : chunk5_73.all (routes 4 pool5_73.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_73,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_14 _ hm
private def chunk5_74 : List (List T) := [[wire33855,wire97346,wire169957,wire270600,wire541200,wire1015808],
  [wire34785,wire64545,wire67679,wire135300,wire270600,wire1032720],
  [wire34785,wire64545,wire67679,wire135300,wire541200,wire1024264],
  [wire34785,wire64545,wire67679,wire135300,wire811800,wire1015808]]
private def pool5_74 : List (List (List T)) := [chunk4_14, chunk4_15, chunk4_16]
private theorem checked5_74 : ∀ w ∈ chunk5_74, ¬ Need 5 w.toFinset := by
  have h : chunk5_74.all (routes 4 pool5_74.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_74,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
private def chunk5_75 : List (List T) := [[wire34785,wire64545,wire67679,wire270600,wire541200,wire1020036],
  [wire37921,wire67679,wire136164,wire270600,wire541200,wire1015808],
  [wire64545,wire67679,wire136164,wire270600,wire541200,wire1016865],
  [wire64545,wire67679,wire169957,wire270600,wire541200,wire1015808]]
private def pool5_75 : List (List (List T)) := [chunk4_15, chunk4_16]
private theorem checked5_75 : ∀ w ∈ chunk5_75, ¬ Need 5 w.toFinset := by
  have h : chunk5_75.all (routes 4 pool5_75.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_75,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
#print axioms checked5_75
private def chunk6_0 : List (List T) := [[wire31,wire992,wire4096,wire33825,wire67650,wire135300,wire1041176],
  [wire31,wire992,wire4096,wire33825,wire67650,wire811800,wire1020036],
  [wire31,wire992,wire4100,wire33825,wire67650,wire270600,wire1032720],
  [wire31,wire992,wire4100,wire33825,wire67650,wire541200,wire1024264]]
private def pool6_0 : List (List (List T)) := [chunk5_0, chunk5_2, chunk5_4, chunk5_5, chunk5_33, chunk5_34]
private theorem checked6_0 : ∀ w ∈ chunk6_0, ¬ Need 6 w.toFinset := by
  have h : chunk6_0.all (routes 5 pool6_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_2 _ hm
  · exact checked5_4 _ hm
  · exact checked5_5 _ hm
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
private def chunk6_1 : List (List T) := [[wire31,wire992,wire4100,wire33825,wire67650,wire811800,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire65600,wire135300,wire811800],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire877336],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire1041176]]
private def pool6_1 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_5, chunk5_11, chunk5_34, chunk5_35]
private theorem checked6_1 : ∀ w ∈ chunk6_1, ¬ Need 6 w.toFinset := by
  have h : chunk6_1.all (routes 5 pool6_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_5 _ hm
  · exact checked5_11 _ hm
  · exact checked5_34 _ hm
  · exact checked5_35 _ hm
private def chunk6_2 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire1042233],
  [wire31,wire992,wire31744,wire33825,wire67650,wire136164,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67650,wire169125,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67650,wire200836,wire811800]]
private def pool6_2 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_2, chunk5_6, chunk5_11, chunk5_35, chunk5_36, chunk5_38]
private theorem checked6_2 : ∀ w ∈ chunk6_2, ¬ Need 6 w.toFinset := by
  have h : chunk6_2.all (routes 5 pool6_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_6 _ hm
  · exact checked5_11 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_38 _ hm
private def chunk6_3 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire811800,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire811800,wire1020900],
  [wire31,wire992,wire31744,wire33825,wire67650,wire811800,wire1021093],
  [wire31,wire992,wire31744,wire33825,wire67650,wire818968,wire1020036]]
private def pool6_3 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_3, chunk5_6, chunk5_36, chunk5_38]
private theorem checked6_3 : ∀ w ∈ chunk6_3, ¬ Need 6 w.toFinset := by
  have h : chunk6_3.all (routes 5 pool6_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_6 _ hm
  · exact checked5_36 _ hm
  · exact checked5_38 _ hm
private def chunk6_4 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire845625,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire1020036,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67679,wire135300,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67679,wire811800,wire1020036]]
private def pool6_4 : List (List (List T)) := [chunk5_1, chunk5_3, chunk5_4, chunk5_12, chunk5_35, chunk5_36, chunk5_37, chunk5_38, chunk5_43]
private theorem checked6_4 : ∀ w ∈ chunk6_4, ¬ Need 6 w.toFinset := by
  have h : chunk6_4.all (routes 5 pool6_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_12 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_38 _ hm
  · exact checked5_43 _ hm
private def chunk6_5 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire97346,wire811800,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire101475,wire135300,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire101475,wire811800,wire1020036],
  [wire31,wire992,wire31744,wire67650,wire99361,wire135300,wire811800]]
private def pool6_5 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_2, chunk5_3, chunk5_4, chunk5_6, chunk5_7, chunk5_12, chunk5_37, chunk5_39]
private theorem checked6_5 : ∀ w ∈ chunk6_5, ¬ Need 6 w.toFinset := by
  have h : chunk6_5.all (routes 5 pool6_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_12 _ hm
  · exact checked5_37 _ hm
  · exact checked5_39 _ hm
private def chunk6_6 : List (List T) := [[wire31,wire992,wire31744,wire67650,wire169125,wire304425,wire1032720],
  [wire31,wire992,wire31744,wire67650,wire169125,wire575025,wire1024264],
  [wire31,wire992,wire31744,wire67650,wire169125,wire845625,wire1015808],
  [wire31,wire992,wire31744,wire67650,wire304425,wire575025,wire1020036]]
private def pool6_6 : List (List (List T)) := [chunk5_6, chunk5_7, chunk5_8, chunk5_13, chunk5_39, chunk5_40]
private theorem checked6_6 : ∀ w ∈ chunk6_6, ¬ Need 6 w.toFinset := by
  have h : chunk6_6.all (routes 5 pool6_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_13 _ hm
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
private def chunk6_7 : List (List T) := [[wire31,wire992,wire31744,wire99425,wire135300,wire270600,wire541200],
  [wire31,wire992,wire31744,wire101475,wire135300,wire270600,wire1033777],
  [wire31,wire992,wire31744,wire101475,wire135300,wire304425,wire1032720],
  [wire31,wire992,wire31744,wire101475,wire135300,wire541200,wire1025321]]
private def pool6_7 : List (List (List T)) := [chunk5_0, chunk5_8, chunk5_9, chunk5_13, chunk5_40]
private theorem checked6_7 : ∀ w ∈ chunk6_7, ¬ Need 6 w.toFinset := by
  have h : chunk6_7.all (routes 5 pool6_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_13 _ hm
  · exact checked5_40 _ hm
private def chunk6_8 : List (List T) := [[wire31,wire992,wire31744,wire101475,wire135300,wire575025,wire1024264],
  [wire31,wire992,wire31744,wire101475,wire135300,wire811800,wire1016865],
  [wire31,wire992,wire31744,wire101475,wire135300,wire845625,wire1015808],
  [wire31,wire992,wire31744,wire101475,wire169125,wire270600,wire1032720]]
private def pool6_8 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_9, chunk5_10, chunk5_13, chunk5_41]
private theorem checked6_8 : ∀ w ∈ chunk6_8, ¬ Need 6 w.toFinset := by
  have h : chunk6_8.all (routes 5 pool6_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_13 _ hm
  · exact checked5_41 _ hm
private def chunk6_9 : List (List T) := [[wire31,wire992,wire31744,wire101475,wire169125,wire541200,wire1024264],
  [wire31,wire992,wire31744,wire101475,wire169125,wire811800,wire1015808],
  [wire31,wire992,wire31744,wire101475,wire270600,wire541200,wire1021093],
  [wire31,wire992,wire31744,wire101475,wire270600,wire575025,wire1020036]]
private def pool6_9 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_9, chunk5_10, chunk5_14, chunk5_42]
private theorem checked6_9 : ∀ w ∈ chunk6_9, ¬ Need 6 w.toFinset := by
  have h : chunk6_9.all (routes 5 pool6_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_14 _ hm
  · exact checked5_42 _ hm
private def chunk6_10 : List (List T) := [[wire31,wire992,wire31744,wire101475,wire304425,wire541200,wire1020036],
  [wire31,wire992,wire31775,wire33825,wire67650,wire135300,wire1041176],
  [wire31,wire992,wire31775,wire33825,wire67650,wire811800,wire1020036],
  [wire31,wire992,wire33825,wire64545,wire67650,wire135300,wire1041176]]
private def pool6_10 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_4, chunk5_6, chunk5_23, chunk5_43, chunk5_44, chunk5_48]
private theorem checked6_10 : ∀ w ∈ chunk6_10, ¬ Need 6 w.toFinset := by
  have h : chunk6_10.all (routes 5 pool6_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_4 _ hm
  · exact checked5_6 _ hm
  · exact checked5_23 _ hm
  · exact checked5_43 _ hm
  · exact checked5_44 _ hm
  · exact checked5_48 _ hm
private def chunk6_11 : List (List T) := [[wire31,wire992,wire33825,wire64545,wire67650,wire811800,wire1020036],
  [wire31,wire992,wire33825,wire65536,wire67650,wire135300,wire818968],
  [wire31,wire992,wire33825,wire65536,wire97346,wire135300,wire811800],
  [wire31,wire992,wire33825,wire65600,wire135300,wire270600,wire556560]]
private def pool6_11 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_4, chunk5_6, chunk5_7, chunk5_8, chunk5_14, chunk5_15, chunk5_23, chunk5_44, chunk5_48]
private theorem checked6_11 : ∀ w ∈ chunk6_11, ¬ Need 6 w.toFinset := by
  have h : chunk6_11.all (routes 5 pool6_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_4 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_23 _ hm
  · exact checked5_44 _ hm
  · exact checked5_48 _ hm
private def chunk6_12 : List (List T) := [[wire31,wire992,wire33825,wire65600,wire135300,wire294152,wire541200],
  [wire31,wire992,wire33825,wire67650,wire97346,wire135300,wire1041176],
  [wire31,wire992,wire33825,wire67650,wire97346,wire811800,wire1020036],
  [wire31,wire992,wire33825,wire67650,wire135300,wire274696,wire1032720]]
private def pool6_12 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_8, chunk5_15, chunk5_44, chunk5_45]
private theorem checked6_12 : ∀ w ∈ chunk6_12, ¬ Need 6 w.toFinset := by
  have h : chunk6_12.all (routes 5 pool6_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_8 _ hm
  · exact checked5_15 _ hm
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
private def chunk6_13 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire606736],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire1032720],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire1033777],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire1041176]]
private def pool6_13 : List (List (List T)) := [chunk5_8, chunk5_16, chunk5_24, chunk5_46, chunk5_48]
private theorem checked6_13 : ∀ w ∈ chunk6_13, ¬ Need 6 w.toFinset := by
  have h : chunk6_13.all (routes 5 pool6_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_16 _ hm
  · exact checked5_24 _ hm
  · exact checked5_46 _ hm
  · exact checked5_48 _ hm
private def chunk6_14 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire326953,wire1032720],
  [wire31,wire992,wire33825,wire67650,wire135300,wire336136,wire556560],
  [wire31,wire992,wire33825,wire67650,wire135300,wire545296,wire1024264],
  [wire31,wire992,wire33825,wire67650,wire135300,wire556560,wire1024264]]
private def pool6_14 : List (List (List T)) := [chunk5_6, chunk5_16, chunk5_24, chunk5_46, chunk5_49]
private theorem checked6_14 : ∀ w ∈ chunk6_14, ¬ Need 6 w.toFinset := by
  have h : chunk6_14.all (routes 5 pool6_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_16 _ hm
  · exact checked5_24 _ hm
  · exact checked5_46 _ hm
  · exact checked5_49 _ hm
private def chunk6_15 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire556560,wire1025321],
  [wire31,wire992,wire33825,wire67650,wire135300,wire556560,wire1041176],
  [wire31,wire992,wire33825,wire67650,wire135300,wire589361,wire1024264],
  [wire31,wire992,wire33825,wire67650,wire135300,wire815896,wire1015808]]
private def pool6_15 : List (List (List T)) := [chunk5_7, chunk5_9, chunk5_16, chunk5_24, chunk5_46, chunk5_49]
private theorem checked6_15 : ∀ w ∈ chunk6_15, ¬ Need 6 w.toFinset := by
  have h : chunk6_15.all (routes 5 pool6_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_7 _ hm
  · exact checked5_9 _ hm
  · exact checked5_16 _ hm
  · exact checked5_24 _ hm
  · exact checked5_46 _ hm
  · exact checked5_49 _ hm
private def chunk6_16 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire818968,wire1016800],
  [wire31,wire992,wire33825,wire67650,wire135300,wire818968,wire1016865],
  [wire31,wire992,wire33825,wire67650,wire135300,wire818968,wire1020036]]
private def pool6_16 : List (List (List T)) := [chunk5_1, chunk5_9, chunk5_16, chunk5_17, chunk5_25, chunk5_49]
private theorem checked6_16 : ∀ w ∈ chunk6_16, ¬ Need 6 w.toFinset := by
  have h : chunk6_16.all (routes 5 pool6_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_9 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_25 _ hm
  · exact checked5_49 _ hm
private def chunk6_17 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire818968,wire1024264],
  [wire31,wire992,wire33825,wire67650,wire135300,wire818968,wire1032720],
  [wire31,wire992,wire33825,wire67650,wire135300,wire818968,wire1041176],
  [wire31,wire992,wire33825,wire67650,wire135300,wire851769,wire1015808]]
private def pool6_17 : List (List (List T)) := [chunk5_7, chunk5_18, chunk5_25, chunk5_47, chunk5_50]
private theorem checked6_17 : ∀ w ∈ chunk6_17, ¬ Need 6 w.toFinset := by
  have h : chunk6_17.all (routes 5 pool6_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_7 _ hm
  · exact checked5_18 _ hm
  · exact checked5_25 _ hm
  · exact checked5_47 _ hm
  · exact checked5_50 _ hm
private def chunk6_18 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire136164,wire294152,wire1032720],
  [wire31,wire992,wire33825,wire67650,wire136164,wire556560,wire1024264],
  [wire31,wire992,wire33825,wire67650,wire136164,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire169125,wire294152,wire1032720]]
private def pool6_18 : List (List (List T)) := [chunk5_6, chunk5_9, chunk5_16, chunk5_17, chunk5_50]
private theorem checked6_18 : ∀ w ∈ chunk6_18, ¬ Need 6 w.toFinset := by
  have h : chunk6_18.all (routes 5 pool6_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_9 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_50 _ hm
private def chunk6_19 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire169125,wire556560,wire1024264],
  [wire31,wire992,wire33825,wire67650,wire169125,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire200836,wire270600,wire556560],
  [wire31,wire992,wire33825,wire67650,wire200836,wire294152,wire541200]]
private def pool6_19 : List (List (List T)) := [chunk5_1, chunk5_7, chunk5_9, chunk5_10, chunk5_19, chunk5_50]
private theorem checked6_19 : ∀ w ∈ chunk6_19, ¬ Need 6 w.toFinset := by
  have h : chunk6_19.all (routes 5 pool6_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_7 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_19 _ hm
  · exact checked5_50 _ hm
private def chunk6_20 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire294152,wire556560,wire1020036],
  [wire31,wire992,wire33825,wire67679,wire135300,wire294152,wire1032720],
  [wire31,wire992,wire33825,wire67679,wire135300,wire556560,wire1024264],
  [wire31,wire992,wire33825,wire67679,wire135300,wire818968,wire1015808]]
private def pool6_20 : List (List (List T)) := [chunk5_19]
private theorem checked6_20 : ∀ w ∈ chunk6_20, ¬ Need 6 w.toFinset := by
  have h : chunk6_20.all (routes 5 pool6_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_19 _ hm
private def chunk6_21 : List (List T) := [[wire31,wire992,wire33825,wire71746,wire135300,wire270600,wire1032720],
  [wire31,wire992,wire33825,wire71746,wire135300,wire541200,wire1024264],
  [wire31,wire992,wire33825,wire71746,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire71746,wire270600,wire541200,wire1020036]]
private def pool6_21 : List (List (List T)) := [chunk5_2, chunk5_20, chunk5_47, chunk5_48]
private theorem checked6_21 : ∀ w ∈ chunk6_21, ¬ Need 6 w.toFinset := by
  have h : chunk6_21.all (routes 5 pool6_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_20 _ hm
  · exact checked5_47 _ hm
  · exact checked5_48 _ hm
private def chunk6_22 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire811800,wire1016800],
  [wire31,wire992,wire33825,wire97346,wire135300,wire811800,wire1016865],
  [wire31,wire992,wire33825,wire97346,wire135300,wire811800,wire1020036]]
private def pool6_22 : List (List (List T)) := [chunk5_2, chunk5_3, chunk5_10, chunk5_20, chunk5_21, chunk5_25, chunk5_51]
private theorem checked6_22 : ∀ w ∈ chunk6_22, ¬ Need 6 w.toFinset := by
  have h : chunk6_22.all (routes 5 pool6_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_10 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_25 _ hm
  · exact checked5_51 _ hm
private def chunk6_23 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire135300,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire845625,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire1015808,wire1041176],
  [wire31,wire992,wire33825,wire97346,wire135300,wire1024264,wire1032720]]
private def pool6_23 : List (List (List T)) := [chunk5_3, chunk5_4, chunk5_7, chunk5_21, chunk5_22, chunk5_25, chunk5_51]
private theorem checked6_23 : ∀ w ∈ chunk6_23, ¬ Need 6 w.toFinset := by
  have h : chunk6_23.all (routes 5 pool6_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_7 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_25 _ hm
  · exact checked5_51 _ hm
private def chunk6_24 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire136164,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire169125,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire200836,wire270600,wire541200],
  [wire31,wire992,wire33825,wire97346,wire270600,wire541200,wire1020036]]
private def pool6_24 : List (List (List T)) := [chunk5_2, chunk5_3, chunk5_7, chunk5_10, chunk5_20, chunk5_22, chunk5_51]
private theorem checked6_24 : ∀ w ∈ chunk6_24, ¬ Need 6 w.toFinset := by
  have h : chunk6_24.all (routes 5 pool6_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_7 _ hm
  · exact checked5_10 _ hm
  · exact checked5_20 _ hm
  · exact checked5_22 _ hm
  · exact checked5_51 _ hm
private def chunk6_25 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire270600,wire541200,wire1020900],
  [wire31,wire992,wire33825,wire97346,wire270600,wire541200,wire1021093],
  [wire31,wire992,wire33825,wire97346,wire270600,wire556560,wire1020036],
  [wire31,wire992,wire33825,wire97346,wire270600,wire575025,wire1020036]]
private def pool6_25 : List (List (List T)) := [chunk5_3, chunk5_8, chunk5_10, chunk5_26, chunk5_51, chunk5_52]
private theorem checked6_25 : ∀ w ∈ chunk6_25, ¬ Need 6 w.toFinset := by
  have h : chunk6_25.all (routes 5 pool6_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_8 _ hm
  · exact checked5_10 _ hm
  · exact checked5_26 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
private def chunk6_26 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire270600,wire811800,wire1020036],
  [wire31,wire992,wire33825,wire97346,wire270600,wire1020036,wire1032720],
  [wire31,wire992,wire33825,wire97346,wire294152,wire541200,wire1020036],
  [wire31,wire992,wire33825,wire97346,wire304425,wire541200,wire1020036]]
private def pool6_26 : List (List (List T)) := [chunk5_2, chunk5_3, chunk5_4, chunk5_8, chunk5_26, chunk5_52]
private theorem checked6_26 : ∀ w ∈ chunk6_26, ¬ Need 6 w.toFinset := by
  have h : chunk6_26.all (routes 5 pool6_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_8 _ hm
  · exact checked5_26 _ hm
  · exact checked5_52 _ hm
private def chunk6_27 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire541200,wire811800,wire1020036],
  [wire31,wire992,wire33825,wire97346,wire541200,wire1020036,wire1024264],
  [wire31,wire992,wire33825,wire97346,wire811800,wire1015808,wire1020036],
  [wire31,wire992,wire33825,wire97346,wire811800,wire1020036]]
private def pool6_27 : List (List (List T)) := [chunk5_2, chunk5_3, chunk5_4, chunk5_14, chunk5_43]
private theorem checked6_27 : ∀ w ∈ chunk6_27, ¬ Need 6 w.toFinset := by
  have h : chunk6_27.all (routes 5 pool6_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_14 _ hm
  · exact checked5_43 _ hm
private def chunk6_28 : List (List T) := [[wire31,wire992,wire33825,wire97375,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire97375,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire33825,wire101475,wire135300,wire294152,wire1032720],
  [wire31,wire992,wire33825,wire101475,wire135300,wire556560,wire1024264]]
private def pool6_28 : List (List (List T)) := [chunk5_4, chunk5_8, chunk5_9, chunk5_22, chunk5_26]
private theorem checked6_28 : ∀ w ∈ chunk6_28, ¬ Need 6 w.toFinset := by
  have h : chunk6_28.all (routes 5 pool6_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_22 _ hm
  · exact checked5_26 _ hm
private def chunk6_29 : List (List T) := [[wire31,wire992,wire33825,wire101475,wire135300,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire130147,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire130147,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire37921,wire67650,wire135300,wire270600,wire1032720]]
private def pool6_29 : List (List (List T)) := [chunk5_4, chunk5_9, chunk5_10, chunk5_23, chunk5_27, chunk5_52]
private theorem checked6_29 : ∀ w ∈ chunk6_29, ¬ Need 6 w.toFinset := by
  have h : chunk6_29.all (routes 5 pool6_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_23 _ hm
  · exact checked5_27 _ hm
  · exact checked5_52 _ hm
private def chunk6_30 : List (List T) := [[wire31,wire992,wire37921,wire67650,wire135300,wire541200,wire1024264],
  [wire31,wire992,wire37921,wire67650,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire37921,wire67650,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire37925,wire67650,wire270600,wire541200,wire1015808]]
private def pool6_30 : List (List (List T)) := [chunk5_4, chunk5_5, chunk5_27, chunk5_52, chunk5_53]
private theorem checked6_30 : ∀ w ∈ chunk6_30, ¬ Need 6 w.toFinset := by
  have h : chunk6_30.all (routes 5 pool6_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_5 _ hm
  · exact checked5_27 _ hm
  · exact checked5_52 _ hm
  · exact checked5_53 _ hm
private def chunk6_31 : List (List T) := [[wire31,wire992,wire64545,wire67650,wire135300,wire811800,wire1016865],
  [wire31,wire992,wire64545,wire67650,wire169125,wire270600,wire1032720],
  [wire31,wire992,wire64545,wire67650,wire169125,wire541200,wire1024264],
  [wire31,wire992,wire64545,wire67650,wire169125,wire811800,wire1015808]]
private def pool6_31 : List (List (List T)) := [chunk5_6, chunk5_7, chunk5_10, chunk5_28, chunk5_53, chunk5_54]
private theorem checked6_31 : ∀ w ∈ chunk6_31, ¬ Need 6 w.toFinset := by
  have h : chunk6_31.all (routes 5 pool6_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_10 _ hm
  · exact checked5_28 _ hm
  · exact checked5_53 _ hm
  · exact checked5_54 _ hm
private def chunk6_32 : List (List T) := [[wire31,wire992,wire64545,wire67650,wire270600,wire541200,wire1021093],
  [wire31,wire992,wire67650,wire99361,wire135300,wire270600,wire556560],
  [wire31,wire992,wire67650,wire99361,wire135300,wire294152,wire541200],
  [wire31,wire992,wire67650,wire169125,wire270600,wire589361,wire1015808]]
private def pool6_32 : List (List (List T)) := [chunk5_6, chunk5_7, chunk5_10, chunk5_28, chunk5_29, chunk5_54]
private theorem checked6_32 : ∀ w ∈ chunk6_32, ¬ Need 6 w.toFinset := by
  have h : chunk6_32.all (routes 5 pool6_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_10 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_54 _ hm
private def chunk6_33 : List (List T) := [[wire31,wire992,wire67650,wire169125,wire294152,wire575025,wire1015808],
  [wire31,wire992,wire67650,wire169125,wire304425,wire556560,wire1015808],
  [wire31,wire992,wire67650,wire169125,wire326953,wire541200,wire1015808],
  [wire31,wire992,wire97346,wire99361,wire135300,wire270600,wire541200]]
private def pool6_33 : List (List (List T)) := [chunk5_6, chunk5_7, chunk5_29, chunk5_30]
private theorem checked6_33 : ∀ w ∈ chunk6_33, ¬ Need 6 w.toFinset := by
  have h : chunk6_33.all (routes 5 pool6_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
private def chunk6_34 : List (List T) := [[wire31,wire992,wire97346,wire135300,wire304425,wire575025,wire1015808],
  [wire31,wire992,wire97346,wire169125,wire270600,wire575025,wire1015808],
  [wire31,wire992,wire97346,wire169125,wire304425,wire541200,wire1015808],
  [wire31,wire992,wire101475,wire135300,wire270600,wire556560,wire1016865]]
private def pool6_34 : List (List (List T)) := [chunk5_7, chunk5_8, chunk5_9, chunk5_30, chunk5_31]
private theorem checked6_34 : ∀ w ∈ chunk6_34, ¬ Need 6 w.toFinset := by
  have h : chunk6_34.all (routes 5 pool6_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
private def chunk6_35 : List (List T) := [[wire31,wire992,wire101475,wire135300,wire294152,wire541200,wire1016865],
  [wire31,wire992,wire101475,wire135300,wire294152,wire575025,wire1015808],
  [wire31,wire992,wire101475,wire135300,wire304425,wire556560,wire1015808],
  [wire31,wire992,wire101475,wire169125,wire270600,wire556560,wire1015808]]
private def pool6_35 : List (List (List T)) := [chunk5_8, chunk5_9, chunk5_10, chunk5_31, chunk5_32]
private theorem checked6_35 : ∀ w ∈ chunk6_35, ¬ Need 6 w.toFinset := by
  have h : chunk6_35.all (routes 5 pool6_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
private def chunk6_36 : List (List T) := [[wire31,wire992,wire101475,wire169125,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire130147,wire135300,wire270600,wire541200,wire1016865],
  [wire31,wire992,wire130147,wire169125,wire270600,wire541200,wire1015808],
  [wire31,wire4096,wire33825,wire67650,wire136164,wire811800,wire1015808]]
private def pool6_36 : List (List (List T)) := [chunk5_9, chunk5_10, chunk5_16, chunk5_20, chunk5_27, chunk5_32, chunk5_55]
private theorem checked6_36 : ∀ w ∈ chunk6_36, ¬ Need 6 w.toFinset := by
  have h : chunk6_36.all (routes 5 pool6_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_36,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_16 _ hm
  · exact checked5_20 _ hm
  · exact checked5_27 _ hm
  · exact checked5_32 _ hm
  · exact checked5_55 _ hm
private def chunk6_37 : List (List T) := [[wire31,wire31744,wire33825,wire34785,wire67650,wire135300,wire1041176],
  [wire31,wire31744,wire33825,wire34785,wire67650,wire811800,wire1020036],
  [wire31,wire31744,wire33825,wire65536,wire67650,wire136164,wire811800],
  [wire31,wire31744,wire33825,wire65600,wire136164,wire270600,wire541200]]
private def pool6_37 : List (List (List T)) := [chunk5_11, chunk5_12, chunk5_13, chunk5_14, chunk5_15, chunk5_23, chunk5_55, chunk5_56, chunk5_60]
private theorem checked6_37 : ∀ w ∈ chunk6_37, ¬ Need 6 w.toFinset := by
  have h : chunk6_37.all (routes 5 pool6_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_23 _ hm
  · exact checked5_55 _ hm
  · exact checked5_56 _ hm
  · exact checked5_60 _ hm
private def chunk6_38 : List (List T) := [[wire31,wire31744,wire33825,wire66528,wire67650,wire135300,wire811800],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire606736],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire336136,wire541200],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire811800,wire1015808]]
private def pool6_38 : List (List (List T)) := [chunk5_11, chunk5_15, chunk5_16, chunk5_20, chunk5_56, chunk5_57]
private theorem checked6_38 : ∀ w ∈ chunk6_38, ¬ Need 6 w.toFinset := by
  have h : chunk6_38.all (routes 5 pool6_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_38,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_11 _ hm
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_20 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
private def chunk6_39 : List (List T) := [[wire31,wire31744,wire33825,wire67650,wire136164,wire811800,wire1016800],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire811800,wire1016865],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire811800,wire1020036],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire811800,wire1020900]]
private def pool6_39 : List (List (List T)) := [chunk5_11, chunk5_13, chunk5_17, chunk5_20, chunk5_21, chunk5_28, chunk5_57, chunk5_58, chunk5_60]
private theorem checked6_39 : ∀ w ∈ chunk6_39, ¬ Need 6 w.toFinset := by
  have h : chunk6_39.all (routes 5 pool6_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_11 _ hm
  · exact checked5_13 _ hm
  · exact checked5_17 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_28 _ hm
  · exact checked5_57 _ hm
  · exact checked5_58 _ hm
  · exact checked5_60 _ hm
private def chunk6_40 : List (List T) := [[wire31,wire31744,wire33825,wire67650,wire136164,wire811800,wire1024264],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire811800,wire1032720],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire811800,wire1041176],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire818968,wire1015808]]
private def pool6_40 : List (List (List T)) := [chunk5_16, chunk5_18, chunk5_21, chunk5_58]
private theorem checked6_40 : ∀ w ∈ chunk6_40, ¬ Need 6 w.toFinset := by
  have h : chunk6_40.all (routes 5 pool6_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_40,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_16 _ hm
  · exact checked5_18 _ hm
  · exact checked5_21 _ hm
  · exact checked5_58 _ hm
private def chunk6_41 : List (List T) := [[wire31,wire31744,wire33825,wire67650,wire136164,wire845625,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire169957,wire811800,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire201700,wire270600,wire541200],
  [wire31,wire31744,wire33825,wire67679,wire136164,wire811800,wire1015808]]
private def pool6_41 : List (List (List T)) := [chunk5_11, chunk5_13, chunk5_14, chunk5_18, chunk5_19, chunk5_22, chunk5_28, chunk5_57, chunk5_59, chunk5_60, chunk5_61, chunk5_66]
private theorem checked6_41 : ∀ w ∈ chunk6_41, ¬ Need 6 w.toFinset := by
  have h : chunk6_41.all (routes 5 pool6_41.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_41,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_11 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_22 _ hm
  · exact checked5_28 _ hm
  · exact checked5_57 _ hm
  · exact checked5_59 _ hm
  · exact checked5_60 _ hm
  · exact checked5_61 _ hm
  · exact checked5_66 _ hm
private def chunk6_42 : List (List T) := [[wire31,wire31744,wire33825,wire97346,wire136164,wire811800,wire1015808],
  [wire31,wire31744,wire33825,wire101475,wire136164,wire811800,wire1015808],
  [wire31,wire31744,wire34785,wire67650,wire135300,wire270600,wire1033777],
  [wire31,wire31744,wire34785,wire67650,wire135300,wire304425,wire1032720]]
private def pool6_42 : List (List (List T)) := [chunk5_11, chunk5_13, chunk5_14, chunk5_20, chunk5_21, chunk5_23, chunk5_24, chunk5_59, chunk5_61]
private theorem checked6_42 : ∀ w ∈ chunk6_42, ¬ Need 6 w.toFinset := by
  have h : chunk6_42.all (routes 5 pool6_42.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_42,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_11 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_59 _ hm
  · exact checked5_61 _ hm
private def chunk6_43 : List (List T) := [[wire31,wire31744,wire34785,wire67650,wire135300,wire541200,wire1025321],
  [wire31,wire31744,wire34785,wire67650,wire135300,wire575025,wire1024264],
  [wire31,wire31744,wire34785,wire67650,wire135300,wire811800,wire1016865],
  [wire31,wire31744,wire34785,wire67650,wire135300,wire845625,wire1015808]]
private def pool6_43 : List (List (List T)) := [chunk5_11, chunk5_12, chunk5_13, chunk5_24, chunk5_25, chunk5_61, chunk5_62]
private theorem checked6_43 : ∀ w ∈ chunk6_43, ¬ Need 6 w.toFinset := by
  have h : chunk6_43.all (routes 5 pool6_43.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_43,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_61 _ hm
  · exact checked5_62 _ hm
private def chunk6_44 : List (List T) := [[wire31,wire31744,wire34785,wire67650,wire270600,wire575025,wire1020036],
  [wire31,wire31744,wire34785,wire67650,wire304425,wire541200,wire1020036],
  [wire31,wire31744,wire34785,wire101475,wire135300,wire270600,wire1032720],
  [wire31,wire31744,wire34785,wire101475,wire135300,wire541200,wire1024264]]
private def pool6_44 : List (List (List T)) := [chunk5_12, chunk5_26, chunk5_62, chunk5_63]
private theorem checked6_44 : ∀ w ∈ chunk6_44, ¬ Need 6 w.toFinset := by
  have h : chunk6_44.all (routes 5 pool6_44.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_44,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_12 _ hm
  · exact checked5_26 _ hm
  · exact checked5_62 _ hm
  · exact checked5_63 _ hm
private def chunk6_45 : List (List T) := [[wire31,wire31744,wire34785,wire101475,wire135300,wire811800,wire1015808],
  [wire31,wire31744,wire34785,wire101475,wire270600,wire541200,wire1020036],
  [wire31,wire31744,wire67650,wire99361,wire136164,wire270600,wire541200],
  [wire31,wire31744,wire67650,wire136164,wire304425,wire575025,wire1015808]]
private def pool6_45 : List (List (List T)) := [chunk5_12, chunk5_14, chunk5_27, chunk5_28, chunk5_30, chunk5_63, chunk5_64]
private theorem checked6_45 : ∀ w ∈ chunk6_45, ¬ Need 6 w.toFinset := by
  have h : chunk6_45.all (routes 5 pool6_45.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_45,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_12 _ hm
  · exact checked5_14 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_30 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
private def chunk6_46 : List (List T) := [[wire31,wire31744,wire67650,wire169957,wire270600,wire575025,wire1015808],
  [wire31,wire31744,wire67650,wire169957,wire304425,wire541200,wire1015808],
  [wire31,wire31744,wire101475,wire136164,wire270600,wire541200,wire1016865],
  [wire31,wire31744,wire101475,wire136164,wire270600,wire575025,wire1015808]]
private def pool6_46 : List (List (List T)) := [chunk5_13, chunk5_29, chunk5_30, chunk5_31, chunk5_32, chunk5_64, chunk5_65]
private theorem checked6_46 : ∀ w ∈ chunk6_46, ¬ Need 6 w.toFinset := by
  have h : chunk6_46.all (routes 5 pool6_46.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_46,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_13 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
private def chunk6_47 : List (List T) := [[wire31,wire31744,wire101475,wire136164,wire304425,wire541200,wire1015808],
  [wire31,wire31744,wire101475,wire169957,wire270600,wire541200,wire1015808],
  [wire31,wire31775,wire33825,wire67650,wire136164,wire811800,wire1015808],
  [wire31,wire33825,wire34785,wire67650,wire135300,wire294152,wire1032720]]
private def pool6_47 : List (List (List T)) := [chunk5_13, chunk5_14, chunk5_22, chunk5_24, chunk5_26, chunk5_31, chunk5_32, chunk5_65, chunk5_66, chunk5_69]
private theorem checked6_47 : ∀ w ∈ chunk6_47, ¬ Need 6 w.toFinset := by
  have h : chunk6_47.all (routes 5 pool6_47.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_47,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_22 _ hm
  · exact checked5_24 _ hm
  · exact checked5_26 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
  · exact checked5_69 _ hm
private def chunk6_48 : List (List T) := [[wire31,wire33825,wire34785,wire67650,wire135300,wire556560,wire1024264],
  [wire31,wire33825,wire34785,wire67650,wire135300,wire818968,wire1015808],
  [wire31,wire33825,wire34785,wire97346,wire135300,wire811800,wire1015808],
  [wire31,wire33825,wire34785,wire97346,wire270600,wire541200,wire1020036]]
private def pool6_48 : List (List (List T)) := [chunk5_14, chunk5_19, chunk5_22, chunk5_24, chunk5_25, chunk5_26, chunk5_27, chunk5_70]
private theorem checked6_48 : ∀ w ∈ chunk6_48, ¬ Need 6 w.toFinset := by
  have h : chunk6_48.all (routes 5 pool6_48.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_48,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_19 _ hm
  · exact checked5_22 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_70 _ hm
private def chunk6_49 : List (List T) := [[wire31,wire33825,wire64545,wire67650,wire136164,wire811800,wire1015808],
  [wire31,wire33825,wire65536,wire67650,wire136164,wire270600,wire556560],
  [wire31,wire33825,wire65536,wire67650,wire136164,wire294152,wire541200],
  [wire31,wire33825,wire65536,wire97346,wire136164,wire270600,wire541200]]
private def pool6_49 : List (List (List T)) := [chunk5_14, chunk5_16, chunk5_18, chunk5_19, chunk5_22, chunk5_23, chunk5_28, chunk5_30, chunk5_67, chunk5_71]
private theorem checked6_49 : ∀ w ∈ chunk6_49, ¬ Need 6 w.toFinset := by
  have h : chunk6_49.all (routes 5 pool6_49.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_49,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_16 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_28 _ hm
  · exact checked5_30 _ hm
  · exact checked5_67 _ hm
  · exact checked5_71 _ hm
private def chunk6_50 : List (List T) := [[wire31,wire33825,wire66528,wire67650,wire135300,wire270600,wire556560],
  [wire31,wire33825,wire66528,wire67650,wire135300,wire294152,wire541200],
  [wire31,wire33825,wire66528,wire97346,wire135300,wire270600,wire541200],
  [wire31,wire33825,wire67650,wire97346,wire136164,wire811800,wire1015808]]
private def pool6_50 : List (List (List T)) := [chunk5_14, chunk5_15, chunk5_19, chunk5_20, chunk5_22, chunk5_67]
private theorem checked6_50 : ∀ w ∈ chunk6_50, ¬ Need 6 w.toFinset := by
  have h : chunk6_50.all (routes 5 pool6_50.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_50,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_22 _ hm
  · exact checked5_67 _ hm
private def chunk6_51 : List (List T) := [[wire31,wire33825,wire67650,wire135300,wire136164,wire818968,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire545296,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire556560,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire556560,wire1016800]]
private def pool6_51 : List (List (List T)) := [chunk5_15, chunk5_16, chunk5_17, chunk5_67]
private theorem checked6_51 : ∀ w ∈ chunk6_51, ¬ Need 6 w.toFinset := by
  have h : chunk6_51.all (routes 5 pool6_51.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_51,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_67 _ hm
private def chunk6_52 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire270600,wire556560,wire1016865],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire556560,wire1020036],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire556560,wire1020900],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire556560,wire1024264]]
private def pool6_52 : List (List (List T)) := [chunk5_15, chunk5_17, chunk5_18, chunk5_31, chunk5_71]
private theorem checked6_52 : ∀ w ∈ chunk6_52, ¬ Need 6 w.toFinset := by
  have h : chunk6_52.all (routes 5 pool6_52.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_52,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_31 _ hm
  · exact checked5_71 _ hm
private def chunk6_53 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire270600,wire556560,wire1032720],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire589361,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire818968,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire274696,wire541200,wire1015808]]
private def pool6_53 : List (List (List T)) := [chunk5_16, chunk5_18, chunk5_29, chunk5_68, chunk5_71]
private theorem checked6_53 : ∀ w ∈ chunk6_53, ¬ Need 6 w.toFinset := by
  have h : chunk6_53.all (routes 5 pool6_53.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_53,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_16 _ hm
  · exact checked5_18 _ hm
  · exact checked5_29 _ hm
  · exact checked5_68 _ hm
  · exact checked5_71 _ hm
private def chunk6_54 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire294152,wire541200,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire294152,wire541200,wire1016800],
  [wire31,wire33825,wire67650,wire136164,wire294152,wire541200,wire1016865],
  [wire31,wire33825,wire67650,wire136164,wire294152,wire541200,wire1020036]]
private def pool6_54 : List (List (List T)) := [chunk5_15, chunk5_16, chunk5_17, chunk5_31, chunk5_71]
private theorem checked6_54 : ∀ w ∈ chunk6_54, ¬ Need 6 w.toFinset := by
  have h : chunk6_54.all (routes 5 pool6_54.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_54,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_31 _ hm
  · exact checked5_71 _ hm
private def chunk6_55 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire294152,wire541200,wire1020900],
  [wire31,wire33825,wire67650,wire136164,wire294152,wire541200,wire1024264],
  [wire31,wire33825,wire67650,wire136164,wire294152,wire541200,wire1032720],
  [wire31,wire33825,wire67650,wire136164,wire294152,wire556560,wire1015808]]
private def pool6_55 : List (List (List T)) := [chunk5_15, chunk5_16, chunk5_17, chunk5_18, chunk5_68]
private theorem checked6_55 : ∀ w ∈ chunk6_55, ¬ Need 6 w.toFinset := by
  have h : chunk6_55.all (routes 5 pool6_55.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_55,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_68 _ hm
private def chunk6_56 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire294152,wire575025,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire294152,wire811800,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire294152,wire818968,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire304425,wire556560,wire1015808]]
private def pool6_56 : List (List (List T)) := [chunk5_16, chunk5_18, chunk5_29, chunk5_31, chunk5_68, chunk5_72]
private theorem checked6_56 : ∀ w ∈ chunk6_56, ¬ Need 6 w.toFinset := by
  have h : chunk6_56.all (routes 5 pool6_56.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_56,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_16 _ hm
  · exact checked5_18 _ hm
  · exact checked5_29 _ hm
  · exact checked5_31 _ hm
  · exact checked5_68 _ hm
  · exact checked5_72 _ hm
private def chunk6_57 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire326953,wire541200,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire541200,wire818968,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire556560,wire811800,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire556560,wire818968,wire1015808]]
private def pool6_57 : List (List (List T)) := [chunk5_16, chunk5_18, chunk5_29, chunk5_69, chunk5_72]
private theorem checked6_57 : ∀ w ∈ chunk6_57, ¬ Need 6 w.toFinset := by
  have h : chunk6_57.all (routes 5 pool6_57.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_57,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_16 _ hm
  · exact checked5_18 _ hm
  · exact checked5_29 _ hm
  · exact checked5_69 _ hm
  · exact checked5_72 _ hm
private def chunk6_58 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire811800,wire818968,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire818968,wire1015808],
  [wire31,wire33825,wire67650,wire169957,wire270600,wire556560,wire1015808],
  [wire31,wire33825,wire67650,wire169957,wire294152,wire541200,wire1015808]]
private def pool6_58 : List (List (List T)) := [chunk5_14, chunk5_16, chunk5_17, chunk5_18, chunk5_19, chunk5_23, chunk5_29, chunk5_32, chunk5_66, chunk5_69, chunk5_72, chunk5_73]
private theorem checked6_58 : ∀ w ∈ chunk6_58, ¬ Need 6 w.toFinset := by
  have h : chunk6_58.all (routes 5 pool6_58.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_58,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_23 _ hm
  · exact checked5_29 _ hm
  · exact checked5_32 _ hm
  · exact checked5_66 _ hm
  · exact checked5_69 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
private def chunk6_59 : List (List T) := [[wire31,wire33825,wire67679,wire136164,wire270600,wire556560,wire1015808],
  [wire31,wire33825,wire67679,wire136164,wire294152,wire541200,wire1015808],
  [wire31,wire33825,wire71746,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire33825,wire97346,wire135300,wire136164,wire811800,wire1015808]]
private def pool6_59 : List (List (List T)) := [chunk5_19, chunk5_20, chunk5_21, chunk5_69]
private theorem checked6_59 : ∀ w ∈ chunk6_59, ¬ Need 6 w.toFinset := by
  have h : chunk6_59.all (routes 5 pool6_59.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_59,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_69 _ hm
private def chunk6_60 : List (List T) := [[wire31,wire33825,wire97346,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire33825,wire97346,wire136164,wire270600,wire541200,wire1016800],
  [wire31,wire33825,wire97346,wire136164,wire270600,wire541200,wire1016865],
  [wire31,wire33825,wire97346,wire136164,wire270600,wire541200,wire1020036]]
private def pool6_60 : List (List (List T)) := [chunk5_20, chunk5_21, chunk5_32, chunk5_73]
private theorem checked6_60 : ∀ w ∈ chunk6_60, ¬ Need 6 w.toFinset := by
  have h : chunk6_60.all (routes 5 pool6_60.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_60,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_32 _ hm
  · exact checked5_73 _ hm
private def chunk6_61 : List (List T) := [[wire31,wire33825,wire97346,wire136164,wire270600,wire541200,wire1020900],
  [wire31,wire33825,wire97346,wire136164,wire270600,wire556560,wire1015808],
  [wire31,wire33825,wire97346,wire136164,wire270600,wire575025,wire1015808],
  [wire31,wire33825,wire97346,wire136164,wire270600,wire811800,wire1015808]]
private def pool6_61 : List (List (List T)) := [chunk5_20, chunk5_21, chunk5_22, chunk5_30, chunk5_73]
private theorem checked6_61 : ∀ w ∈ chunk6_61, ¬ Need 6 w.toFinset := by
  have h : chunk6_61.all (routes 5 pool6_61.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_61,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_30 _ hm
  · exact checked5_73 _ hm
private def chunk6_62 : List (List T) := [[wire31,wire33825,wire97346,wire136164,wire294152,wire541200,wire1015808],
  [wire31,wire33825,wire97346,wire136164,wire304425,wire541200,wire1015808],
  [wire31,wire33825,wire97346,wire136164,wire541200,wire811800,wire1015808],
  [wire31,wire33825,wire97346,wire136164,wire811800,wire1015808]]
private def pool6_62 : List (List (List T)) := [chunk5_14, chunk5_20, chunk5_21, chunk5_22, chunk5_23, chunk5_30, chunk5_66, chunk5_73]
private theorem checked6_62 : ∀ w ∈ chunk6_62, ¬ Need 6 w.toFinset := by
  have h : chunk6_62.all (routes 5 pool6_62.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_62,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_30 _ hm
  · exact checked5_66 _ hm
  · exact checked5_73 _ hm
private def chunk6_63 : List (List T) := [[wire31,wire33825,wire97346,wire169957,wire270600,wire541200,wire1015808],
  [wire31,wire33825,wire97375,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire33825,wire101475,wire136164,wire270600,wire556560,wire1015808],
  [wire31,wire33825,wire101475,wire136164,wire294152,wire541200,wire1015808]]
private def pool6_63 : List (List (List T)) := [chunk5_22, chunk5_23, chunk5_30, chunk5_31, chunk5_32, chunk5_74]
private theorem checked6_63 : ∀ w ∈ chunk6_63, ¬ Need 6 w.toFinset := by
  have h : chunk6_63.all (routes 5 pool6_63.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_63,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_74 _ hm
private def chunk6_64 : List (List T) := [[wire31,wire33825,wire130147,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire34785,wire64545,wire67650,wire135300,wire270600,wire1032720],
  [wire31,wire34785,wire64545,wire67650,wire135300,wire541200,wire1024264],
  [wire31,wire34785,wire64545,wire67650,wire135300,wire811800,wire1015808]]
private def pool6_64 : List (List (List T)) := [chunk5_23, chunk5_24, chunk5_25, chunk5_27, chunk5_28, chunk5_32, chunk5_74]
private theorem checked6_64 : ∀ w ∈ chunk6_64, ¬ Need 6 w.toFinset := by
  have h : chunk6_64.all (routes 5 pool6_64.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_64,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_32 _ hm
  · exact checked5_74 _ hm
private def chunk6_65 : List (List T) := [[wire31,wire34785,wire64545,wire67650,wire270600,wire541200,wire1020036],
  [wire31,wire34785,wire67650,wire135300,wire270600,wire556560,wire1016865],
  [wire31,wire34785,wire67650,wire135300,wire270600,wire589361,wire1015808],
  [wire31,wire34785,wire67650,wire135300,wire294152,wire541200,wire1016865]]
private def pool6_65 : List (List (List T)) := [chunk5_23, chunk5_24, chunk5_25, chunk5_27, chunk5_29, chunk5_75]
private theorem checked6_65 : ∀ w ∈ chunk6_65, ¬ Need 6 w.toFinset := by
  have h : chunk6_65.all (routes 5 pool6_65.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_65,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_27 _ hm
  · exact checked5_29 _ hm
  · exact checked5_75 _ hm
private def chunk6_66 : List (List T) := [[wire31,wire34785,wire67650,wire135300,wire294152,wire575025,wire1015808],
  [wire31,wire34785,wire67650,wire135300,wire304425,wire556560,wire1015808],
  [wire31,wire34785,wire67650,wire135300,wire326953,wire541200,wire1015808],
  [wire31,wire34785,wire97346,wire135300,wire270600,wire541200,wire1016865]]
private def pool6_66 : List (List (List T)) := [chunk5_24, chunk5_25, chunk5_29]
private theorem checked6_66 : ∀ w ∈ chunk6_66, ¬ Need 6 w.toFinset := by
  have h : chunk6_66.all (routes 5 pool6_66.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_66,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_29 _ hm
private def chunk6_67 : List (List T) := [[wire31,wire34785,wire97346,wire135300,wire270600,wire575025,wire1015808],
  [wire31,wire34785,wire97346,wire135300,wire304425,wire541200,wire1015808],
  [wire31,wire34785,wire101475,wire135300,wire270600,wire556560,wire1015808],
  [wire31,wire34785,wire101475,wire135300,wire294152,wire541200,wire1015808]]
private def pool6_67 : List (List (List T)) := [chunk5_25, chunk5_26, chunk5_27, chunk5_30, chunk5_32]
private theorem checked6_67 : ∀ w ∈ chunk6_67, ¬ Need 6 w.toFinset := by
  have h : chunk6_67.all (routes 5 pool6_67.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_67,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_25 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_30 _ hm
  · exact checked5_32 _ hm
private def chunk6_68 : List (List T) := [[wire31,wire34785,wire130147,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire37921,wire67650,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire64545,wire67650,wire136164,wire270600,wire541200,wire1016865],
  [wire31,wire64545,wire67650,wire169957,wire270600,wire541200,wire1015808]]
private def pool6_68 : List (List (List T)) := [chunk5_27, chunk5_28, chunk5_29, chunk5_32, chunk5_75]
private theorem checked6_68 : ∀ w ∈ chunk6_68, ¬ Need 6 w.toFinset := by
  have h : chunk6_68.all (routes 5 pool6_68.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_68,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_32 _ hm
  · exact checked5_75 _ hm
private def chunk6_69 : List (List T) := [[wire992,wire4096,wire33825,wire67679,wire135300,wire270600,wire1032720],
  [wire992,wire4096,wire33825,wire67679,wire135300,wire541200,wire1024264],
  [wire992,wire4096,wire33825,wire67679,wire135300,wire811800,wire1015808],
  [wire992,wire4096,wire33825,wire67679,wire270600,wire541200,wire1020036]]
private def pool6_69 : List (List (List T)) := [chunk5_33, chunk5_45, chunk5_46, chunk5_47, chunk5_48, chunk5_52, chunk5_53, chunk5_55]
private theorem checked6_69 : ∀ w ∈ chunk6_69, ¬ Need 6 w.toFinset := by
  have h : chunk6_69.all (routes 5 pool6_69.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_69,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_45 _ hm
  · exact checked5_46 _ hm
  · exact checked5_47 _ hm
  · exact checked5_48 _ hm
  · exact checked5_52 _ hm
  · exact checked5_53 _ hm
  · exact checked5_55 _ hm
private def chunk6_70 : List (List T) := [[wire992,wire4100,wire33825,wire67679,wire270600,wire541200,wire1015808],
  [wire992,wire4127,wire33825,wire67650,wire135300,wire270600,wire1032720],
  [wire992,wire4127,wire33825,wire67650,wire135300,wire541200,wire1024264],
  [wire992,wire4127,wire33825,wire67650,wire135300,wire811800,wire1015808]]
private def pool6_70 : List (List (List T)) := [chunk5_33, chunk5_34, chunk5_47, chunk5_53, chunk5_55]
private theorem checked6_70 : ∀ w ∈ chunk6_70, ¬ Need 6 w.toFinset := by
  have h : chunk6_70.all (routes 5 pool6_70.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_70,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
  · exact checked5_47 _ hm
  · exact checked5_53 _ hm
  · exact checked5_55 _ hm
private def chunk6_71 : List (List T) := [[wire992,wire4127,wire33825,wire67650,wire270600,wire541200,wire1020036],
  [wire992,wire31744,wire33825,wire33855,wire67650,wire135300,wire1041176],
  [wire992,wire31744,wire33825,wire33855,wire67650,wire811800,wire1020036],
  [wire992,wire31744,wire33825,wire65536,wire67679,wire135300,wire811800]]
private def pool6_71 : List (List (List T)) := [chunk5_34, chunk5_36, chunk5_37, chunk5_38, chunk5_39, chunk5_43, chunk5_48, chunk5_56, chunk5_60]
private theorem checked6_71 : ∀ w ∈ chunk6_71, ¬ Need 6 w.toFinset := by
  have h : chunk6_71.all (routes 5 pool6_71.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_71,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_34 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_38 _ hm
  · exact checked5_39 _ hm
  · exact checked5_43 _ hm
  · exact checked5_48 _ hm
  · exact checked5_56 _ hm
  · exact checked5_60 _ hm
private def chunk6_72 : List (List T) := [[wire992,wire31744,wire33825,wire67650,wire67679,wire135300,wire1041176],
  [wire992,wire31744,wire33825,wire67650,wire67679,wire811800,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire606736],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire1032720]]
private def pool6_72 : List (List (List T)) := [chunk5_34, chunk5_35, chunk5_36, chunk5_44, chunk5_45, chunk5_56]
private theorem checked6_72 : ∀ w ∈ chunk6_72, ¬ Need 6 w.toFinset := by
  have h : chunk6_72.all (routes 5 pool6_72.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_72,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_34 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
  · exact checked5_56 _ hm
private def chunk6_73 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire1033777],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire1041176],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire304425,wire1032720],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire336136,wire541200]]
private def pool6_73 : List (List (List T)) := [chunk5_34, chunk5_35, chunk5_39, chunk5_40, chunk5_46, chunk5_56, chunk5_61]
private theorem checked6_73 : ∀ w ∈ chunk6_73, ¬ Need 6 w.toFinset := by
  have h : chunk6_73.all (routes 5 pool6_73.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_73,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_34 _ hm
  · exact checked5_35 _ hm
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_46 _ hm
  · exact checked5_56 _ hm
  · exact checked5_61 _ hm
private def chunk6_74 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire541200,wire1024264],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire541200,wire1025321],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire541200,wire1041176],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire575025,wire1024264]]
private def pool6_74 : List (List (List T)) := [chunk5_35, chunk5_39, chunk5_40, chunk5_41, chunk5_46, chunk5_61, chunk5_62]
private theorem checked6_74 : ∀ w ∈ chunk6_74, ¬ Need 6 w.toFinset := by
  have h : chunk6_74.all (routes 5 pool6_74.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_74,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_35 _ hm
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_46 _ hm
  · exact checked5_61 _ hm
  · exact checked5_62 _ hm
private def chunk6_75 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire811800,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire811800,wire1016800],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire811800,wire1016865],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire811800,wire1020036]]
private def pool6_75 : List (List (List T)) := [chunk5_33, chunk5_35, chunk5_36, chunk5_41, chunk5_53, chunk5_57, chunk5_62]
private theorem checked6_75 : ∀ w ∈ chunk6_75, ¬ Need 6 w.toFinset := by
  have h : chunk6_75.all (routes 5 pool6_75.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_75,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_41 _ hm
  · exact checked5_53 _ hm
  · exact checked5_57 _ hm
  · exact checked5_62 _ hm
private def chunk6_76 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire811800,wire1024264],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire811800,wire1032720],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire811800,wire1041176],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire845625,wire1015808]]
private def pool6_76 : List (List (List T)) := [chunk5_35, chunk5_37, chunk5_39, chunk5_41, chunk5_47, chunk5_58, chunk5_59, chunk5_62]
private theorem checked6_76 : ∀ w ∈ chunk6_76, ¬ Need 6 w.toFinset := by
  have h : chunk6_76.all (routes 5 pool6_76.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_76,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_35 _ hm
  · exact checked5_37 _ hm
  · exact checked5_39 _ hm
  · exact checked5_41 _ hm
  · exact checked5_47 _ hm
  · exact checked5_58 _ hm
  · exact checked5_59 _ hm
  · exact checked5_62 _ hm
private def chunk6_77 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire1015808,wire1041176],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire1024264,wire1032720],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire1024264,wire1041176],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire1032720,wire1041176]]
private def pool6_77 : List (List (List T)) := [chunk5_35, chunk5_37]
private theorem checked6_77 : ∀ w ∈ chunk6_77, ¬ Need 6 w.toFinset := by
  have h : chunk6_77.all (routes 5 pool6_77.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_77,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_35 _ hm
  · exact checked5_37 _ hm
private def chunk6_78 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire1041176],
  [wire992,wire31744,wire33825,wire67679,wire136164,wire270600,wire1032720],
  [wire992,wire31744,wire33825,wire67679,wire136164,wire541200,wire1024264],
  [wire992,wire31744,wire33825,wire67679,wire136164,wire811800,wire1015808]]
private def pool6_78 : List (List (List T)) := [chunk5_33, chunk5_35, chunk5_36, chunk5_37, chunk5_44, chunk5_45, chunk5_55, chunk5_57]
private theorem checked6_78 : ∀ w ∈ chunk6_78, ¬ Need 6 w.toFinset := by
  have h : chunk6_78.all (routes 5 pool6_78.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_78,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
  · exact checked5_55 _ hm
  · exact checked5_57 _ hm
private def chunk6_79 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire169125,wire270600,wire1032720],
  [wire992,wire31744,wire33825,wire67679,wire169125,wire541200,wire1024264],
  [wire992,wire31744,wire33825,wire67679,wire169125,wire811800,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire200836,wire270600,wire541200]]
private def pool6_79 : List (List (List T)) := [chunk5_35, chunk5_36, chunk5_39, chunk5_41, chunk5_42, chunk5_54, chunk5_59]
private theorem checked6_79 : ∀ w ∈ chunk6_79, ¬ Need 6 w.toFinset := by
  have h : chunk6_79.all (routes 5 pool6_79.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_79,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_39 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_54 _ hm
  · exact checked5_59 _ hm
private def chunk6_80 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire270600,wire541200,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire270600,wire541200,wire1020900],
  [wire992,wire31744,wire33825,wire67679,wire270600,wire541200,wire1021093],
  [wire992,wire31744,wire33825,wire67679,wire270600,wire575025,wire1020036]]
private def pool6_80 : List (List (List T)) := [chunk5_36, chunk5_37, chunk5_40, chunk5_42, chunk5_54, chunk5_62]
private theorem checked6_80 : ∀ w ∈ chunk6_80, ¬ Need 6 w.toFinset := by
  have h : chunk6_80.all (routes 5 pool6_80.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_80,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_40 _ hm
  · exact checked5_42 _ hm
  · exact checked5_54 _ hm
  · exact checked5_62 _ hm
private def chunk6_81 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire270600,wire811800,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire270600,wire1020036,wire1032720],
  [wire992,wire31744,wire33825,wire67679,wire304425,wire541200,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire541200,wire811800,wire1020036]]
private def pool6_81 : List (List (List T)) := [chunk5_36, chunk5_37, chunk5_40, chunk5_43, chunk5_63]
private theorem checked6_81 : ∀ w ∈ chunk6_81, ¬ Need 6 w.toFinset := by
  have h : chunk6_81.all (routes 5 pool6_81.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_81,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_40 _ hm
  · exact checked5_43 _ hm
  · exact checked5_63 _ hm
private def chunk6_82 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire541200,wire1020036,wire1024264],
  [wire992,wire31744,wire33825,wire67679,wire811800,wire1015808,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire811800,wire1020036],
  [wire992,wire31744,wire33825,wire101503,wire135300,wire270600,wire1032720]]
private def pool6_82 : List (List (List T)) := [chunk5_33, chunk5_36, chunk5_37, chunk5_40, chunk5_41, chunk5_44, chunk5_45, chunk5_55, chunk5_63]
private theorem checked6_82 : ∀ w ∈ chunk6_82, ¬ Need 6 w.toFinset := by
  have h : chunk6_82.all (routes 5 pool6_82.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_82,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
  · exact checked5_55 _ hm
  · exact checked5_63 _ hm
private def chunk6_83 : List (List T) := [[wire992,wire31744,wire33825,wire101503,wire135300,wire541200,wire1024264],
  [wire992,wire31744,wire33825,wire101503,wire135300,wire811800,wire1015808],
  [wire992,wire31744,wire33825,wire101503,wire270600,wire541200,wire1020036],
  [wire992,wire31744,wire33855,wire67650,wire135300,wire270600,wire1033777]]
private def pool6_83 : List (List (List T)) := [chunk5_37, chunk5_38, chunk5_40, chunk5_41, chunk5_42, chunk5_43, chunk5_48, chunk5_59, chunk5_63, chunk5_64]
private theorem checked6_83 : ∀ w ∈ chunk6_83, ¬ Need 6 w.toFinset := by
  have h : chunk6_83.all (routes 5 pool6_83.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_83,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_37 _ hm
  · exact checked5_38 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_43 _ hm
  · exact checked5_48 _ hm
  · exact checked5_59 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
private def chunk6_84 : List (List T) := [[wire992,wire31744,wire33855,wire67650,wire135300,wire304425,wire1032720],
  [wire992,wire31744,wire33855,wire67650,wire135300,wire541200,wire1025321],
  [wire992,wire31744,wire33855,wire67650,wire135300,wire575025,wire1024264],
  [wire992,wire31744,wire33855,wire67650,wire135300,wire811800,wire1016865]]
private def pool6_84 : List (List (List T)) := [chunk5_38, chunk5_40, chunk5_41, chunk5_49, chunk5_51, chunk5_60]
private theorem checked6_84 : ∀ w ∈ chunk6_84, ¬ Need 6 w.toFinset := by
  have h : chunk6_84.all (routes 5 pool6_84.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_84,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_38 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_49 _ hm
  · exact checked5_51 _ hm
  · exact checked5_60 _ hm
private def chunk6_85 : List (List T) := [[wire992,wire31744,wire33855,wire67650,wire135300,wire845625,wire1015808],
  [wire992,wire31744,wire33855,wire67650,wire169125,wire270600,wire1032720],
  [wire992,wire31744,wire33855,wire67650,wire169125,wire541200,wire1024264],
  [wire992,wire31744,wire33855,wire67650,wire169125,wire811800,wire1015808]]
private def pool6_85 : List (List (List T)) := [chunk5_38, chunk5_41, chunk5_42, chunk5_50, chunk5_51, chunk5_60, chunk5_61]
private theorem checked6_85 : ∀ w ∈ chunk6_85, ¬ Need 6 w.toFinset := by
  have h : chunk6_85.all (routes 5 pool6_85.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_85,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_38 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_50 _ hm
  · exact checked5_51 _ hm
  · exact checked5_60 _ hm
  · exact checked5_61 _ hm
private def chunk6_86 : List (List T) := [[wire992,wire31744,wire33855,wire67650,wire270600,wire541200,wire1021093],
  [wire992,wire31744,wire33855,wire67650,wire270600,wire575025,wire1020036],
  [wire992,wire31744,wire33855,wire67650,wire304425,wire541200,wire1020036],
  [wire992,wire31744,wire67679,wire99361,wire135300,wire270600,wire541200]]
private def pool6_86 : List (List (List T)) := [chunk5_38, chunk5_39, chunk5_42, chunk5_43, chunk5_51, chunk5_52, chunk5_64]
private theorem checked6_86 : ∀ w ∈ chunk6_86, ¬ Need 6 w.toFinset := by
  have h : chunk6_86.all (routes 5 pool6_86.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_86,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_38 _ hm
  · exact checked5_39 _ hm
  · exact checked5_42 _ hm
  · exact checked5_43 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_64 _ hm
private def chunk6_87 : List (List T) := [[wire992,wire31744,wire67679,wire135300,wire304425,wire575025,wire1015808],
  [wire992,wire31744,wire67679,wire169125,wire270600,wire575025,wire1015808],
  [wire992,wire31744,wire67679,wire169125,wire304425,wire541200,wire1015808],
  [wire992,wire31744,wire101503,wire135300,wire270600,wire541200,wire1016865]]
private def pool6_87 : List (List (List T)) := [chunk5_39, chunk5_40, chunk5_41, chunk5_42, chunk5_64, chunk5_65]
private theorem checked6_87 : ∀ w ∈ chunk6_87, ¬ Need 6 w.toFinset := by
  have h : chunk6_87.all (routes 5 pool6_87.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_87,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
private def chunk6_88 : List (List T) := [[wire992,wire31744,wire101503,wire135300,wire270600,wire575025,wire1015808],
  [wire992,wire31744,wire101503,wire135300,wire304425,wire541200,wire1015808],
  [wire992,wire31744,wire101503,wire169125,wire270600,wire541200,wire1015808],
  [wire992,wire31775,wire33825,wire67679,wire135300,wire270600,wire1032720]]
private def pool6_88 : List (List (List T)) := [chunk5_33, chunk5_40, chunk5_41, chunk5_42, chunk5_43, chunk5_65, chunk5_66]
private theorem checked6_88 : ∀ w ∈ chunk6_88, ¬ Need 6 w.toFinset := by
  have h : chunk6_88.all (routes 5 pool6_88.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_88,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_43 _ hm
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
private def chunk6_89 : List (List T) := [[wire992,wire31775,wire33825,wire67679,wire135300,wire541200,wire1024264],
  [wire992,wire31775,wire33825,wire67679,wire135300,wire811800,wire1015808],
  [wire992,wire31775,wire33825,wire67679,wire270600,wire541200,wire1020036],
  [wire992,wire33825,wire33855,wire67650,wire135300,wire294152,wire1032720]]
private def pool6_89 : List (List (List T)) := [chunk5_33, chunk5_34, chunk5_43, chunk5_48, chunk5_49, chunk5_50, chunk5_66, chunk5_69]
private theorem checked6_89 : ∀ w ∈ chunk6_89, ¬ Need 6 w.toFinset := by
  have h : chunk6_89.all (routes 5 pool6_89.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_89,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
  · exact checked5_43 _ hm
  · exact checked5_48 _ hm
  · exact checked5_49 _ hm
  · exact checked5_50 _ hm
  · exact checked5_66 _ hm
  · exact checked5_69 _ hm
private def chunk6_90 : List (List T) := [[wire992,wire33825,wire33855,wire67650,wire135300,wire556560,wire1024264],
  [wire992,wire33825,wire33855,wire67650,wire135300,wire818968,wire1015808],
  [wire992,wire33825,wire33855,wire97346,wire135300,wire811800,wire1015808],
  [wire992,wire33825,wire33855,wire97346,wire270600,wire541200,wire1020036]]
private def pool6_90 : List (List (List T)) := [chunk5_43, chunk5_49, chunk5_50, chunk5_51, chunk5_52, chunk5_66, chunk5_70]
private theorem checked6_90 : ∀ w ∈ chunk6_90, ¬ Need 6 w.toFinset := by
  have h : chunk6_90.all (routes 5 pool6_90.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_90,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_43 _ hm
  · exact checked5_49 _ hm
  · exact checked5_50 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_66 _ hm
  · exact checked5_70 _ hm
private def chunk6_91 : List (List T) := [[wire992,wire33825,wire64545,wire67679,wire135300,wire270600,wire1032720],
  [wire992,wire33825,wire64545,wire67679,wire135300,wire541200,wire1024264],
  [wire992,wire33825,wire64545,wire67679,wire135300,wire811800,wire1015808],
  [wire992,wire33825,wire64545,wire67679,wire270600,wire541200,wire1020036]]
private def pool6_91 : List (List (List T)) := [chunk5_44, chunk5_53, chunk5_54, chunk5_67, chunk5_74, chunk5_75]
private theorem checked6_91 : ∀ w ∈ chunk6_91, ¬ Need 6 w.toFinset := by
  have h : chunk6_91.all (routes 5 pool6_91.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_91,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_44 _ hm
  · exact checked5_53 _ hm
  · exact checked5_54 _ hm
  · exact checked5_67 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
private def chunk6_92 : List (List T) := [[wire992,wire33825,wire67679,wire97346,wire135300,wire270600,wire1032720],
  [wire992,wire33825,wire67679,wire97346,wire135300,wire541200,wire1024264],
  [wire992,wire33825,wire67679,wire97346,wire135300,wire811800,wire1015808],
  [wire992,wire33825,wire67679,wire97346,wire270600,wire541200,wire1020036]]
private def pool6_92 : List (List (List T)) := [chunk5_44, chunk5_45, chunk5_67]
private theorem checked6_92 : ∀ w ∈ chunk6_92, ¬ Need 6 w.toFinset := by
  have h : chunk6_92.all (routes 5 pool6_92.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_92,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
  · exact checked5_67 _ hm
private def chunk6_93 : List (List T) := [[wire992,wire33825,wire67679,wire97375,wire135300,wire270600,wire1032720],
  [wire992,wire33825,wire67679,wire97375,wire135300,wire541200,wire1024264],
  [wire992,wire33825,wire67679,wire97375,wire135300,wire811800,wire1015808],
  [wire992,wire33825,wire67679,wire97375,wire270600,wire541200,wire1020036]]
private def pool6_93 : List (List (List T)) := [chunk5_33, chunk5_34, chunk5_44, chunk5_45, chunk5_67]
private theorem checked6_93 : ∀ w ∈ chunk6_93, ¬ Need 6 w.toFinset := by
  have h : chunk6_93.all (routes 5 pool6_93.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_93,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
  · exact checked5_67 _ hm
private def chunk6_94 : List (List T) := [[wire992,wire33825,wire67679,wire135300,wire270600,wire294152,wire1032720],
  [wire992,wire33825,wire67679,wire135300,wire270600,wire545296,wire1015808],
  [wire992,wire33825,wire67679,wire135300,wire270600,wire556560,wire1032720],
  [wire992,wire33825,wire67679,wire135300,wire274696,wire541200,wire1015808]]
private def pool6_94 : List (List (List T)) := [chunk5_45, chunk5_46, chunk5_67, chunk5_68]
private theorem checked6_94 : ∀ w ∈ chunk6_94, ¬ Need 6 w.toFinset := by
  have h : chunk6_94.all (routes 5 pool6_94.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_94,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_45 _ hm
  · exact checked5_46 _ hm
  · exact checked5_67 _ hm
  · exact checked5_68 _ hm
private def chunk6_95 : List (List T) := [[wire992,wire33825,wire67679,wire135300,wire294152,wire541200,wire1024264],
  [wire992,wire33825,wire67679,wire135300,wire294152,wire811800,wire1015808],
  [wire992,wire33825,wire67679,wire135300,wire541200,wire556560,wire1024264],
  [wire992,wire33825,wire67679,wire135300,wire556560,wire811800,wire1015808]]
private def pool6_95 : List (List (List T)) := [chunk5_46, chunk5_68, chunk5_69]
private theorem checked6_95 : ∀ w ∈ chunk6_95, ¬ Need 6 w.toFinset := by
  have h : chunk6_95.all (routes 5 pool6_95.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_95,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_46 _ hm
  · exact checked5_68 _ hm
  · exact checked5_69 _ hm
private def chunk6_96 : List (List T) := [[wire992,wire33825,wire67679,wire135300,wire811800,wire818968,wire1015808],
  [wire992,wire33825,wire71775,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire33855,wire64545,wire67650,wire135300,wire270600,wire1032720],
  [wire992,wire33855,wire64545,wire67650,wire135300,wire541200,wire1024264]]
private def pool6_96 : List (List (List T)) := [chunk5_47, chunk5_48, chunk5_49, chunk5_69]
private theorem checked6_96 : ∀ w ∈ chunk6_96, ¬ Need 6 w.toFinset := by
  have h : chunk6_96.all (routes 5 pool6_96.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_96,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_47 _ hm
  · exact checked5_48 _ hm
  · exact checked5_49 _ hm
  · exact checked5_69 _ hm
private def chunk6_97 : List (List T) := [[wire992,wire33855,wire64545,wire67650,wire135300,wire811800,wire1015808],
  [wire992,wire33855,wire64545,wire67650,wire270600,wire541200,wire1020036],
  [wire992,wire33855,wire67650,wire135300,wire270600,wire556560,wire1016865],
  [wire992,wire33855,wire67650,wire135300,wire270600,wire589361,wire1015808]]
private def pool6_97 : List (List (List T)) := [chunk5_48, chunk5_49, chunk5_50, chunk5_71]
private theorem checked6_97 : ∀ w ∈ chunk6_97, ¬ Need 6 w.toFinset := by
  have h : chunk6_97.all (routes 5 pool6_97.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_97,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_48 _ hm
  · exact checked5_49 _ hm
  · exact checked5_50 _ hm
  · exact checked5_71 _ hm
private def chunk6_98 : List (List T) := [[wire992,wire33855,wire67650,wire135300,wire294152,wire541200,wire1016865],
  [wire992,wire33855,wire67650,wire135300,wire294152,wire575025,wire1015808],
  [wire992,wire33855,wire67650,wire135300,wire304425,wire556560,wire1015808],
  [wire992,wire33855,wire67650,wire135300,wire326953,wire541200,wire1015808]]
private def pool6_98 : List (List (List T)) := [chunk5_48, chunk5_49, chunk5_50, chunk5_71, chunk5_72]
private theorem checked6_98 : ∀ w ∈ chunk6_98, ¬ Need 6 w.toFinset := by
  have h : chunk6_98.all (routes 5 pool6_98.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_98,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_48 _ hm
  · exact checked5_49 _ hm
  · exact checked5_50 _ hm
  · exact checked5_71 _ hm
  · exact checked5_72 _ hm
private def chunk6_99 : List (List T) := [[wire992,wire33855,wire67650,wire169125,wire270600,wire556560,wire1015808],
  [wire992,wire33855,wire67650,wire169125,wire294152,wire541200,wire1015808],
  [wire992,wire33855,wire97346,wire135300,wire270600,wire541200,wire1016865],
  [wire992,wire33855,wire97346,wire135300,wire270600,wire575025,wire1015808]]
private def pool6_99 : List (List (List T)) := [chunk5_50, chunk5_51, chunk5_52, chunk5_72, chunk5_73]
private theorem checked6_99 : ∀ w ∈ chunk6_99, ¬ Need 6 w.toFinset := by
  have h : chunk6_99.all (routes 5 pool6_99.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_99,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_50 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
private def chunk6_100 : List (List T) := [[wire992,wire33855,wire97346,wire135300,wire304425,wire541200,wire1015808],
  [wire992,wire33855,wire97346,wire169125,wire270600,wire541200,wire1015808],
  [wire992,wire37921,wire67679,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire64545,wire67679,wire135300,wire270600,wire541200,wire1016865]]
private def pool6_100 : List (List (List T)) := [chunk5_51, chunk5_52, chunk5_53, chunk5_54, chunk5_73, chunk5_74, chunk5_75]
private theorem checked6_100 : ∀ w ∈ chunk6_100, ¬ Need 6 w.toFinset := by
  have h : chunk6_100.all (routes 5 pool6_100.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_100,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_53 _ hm
  · exact checked5_54 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
private def chunk6_101 : List (List T) := [[wire992,wire64545,wire67679,wire169125,wire270600,wire541200,wire1015808],
  [wire4096,wire33825,wire67679,wire136164,wire270600,wire541200,wire1015808],
  [wire4127,wire33825,wire67650,wire136164,wire270600,wire541200,wire1015808],
  [wire31744,wire33825,wire33855,wire67650,wire136164,wire811800,wire1015808]]
private def pool6_101 : List (List (List T)) := [chunk5_54, chunk5_55, chunk5_59, chunk5_60, chunk5_61, chunk5_66, chunk5_67, chunk5_68, chunk5_69, chunk5_71, chunk5_75]
private theorem checked6_101 : ∀ w ∈ chunk6_101, ¬ Need 6 w.toFinset := by
  have h : chunk6_101.all (routes 5 pool6_101.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_101,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_54 _ hm
  · exact checked5_55 _ hm
  · exact checked5_59 _ hm
  · exact checked5_60 _ hm
  · exact checked5_61 _ hm
  · exact checked5_66 _ hm
  · exact checked5_67 _ hm
  · exact checked5_68 _ hm
  · exact checked5_69 _ hm
  · exact checked5_71 _ hm
  · exact checked5_75 _ hm
private def chunk6_102 : List (List T) := [[wire31744,wire33825,wire34785,wire67679,wire135300,wire270600,wire1032720],
  [wire31744,wire33825,wire34785,wire67679,wire135300,wire541200,wire1024264],
  [wire31744,wire33825,wire34785,wire67679,wire135300,wire811800,wire1015808],
  [wire31744,wire33825,wire34785,wire67679,wire270600,wire541200,wire1020036]]
private def pool6_102 : List (List (List T)) := [chunk5_55, chunk5_59, chunk5_61, chunk5_62, chunk5_63, chunk5_64, chunk5_74, chunk5_75]
private theorem checked6_102 : ∀ w ∈ chunk6_102, ¬ Need 6 w.toFinset := by
  have h : chunk6_102.all (routes 5 pool6_102.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_102,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_55 _ hm
  · exact checked5_59 _ hm
  · exact checked5_61 _ hm
  · exact checked5_62 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
private def chunk6_103 : List (List T) := [[wire31744,wire33825,wire65536,wire67679,wire136164,wire270600,wire541200],
  [wire31744,wire33825,wire66528,wire67679,wire135300,wire270600,wire541200],
  [wire31744,wire33825,wire67650,wire67679,wire136164,wire811800,wire1015808],
  [wire31744,wire33825,wire67679,wire135300,wire136164,wire811800,wire1015808]]
private def pool6_103 : List (List (List T)) := [chunk5_55, chunk5_56, chunk5_57, chunk5_59, chunk5_64, chunk5_67]
private theorem checked6_103 : ∀ w ∈ chunk6_103, ¬ Need 6 w.toFinset := by
  have h : chunk6_103.all (routes 5 pool6_103.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_103,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_55 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
  · exact checked5_59 _ hm
  · exact checked5_64 _ hm
  · exact checked5_67 _ hm
private def chunk6_104 : List (List T) := [[wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1015808],
  [wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1016800],
  [wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1016865],
  [wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1020036]]
private def pool6_104 : List (List (List T)) := [chunk5_57, chunk5_65, chunk5_75]
private theorem checked6_104 : ∀ w ∈ chunk6_104, ¬ Need 6 w.toFinset := by
  have h : chunk6_104.all (routes 5 pool6_104.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_104,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_57 _ hm
  · exact checked5_65 _ hm
  · exact checked5_75 _ hm
private def chunk6_105 : List (List T) := [[wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1020900],
  [wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1024264],
  [wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1032720],
  [wire31744,wire33825,wire67679,wire136164,wire270600,wire575025,wire1015808]]
private def pool6_105 : List (List (List T)) := [chunk5_58, chunk5_59, chunk5_64, chunk5_65, chunk5_68]
private theorem checked6_105 : ∀ w ∈ chunk6_105, ¬ Need 6 w.toFinset := by
  have h : chunk6_105.all (routes 5 pool6_105.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_105,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_58 _ hm
  · exact checked5_59 _ hm
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
  · exact checked5_68 _ hm
private def chunk6_106 : List (List T) := [[wire31744,wire33825,wire67679,wire136164,wire270600,wire811800,wire1015808],
  [wire31744,wire33825,wire67679,wire136164,wire304425,wire541200,wire1015808],
  [wire31744,wire33825,wire67679,wire136164,wire541200,wire811800,wire1015808],
  [wire31744,wire33825,wire67679,wire136164,wire811800,wire1015808]]
private def pool6_106 : List (List (List T)) := [chunk5_55, chunk5_56, chunk5_57, chunk5_58, chunk5_59, chunk5_64, chunk5_65, chunk5_67, chunk5_68, chunk5_69]
private theorem checked6_106 : ∀ w ∈ chunk6_106, ¬ Need 6 w.toFinset := by
  have h : chunk6_106.all (routes 5 pool6_106.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_106,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_55 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
  · exact checked5_58 _ hm
  · exact checked5_59 _ hm
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
  · exact checked5_67 _ hm
  · exact checked5_68 _ hm
  · exact checked5_69 _ hm
private def chunk6_107 : List (List T) := [[wire31744,wire33825,wire67679,wire169957,wire270600,wire541200,wire1015808],
  [wire31744,wire33825,wire101503,wire136164,wire270600,wire541200,wire1015808],
  [wire31744,wire33855,wire34785,wire67650,wire135300,wire270600,wire1032720],
  [wire31744,wire33855,wire34785,wire67650,wire135300,wire541200,wire1024264]]
private def pool6_107 : List (List (List T)) := [chunk5_59, chunk5_60, chunk5_63, chunk5_64, chunk5_65, chunk5_66, chunk5_69, chunk5_70, chunk5_75]
private theorem checked6_107 : ∀ w ∈ chunk6_107, ¬ Need 6 w.toFinset := by
  have h : chunk6_107.all (routes 5 pool6_107.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_107,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_59 _ hm
  · exact checked5_60 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
  · exact checked5_69 _ hm
  · exact checked5_70 _ hm
  · exact checked5_75 _ hm
private def chunk6_108 : List (List T) := [[wire31744,wire33855,wire34785,wire67650,wire135300,wire811800,wire1015808],
  [wire31744,wire33855,wire34785,wire67650,wire270600,wire541200,wire1020036],
  [wire31744,wire33855,wire67650,wire136164,wire270600,wire541200,wire1016865],
  [wire31744,wire33855,wire67650,wire136164,wire270600,wire575025,wire1015808]]
private def pool6_108 : List (List (List T)) := [chunk5_60, chunk5_61, chunk5_63, chunk5_64, chunk5_65, chunk5_70, chunk5_71, chunk5_72, chunk5_73]
private theorem checked6_108 : ∀ w ∈ chunk6_108, ¬ Need 6 w.toFinset := by
  have h : chunk6_108.all (routes 5 pool6_108.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_108,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_60 _ hm
  · exact checked5_61 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
  · exact checked5_70 _ hm
  · exact checked5_71 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
private def chunk6_109 : List (List T) := [[wire31744,wire33855,wire67650,wire136164,wire304425,wire541200,wire1015808],
  [wire31744,wire33855,wire67650,wire169957,wire270600,wire541200,wire1015808],
  [wire31744,wire34785,wire67679,wire135300,wire270600,wire541200,wire1016865],
  [wire31744,wire34785,wire67679,wire135300,wire270600,wire575025,wire1015808]]
private def pool6_109 : List (List (List T)) := [chunk5_60, chunk5_61, chunk5_62, chunk5_64, chunk5_65, chunk5_66, chunk5_72, chunk5_73, chunk5_74]
private theorem checked6_109 : ∀ w ∈ chunk6_109, ¬ Need 6 w.toFinset := by
  have h : chunk6_109.all (routes 5 pool6_109.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_109,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_60 _ hm
  · exact checked5_61 _ hm
  · exact checked5_62 _ hm
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
private def chunk6_110 : List (List T) := [[wire31744,wire34785,wire67679,wire135300,wire304425,wire541200,wire1015808],
  [wire31744,wire34785,wire101503,wire135300,wire270600,wire541200,wire1015808],
  [wire31775,wire33825,wire67679,wire136164,wire270600,wire541200,wire1015808],
  [wire33825,wire33855,wire67650,wire136164,wire270600,wire556560,wire1015808]]
private def pool6_110 : List (List (List T)) := [chunk5_61, chunk5_62, chunk5_63, chunk5_64, chunk5_65, chunk5_66, chunk5_71, chunk5_72]
private theorem checked6_110 : ∀ w ∈ chunk6_110, ¬ Need 6 w.toFinset := by
  have h : chunk6_110.all (routes 5 pool6_110.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_110,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_61 _ hm
  · exact checked5_62 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
  · exact checked5_71 _ hm
  · exact checked5_72 _ hm
private def chunk6_111 : List (List T) := [[wire33825,wire33855,wire67650,wire136164,wire294152,wire541200,wire1015808],
  [wire33825,wire33855,wire97346,wire136164,wire270600,wire541200,wire1015808],
  [wire33825,wire64545,wire67679,wire136164,wire270600,wire541200,wire1015808],
  [wire33825,wire67679,wire97346,wire136164,wire270600,wire541200,wire1015808]]
private def pool6_111 : List (List (List T)) := [chunk5_66, chunk5_67, chunk5_71, chunk5_72, chunk5_73, chunk5_74, chunk5_75]
private theorem checked6_111 : ∀ w ∈ chunk6_111, ¬ Need 6 w.toFinset := by
  have h : chunk6_111.all (routes 5 pool6_111.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_111,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_66 _ hm
  · exact checked5_67 _ hm
  · exact checked5_71 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
private def chunk6_112 : List (List T) := [[wire33825,wire67679,wire97375,wire136164,wire270600,wire541200,wire1015808],
  [wire33825,wire67679,wire136164,wire270600,wire294152,wire541200,wire1015808],
  [wire33825,wire67679,wire136164,wire270600,wire541200,wire556560,wire1015808],
  [wire33855,wire34785,wire67650,wire135300,wire270600,wire556560,wire1015808]]
private def pool6_112 : List (List (List T)) := [chunk5_67, chunk5_68, chunk5_69, chunk5_70, chunk5_72]
private theorem checked6_112 : ∀ w ∈ chunk6_112, ¬ Need 6 w.toFinset := by
  have h : chunk6_112.all (routes 5 pool6_112.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_112,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_67 _ hm
  · exact checked5_68 _ hm
  · exact checked5_69 _ hm
  · exact checked5_70 _ hm
  · exact checked5_72 _ hm
private def chunk6_113 : List (List T) := [[wire33855,wire34785,wire67650,wire135300,wire294152,wire541200,wire1015808],
  [wire33855,wire34785,wire97346,wire135300,wire270600,wire541200,wire1015808],
  [wire33855,wire64545,wire67650,wire136164,wire270600,wire541200,wire1015808],
  [wire34785,wire64545,wire67679,wire135300,wire270600,wire541200,wire1015808]]
private def pool6_113 : List (List (List T)) := [chunk5_69, chunk5_70, chunk5_71, chunk5_72, chunk5_73, chunk5_74, chunk5_75]
private theorem checked6_113 : ∀ w ∈ chunk6_113, ¬ Need 6 w.toFinset := by
  have h : chunk6_113.all (routes 5 pool6_113.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_113,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_69 _ hm
  · exact checked5_70 _ hm
  · exact checked5_71 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
#print axioms checked6_113
private def chunk7_0 : List (List T) := [[wire31,wire992,wire4096,wire33825,wire67650,wire135300,wire270600,wire1032720],
  [wire31,wire992,wire4096,wire33825,wire67650,wire135300,wire541200,wire1024264],
  [wire31,wire992,wire4096,wire33825,wire67650,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire4096,wire33825,wire67650,wire270600,wire541200,wire1020036]]
private def pool7_0 : List (List (List T)) := [chunk6_0, chunk6_12, chunk6_14, chunk6_15, chunk6_21, chunk6_29, chunk6_30, chunk6_36, chunk6_69, chunk6_70, chunk6_71]
private theorem checked7_0 : ∀ w ∈ chunk7_0, ¬ Need 7 w.toFinset := by
  have h : chunk7_0.all (routes 6 pool7_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_12 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_21 _ hm
  · exact checked6_29 _ hm
  · exact checked6_30 _ hm
  · exact checked6_36 _ hm
  · exact checked6_69 _ hm
  · exact checked6_70 _ hm
  · exact checked6_71 _ hm
private def chunk7_1 : List (List T) := [[wire31,wire992,wire4100,wire33825,wire67650,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire65536,wire67650,wire135300,wire811800],
  [wire31,wire992,wire31744,wire33825,wire65600,wire135300,wire270600,wire541200],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire606736]]
private def pool7_1 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_5, chunk6_7, chunk6_11, chunk6_12, chunk6_13, chunk6_30, chunk6_37, chunk6_38, chunk6_70, chunk6_71, chunk6_72]
private theorem checked7_1 : ∀ w ∈ chunk7_1, ¬ Need 7 w.toFinset := by
  have h : chunk7_1.all (routes 6 pool7_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_5 _ hm
  · exact checked6_7 _ hm
  · exact checked6_11 _ hm
  · exact checked6_12 _ hm
  · exact checked6_13 _ hm
  · exact checked6_30 _ hm
  · exact checked6_37 _ hm
  · exact checked6_38 _ hm
  · exact checked6_70 _ hm
  · exact checked6_71 _ hm
  · exact checked6_72 _ hm
private def chunk7_2 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire1032720],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire1033777],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire294152,wire1032720]]
private def pool7_2 : List (List (List T)) := [chunk6_1, chunk6_2, chunk6_7, chunk6_13, chunk6_42, chunk6_72, chunk6_73, chunk6_83]
private theorem checked7_2 : ∀ w ∈ chunk7_2, ¬ Need 7 w.toFinset := by
  have h : chunk7_2.all (routes 6 pool7_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_7 _ hm
  · exact checked6_13 _ hm
  · exact checked6_42 _ hm
  · exact checked6_72 _ hm
  · exact checked6_73 _ hm
  · exact checked6_83 _ hm
private def chunk7_3 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire304425,wire1032720],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire336136,wire541200],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire541200,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire541200,wire1025321]]
private def pool7_3 : List (List (List T)) := [chunk6_1, chunk6_2, chunk6_6, chunk6_7, chunk6_14, chunk6_15, chunk6_38, chunk6_42, chunk6_43, chunk6_73, chunk6_74, chunk6_84]
private theorem checked7_3 : ∀ w ∈ chunk7_3, ¬ Need 7 w.toFinset := by
  have h : chunk7_3.all (routes 6 pool7_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_38 _ hm
  · exact checked6_42 _ hm
  · exact checked6_43 _ hm
  · exact checked6_73 _ hm
  · exact checked6_74 _ hm
  · exact checked6_84 _ hm
private def chunk7_4 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire541200,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire556560,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire575025,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire811800,wire1015808]]
private def pool7_4 : List (List (List T)) := [chunk6_1, chunk6_2, chunk6_3, chunk6_6, chunk6_8, chunk6_14, chunk6_15, chunk6_16, chunk6_22, chunk6_38, chunk6_43, chunk6_74, chunk6_75, chunk6_84]
private theorem checked7_4 : ∀ w ∈ chunk7_4, ¬ Need 7 w.toFinset := by
  have h : chunk7_4.all (routes 6 pool7_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_6 _ hm
  · exact checked6_8 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_16 _ hm
  · exact checked6_22 _ hm
  · exact checked6_38 _ hm
  · exact checked6_43 _ hm
  · exact checked6_74 _ hm
  · exact checked6_75 _ hm
  · exact checked6_84 _ hm
private def chunk7_5 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire811800,wire1016800],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire811800,wire1016865],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire811800,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire811800,wire1024264]]
private def pool7_5 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_3, chunk6_8, chunk6_16, chunk6_17, chunk6_22, chunk6_31, chunk6_39, chunk6_40, chunk6_43, chunk6_75, chunk6_76, chunk6_84]
private theorem checked7_5 : ∀ w ∈ chunk7_5, ¬ Need 7 w.toFinset := by
  have h : chunk7_5.all (routes 6 pool7_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_8 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_22 _ hm
  · exact checked6_31 _ hm
  · exact checked6_39 _ hm
  · exact checked6_40 _ hm
  · exact checked6_43 _ hm
  · exact checked6_75 _ hm
  · exact checked6_76 _ hm
  · exact checked6_84 _ hm
private def chunk7_6 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire811800,wire1032720],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire811800,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire818968,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire845625,wire1015808]]
private def pool7_6 : List (List (List T)) := [chunk6_1, chunk6_2, chunk6_3, chunk6_4, chunk6_6, chunk6_8, chunk6_16, chunk6_17, chunk6_23, chunk6_40, chunk6_41, chunk6_43, chunk6_76, chunk6_85]
private theorem checked7_6 : ∀ w ∈ chunk7_6, ¬ Need 7 w.toFinset := by
  have h : chunk7_6.all (routes 6 pool7_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_6 _ hm
  · exact checked6_8 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_23 _ hm
  · exact checked6_40 _ hm
  · exact checked6_41 _ hm
  · exact checked6_43 _ hm
  · exact checked6_76 _ hm
  · exact checked6_85 _ hm
private def chunk7_7 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire1015808,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire1024264,wire1032720],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire1024264,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire1032720,wire1041176]]
private def pool7_7 : List (List (List T)) := [chunk6_1, chunk6_4, chunk6_23, chunk6_77]
private theorem checked7_7 : ∀ w ∈ chunk7_7, ¬ Need 7 w.toFinset := by
  have h : chunk7_7.all (routes 6 pool7_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_4 _ hm
  · exact checked6_23 _ hm
  · exact checked6_77 _ hm
private def chunk7_8 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire1041176],
  [wire31,wire992,wire31744,wire33825,wire67650,wire136164,wire270600,wire1032720],
  [wire31,wire992,wire31744,wire33825,wire67650,wire136164,wire541200,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67650,wire136164,wire811800,wire1015808]]
private def pool7_8 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_3, chunk6_4, chunk6_5, chunk6_10, chunk6_12, chunk6_18, chunk6_24, chunk6_37, chunk6_38, chunk6_39, chunk6_71, chunk6_72, chunk6_78]
private theorem checked7_8 : ∀ w ∈ chunk7_8, ¬ Need 7 w.toFinset := by
  have h : chunk7_8.all (routes 6 pool7_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_5 _ hm
  · exact checked6_10 _ hm
  · exact checked6_12 _ hm
  · exact checked6_18 _ hm
  · exact checked6_24 _ hm
  · exact checked6_37 _ hm
  · exact checked6_38 _ hm
  · exact checked6_39 _ hm
  · exact checked6_71 _ hm
  · exact checked6_72 _ hm
  · exact checked6_78 _ hm
private def chunk7_9 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire169125,wire270600,wire1032720],
  [wire31,wire992,wire31744,wire33825,wire67650,wire169125,wire541200,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67650,wire169125,wire811800,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire200836,wire270600,wire541200]]
private def pool7_9 : List (List (List T)) := [chunk6_2, chunk6_3, chunk6_6, chunk6_8, chunk6_9, chunk6_18, chunk6_19, chunk6_24, chunk6_31, chunk6_41, chunk6_79, chunk6_85]
private theorem checked7_9 : ∀ w ∈ chunk7_9, ¬ Need 7 w.toFinset := by
  have h : chunk7_9.all (routes 6 pool7_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_6 _ hm
  · exact checked6_8 _ hm
  · exact checked6_9 _ hm
  · exact checked6_18 _ hm
  · exact checked6_19 _ hm
  · exact checked6_24 _ hm
  · exact checked6_31 _ hm
  · exact checked6_41 _ hm
  · exact checked6_79 _ hm
  · exact checked6_85 _ hm
private def chunk7_10 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire270600,wire541200,wire1020900],
  [wire31,wire992,wire31744,wire33825,wire67650,wire270600,wire541200,wire1021093],
  [wire31,wire992,wire31744,wire33825,wire67650,wire270600,wire556560,wire1020036]]
private def pool7_10 : List (List (List T)) := [chunk6_3, chunk6_9, chunk6_20, chunk6_24, chunk6_25, chunk6_32, chunk6_80, chunk6_86]
private theorem checked7_10 : ∀ w ∈ chunk7_10, ¬ Need 7 w.toFinset := by
  have h : chunk7_10.all (routes 6 pool7_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_3 _ hm
  · exact checked6_9 _ hm
  · exact checked6_20 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_32 _ hm
  · exact checked6_80 _ hm
  · exact checked6_86 _ hm
private def chunk7_11 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire270600,wire575025,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire270600,wire811800,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire270600,wire1020036,wire1032720],
  [wire31,wire992,wire31744,wire33825,wire67650,wire294152,wire541200,wire1020036]]
private def pool7_11 : List (List (List T)) := [chunk6_3, chunk6_4, chunk6_6, chunk6_9, chunk6_20, chunk6_25, chunk6_26, chunk6_44, chunk6_80, chunk6_81, chunk6_86]
private theorem checked7_11 : ∀ w ∈ chunk7_11, ¬ Need 7 w.toFinset := by
  have h : chunk7_11.all (routes 6 pool7_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_6 _ hm
  · exact checked6_9 _ hm
  · exact checked6_20 _ hm
  · exact checked6_25 _ hm
  · exact checked6_26 _ hm
  · exact checked6_44 _ hm
  · exact checked6_80 _ hm
  · exact checked6_81 _ hm
  · exact checked6_86 _ hm
private def chunk7_12 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire304425,wire541200,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire541200,wire811800,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire541200,wire1020036,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67650,wire811800,wire1015808,wire1020036]]
private def pool7_12 : List (List (List T)) := [chunk6_3, chunk6_4, chunk6_6, chunk6_10, chunk6_26, chunk6_27, chunk6_44, chunk6_81, chunk6_82, chunk6_86]
private theorem checked7_12 : ∀ w ∈ chunk7_12, ¬ Need 7 w.toFinset := by
  have h : chunk7_12.all (routes 6 pool7_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_6 _ hm
  · exact checked6_10 _ hm
  · exact checked6_26 _ hm
  · exact checked6_27 _ hm
  · exact checked6_44 _ hm
  · exact checked6_81 _ hm
  · exact checked6_82 _ hm
  · exact checked6_86 _ hm
private def chunk7_13 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire811800,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire1032720],
  [wire31,wire992,wire31744,wire33825,wire67679,wire135300,wire541200,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67679,wire135300,wire811800,wire1015808]]
private def pool7_13 : List (List (List T)) := [chunk6_0, chunk6_3, chunk6_4, chunk6_5, chunk6_10, chunk6_11, chunk6_12, chunk6_20, chunk6_27, chunk6_28, chunk6_37, chunk6_41, chunk6_71, chunk6_72, chunk6_74, chunk6_75, chunk6_82, chunk6_88, chunk6_89]
private theorem checked7_13 : ∀ w ∈ chunk7_13, ¬ Need 7 w.toFinset := by
  have h : chunk7_13.all (routes 6 pool7_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_5 _ hm
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_12 _ hm
  · exact checked6_20 _ hm
  · exact checked6_27 _ hm
  · exact checked6_28 _ hm
  · exact checked6_37 _ hm
  · exact checked6_41 _ hm
  · exact checked6_71 _ hm
  · exact checked6_72 _ hm
  · exact checked6_74 _ hm
  · exact checked6_75 _ hm
  · exact checked6_82 _ hm
  · exact checked6_88 _ hm
  · exact checked6_89 _ hm
private def chunk7_14 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67679,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire97346,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire97346,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire101475,wire135300,wire270600,wire1032720]]
private def pool7_14 : List (List (List T)) := [chunk6_4, chunk6_5, chunk6_7, chunk6_8, chunk6_22, chunk6_23, chunk6_24, chunk6_25, chunk6_26, chunk6_28, chunk6_42, chunk6_44, chunk6_80, chunk6_82, chunk6_89]
private theorem checked7_14 : ∀ w ∈ chunk7_14, ¬ Need 7 w.toFinset := by
  have h : chunk7_14.all (routes 6 pool7_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_4 _ hm
  · exact checked6_5 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_26 _ hm
  · exact checked6_28 _ hm
  · exact checked6_42 _ hm
  · exact checked6_44 _ hm
  · exact checked6_80 _ hm
  · exact checked6_82 _ hm
  · exact checked6_89 _ hm
private def chunk7_15 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire101475,wire135300,wire541200,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire101475,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire101475,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire31744,wire67650,wire99361,wire135300,wire270600,wire541200]]
private def pool7_15 : List (List (List T)) := [chunk6_5, chunk6_7, chunk6_8, chunk6_9, chunk6_10, chunk6_28, chunk6_29, chunk6_32, chunk6_33, chunk6_42, chunk6_44, chunk6_45, chunk6_83, chunk6_86]
private theorem checked7_15 : ∀ w ∈ chunk7_15, ¬ Need 7 w.toFinset := by
  have h : chunk7_15.all (routes 6 pool7_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_5 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_9 _ hm
  · exact checked6_10 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_32 _ hm
  · exact checked6_33 _ hm
  · exact checked6_42 _ hm
  · exact checked6_44 _ hm
  · exact checked6_45 _ hm
  · exact checked6_83 _ hm
  · exact checked6_86 _ hm
private def chunk7_16 : List (List T) := [[wire31,wire992,wire31744,wire67650,wire135300,wire304425,wire575025,wire1015808],
  [wire31,wire992,wire31744,wire67650,wire169125,wire270600,wire575025,wire1015808],
  [wire31,wire992,wire31744,wire67650,wire169125,wire304425,wire541200,wire1015808],
  [wire31,wire992,wire31744,wire101475,wire135300,wire270600,wire541200,wire1016865]]
private def pool7_16 : List (List (List T)) := [chunk6_6, chunk6_7, chunk6_8, chunk6_9, chunk6_32, chunk6_33, chunk6_34, chunk6_35, chunk6_36, chunk6_45, chunk6_46, chunk6_87]
private theorem checked7_16 : ∀ w ∈ chunk7_16, ¬ Need 7 w.toFinset := by
  have h : chunk7_16.all (routes 6 pool7_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_9 _ hm
  · exact checked6_32 _ hm
  · exact checked6_33 _ hm
  · exact checked6_34 _ hm
  · exact checked6_35 _ hm
  · exact checked6_36 _ hm
  · exact checked6_45 _ hm
  · exact checked6_46 _ hm
  · exact checked6_87 _ hm
private def chunk7_17 : List (List T) := [[wire31,wire992,wire31744,wire101475,wire135300,wire270600,wire575025,wire1015808],
  [wire31,wire992,wire31744,wire101475,wire135300,wire304425,wire541200,wire1015808],
  [wire31,wire992,wire31744,wire101475,wire169125,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire31775,wire33825,wire67650,wire135300,wire270600,wire1032720]]
private def pool7_17 : List (List (List T)) := [chunk6_0, chunk6_7, chunk6_8, chunk6_9, chunk6_10, chunk6_35, chunk6_36, chunk6_46, chunk6_47, chunk6_88]
private theorem checked7_17 : ∀ w ∈ chunk7_17, ¬ Need 7 w.toFinset := by
  have h : chunk7_17.all (routes 6 pool7_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_9 _ hm
  · exact checked6_10 _ hm
  · exact checked6_35 _ hm
  · exact checked6_36 _ hm
  · exact checked6_46 _ hm
  · exact checked6_47 _ hm
  · exact checked6_88 _ hm
private def chunk7_18 : List (List T) := [[wire31,wire992,wire31775,wire33825,wire67650,wire135300,wire541200,wire1024264],
  [wire31,wire992,wire31775,wire33825,wire67650,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire31775,wire33825,wire67650,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire33825,wire64545,wire67650,wire135300,wire270600,wire1032720]]
private def pool7_18 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_10, chunk6_14, chunk6_28, chunk6_31, chunk6_47, chunk6_64, chunk6_89, chunk6_91, chunk6_96]
private theorem checked7_18 : ∀ w ∈ chunk7_18, ¬ Need 7 w.toFinset := by
  have h : chunk7_18.all (routes 6 pool7_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_10 _ hm
  · exact checked6_14 _ hm
  · exact checked6_28 _ hm
  · exact checked6_31 _ hm
  · exact checked6_47 _ hm
  · exact checked6_64 _ hm
  · exact checked6_89 _ hm
  · exact checked6_91 _ hm
  · exact checked6_96 _ hm
private def chunk7_19 : List (List T) := [[wire31,wire992,wire33825,wire64545,wire67650,wire135300,wire541200,wire1024264],
  [wire31,wire992,wire33825,wire64545,wire67650,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire64545,wire67650,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire33825,wire65536,wire67650,wire135300,wire270600,wire556560]]
private def pool7_19 : List (List (List T)) := [chunk6_10, chunk6_11, chunk6_14, chunk6_15, chunk6_17, chunk6_19, chunk6_29, chunk6_31, chunk6_32, chunk6_49, chunk6_50, chunk6_64, chunk6_65, chunk6_91, chunk6_96, chunk6_97]
private theorem checked7_19 : ∀ w ∈ chunk7_19, ¬ Need 7 w.toFinset := by
  have h : chunk7_19.all (routes 6 pool7_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_17 _ hm
  · exact checked6_19 _ hm
  · exact checked6_29 _ hm
  · exact checked6_31 _ hm
  · exact checked6_32 _ hm
  · exact checked6_49 _ hm
  · exact checked6_50 _ hm
  · exact checked6_64 _ hm
  · exact checked6_65 _ hm
  · exact checked6_91 _ hm
  · exact checked6_96 _ hm
  · exact checked6_97 _ hm
private def chunk7_20 : List (List T) := [[wire31,wire992,wire33825,wire65536,wire67650,wire135300,wire294152,wire541200],
  [wire31,wire992,wire33825,wire65536,wire97346,wire135300,wire270600,wire541200],
  [wire31,wire992,wire33825,wire67650,wire97346,wire135300,wire270600,wire1032720],
  [wire31,wire992,wire33825,wire67650,wire97346,wire135300,wire541200,wire1024264]]
private def pool7_20 : List (List (List T)) := [chunk6_11, chunk6_12, chunk6_13, chunk6_19, chunk6_24, chunk6_32, chunk6_33, chunk6_49, chunk6_50, chunk6_92]
private theorem checked7_20 : ∀ w ∈ chunk7_20, ¬ Need 7 w.toFinset := by
  have h : chunk7_20.all (routes 6 pool7_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_11 _ hm
  · exact checked6_12 _ hm
  · exact checked6_13 _ hm
  · exact checked6_19 _ hm
  · exact checked6_24 _ hm
  · exact checked6_32 _ hm
  · exact checked6_33 _ hm
  · exact checked6_49 _ hm
  · exact checked6_50 _ hm
  · exact checked6_92 _ hm
private def chunk7_21 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire97346,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire97346,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire294152,wire1032720],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire545296,wire1015808]]
private def pool7_21 : List (List (List T)) := [chunk6_11, chunk6_12, chunk6_13, chunk6_14, chunk6_15, chunk6_22, chunk6_24, chunk6_50, chunk6_51, chunk6_92, chunk6_94]
private theorem checked7_21 : ∀ w ∈ chunk7_21, ¬ Need 7 w.toFinset := by
  have h : chunk7_21.all (routes 6 pool7_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_11 _ hm
  · exact checked6_12 _ hm
  · exact checked6_13 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_22 _ hm
  · exact checked6_24 _ hm
  · exact checked6_50 _ hm
  · exact checked6_51 _ hm
  · exact checked6_92 _ hm
  · exact checked6_94 _ hm
private def chunk7_22 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire556560,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire556560,wire1016800],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire556560,wire1016865],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire556560,wire1020036]]
private def pool7_22 : List (List (List T)) := [chunk6_11, chunk6_14, chunk6_15, chunk6_16, chunk6_34, chunk6_51, chunk6_52, chunk6_65, chunk6_97]
private theorem checked7_22 : ∀ w ∈ chunk7_22, ¬ Need 7 w.toFinset := by
  have h : chunk7_22.all (routes 6 pool7_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_11 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_16 _ hm
  · exact checked6_34 _ hm
  · exact checked6_51 _ hm
  · exact checked6_52 _ hm
  · exact checked6_65 _ hm
  · exact checked6_97 _ hm
private def chunk7_23 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire556560,wire1024264],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire556560,wire1032720],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire589361,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire818968,wire1015808]]
private def pool7_23 : List (List (List T)) := [chunk6_14, chunk6_15, chunk6_16, chunk6_17, chunk6_32, chunk6_52, chunk6_53, chunk6_65, chunk6_94, chunk6_97]
private theorem checked7_23 : ∀ w ∈ chunk7_23, ¬ Need 7 w.toFinset := by
  have h : chunk7_23.all (routes 6 pool7_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_32 _ hm
  · exact checked6_52 _ hm
  · exact checked6_53 _ hm
  · exact checked6_65 _ hm
  · exact checked6_94 _ hm
  · exact checked6_97 _ hm
private def chunk7_24 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire274696,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire541200,wire1016800],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire541200,wire1016865]]
private def pool7_24 : List (List (List T)) := [chunk6_12, chunk6_13, chunk6_15, chunk6_16, chunk6_35, chunk6_53, chunk6_54, chunk6_65, chunk6_94, chunk6_98]
private theorem checked7_24 : ∀ w ∈ chunk7_24, ¬ Need 7 w.toFinset := by
  have h : chunk7_24.all (routes 6 pool7_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_12 _ hm
  · exact checked6_13 _ hm
  · exact checked6_15 _ hm
  · exact checked6_16 _ hm
  · exact checked6_35 _ hm
  · exact checked6_53 _ hm
  · exact checked6_54 _ hm
  · exact checked6_65 _ hm
  · exact checked6_94 _ hm
  · exact checked6_98 _ hm
private def chunk7_25 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire541200,wire1020036],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire541200,wire1024264],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire541200,wire1032720],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire556560,wire1015808]]
private def pool7_25 : List (List (List T)) := [chunk6_13, chunk6_16, chunk6_17, chunk6_20, chunk6_54, chunk6_55, chunk6_95]
private theorem checked7_25 : ∀ w ∈ chunk7_25, ¬ Need 7 w.toFinset := by
  have h : chunk7_25.all (routes 6 pool7_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_13 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_20 _ hm
  · exact checked6_54 _ hm
  · exact checked6_55 _ hm
  · exact checked6_95 _ hm
private def chunk7_26 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire575025,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire1015808,wire1032720]]
private def pool7_26 : List (List (List T)) := [chunk6_13, chunk6_16, chunk6_17, chunk6_33, chunk6_35, chunk6_56, chunk6_66, chunk6_95, chunk6_98]
private theorem checked7_26 : ∀ w ∈ chunk7_26, ¬ Need 7 w.toFinset := by
  have h : chunk7_26.all (routes 6 pool7_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_13 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_33 _ hm
  · exact checked6_35 _ hm
  · exact checked6_56 _ hm
  · exact checked6_66 _ hm
  · exact checked6_95 _ hm
  · exact checked6_98 _ hm
private def chunk7_27 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire1032720],
  [wire31,wire992,wire33825,wire67650,wire135300,wire304425,wire556560,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire326953,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire541200,wire556560,wire1024264]]
private def pool7_27 : List (List (List T)) := [chunk6_13, chunk6_14, chunk6_15, chunk6_17, chunk6_18, chunk6_20, chunk6_28, chunk6_33, chunk6_35, chunk6_47, chunk6_56, chunk6_57, chunk6_66, chunk6_89, chunk6_95, chunk6_98]
private theorem checked7_27 : ∀ w ∈ chunk7_27, ¬ Need 7 w.toFinset := by
  have h : chunk7_27.all (routes 6 pool7_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_13 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_17 _ hm
  · exact checked6_18 _ hm
  · exact checked6_20 _ hm
  · exact checked6_28 _ hm
  · exact checked6_33 _ hm
  · exact checked6_35 _ hm
  · exact checked6_47 _ hm
  · exact checked6_56 _ hm
  · exact checked6_57 _ hm
  · exact checked6_66 _ hm
  · exact checked6_89 _ hm
  · exact checked6_95 _ hm
  · exact checked6_98 _ hm
private def chunk7_28 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire541200,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire556560,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire556560,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire556560,wire1015808,wire1024264]]
private def pool7_28 : List (List (List T)) := [chunk6_14, chunk6_15, chunk6_16, chunk6_17, chunk6_57, chunk6_95]
private theorem checked7_28 : ∀ w ∈ chunk7_28, ¬ Need 7 w.toFinset := by
  have h : chunk7_28.all (routes 6 pool7_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_57 _ hm
  · exact checked6_95 _ hm
private def chunk7_29 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire556560,wire1024264],
  [wire31,wire992,wire33825,wire67650,wire135300,wire811800,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire818968,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire136164,wire270600,wire556560,wire1015808]]
private def pool7_29 : List (List (List T)) := [chunk6_11, chunk6_14, chunk6_15, chunk6_16, chunk6_17, chunk6_18, chunk6_19, chunk6_20, chunk6_28, chunk6_29, chunk6_48, chunk6_51, chunk6_58, chunk6_90, chunk6_96]
private theorem checked7_29 : ∀ w ∈ chunk7_29, ¬ Need 7 w.toFinset := by
  have h : chunk7_29.all (routes 6 pool7_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_11 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_18 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_48 _ hm
  · exact checked6_51 _ hm
  · exact checked6_58 _ hm
  · exact checked6_90 _ hm
  · exact checked6_96 _ hm
private def chunk7_30 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire136164,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire169125,wire270600,wire556560,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire169125,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire67679,wire135300,wire270600,wire556560,wire1015808]]
private def pool7_30 : List (List (List T)) := [chunk6_18, chunk6_19, chunk6_20, chunk6_32, chunk6_33, chunk6_35, chunk6_36, chunk6_54, chunk6_58, chunk6_59, chunk6_99]
private theorem checked7_30 : ∀ w ∈ chunk7_30, ¬ Need 7 w.toFinset := by
  have h : chunk7_30.all (routes 6 pool7_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_18 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_32 _ hm
  · exact checked6_33 _ hm
  · exact checked6_35 _ hm
  · exact checked6_36 _ hm
  · exact checked6_54 _ hm
  · exact checked6_58 _ hm
  · exact checked6_59 _ hm
  · exact checked6_99 _ hm
private def chunk7_31 : List (List T) := [[wire31,wire992,wire33825,wire67679,wire135300,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire71746,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire270600,wire541200,wire1016800]]
private def pool7_31 : List (List (List T)) := [chunk6_20, chunk6_21, chunk6_22, chunk6_24, chunk6_25, chunk6_59, chunk6_60, chunk6_96]
private theorem checked7_31 : ∀ w ∈ chunk7_31, ¬ Need 7 w.toFinset := by
  have h : chunk7_31.all (routes 6 pool7_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_20 _ hm
  · exact checked6_21 _ hm
  · exact checked6_22 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_59 _ hm
  · exact checked6_60 _ hm
  · exact checked6_96 _ hm
private def chunk7_32 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire135300,wire270600,wire541200,wire1016865],
  [wire31,wire992,wire33825,wire97346,wire135300,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire33825,wire97346,wire135300,wire270600,wire556560,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire270600,wire575025,wire1015808]]
private def pool7_32 : List (List (List T)) := [chunk6_22, chunk6_23, chunk6_24, chunk6_25, chunk6_34, chunk6_36, chunk6_60, chunk6_61, chunk6_66, chunk6_67, chunk6_99]
private theorem checked7_32 : ∀ w ∈ chunk7_32, ¬ Need 7 w.toFinset := by
  have h : chunk7_32.all (routes 6 pool7_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_34 _ hm
  · exact checked6_36 _ hm
  · exact checked6_60 _ hm
  · exact checked6_61 _ hm
  · exact checked6_66 _ hm
  · exact checked6_67 _ hm
  · exact checked6_99 _ hm
private def chunk7_33 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire135300,wire270600,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire270600,wire1015808,wire1032720],
  [wire31,wire992,wire33825,wire97346,wire135300,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire304425,wire541200,wire1015808]]
private def pool7_33 : List (List (List T)) := [chunk6_22, chunk6_23, chunk6_26, chunk6_34, chunk6_61, chunk6_62, chunk6_67, chunk6_100]
private theorem checked7_33 : ∀ w ∈ chunk7_33, ¬ Need 7 w.toFinset := by
  have h : chunk7_33.all (routes 6 pool7_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_26 _ hm
  · exact checked6_34 _ hm
  · exact checked6_61 _ hm
  · exact checked6_62 _ hm
  · exact checked6_67 _ hm
  · exact checked6_100 _ hm
private def chunk7_34 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire135300,wire541200,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire541200,wire1015808,wire1024264],
  [wire31,wire992,wire33825,wire97346,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire136164,wire270600,wire541200,wire1015808]]
private def pool7_34 : List (List (List T)) := [chunk6_11, chunk6_22, chunk6_23, chunk6_24, chunk6_25, chunk6_27, chunk6_28, chunk6_29, chunk6_48, chunk6_59, chunk6_60, chunk6_62, chunk6_90]
private theorem checked7_34 : ∀ w ∈ chunk7_34, ¬ Need 7 w.toFinset := by
  have h : chunk7_34.all (routes 6 pool7_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_11 _ hm
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_27 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_48 _ hm
  · exact checked6_59 _ hm
  · exact checked6_60 _ hm
  · exact checked6_62 _ hm
  · exact checked6_90 _ hm
private def chunk7_35 : List (List T) := [[wire31,wire992,wire33825,wire97346,wire169125,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire270600,wire541200,wire1015808,wire1020036],
  [wire31,wire992,wire33825,wire97346,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire33825,wire97375,wire135300,wire270600,wire541200,wire1015808]]
private def pool7_35 : List (List (List T)) := [chunk6_24, chunk6_25, chunk6_26, chunk6_27, chunk6_28, chunk6_29, chunk6_34, chunk6_36, chunk6_48, chunk6_63, chunk6_90, chunk6_100]
private theorem checked7_35 : ∀ w ∈ chunk7_35, ¬ Need 7 w.toFinset := by
  have h : chunk7_35.all (routes 6 pool7_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_26 _ hm
  · exact checked6_27 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_34 _ hm
  · exact checked6_36 _ hm
  · exact checked6_48 _ hm
  · exact checked6_63 _ hm
  · exact checked6_90 _ hm
  · exact checked6_100 _ hm
private def chunk7_36 : List (List T) := [[wire31,wire992,wire33825,wire101475,wire135300,wire270600,wire556560,wire1015808],
  [wire31,wire992,wire33825,wire101475,wire135300,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire130147,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire37921,wire67650,wire135300,wire270600,wire541200,wire1015808]]
private def pool7_36 : List (List (List T)) := [chunk6_28, chunk6_29, chunk6_30, chunk6_34, chunk6_35, chunk6_36, chunk6_63, chunk6_64, chunk6_67, chunk6_68, chunk6_100]
private theorem checked7_36 : ∀ w ∈ chunk7_36, ¬ Need 7 w.toFinset := by
  have h : chunk7_36.all (routes 6 pool7_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_36,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_30 _ hm
  · exact checked6_34 _ hm
  · exact checked6_35 _ hm
  · exact checked6_36 _ hm
  · exact checked6_63 _ hm
  · exact checked6_64 _ hm
  · exact checked6_67 _ hm
  · exact checked6_68 _ hm
  · exact checked6_100 _ hm
private def chunk7_37 : List (List T) := [[wire31,wire992,wire64545,wire67650,wire135300,wire270600,wire541200,wire1016865],
  [wire31,wire992,wire64545,wire67650,wire169125,wire270600,wire541200,wire1015808],
  [wire31,wire4096,wire33825,wire67650,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire31744,wire33825,wire34785,wire67650,wire135300,wire270600,wire1032720]]
private def pool7_37 : List (List (List T)) := [chunk6_31, chunk6_32, chunk6_33, chunk6_36, chunk6_37, chunk6_42, chunk6_44, chunk6_47, chunk6_51, chunk6_53, chunk6_59, chunk6_64, chunk6_68, chunk6_100, chunk6_101, chunk6_102, chunk6_107]
private theorem checked7_37 : ∀ w ∈ chunk7_37, ¬ Need 7 w.toFinset := by
  have h : chunk7_37.all (routes 6 pool7_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_31 _ hm
  · exact checked6_32 _ hm
  · exact checked6_33 _ hm
  · exact checked6_36 _ hm
  · exact checked6_37 _ hm
  · exact checked6_42 _ hm
  · exact checked6_44 _ hm
  · exact checked6_47 _ hm
  · exact checked6_51 _ hm
  · exact checked6_53 _ hm
  · exact checked6_59 _ hm
  · exact checked6_64 _ hm
  · exact checked6_68 _ hm
  · exact checked6_100 _ hm
  · exact checked6_101 _ hm
  · exact checked6_102 _ hm
  · exact checked6_107 _ hm
private def chunk7_38 : List (List T) := [[wire31,wire31744,wire33825,wire34785,wire67650,wire135300,wire541200,wire1024264],
  [wire31,wire31744,wire33825,wire34785,wire67650,wire135300,wire811800,wire1015808],
  [wire31,wire31744,wire33825,wire34785,wire67650,wire270600,wire541200,wire1020036],
  [wire31,wire31744,wire33825,wire65536,wire67650,wire136164,wire270600,wire541200]]
private def pool7_38 : List (List (List T)) := [chunk6_37, chunk6_38, chunk6_41, chunk6_43, chunk6_44, chunk6_45, chunk6_48, chunk6_49, chunk6_64, chunk6_65, chunk6_102, chunk6_103, chunk6_107, chunk6_108]
private theorem checked7_38 : ∀ w ∈ chunk7_38, ¬ Need 7 w.toFinset := by
  have h : chunk7_38.all (routes 6 pool7_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_38,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_37 _ hm
  · exact checked6_38 _ hm
  · exact checked6_41 _ hm
  · exact checked6_43 _ hm
  · exact checked6_44 _ hm
  · exact checked6_45 _ hm
  · exact checked6_48 _ hm
  · exact checked6_49 _ hm
  · exact checked6_64 _ hm
  · exact checked6_65 _ hm
  · exact checked6_102 _ hm
  · exact checked6_103 _ hm
  · exact checked6_107 _ hm
  · exact checked6_108 _ hm
private def chunk7_39 : List (List T) := [[wire31,wire31744,wire33825,wire66528,wire67650,wire135300,wire270600,wire541200],
  [wire31,wire31744,wire33825,wire67650,wire135300,wire136164,wire811800,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire541200,wire1016800]]
private def pool7_39 : List (List (List T)) := [chunk6_36, chunk6_37, chunk6_38, chunk6_39, chunk6_41, chunk6_50, chunk6_51, chunk6_54, chunk6_59, chunk6_60, chunk6_103, chunk6_104]
private theorem checked7_39 : ∀ w ∈ chunk7_39, ¬ Need 7 w.toFinset := by
  have h : chunk7_39.all (routes 6 pool7_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_36 _ hm
  · exact checked6_37 _ hm
  · exact checked6_38 _ hm
  · exact checked6_39 _ hm
  · exact checked6_41 _ hm
  · exact checked6_50 _ hm
  · exact checked6_51 _ hm
  · exact checked6_54 _ hm
  · exact checked6_59 _ hm
  · exact checked6_60 _ hm
  · exact checked6_103 _ hm
  · exact checked6_104 _ hm
private def chunk7_40 : List (List T) := [[wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire541200,wire1016865],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire541200,wire1020036],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire541200,wire1020900],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire541200,wire1024264]]
private def pool7_40 : List (List (List T)) := [chunk6_37, chunk6_39, chunk6_40, chunk6_46, chunk6_52, chunk6_54, chunk6_55, chunk6_60, chunk6_61, chunk6_68, chunk6_104, chunk6_105, chunk6_108]
private theorem checked7_40 : ∀ w ∈ chunk7_40, ¬ Need 7 w.toFinset := by
  have h : chunk7_40.all (routes 6 pool7_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_40,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_37 _ hm
  · exact checked6_39 _ hm
  · exact checked6_40 _ hm
  · exact checked6_46 _ hm
  · exact checked6_52 _ hm
  · exact checked6_54 _ hm
  · exact checked6_55 _ hm
  · exact checked6_60 _ hm
  · exact checked6_61 _ hm
  · exact checked6_68 _ hm
  · exact checked6_104 _ hm
  · exact checked6_105 _ hm
  · exact checked6_108 _ hm
private def chunk7_41 : List (List T) := [[wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire541200,wire1032720],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire556560,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire575025,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire811800,wire1015808]]
private def pool7_41 : List (List (List T)) := [chunk6_38, chunk6_40, chunk6_41, chunk6_45, chunk6_46, chunk6_51, chunk6_53, chunk6_55, chunk6_56, chunk6_61, chunk6_105, chunk6_106, chunk6_108]
private theorem checked7_41 : ∀ w ∈ chunk7_41, ¬ Need 7 w.toFinset := by
  have h : chunk7_41.all (routes 6 pool7_41.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_41,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_38 _ hm
  · exact checked6_40 _ hm
  · exact checked6_41 _ hm
  · exact checked6_45 _ hm
  · exact checked6_46 _ hm
  · exact checked6_51 _ hm
  · exact checked6_53 _ hm
  · exact checked6_55 _ hm
  · exact checked6_56 _ hm
  · exact checked6_61 _ hm
  · exact checked6_105 _ hm
  · exact checked6_106 _ hm
  · exact checked6_108 _ hm
private def chunk7_42 : List (List T) := [[wire31,wire31744,wire33825,wire67650,wire136164,wire294152,wire541200,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire304425,wire541200,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire541200,wire811800,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire136164,wire811800,wire1015808]]
private def pool7_42 : List (List (List T)) := [chunk6_36, chunk6_37, chunk6_38, chunk6_39, chunk6_40, chunk6_41, chunk6_42, chunk6_45, chunk6_46, chunk6_47, chunk6_49, chunk6_50, chunk6_54, chunk6_55, chunk6_56, chunk6_57, chunk6_58, chunk6_62, chunk6_101, chunk6_103, chunk6_106, chunk6_109]
private theorem checked7_42 : ∀ w ∈ chunk7_42, ¬ Need 7 w.toFinset := by
  have h : chunk7_42.all (routes 6 pool7_42.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_42,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_36 _ hm
  · exact checked6_37 _ hm
  · exact checked6_38 _ hm
  · exact checked6_39 _ hm
  · exact checked6_40 _ hm
  · exact checked6_41 _ hm
  · exact checked6_42 _ hm
  · exact checked6_45 _ hm
  · exact checked6_46 _ hm
  · exact checked6_47 _ hm
  · exact checked6_49 _ hm
  · exact checked6_50 _ hm
  · exact checked6_54 _ hm
  · exact checked6_55 _ hm
  · exact checked6_56 _ hm
  · exact checked6_57 _ hm
  · exact checked6_58 _ hm
  · exact checked6_62 _ hm
  · exact checked6_101 _ hm
  · exact checked6_103 _ hm
  · exact checked6_106 _ hm
  · exact checked6_109 _ hm
private def chunk7_43 : List (List T) := [[wire31,wire31744,wire33825,wire67650,wire169957,wire270600,wire541200,wire1015808],
  [wire31,wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire31744,wire33825,wire97346,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire31744,wire33825,wire101475,wire136164,wire270600,wire541200,wire1015808]]
private def pool7_43 : List (List (List T)) := [chunk6_41, chunk6_42, chunk6_46, chunk6_47, chunk6_58, chunk6_59, chunk6_60, chunk6_61, chunk6_62, chunk6_63, chunk6_64, chunk6_68, chunk6_104, chunk6_107, chunk6_109, chunk6_110]
private theorem checked7_43 : ∀ w ∈ chunk7_43, ¬ Need 7 w.toFinset := by
  have h : chunk7_43.all (routes 6 pool7_43.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_43,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_41 _ hm
  · exact checked6_42 _ hm
  · exact checked6_46 _ hm
  · exact checked6_47 _ hm
  · exact checked6_58 _ hm
  · exact checked6_59 _ hm
  · exact checked6_60 _ hm
  · exact checked6_61 _ hm
  · exact checked6_62 _ hm
  · exact checked6_63 _ hm
  · exact checked6_64 _ hm
  · exact checked6_68 _ hm
  · exact checked6_104 _ hm
  · exact checked6_107 _ hm
  · exact checked6_109 _ hm
  · exact checked6_110 _ hm
private def chunk7_44 : List (List T) := [[wire31,wire31744,wire34785,wire67650,wire135300,wire270600,wire541200,wire1016865],
  [wire31,wire31744,wire34785,wire67650,wire135300,wire270600,wire575025,wire1015808],
  [wire31,wire31744,wire34785,wire67650,wire135300,wire304425,wire541200,wire1015808],
  [wire31,wire31744,wire34785,wire101475,wire135300,wire270600,wire541200,wire1015808]]
private def pool7_44 : List (List (List T)) := [chunk6_42, chunk6_43, chunk6_44, chunk6_45, chunk6_46, chunk6_47, chunk6_65, chunk6_66, chunk6_67, chunk6_68, chunk6_109, chunk6_110]
private theorem checked7_44 : ∀ w ∈ chunk7_44, ¬ Need 7 w.toFinset := by
  have h : chunk7_44.all (routes 6 pool7_44.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_44,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_42 _ hm
  · exact checked6_43 _ hm
  · exact checked6_44 _ hm
  · exact checked6_45 _ hm
  · exact checked6_46 _ hm
  · exact checked6_47 _ hm
  · exact checked6_65 _ hm
  · exact checked6_66 _ hm
  · exact checked6_67 _ hm
  · exact checked6_68 _ hm
  · exact checked6_109 _ hm
  · exact checked6_110 _ hm
private def chunk7_45 : List (List T) := [[wire31,wire31775,wire33825,wire67650,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire33825,wire34785,wire67650,wire135300,wire270600,wire556560,wire1015808],
  [wire31,wire33825,wire34785,wire67650,wire135300,wire294152,wire541200,wire1015808],
  [wire31,wire33825,wire34785,wire97346,wire135300,wire270600,wire541200,wire1015808]]
private def pool7_45 : List (List (List T)) := [chunk6_47, chunk6_48, chunk6_58, chunk6_63, chunk6_65, chunk6_66, chunk6_67, chunk6_68, chunk6_110, chunk6_112, chunk6_113]
private theorem checked7_45 : ∀ w ∈ chunk7_45, ¬ Need 7 w.toFinset := by
  have h : chunk7_45.all (routes 6 pool7_45.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_45,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_47 _ hm
  · exact checked6_48 _ hm
  · exact checked6_58 _ hm
  · exact checked6_63 _ hm
  · exact checked6_65 _ hm
  · exact checked6_66 _ hm
  · exact checked6_67 _ hm
  · exact checked6_68 _ hm
  · exact checked6_110 _ hm
  · exact checked6_112 _ hm
  · exact checked6_113 _ hm
private def chunk7_46 : List (List T) := [[wire31,wire33825,wire64545,wire67650,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire33825,wire67650,wire97346,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire33825,wire67650,wire135300,wire136164,wire270600,wire556560,wire1015808],
  [wire31,wire33825,wire67650,wire135300,wire136164,wire294152,wire541200,wire1015808]]
private def pool7_46 : List (List (List T)) := [chunk6_49, chunk6_50, chunk6_51, chunk6_52, chunk6_53, chunk6_54, chunk6_57, chunk6_60, chunk6_64, chunk6_68, chunk6_111, chunk6_113]
private theorem checked7_46 : ∀ w ∈ chunk7_46, ¬ Need 7 w.toFinset := by
  have h : chunk7_46.all (routes 6 pool7_46.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_46,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_49 _ hm
  · exact checked6_50 _ hm
  · exact checked6_51 _ hm
  · exact checked6_52 _ hm
  · exact checked6_53 _ hm
  · exact checked6_54 _ hm
  · exact checked6_57 _ hm
  · exact checked6_60 _ hm
  · exact checked6_64 _ hm
  · exact checked6_68 _ hm
  · exact checked6_111 _ hm
  · exact checked6_113 _ hm
private def chunk7_47 : List (List T) := [[wire31,wire33825,wire67650,wire136164,wire270600,wire294152,wire541200,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire541200,wire556560,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire270600,wire556560,wire1015808],
  [wire31,wire33825,wire67650,wire136164,wire294152,wire541200,wire1015808]]
private def pool7_47 : List (List (List T)) := [chunk6_49, chunk6_51, chunk6_52, chunk6_53, chunk6_54, chunk6_55, chunk6_56, chunk6_57, chunk6_58, chunk6_59, chunk6_63, chunk6_110, chunk6_111, chunk6_112]
private theorem checked7_47 : ∀ w ∈ chunk7_47, ¬ Need 7 w.toFinset := by
  have h : chunk7_47.all (routes 6 pool7_47.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_47,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_49 _ hm
  · exact checked6_51 _ hm
  · exact checked6_52 _ hm
  · exact checked6_53 _ hm
  · exact checked6_54 _ hm
  · exact checked6_55 _ hm
  · exact checked6_56 _ hm
  · exact checked6_57 _ hm
  · exact checked6_58 _ hm
  · exact checked6_59 _ hm
  · exact checked6_63 _ hm
  · exact checked6_110 _ hm
  · exact checked6_111 _ hm
  · exact checked6_112 _ hm
private def chunk7_48 : List (List T) := [[wire31,wire33825,wire97346,wire135300,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire33825,wire97346,wire136164,wire270600,wire541200,wire1015808],
  [wire31,wire34785,wire64545,wire67650,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire4096,wire33825,wire67679,wire135300,wire270600,wire541200,wire1015808]]
private def pool7_48 : List (List (List T)) := [chunk6_49, chunk6_59, chunk6_60, chunk6_61, chunk6_62, chunk6_63, chunk6_64, chunk6_65, chunk6_66, chunk6_68, chunk6_69, chunk6_94, chunk6_96, chunk6_100, chunk6_101, chunk6_111, chunk6_113]
private theorem checked7_48 : ∀ w ∈ chunk7_48, ¬ Need 7 w.toFinset := by
  have h : chunk7_48.all (routes 6 pool7_48.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_48,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_49 _ hm
  · exact checked6_59 _ hm
  · exact checked6_60 _ hm
  · exact checked6_61 _ hm
  · exact checked6_62 _ hm
  · exact checked6_63 _ hm
  · exact checked6_64 _ hm
  · exact checked6_65 _ hm
  · exact checked6_66 _ hm
  · exact checked6_68 _ hm
  · exact checked6_69 _ hm
  · exact checked6_94 _ hm
  · exact checked6_96 _ hm
  · exact checked6_100 _ hm
  · exact checked6_101 _ hm
  · exact checked6_111 _ hm
  · exact checked6_113 _ hm
private def chunk7_49 : List (List T) := [[wire992,wire4127,wire33825,wire67650,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire31744,wire33825,wire33855,wire67650,wire135300,wire270600,wire1032720],
  [wire992,wire31744,wire33825,wire33855,wire67650,wire135300,wire541200,wire1024264],
  [wire992,wire31744,wire33825,wire33855,wire67650,wire135300,wire811800,wire1015808]]
private def pool7_49 : List (List (List T)) := [chunk6_70, chunk6_71, chunk6_82, chunk6_83, chunk6_84, chunk6_85, chunk6_89, chunk6_90, chunk6_96, chunk6_97, chunk6_101, chunk6_107, chunk6_108]
private theorem checked7_49 : ∀ w ∈ chunk7_49, ¬ Need 7 w.toFinset := by
  have h : chunk7_49.all (routes 6 pool7_49.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_49,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_70 _ hm
  · exact checked6_71 _ hm
  · exact checked6_82 _ hm
  · exact checked6_83 _ hm
  · exact checked6_84 _ hm
  · exact checked6_85 _ hm
  · exact checked6_89 _ hm
  · exact checked6_90 _ hm
  · exact checked6_96 _ hm
  · exact checked6_97 _ hm
  · exact checked6_101 _ hm
  · exact checked6_107 _ hm
  · exact checked6_108 _ hm
private def chunk7_50 : List (List T) := [[wire992,wire31744,wire33825,wire33855,wire67650,wire270600,wire541200,wire1020036],
  [wire992,wire31744,wire33825,wire65536,wire67679,wire135300,wire270600,wire541200],
  [wire992,wire31744,wire33825,wire67650,wire67679,wire135300,wire270600,wire1032720],
  [wire992,wire31744,wire33825,wire67650,wire67679,wire135300,wire541200,wire1024264]]
private def pool7_50 : List (List (List T)) := [chunk6_71, chunk6_72, chunk6_73, chunk6_74, chunk6_79, chunk6_83, chunk6_86, chunk6_90, chunk6_92, chunk6_97, chunk6_103, chunk6_108]
private theorem checked7_50 : ∀ w ∈ chunk7_50, ¬ Need 7 w.toFinset := by
  have h : chunk7_50.all (routes 6 pool7_50.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_50,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_71 _ hm
  · exact checked6_72 _ hm
  · exact checked6_73 _ hm
  · exact checked6_74 _ hm
  · exact checked6_79 _ hm
  · exact checked6_83 _ hm
  · exact checked6_86 _ hm
  · exact checked6_90 _ hm
  · exact checked6_92 _ hm
  · exact checked6_97 _ hm
  · exact checked6_103 _ hm
  · exact checked6_108 _ hm
private def chunk7_51 : List (List T) := [[wire992,wire31744,wire33825,wire67650,wire67679,wire135300,wire811800,wire1015808],
  [wire992,wire31744,wire33825,wire67650,wire67679,wire270600,wire541200,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire541200,wire1016800]]
private def pool7_51 : List (List (List T)) := [chunk6_71, chunk6_72, chunk6_74, chunk6_75, chunk6_80, chunk6_92, chunk6_103, chunk6_104]
private theorem checked7_51 : ∀ w ∈ chunk7_51, ¬ Need 7 w.toFinset := by
  have h : chunk7_51.all (routes 6 pool7_51.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_51,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_71 _ hm
  · exact checked6_72 _ hm
  · exact checked6_74 _ hm
  · exact checked6_75 _ hm
  · exact checked6_80 _ hm
  · exact checked6_92 _ hm
  · exact checked6_103 _ hm
  · exact checked6_104 _ hm
private def chunk7_52 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire541200,wire1016865],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire541200,wire1020036],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire541200,wire1024264],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire541200,wire1032720]]
private def pool7_52 : List (List (List T)) := [chunk6_69, chunk6_72, chunk6_73, chunk6_74, chunk6_75, chunk6_76, chunk6_80, chunk6_87, chunk6_94, chunk6_95, chunk6_100, chunk6_104, chunk6_105, chunk6_109]
private theorem checked7_52 : ∀ w ∈ chunk7_52, ¬ Need 7 w.toFinset := by
  have h : chunk7_52.all (routes 6 pool7_52.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_52,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_69 _ hm
  · exact checked6_72 _ hm
  · exact checked6_73 _ hm
  · exact checked6_74 _ hm
  · exact checked6_75 _ hm
  · exact checked6_76 _ hm
  · exact checked6_80 _ hm
  · exact checked6_87 _ hm
  · exact checked6_94 _ hm
  · exact checked6_95 _ hm
  · exact checked6_100 _ hm
  · exact checked6_104 _ hm
  · exact checked6_105 _ hm
  · exact checked6_109 _ hm
private def chunk7_53 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire575025,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire811800,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire1015808,wire1032720],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire1032720]]
private def pool7_53 : List (List (List T)) := [chunk6_69, chunk6_72, chunk6_73, chunk6_74, chunk6_75, chunk6_76, chunk6_77, chunk6_78, chunk6_79, chunk6_80, chunk6_81, chunk6_82, chunk6_87, chunk6_88, chunk6_91, chunk6_93, chunk6_94, chunk6_95, chunk6_102, chunk6_105, chunk6_106, chunk6_109]
private theorem checked7_53 : ∀ w ∈ chunk7_53, ¬ Need 7 w.toFinset := by
  have h : chunk7_53.all (routes 6 pool7_53.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_53,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_69 _ hm
  · exact checked6_72 _ hm
  · exact checked6_73 _ hm
  · exact checked6_74 _ hm
  · exact checked6_75 _ hm
  · exact checked6_76 _ hm
  · exact checked6_77 _ hm
  · exact checked6_78 _ hm
  · exact checked6_79 _ hm
  · exact checked6_80 _ hm
  · exact checked6_81 _ hm
  · exact checked6_82 _ hm
  · exact checked6_87 _ hm
  · exact checked6_88 _ hm
  · exact checked6_91 _ hm
  · exact checked6_93 _ hm
  · exact checked6_94 _ hm
  · exact checked6_95 _ hm
  · exact checked6_102 _ hm
  · exact checked6_105 _ hm
  · exact checked6_106 _ hm
  · exact checked6_109 _ hm
private def chunk7_54 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire304425,wire541200,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire541200,wire811800,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire541200,wire1015808,wire1024264],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire541200,wire1024264]]
private def pool7_54 : List (List (List T)) := [chunk6_69, chunk6_73, chunk6_74, chunk6_75, chunk6_76, chunk6_77, chunk6_78, chunk6_79, chunk6_81, chunk6_82, chunk6_83, chunk6_87, chunk6_88, chunk6_91, chunk6_93, chunk6_95, chunk6_102, chunk6_106, chunk6_110]
private theorem checked7_54 : ∀ w ∈ chunk7_54, ¬ Need 7 w.toFinset := by
  have h : chunk7_54.all (routes 6 pool7_54.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_54,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_69 _ hm
  · exact checked6_73 _ hm
  · exact checked6_74 _ hm
  · exact checked6_75 _ hm
  · exact checked6_76 _ hm
  · exact checked6_77 _ hm
  · exact checked6_78 _ hm
  · exact checked6_79 _ hm
  · exact checked6_81 _ hm
  · exact checked6_82 _ hm
  · exact checked6_83 _ hm
  · exact checked6_87 _ hm
  · exact checked6_88 _ hm
  · exact checked6_91 _ hm
  · exact checked6_93 _ hm
  · exact checked6_95 _ hm
  · exact checked6_102 _ hm
  · exact checked6_106 _ hm
  · exact checked6_110 _ hm
private def chunk7_55 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire135300,wire811800,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire169125,wire270600,wire541200,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire270600,wire541200,wire1015808,wire1020036]]
private def pool7_55 : List (List (List T)) := [chunk6_69, chunk6_71, chunk6_75, chunk6_76, chunk6_77, chunk6_78, chunk6_79, chunk6_80, chunk6_81, chunk6_82, chunk6_83, chunk6_87, chunk6_88, chunk6_91, chunk6_93, chunk6_96, chunk6_101, chunk6_102, chunk6_103, chunk6_104, chunk6_106, chunk6_107]
private theorem checked7_55 : ∀ w ∈ chunk7_55, ¬ Need 7 w.toFinset := by
  have h : chunk7_55.all (routes 6 pool7_55.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_55,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_69 _ hm
  · exact checked6_71 _ hm
  · exact checked6_75 _ hm
  · exact checked6_76 _ hm
  · exact checked6_77 _ hm
  · exact checked6_78 _ hm
  · exact checked6_79 _ hm
  · exact checked6_80 _ hm
  · exact checked6_81 _ hm
  · exact checked6_82 _ hm
  · exact checked6_83 _ hm
  · exact checked6_87 _ hm
  · exact checked6_88 _ hm
  · exact checked6_91 _ hm
  · exact checked6_93 _ hm
  · exact checked6_96 _ hm
  · exact checked6_101 _ hm
  · exact checked6_102 _ hm
  · exact checked6_103 _ hm
  · exact checked6_104 _ hm
  · exact checked6_106 _ hm
  · exact checked6_107 _ hm
private def chunk7_56 : List (List T) := [[wire992,wire31744,wire33825,wire67679,wire270600,wire541200,wire1020036],
  [wire992,wire31744,wire33825,wire101503,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire31744,wire33855,wire67650,wire135300,wire270600,wire541200,wire1016865],
  [wire992,wire31744,wire33855,wire67650,wire135300,wire270600,wire575025,wire1015808]]
private def pool7_56 : List (List (List T)) := [chunk6_69, chunk6_80, chunk6_81, chunk6_82, chunk6_83, chunk6_84, chunk6_85, chunk6_86, chunk6_87, chunk6_88, chunk6_91, chunk6_93, chunk6_97, chunk6_98, chunk6_99, chunk6_102, chunk6_107, chunk6_108, chunk6_110]
private theorem checked7_56 : ∀ w ∈ chunk7_56, ¬ Need 7 w.toFinset := by
  have h : chunk7_56.all (routes 6 pool7_56.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_56,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_69 _ hm
  · exact checked6_80 _ hm
  · exact checked6_81 _ hm
  · exact checked6_82 _ hm
  · exact checked6_83 _ hm
  · exact checked6_84 _ hm
  · exact checked6_85 _ hm
  · exact checked6_86 _ hm
  · exact checked6_87 _ hm
  · exact checked6_88 _ hm
  · exact checked6_91 _ hm
  · exact checked6_93 _ hm
  · exact checked6_97 _ hm
  · exact checked6_98 _ hm
  · exact checked6_99 _ hm
  · exact checked6_102 _ hm
  · exact checked6_107 _ hm
  · exact checked6_108 _ hm
  · exact checked6_110 _ hm
private def chunk7_57 : List (List T) := [[wire992,wire31744,wire33855,wire67650,wire135300,wire304425,wire541200,wire1015808],
  [wire992,wire31744,wire33855,wire67650,wire169125,wire270600,wire541200,wire1015808],
  [wire992,wire31775,wire33825,wire67679,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire33825,wire33855,wire67650,wire135300,wire270600,wire556560,wire1015808]]
private def pool7_57 : List (List (List T)) := [chunk6_70, chunk6_84, chunk6_85, chunk6_86, chunk6_88, chunk6_89, chunk6_90, chunk6_97, chunk6_98, chunk6_99, chunk6_100, chunk6_109, chunk6_110, chunk6_112]
private theorem checked7_57 : ∀ w ∈ chunk7_57, ¬ Need 7 w.toFinset := by
  have h : chunk7_57.all (routes 6 pool7_57.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_57,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_70 _ hm
  · exact checked6_84 _ hm
  · exact checked6_85 _ hm
  · exact checked6_86 _ hm
  · exact checked6_88 _ hm
  · exact checked6_89 _ hm
  · exact checked6_90 _ hm
  · exact checked6_97 _ hm
  · exact checked6_98 _ hm
  · exact checked6_99 _ hm
  · exact checked6_100 _ hm
  · exact checked6_109 _ hm
  · exact checked6_110 _ hm
  · exact checked6_112 _ hm
private def chunk7_58 : List (List T) := [[wire992,wire33825,wire33855,wire67650,wire135300,wire294152,wire541200,wire1015808],
  [wire992,wire33825,wire33855,wire97346,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire33825,wire64545,wire67679,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire33825,wire67679,wire97346,wire135300,wire270600,wire541200,wire1015808]]
private def pool7_58 : List (List (List T)) := [chunk6_89, chunk6_90, chunk6_91, chunk6_92, chunk6_98, chunk6_99, chunk6_100, chunk6_101, chunk6_111, chunk6_113]
private theorem checked7_58 : ∀ w ∈ chunk7_58, ¬ Need 7 w.toFinset := by
  have h : chunk7_58.all (routes 6 pool7_58.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_58,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_89 _ hm
  · exact checked6_90 _ hm
  · exact checked6_91 _ hm
  · exact checked6_92 _ hm
  · exact checked6_98 _ hm
  · exact checked6_99 _ hm
  · exact checked6_100 _ hm
  · exact checked6_101 _ hm
  · exact checked6_111 _ hm
  · exact checked6_113 _ hm
private def chunk7_59 : List (List T) := [[wire992,wire33825,wire67679,wire97375,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire33825,wire67679,wire135300,wire270600,wire294152,wire541200,wire1015808],
  [wire992,wire33825,wire67679,wire135300,wire270600,wire541200,wire556560,wire1015808],
  [wire992,wire33855,wire64545,wire67650,wire135300,wire270600,wire541200,wire1015808]]
private def pool7_59 : List (List (List T)) := [chunk6_70, chunk6_93, chunk6_94, chunk6_95, chunk6_96, chunk6_97, chunk6_98, chunk6_112, chunk6_113]
private theorem checked7_59 : ∀ w ∈ chunk7_59, ¬ Need 7 w.toFinset := by
  have h : chunk7_59.all (routes 6 pool7_59.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_59,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_70 _ hm
  · exact checked6_93 _ hm
  · exact checked6_94 _ hm
  · exact checked6_95 _ hm
  · exact checked6_96 _ hm
  · exact checked6_97 _ hm
  · exact checked6_98 _ hm
  · exact checked6_112 _ hm
  · exact checked6_113 _ hm
private def chunk7_60 : List (List T) := [[wire31744,wire33825,wire33855,wire67650,wire136164,wire270600,wire541200,wire1015808],
  [wire31744,wire33825,wire34785,wire67679,wire135300,wire270600,wire541200,wire1015808],
  [wire31744,wire33825,wire67650,wire67679,wire136164,wire270600,wire541200,wire1015808],
  [wire31744,wire33825,wire67679,wire135300,wire136164,wire270600,wire541200,wire1015808]]
private def pool7_60 : List (List (List T)) := [chunk6_101, chunk6_102, chunk6_103, chunk6_104, chunk6_107, chunk6_108, chunk6_109, chunk6_110, chunk6_111, chunk6_113]
private theorem checked7_60 : ∀ w ∈ chunk7_60, ¬ Need 7 w.toFinset := by
  have h : chunk7_60.all (routes 6 pool7_60.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_60,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_101 _ hm
  · exact checked6_102 _ hm
  · exact checked6_103 _ hm
  · exact checked6_104 _ hm
  · exact checked6_107 _ hm
  · exact checked6_108 _ hm
  · exact checked6_109 _ hm
  · exact checked6_110 _ hm
  · exact checked6_111 _ hm
  · exact checked6_113 _ hm
private def chunk7_61 : List (List T) := [[wire31744,wire33825,wire67679,wire136164,wire270600,wire541200,wire1015808],
  [wire31744,wire33855,wire34785,wire67650,wire135300,wire270600,wire541200,wire1015808]]
private def pool7_61 : List (List (List T)) := [chunk6_101, chunk6_103, chunk6_104, chunk6_105, chunk6_106, chunk6_107, chunk6_108, chunk6_109, chunk6_110, chunk6_111, chunk6_112, chunk6_113]
private theorem checked7_61 : ∀ w ∈ chunk7_61, ¬ Need 7 w.toFinset := by
  have h : chunk7_61.all (routes 6 pool7_61.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_61,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_101 _ hm
  · exact checked6_103 _ hm
  · exact checked6_104 _ hm
  · exact checked6_105 _ hm
  · exact checked6_106 _ hm
  · exact checked6_107 _ hm
  · exact checked6_108 _ hm
  · exact checked6_109 _ hm
  · exact checked6_110 _ hm
  · exact checked6_111 _ hm
  · exact checked6_112 _ hm
  · exact checked6_113 _ hm
#print axioms checked7_61
private def chunk8_0 : List (List T) := [[wire31,wire992,wire4096,wire33825,wire67650,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire65536,wire67650,wire135300,wire270600,wire541200],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire541200,wire1016800]]
private def pool8_0 : List (List (List T)) := [chunk7_0, chunk7_1, chunk7_2, chunk7_3, chunk7_4, chunk7_5, chunk7_9, chunk7_10, chunk7_15, chunk7_19, chunk7_20, chunk7_21, chunk7_22, chunk7_24, chunk7_31, chunk7_36, chunk7_37, chunk7_38, chunk7_39, chunk7_48, chunk7_49, chunk7_50, chunk7_51]
private theorem checked8_0 : ∀ w ∈ chunk8_0, ¬ Need 8 w.toFinset := by
  have h : chunk8_0.all (routes 7 pool8_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_0 _ hm
  · exact checked7_1 _ hm
  · exact checked7_2 _ hm
  · exact checked7_3 _ hm
  · exact checked7_4 _ hm
  · exact checked7_5 _ hm
  · exact checked7_9 _ hm
  · exact checked7_10 _ hm
  · exact checked7_15 _ hm
  · exact checked7_19 _ hm
  · exact checked7_20 _ hm
  · exact checked7_21 _ hm
  · exact checked7_22 _ hm
  · exact checked7_24 _ hm
  · exact checked7_31 _ hm
  · exact checked7_36 _ hm
  · exact checked7_37 _ hm
  · exact checked7_38 _ hm
  · exact checked7_39 _ hm
  · exact checked7_48 _ hm
  · exact checked7_49 _ hm
  · exact checked7_50 _ hm
  · exact checked7_51 _ hm
private def chunk8_1 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire541200,wire1016865],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire541200,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire541200,wire1032720]]
private def pool8_1 : List (List (List T)) := [chunk7_0, chunk7_2, chunk7_3, chunk7_4, chunk7_5, chunk7_6, chunk7_10, chunk7_16, chunk7_22, chunk7_23, chunk7_24, chunk7_25, chunk7_32, chunk7_37, chunk7_40, chunk7_41, chunk7_44, chunk7_52, chunk7_56]
private theorem checked8_1 : ∀ w ∈ chunk8_1, ¬ Need 8 w.toFinset := by
  have h : chunk8_1.all (routes 7 pool8_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_0 _ hm
  · exact checked7_2 _ hm
  · exact checked7_3 _ hm
  · exact checked7_4 _ hm
  · exact checked7_5 _ hm
  · exact checked7_6 _ hm
  · exact checked7_10 _ hm
  · exact checked7_16 _ hm
  · exact checked7_22 _ hm
  · exact checked7_23 _ hm
  · exact checked7_24 _ hm
  · exact checked7_25 _ hm
  · exact checked7_32 _ hm
  · exact checked7_37 _ hm
  · exact checked7_40 _ hm
  · exact checked7_41 _ hm
  · exact checked7_44 _ hm
  · exact checked7_52 _ hm
  · exact checked7_56 _ hm
private def chunk8_2 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire556560,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire575025,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire811800,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire1015808,wire1032720]]
private def pool8_2 : List (List (List T)) := [chunk7_2, chunk7_4, chunk7_5, chunk7_6, chunk7_7, chunk7_10, chunk7_11, chunk7_16, chunk7_17, chunk7_22, chunk7_23, chunk7_25, chunk7_26, chunk7_32, chunk7_33, chunk7_41, chunk7_44, chunk7_53, chunk7_56]
private theorem checked8_2 : ∀ w ∈ chunk8_2, ¬ Need 8 w.toFinset := by
  have h : chunk8_2.all (routes 7 pool8_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_2 _ hm
  · exact checked7_4 _ hm
  · exact checked7_5 _ hm
  · exact checked7_6 _ hm
  · exact checked7_7 _ hm
  · exact checked7_10 _ hm
  · exact checked7_11 _ hm
  · exact checked7_16 _ hm
  · exact checked7_17 _ hm
  · exact checked7_22 _ hm
  · exact checked7_23 _ hm
  · exact checked7_25 _ hm
  · exact checked7_26 _ hm
  · exact checked7_32 _ hm
  · exact checked7_33 _ hm
  · exact checked7_41 _ hm
  · exact checked7_44 _ hm
  · exact checked7_53 _ hm
  · exact checked7_56 _ hm
private def chunk8_3 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire1032720],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire304425,wire541200,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire541200,wire811800,wire1015808]]
private def pool8_3 : List (List (List T)) := [chunk7_0, chunk7_2, chunk7_3, chunk7_4, chunk7_6, chunk7_7, chunk7_8, chunk7_9, chunk7_11, chunk7_12, chunk7_13, chunk7_14, chunk7_16, chunk7_17, chunk7_18, chunk7_20, chunk7_21, chunk7_24, chunk7_25, chunk7_27, chunk7_28, chunk7_33, chunk7_34, chunk7_37, chunk7_42, chunk7_44, chunk7_49, chunk7_50, chunk7_53, chunk7_54, chunk7_57]
private theorem checked8_3 : ∀ w ∈ chunk8_3, ¬ Need 8 w.toFinset := by
  have h : chunk8_3.all (routes 7 pool8_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_0 _ hm
  · exact checked7_2 _ hm
  · exact checked7_3 _ hm
  · exact checked7_4 _ hm
  · exact checked7_6 _ hm
  · exact checked7_7 _ hm
  · exact checked7_8 _ hm
  · exact checked7_9 _ hm
  · exact checked7_11 _ hm
  · exact checked7_12 _ hm
  · exact checked7_13 _ hm
  · exact checked7_14 _ hm
  · exact checked7_16 _ hm
  · exact checked7_17 _ hm
  · exact checked7_18 _ hm
  · exact checked7_20 _ hm
  · exact checked7_21 _ hm
  · exact checked7_24 _ hm
  · exact checked7_25 _ hm
  · exact checked7_27 _ hm
  · exact checked7_28 _ hm
  · exact checked7_33 _ hm
  · exact checked7_34 _ hm
  · exact checked7_37 _ hm
  · exact checked7_42 _ hm
  · exact checked7_44 _ hm
  · exact checked7_49 _ hm
  · exact checked7_50 _ hm
  · exact checked7_53 _ hm
  · exact checked7_54 _ hm
  · exact checked7_57 _ hm
private def chunk8_4 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire541200,wire1015808,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire541200,wire1024264],
  [wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire811800,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire136164,wire270600,wire541200,wire1015808]]
private def pool8_4 : List (List (List T)) := [chunk7_0, chunk7_1, chunk7_3, chunk7_4, chunk7_5, chunk7_6, chunk7_7, chunk7_8, chunk7_9, chunk7_10, chunk7_12, chunk7_13, chunk7_14, chunk7_15, chunk7_18, chunk7_19, chunk7_20, chunk7_21, chunk7_27, chunk7_28, chunk7_29, chunk7_30, chunk7_34, chunk7_38, chunk7_39, chunk7_42, chunk7_49, chunk7_50, chunk7_51, chunk7_54, chunk7_55]
private theorem checked8_4 : ∀ w ∈ chunk8_4, ¬ Need 8 w.toFinset := by
  have h : chunk8_4.all (routes 7 pool8_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_0 _ hm
  · exact checked7_1 _ hm
  · exact checked7_3 _ hm
  · exact checked7_4 _ hm
  · exact checked7_5 _ hm
  · exact checked7_6 _ hm
  · exact checked7_7 _ hm
  · exact checked7_8 _ hm
  · exact checked7_9 _ hm
  · exact checked7_10 _ hm
  · exact checked7_12 _ hm
  · exact checked7_13 _ hm
  · exact checked7_14 _ hm
  · exact checked7_15 _ hm
  · exact checked7_18 _ hm
  · exact checked7_19 _ hm
  · exact checked7_20 _ hm
  · exact checked7_21 _ hm
  · exact checked7_27 _ hm
  · exact checked7_28 _ hm
  · exact checked7_29 _ hm
  · exact checked7_30 _ hm
  · exact checked7_34 _ hm
  · exact checked7_38 _ hm
  · exact checked7_39 _ hm
  · exact checked7_42 _ hm
  · exact checked7_49 _ hm
  · exact checked7_50 _ hm
  · exact checked7_51 _ hm
  · exact checked7_54 _ hm
  · exact checked7_55 _ hm
private def chunk8_5 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire169125,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire67650,wire270600,wire541200,wire1015808,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67650,wire270600,wire541200,wire1020036],
  [wire31,wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire541200,wire1015808]]
private def pool8_5 : List (List (List T)) := [chunk7_0, chunk7_9, chunk7_10, chunk7_11, chunk7_12, chunk7_13, chunk7_14, chunk7_15, chunk7_16, chunk7_17, chunk7_18, chunk7_19, chunk7_21, chunk7_30, chunk7_31, chunk7_35, chunk7_37, chunk7_38, chunk7_43, chunk7_50, chunk7_51, chunk7_55, chunk7_56, chunk7_57]
private theorem checked8_5 : ∀ w ∈ chunk8_5, ¬ Need 8 w.toFinset := by
  have h : chunk8_5.all (routes 7 pool8_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_0 _ hm
  · exact checked7_9 _ hm
  · exact checked7_10 _ hm
  · exact checked7_11 _ hm
  · exact checked7_12 _ hm
  · exact checked7_13 _ hm
  · exact checked7_14 _ hm
  · exact checked7_15 _ hm
  · exact checked7_16 _ hm
  · exact checked7_17 _ hm
  · exact checked7_18 _ hm
  · exact checked7_19 _ hm
  · exact checked7_21 _ hm
  · exact checked7_30 _ hm
  · exact checked7_31 _ hm
  · exact checked7_35 _ hm
  · exact checked7_37 _ hm
  · exact checked7_38 _ hm
  · exact checked7_43 _ hm
  · exact checked7_50 _ hm
  · exact checked7_51 _ hm
  · exact checked7_55 _ hm
  · exact checked7_56 _ hm
  · exact checked7_57 _ hm
private def chunk8_6 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire97346,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire31744,wire33825,wire101475,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire31775,wire33825,wire67650,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire64545,wire67650,wire135300,wire270600,wire541200,wire1015808]]
private def pool8_6 : List (List (List T)) := [chunk7_1, chunk7_14, chunk7_15, chunk7_16, chunk7_17, chunk7_18, chunk7_19, chunk7_23, chunk7_27, chunk7_31, chunk7_32, chunk7_33, chunk7_35, chunk7_36, chunk7_37, chunk7_43, chunk7_44, chunk7_45, chunk7_46, chunk7_48, chunk7_56, chunk7_57, chunk7_58, chunk7_59]
private theorem checked8_6 : ∀ w ∈ chunk8_6, ¬ Need 8 w.toFinset := by
  have h : chunk8_6.all (routes 7 pool8_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_1 _ hm
  · exact checked7_14 _ hm
  · exact checked7_15 _ hm
  · exact checked7_16 _ hm
  · exact checked7_17 _ hm
  · exact checked7_18 _ hm
  · exact checked7_19 _ hm
  · exact checked7_23 _ hm
  · exact checked7_27 _ hm
  · exact checked7_31 _ hm
  · exact checked7_32 _ hm
  · exact checked7_33 _ hm
  · exact checked7_35 _ hm
  · exact checked7_36 _ hm
  · exact checked7_37 _ hm
  · exact checked7_43 _ hm
  · exact checked7_44 _ hm
  · exact checked7_45 _ hm
  · exact checked7_46 _ hm
  · exact checked7_48 _ hm
  · exact checked7_56 _ hm
  · exact checked7_57 _ hm
  · exact checked7_58 _ hm
  · exact checked7_59 _ hm
private def chunk8_7 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire97346,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire541200,wire556560,wire1015808],
  [wire31,wire992,wire33825,wire67650,wire135300,wire270600,wire556560,wire1015808]]
private def pool8_7 : List (List (List T)) := [chunk7_19, chunk7_20, chunk7_21, chunk7_22, chunk7_23, chunk7_24, chunk7_25, chunk7_26, chunk7_27, chunk7_28, chunk7_29, chunk7_30, chunk7_31, chunk7_36, chunk7_45, chunk7_46, chunk7_47, chunk7_57, chunk7_58, chunk7_59]
private theorem checked8_7 : ∀ w ∈ chunk8_7, ¬ Need 8 w.toFinset := by
  have h : chunk8_7.all (routes 7 pool8_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_19 _ hm
  · exact checked7_20 _ hm
  · exact checked7_21 _ hm
  · exact checked7_22 _ hm
  · exact checked7_23 _ hm
  · exact checked7_24 _ hm
  · exact checked7_25 _ hm
  · exact checked7_26 _ hm
  · exact checked7_27 _ hm
  · exact checked7_28 _ hm
  · exact checked7_29 _ hm
  · exact checked7_30 _ hm
  · exact checked7_31 _ hm
  · exact checked7_36 _ hm
  · exact checked7_45 _ hm
  · exact checked7_46 _ hm
  · exact checked7_47 _ hm
  · exact checked7_57 _ hm
  · exact checked7_58 _ hm
  · exact checked7_59 _ hm
private def chunk8_8 : List (List T) := [[wire31,wire992,wire33825,wire67650,wire135300,wire294152,wire541200,wire1015808],
  [wire31,wire992,wire33825,wire97346,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire31744,wire33825,wire34785,wire67650,wire135300,wire270600,wire541200,wire1015808],
  [wire31,wire31744,wire33825,wire67650,wire135300,wire136164,wire270600,wire541200,wire1015808]]
private def pool8_8 : List (List (List T)) := [chunk7_20, chunk7_24, chunk7_25, chunk7_26, chunk7_27, chunk7_28, chunk7_29, chunk7_30, chunk7_31, chunk7_32, chunk7_33, chunk7_34, chunk7_35, chunk7_36, chunk7_37, chunk7_38, chunk7_39, chunk7_40, chunk7_43, chunk7_44, chunk7_45, chunk7_46, chunk7_47, chunk7_48, chunk7_58, chunk7_60, chunk7_61]
private theorem checked8_8 : ∀ w ∈ chunk8_8, ¬ Need 8 w.toFinset := by
  have h : chunk8_8.all (routes 7 pool8_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_20 _ hm
  · exact checked7_24 _ hm
  · exact checked7_25 _ hm
  · exact checked7_26 _ hm
  · exact checked7_27 _ hm
  · exact checked7_28 _ hm
  · exact checked7_29 _ hm
  · exact checked7_30 _ hm
  · exact checked7_31 _ hm
  · exact checked7_32 _ hm
  · exact checked7_33 _ hm
  · exact checked7_34 _ hm
  · exact checked7_35 _ hm
  · exact checked7_36 _ hm
  · exact checked7_37 _ hm
  · exact checked7_38 _ hm
  · exact checked7_39 _ hm
  · exact checked7_40 _ hm
  · exact checked7_43 _ hm
  · exact checked7_44 _ hm
  · exact checked7_45 _ hm
  · exact checked7_46 _ hm
  · exact checked7_47 _ hm
  · exact checked7_48 _ hm
  · exact checked7_58 _ hm
  · exact checked7_60 _ hm
  · exact checked7_61 _ hm
private def chunk8_9 : List (List T) := [[wire31,wire31744,wire33825,wire67650,wire136164,wire270600,wire541200,wire1015808],
  [wire992,wire31744,wire33825,wire33855,wire67650,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire31744,wire33825,wire67650,wire67679,wire135300,wire270600,wire541200,wire1015808],
  [wire992,wire31744,wire33825,wire67679,wire135300,wire270600,wire541200,wire1015808]]
private def pool8_9 : List (List (List T)) := [chunk7_37, chunk7_38, chunk7_39, chunk7_40, chunk7_41, chunk7_42, chunk7_43, chunk7_45, chunk7_46, chunk7_47, chunk7_48, chunk7_49, chunk7_50, chunk7_51, chunk7_52, chunk7_53, chunk7_54, chunk7_55, chunk7_56, chunk7_57, chunk7_58, chunk7_59, chunk7_60, chunk7_61]
private theorem checked8_9 : ∀ w ∈ chunk8_9, ¬ Need 8 w.toFinset := by
  have h : chunk8_9.all (routes 7 pool8_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_37 _ hm
  · exact checked7_38 _ hm
  · exact checked7_39 _ hm
  · exact checked7_40 _ hm
  · exact checked7_41 _ hm
  · exact checked7_42 _ hm
  · exact checked7_43 _ hm
  · exact checked7_45 _ hm
  · exact checked7_46 _ hm
  · exact checked7_47 _ hm
  · exact checked7_48 _ hm
  · exact checked7_49 _ hm
  · exact checked7_50 _ hm
  · exact checked7_51 _ hm
  · exact checked7_52 _ hm
  · exact checked7_53 _ hm
  · exact checked7_54 _ hm
  · exact checked7_55 _ hm
  · exact checked7_56 _ hm
  · exact checked7_57 _ hm
  · exact checked7_58 _ hm
  · exact checked7_59 _ hm
  · exact checked7_60 _ hm
  · exact checked7_61 _ hm
#print axioms checked8_9
private def chunk9_0 : List (List T) := [[wire31,wire992,wire31744,wire33825,wire67650,wire135300,wire270600,wire541200,wire1015808]]
private def pool9_0 : List (List (List T)) := [chunk8_0, chunk8_1, chunk8_2, chunk8_3, chunk8_4, chunk8_5, chunk8_6, chunk8_7, chunk8_8, chunk8_9]
private theorem checked9_0 : ∀ w ∈ chunk9_0, ¬ Need 9 w.toFinset := by
  have h : chunk9_0.all (routes 8 pool9_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool9_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked8_0 _ hm
  · exact checked8_1 _ hm
  · exact checked8_2 _ hm
  · exact checked8_3 _ hm
  · exact checked8_4 _ hm
  · exact checked8_5 _ hm
  · exact checked8_6 _ hm
  · exact checked8_7 _ hm
  · exact checked8_8 _ hm
  · exact checked8_9 _ hm
#print axioms checked9_0
private theorem root : safe 9 ins := initial checked9_0 (by decide +kernel)
def graph (u : Fin 4) (v : Fin 5) := (104317 : Nat).testBit (5 * u.val + v.val)
def row (i : Fin 20) : Fin 4 := ⟨i.val / 5, by have := i.isLt; omega⟩
def col (i : Fin 20) : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
def inputs (i : Fin 20) := PEqualNP.Represents.oneEach (row i) (col i)

theorem exactLower : ¬ PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 5) => (104317 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  rintro ⟨C, hg, hsize, he⟩
  apply exclude C.gates C.output (fun g hm => hg g hm) ins ins (fun ⦃_⦄ h => h) 9 hsize root
  intro k
  have hi : ∀ i : Fin 20, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 20, graph (row i) (col i) = bit i target := by decide +kernel
  have heval : C.eval (inputs k) = graph (row k) (col k) := he (row k) (col k)
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using heval

#print axioms exactLower


def circuit : Circuit :=
  { gates := [⟨.or,[0,2]⟩, ⟨.and,[9,6]⟩, ⟨.or,[1,3]⟩, ⟨.and,[11,5]⟩,
              ⟨.or,[7,8]⟩, ⟨.or,[0,1]⟩, ⟨.and,[13,14]⟩, ⟨.or,[4,10]⟩,
              ⟨.or,[12,15]⟩, ⟨.or,[16,17]⟩], output := 18 }
theorem upper : PEqualNP.Represents.RepSizeAtMost graph 10 := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
#print axioms upper
end Matrix104317
