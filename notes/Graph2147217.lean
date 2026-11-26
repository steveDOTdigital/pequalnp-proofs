import PEqualNP.Defs.Represents

-- The gate semantics and safety induction adapt the Apache-2.0 proof credited in Mask53Exact.lean.
-- Lewis Watson and Nico Habets developed the earlier gate enumeration.
-- Here the twenty-one table entries are all singleton and pair inputs on six pins.
namespace Graph2147217

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 21
private def ins : List T := [63, 1986, 30852, 233736, 860688, 1721376]
private def target : T := 39377
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => (z == u || z == ~~~u) ||
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

private inductive Op
  | zero | ones | wire (x : T) | inv (x : T) | meet (x y : T) | join (x y : T)
  deriving DecidableEq

private def Op.args : Op → List T
  | .zero | .ones => []
  | .wire x | .inv x => [x]
  | .meet x y | .join x y => [x,y]

private def Op.out : Op → T
  | .zero => 0
  | .ones => -1
  | .wire x => x
  | .inv x => ~~~x
  | .meet x y => x &&& y
  | .join x y => x ||| y

private theorem origin {w z} (hz : possible w z) :
    ∃ g : Op, g.out = z ∧ g.args ⊆ w := by
  simp only [possible,Bool.or_eq_true,List.any_eq_true,beq_iff_eq] at hz
  rcases hz with ((h | h) | ⟨x,hx,((h | h) | ⟨y,hy,h | h⟩)⟩) <;> subst z
  · exact ⟨.zero,rfl,by simp [Op.args]⟩
  · exact ⟨.ones,rfl,by simp [Op.args]⟩
  · exact ⟨.wire x,rfl,by simpa [Op.args] using hx⟩
  · exact ⟨.inv x,rfl,by simpa [Op.args] using hx⟩
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

private def absSep (x : T) (p q : Fin 21) : Prop := bit p x ≠ bit q x
private def down (x : T) (p q : Fin 21) : Prop := bit p x = true ∧ bit q x = false
private def covers (r : T → Fin 21 → Fin 21 → Prop) (s : Finset T) :=
  ∀ p q, down target p q → ∃ x ∈ s, r x p q

private theorem absFactors (g : Op) (p q) (h : absSep g.out p q) :
    ∃ x ∈ g.args, absSep x p q := by
  cases g
  case ones =>
    have ho : ∀ i : Fin 21, bit i (-1) = true := by decide +kernel
    exact False.elim (h ((ho p).trans (ho q).symm))
  all_goals simp [Op.out,Op.args,absSep,bit] at *
  all_goals grind

private theorem monoFactors (g : Op) :
    g.args.toFinset.card ≤ 1 ∨
    ∀ p q, down g.out p q → ∃ x ∈ g.args, down x p q := by
  cases g <;> simp [Op.out,Op.args,down,bit] at *
  all_goals grind

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

private theorem bound {n s} (h : Need n s) :
    s.card ≤ n+1 ∧ covers absSep s ∧ (s.card ≤ n ∨ covers down s) := by
  induction h with
  | output =>
    refine ⟨by simp,?_,.inr ?_⟩
    · intro p q h
      exact ⟨target,by simp,by simp [absSep,h.1,h.2]⟩
    · intro p q h
      exact ⟨target,by simp,h⟩
  | skip _ ih => exact ⟨by omega,ih.2.1,.inl ih.1⟩
  | @step n s g hm _ ih =>
    obtain ⟨hc,ha,hd⟩ := ih
    have hpos := Finset.card_pos.mpr ⟨g.out,hm⟩
    have he := Finset.card_erase_of_mem hm
    have hu := Finset.card_union_le (s.erase g.out) g.args.toFinset
    have hlen : g.args.toFinset.card ≤ 2 := by
      calc
        _ ≤ g.args.length := List.toFinset_card_le _
        _ ≤ 2 := by cases g <;> simp [Op.args]
    refine ⟨by omega,transfer ha (absFactors g),?_⟩
    rcases hd with hd | hd
    · exact .inl (by omega)
    · rcases monoFactors g with hh | hh
      · exact .inl (by omega)
      · exact .inr (transfer hd hh)
private def permit (directed : Bool) (x : T) (p : Fin 21) : T :=
  if bit p x then x else if directed then -1 else ~~~x

private def residue (d : Bool) (p : Fin 21) : List T → T
  | [] => ~~~target
  | x::xs => permit d x p &&& residue d p xs

private def rel : Bool → T → Fin 21 → Fin 21 → Prop
  | true => down
  | false => absSep

private theorem permit_bit (d x p q) : bit q (permit d x p) = true ↔ ¬ rel d x p q := by
  have ho : ∀ i : Fin 21, bit i (-1) = true := by decide +kernel
  cases d <;> cases a : bit p x <;> cases b : bit q x <;>
    simp [permit,rel,down,absSep,a,b,show bit q (~~~x) = !(bit q x) by simp [bit]]
  all_goals exact ho q

private theorem residue_bit (d p q) (w : List T) :
    bit q (residue d p w) = true ↔ bit q target = false ∧ ∀ x ∈ w, ¬ rel d x p q := by
  induction w with
  | nil => simp [residue,bit]
  | cons x xs ih =>
    have hb (a b : T) : bit q (a &&& b) = (bit q a && bit q b) := by simp [bit]
    rw [residue,hb]
    simp only [Bool.and_eq_true,permit_bit,ih,List.forall_mem_cons]
    tauto

private def viable (n : Nat) (w : List T) : Bool :=
  decide (w.toFinset.card ≤ n+1) &&
    decide (∀ p : Fin 21, bit p target = true →
      residue (decide (n < w.toFinset.card)) p w = 0)

private theorem fits {n w} (h : Need n w.toFinset) : viable n w = true := by
  obtain ⟨hc,ha,hd⟩ := bound h
  simp only [viable,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨hc,?_⟩
  intro p hp
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let q : Fin 21 := ⟨i,hi⟩
  have cv : covers (rel (decide (n < w.toFinset.card))) w.toFinset := by
    by_cases hs : n < w.toFinset.card
    · simpa [hs,rel] using hd.resolve_left (by omega)
    · simpa [hs,rel] using ha
  change bit q (residue _ p w) = bit q 0
  have hz : bit q 0 = false := by simp [bit]
  rw [hz]
  cases hb : bit q (residue _ p w) with
  | false => rfl
  | true =>
    obtain ⟨hq,hn⟩ := (residue_bit _ p q w).mp hb
    obtain ⟨x,hx,hr⟩ := cv p q ⟨hp,hq⟩
    exact False.elim (hn x (List.mem_toFinset.mp hx) hr)

private def ops (w : List T) : List Op :=
  .zero :: .ones :: w.flatMap (fun x => .wire x :: .inv x ::
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

-- Every listed set is checked against every possible next output and every reuse of its inputs.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def layer1 : List (List T) := []
private theorem good1 (w : List T) (h : w ∈ layer1) : ¬ Need 1 w.toFinset := by simp [layer1] at h
private def chunk2_0 : List (List T) := [[30,2057776]]
private theorem checked2_0 : ∀ w ∈ chunk2_0, ¬ Need 2 w.toFinset := by
  have h : chunk2_0.all (routes 1 layer1) = true := by decide +kernel
  intro w hw
  exact route_sound good1 ((List.all_eq_true.mp h) w hw)
private def chunks2 : List (List (List T)) := [chunk2_0]
private def layer2 := chunks2.flatten
private theorem good2 (w : List T) (hw : w ∈ layer2) : ¬ Need 2 w.toFinset := by
  obtain ⟨c,h,hc⟩ := List.mem_flatten.mp hw
  simp only [chunks2,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl
  · exact checked2_0 _ hc
private def chunk3_0 : List (List T) := [[30,860688,1721376],
  [63,187854,1721376],
  [63,262094,1795616],
  [63,860688,1721390],
  [63,1048542,2057776]]
private theorem checked3_0 : ∀ w ∈ chunk3_0, ¬ Need 3 w.toFinset := by
  have h : chunk3_0.all (routes 2 layer2) = true := by decide +kernel
  intro w hw
  exact route_sound good2 ((List.all_eq_true.mp h) w hw)
private def chunk3_1 : List (List T) := [[63,1721376,1909297],
  [63,1834990,2057776],
  [74303,262094,1721376],
  [860688,1721407,1834990]]
private theorem checked3_1 : ∀ w ∈ chunk3_1, ¬ Need 3 w.toFinset := by
  have h : chunk3_1.all (routes 2 layer2) = true := by decide +kernel
  intro w hw
  exact route_sound good2 ((List.all_eq_true.mp h) w hw)
private def chunks3 : List (List (List T)) := [chunk3_0, chunk3_1]
private def layer3 := chunks3.flatten
private theorem good3 (w : List T) (hw : w ∈ layer3) : ¬ Need 3 w.toFinset := by
  obtain ⟨c,h,hc⟩ := List.mem_flatten.mp hw
  simp only [chunks3,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl
  · exact checked3_0 _ hc
  · exact checked3_1 _ hc
private def chunk4_0 : List (List T) := [[14,63,860688,1721376],
  [63,1986,860688,1721388],
  [63,1986,1047452,2057776],
  [63,1986,1834412,2057776],
  [63,1998,860688,1721376]]
private theorem checked4_0 : ∀ w ∈ chunk4_0, ¬ Need 4 w.toFinset := by
  have h : chunk4_0.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_1 : List (List T) := [[63,30852,860688,1721386],
  [63,30852,1030106,2057776],
  [63,30852,1824746,2057776],
  [63,30862,860688,1721376],
  [63,32710,860688,1721384]]
private theorem checked4_1 : ∀ w ∈ chunk4_1, ¬ Need 4 w.toFinset := by
  have h : chunk4_1.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_2 : List (List T) := [[63,32710,1028888,2057776],
  [63,32710,1824040,2057776],
  [63,32718,860688,1721376],
  [63,74240,262094,1721376],
  [63,233736,860688,1721382]]
private theorem checked4_2 : ∀ w ∈ chunk4_2, ¬ Need 4 w.toFinset := by
  have h : chunk4_2.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_3 : List (List T) := [[63,233736,884694,2057776],
  [63,233736,1736678,2057776],
  [63,233742,860688,1721376],
  [63,235466,860688,1721380],
  [63,235466,883348,2057776]]
private theorem checked4_3 : ∀ w ∈ chunk4_3, ¬ Need 4 w.toFinset := by
  have h : chunk4_3.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_4 : List (List T) := [[63,235466,1735844,2057776],
  [63,235470,860688,1721376],
  [63,260492,860688,1721378],
  [63,260492,862162,2057776],
  [63,260492,1722338,2057776]]
private theorem checked4_4 : ∀ w ∈ chunk4_4, ¬ Need 4 w.toFinset := by
  have h : chunk4_4.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_5 : List (List T) := [[63,260494,860688,1721376],
  [63,262094,375775,860688],
  [63,262094,860688,1721376],
  [63,262094,860688,2057776],
  [63,262094,860735,1721376]]
private theorem checked4_5 : ∀ w ∈ chunk4_5, ¬ Need 4 w.toFinset := by
  have h : chunk4_5.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_6 : List (List T) := [[63,262094,1236463,1721376],
  [63,262094,1721376,2057776],
  [63,860688,1048542,1721376],
  [63,860688,1721376,1834990],
  [63,860688,1721376,1835057]]
private theorem checked4_6 : ∀ w ∈ chunk4_6, ¬ Need 4 w.toFinset := by
  have h : chunk4_6.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_7 : List (List T) := [[1986,860688,1721407,1834412],
  [30852,860688,1721407,1824746],
  [32710,860688,1721407,1824040],
  [233736,860688,1721407,1736678],
  [235466,860688,1721407,1735844]]
private theorem checked4_7 : ∀ w ∈ chunk4_7, ¬ Need 4 w.toFinset := by
  have h : chunk4_7.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_8 : List (List T) := [[260492,860688,1721407,1722338],
  [262094,860688,1721376,1721407],
  [262094,860688,1721376,2097088]]
private theorem checked4_8 : ∀ w ∈ chunk4_8, ¬ Need 4 w.toFinset := by
  have h : chunk4_8.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunks4 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_2, chunk4_3, chunk4_4, chunk4_5, chunk4_6, chunk4_7, chunk4_8]
private def layer4 := chunks4.flatten
private theorem good4 (w : List T) (hw : w ∈ layer4) : ¬ Need 4 w.toFinset := by
  obtain ⟨c,h,hc⟩ := List.mem_flatten.mp hw
  simp only [chunks4,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hc
  · exact checked4_1 _ hc
  · exact checked4_2 _ hc
  · exact checked4_3 _ hc
  · exact checked4_4 _ hc
  · exact checked4_5 _ hc
  · exact checked4_6 _ hc
  · exact checked4_7 _ hc
  · exact checked4_8 _ hc
private def chunk5_0 : List (List T) := [[2,63,260492,860688,1721376],
  [4,63,235466,860688,1721376],
  [6,63,233736,860688,1721376],
  [8,63,32710,860688,1721376],
  [10,63,30852,860688,1721376]]
private theorem checked5_0 : ∀ w ∈ chunk5_0, ¬ Need 5 w.toFinset := by
  have h : chunk5_0.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_1 : List (List T) := [[12,63,1986,860688,1721376],
  [63,1986,30852,860688,1721384],
  [63,1986,30852,1028888,2057776],
  [63,1986,30852,1824040,2057776],
  [63,1986,30860,860688,1721376]]
private theorem checked5_1 : ∀ w ∈ chunk5_1, ¬ Need 5 w.toFinset := by
  have h : chunk5_1.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_2 : List (List T) := [[63,1986,233736,860688,1721380],
  [63,1986,233736,883348,2057776],
  [63,1986,233736,1735844,2057776],
  [63,1986,233740,860688,1721376],
  [63,1986,260492,375775,860688]]
private theorem checked5_2 : ∀ w ∈ chunk5_2, ¬ Need 5 w.toFinset := by
  have h : chunk5_2.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_3 : List (List T) := [[63,1986,260492,860688,1721376],
  [63,1986,260492,860688,2057776],
  [63,1986,260492,860735,1721376],
  [63,1986,260492,1236463,1721376],
  [63,1986,260492,1721376,2057776]]
private theorem checked5_3 : ∀ w ∈ chunk5_3, ¬ Need 5 w.toFinset := by
  have h : chunk5_3.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_4 : List (List T) := [[63,1986,262094,860688,1721376],
  [63,1986,860688,1047452,1721376],
  [63,1986,860688,1721376,1834412],
  [63,1986,860688,1721376,1836659],
  [63,1990,233736,860688,1721376]]
private theorem checked5_4 : ∀ w ∈ chunk5_4, ¬ Need 5 w.toFinset := by
  have h : chunk5_4.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_5 : List (List T) := [[63,1994,30852,860688,1721376],
  [63,30852,233736,860688,1721378],
  [63,30852,233736,862162,2057776],
  [63,30852,233736,1722338,2057776],
  [63,30852,233738,860688,1721376]]
private theorem checked5_5 : ∀ w ∈ chunk5_5, ¬ Need 5 w.toFinset := by
  have h : chunk5_5.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_6 : List (List T) := [[63,30852,235466,375775,860688],
  [63,30852,235466,860688,1721376],
  [63,30852,235466,860688,2057776],
  [63,30852,235466,860735,1721376],
  [63,30852,235466,1236463,1721376]]
private theorem checked5_6 : ∀ w ∈ chunk5_6, ¬ Need 5 w.toFinset := by
  have h : chunk5_6.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_7 : List (List T) := [[63,30852,235466,1721376,2057776],
  [63,30852,262094,860688,1721376],
  [63,30852,860688,1030106,1721376],
  [63,30852,860688,1721376,1824746],
  [63,30852,860688,1721376,1861685]]
private theorem checked5_7 : ∀ w ∈ chunk5_7, ¬ Need 5 w.toFinset := by
  have h : chunk5_7.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_8 : List (List T) := [[63,30854,233736,860688,1721376],
  [63,32710,233736,375775,860688],
  [63,32710,233736,860688,1721376],
  [63,32710,233736,860688,2057776],
  [63,32710,233736,860735,1721376]]
private theorem checked5_8 : ∀ w ∈ chunk5_8, ¬ Need 5 w.toFinset := by
  have h : chunk5_8.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_9 : List (List T) := [[63,32710,233736,1236463,1721376],
  [63,32710,233736,1721376,2057776],
  [63,32710,235466,860688,1721376],
  [63,32710,260492,860688,1721376],
  [63,32710,262094,860688,1721376]]
private theorem checked5_9 : ∀ w ∈ chunk5_9, ¬ Need 5 w.toFinset := by
  have h : chunk5_9.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_10 : List (List T) := [[63,32710,860688,1028888,1721376],
  [63,32710,860688,1721376,1824040],
  [63,32710,860688,1721376,1863415],
  [63,233736,262094,860688,1721376],
  [63,233736,860688,884694,1721376]]
private theorem checked5_10 : ∀ w ∈ chunk5_10, ¬ Need 5 w.toFinset := by
  have h : chunk5_10.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_11 : List (List T) := [[63,233736,860688,1721376,1736678],
  [63,233736,860688,1721376,2064441],
  [63,235466,260492,860688,1721376],
  [63,235466,262094,860688,1721376],
  [63,235466,860688,883348,1721376]]
private theorem checked5_11 : ∀ w ∈ chunk5_11, ¬ Need 5 w.toFinset := by
  have h : chunk5_11.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_12 : List (List T) := [[63,235466,860688,1721376,1735844],
  [63,235466,860688,1721376,2066299],
  [63,260492,262094,860688,1721376],
  [63,260492,860688,862162,1721376],
  [63,260492,860688,1721376,1722338]]
private theorem checked5_12 : ∀ w ∈ chunk5_12, ¬ Need 5 w.toFinset := by
  have h : chunk5_12.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_13 : List (List T) := [[63,260492,860688,1721376,2095165],
  [63,262094,860688,1721376],
  [1986,30852,860688,1721407,1824040],
  [1986,233736,860688,1721407,1735844],
  [1986,260492,860688,1721376,1721407]]
private theorem checked5_13 : ∀ w ∈ chunk5_13, ¬ Need 5 w.toFinset := by
  have h : chunk5_13.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_14 : List (List T) := [[1986,260492,860688,1721376,2097088],
  [30852,233736,860688,1721407,1722338],
  [30852,235466,860688,1721376,1721407],
  [30852,235466,860688,1721376,2097088],
  [32710,233736,860688,1721376,1721407]]
private theorem checked5_14 : ∀ w ∈ chunk5_14, ¬ Need 5 w.toFinset := by
  have h : chunk5_14.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_15 : List (List T) := [[32710,233736,860688,1721376,2097088]]
private theorem checked5_15 : ∀ w ∈ chunk5_15, ¬ Need 5 w.toFinset := by
  have h : chunk5_15.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunks5 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_2, chunk5_3, chunk5_4, chunk5_5, chunk5_6, chunk5_7, chunk5_8, chunk5_9, chunk5_10, chunk5_11, chunk5_12, chunk5_13, chunk5_14, chunk5_15]
private def layer5 := chunks5.flatten
private theorem good5 (w : List T) (hw : w ∈ layer5) : ¬ Need 5 w.toFinset := by
  obtain ⟨c,h,hc⟩ := List.mem_flatten.mp hw
  simp only [chunks5,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hc
  · exact checked5_1 _ hc
  · exact checked5_2 _ hc
  · exact checked5_3 _ hc
  · exact checked5_4 _ hc
  · exact checked5_5 _ hc
  · exact checked5_6 _ hc
  · exact checked5_7 _ hc
  · exact checked5_8 _ hc
  · exact checked5_9 _ hc
  · exact checked5_10 _ hc
  · exact checked5_11 _ hc
  · exact checked5_12 _ hc
  · exact checked5_13 _ hc
  · exact checked5_14 _ hc
  · exact checked5_15 _ hc
private def chunk6_0 : List (List T) := [[2,63,30852,233736,860688,1721376],
  [4,63,1986,233736,860688,1721376],
  [8,63,1986,30852,860688,1721376],
  [63,1986,30852,233736,375775,860688],
  [63,1986,30852,233736,860688,1721376]]
private theorem checked6_0 : ∀ w ∈ chunk6_0, ¬ Need 6 w.toFinset := by
  have h : chunk6_0.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_1 : List (List T) := [[63,1986,30852,233736,860688,2057776],
  [63,1986,30852,233736,860735,1721376],
  [63,1986,30852,233736,1236463,1721376],
  [63,1986,30852,233736,1721376,2057776],
  [63,1986,30852,235466,860688,1721376]]
private theorem checked6_1 : ∀ w ∈ chunk6_1, ¬ Need 6 w.toFinset := by
  have h : chunk6_1.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_2 : List (List T) := [[63,1986,30852,260492,860688,1721376],
  [63,1986,30852,860688,1028888,1721376],
  [63,1986,30852,860688,1721376,1824040],
  [63,1986,30852,860688,1721376,1863415],
  [63,1986,32710,233736,860688,1721376]]
private theorem checked6_2 : ∀ w ∈ chunk6_2, ¬ Need 6 w.toFinset := by
  have h : chunk6_2.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_3 : List (List T) := [[63,1986,233736,260492,860688,1721376],
  [63,1986,233736,860688,883348,1721376],
  [63,1986,233736,860688,1721376,1735844],
  [63,1986,233736,860688,1721376,2066299],
  [63,1986,260492,860688,1721376]]
private theorem checked6_3 : ∀ w ∈ chunk6_3, ¬ Need 6 w.toFinset := by
  have h : chunk6_3.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_4 : List (List T) := [[63,30852,32710,233736,860688,1721376],
  [63,30852,233736,235466,860688,1721376],
  [63,30852,233736,860688,862162,1721376],
  [63,30852,233736,860688,1721376,1722338],
  [63,30852,233736,860688,1721376,2095165]]
private theorem checked6_4 : ∀ w ∈ chunk6_4, ¬ Need 6 w.toFinset := by
  have h : chunk6_4.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_5 : List (List T) := [[63,30852,235466,860688,1721376],
  [63,32710,233736,860688,1721376],
  [1986,30852,233736,860688,1721376,1721407],
  [1986,30852,233736,860688,1721376,2097088]]
private theorem checked6_5 : ∀ w ∈ chunk6_5, ¬ Need 6 w.toFinset := by
  have h : chunk6_5.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunks6 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_3, chunk6_4, chunk6_5]
private def layer6 := chunks6.flatten
private theorem good6 (w : List T) (hw : w ∈ layer6) : ¬ Need 6 w.toFinset := by
  obtain ⟨c,h,hc⟩ := List.mem_flatten.mp hw
  simp only [chunks6,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hc
  · exact checked6_1 _ hc
  · exact checked6_2 _ hc
  · exact checked6_3 _ hc
  · exact checked6_4 _ hc
  · exact checked6_5 _ hc
private def chunk7_0 : List (List T) := [[63,1986,30852,233736,860688,1721376]]
private theorem checked7_0 : ∀ w ∈ chunk7_0, ¬ Need 7 w.toFinset := by
  have h : chunk7_0.all (routes 6 layer6) = true := by decide +kernel
  intro w hw
  exact route_sound good6 ((List.all_eq_true.mp h) w hw)
private def chunks7 : List (List (List T)) := [chunk7_0]
private def layer7 := chunks7.flatten
private theorem good7 (w : List T) (hw : w ∈ layer7) : ¬ Need 7 w.toFinset := by
  obtain ⟨c,h,hc⟩ := List.mem_flatten.mp hw
  simp only [chunks7,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl
  · exact checked7_0 _ hc
private theorem root : safe 7 ins := initial good7 (by decide +kernel)
private def samples : Fin 21 → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
private def inputs (i : Fin 21) :=
  List.ofFn fun k : Fin 6 => decide (k = (samples i).1 ∨ k = (samples i).2)

private theorem tables (C : Circuit)
    (he : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2147217 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :
    ∀ k, (C.gates.foldl step (ins.map (bit k))).getD C.output false = bit k target := by
  intro k
  have hi : ∀ i : Fin 21, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 21, (2147217 : Nat).testBit
      (6 * min (samples i).1.val (samples i).2.val + max (samples i).1.val (samples i).2.val) = bit i target := by decide +kernel
  have h := he (samples k).1 (samples k).2
  change C.eval (inputs k) = _ at h
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using h

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (2147217 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hg,hs,he⟩
  exact exclude C.gates C.output (fun g hm => hg g hm) ins ins
    (fun ⦃_⦄ hx => hx) 7 hs root (tables C he)

#print axioms generalLower

-- Eight gates suffice on all 36 ordered input pairs.
def circuit : Circuit :=
  { gates := [⟨.not,[0]⟩, ⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩,
              ⟨.or,[9,5]⟩, ⟨.and,[4,6]⟩, ⟨.or,[11,10]⟩, ⟨.not,[12]⟩], output := 13 }

theorem eight : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (2147217 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms eight
end Graph2147217
