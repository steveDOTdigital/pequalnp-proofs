import PEqualNP.Defs.Represents

-- The gate semantics and safety induction adapt the Apache-2.0 proof credited in Mask53Exact.lean.
-- Lewis Watson and Nico Habets developed the earlier gate enumeration.
-- Here the twenty-one table entries are all singleton and pair inputs on six pins.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Graph2215743

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev K := 98
private abbrev T := BitVec (2*K)
private def ins : List T := [(((0x3ff : T) <<< 32) ||| 0xffffffff), (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x3f80), (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x1fc000), (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe00000), (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xf0000000), (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x800003f8) <<< 32) ||| 0x0)]
private def target : T := BitVec.zeroExtend (2*K) (-1 : BitVec K)
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => (z == u || z == ~~~u) ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin (2*K)) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin (2*K)) :
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
        · rw [h]; simp [possible, show BitVec.allOnes (2*K) = (-1 : T) by decide +kernel]
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

private def absSep (x : T) (p q : Fin (2*K)) : Prop := bit p x ≠ bit q x
private def down (x : T) (p q : Fin (2*K)) : Prop := bit p x = true ∧ bit q x = false
private def covers (r : T → Fin (2*K) → Fin (2*K) → Prop) (s : Finset T) :=
  ∀ p q, down target p q → ∃ x ∈ s, r x p q

private theorem absFactors (g : Op) (p q) (h : absSep g.out p q) :
    ∃ x ∈ g.args, absSep x p q := by
  cases g
  case ones =>
    have ho : ∀ i : Fin (2*K), bit i (-1) = true := by decide +kernel
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
private def feature (d : Bool) (x : T) : T :=
  let neg := x >>> K
  if d then x &&& ~~~neg else x ^^^ neg

private def joint (d : Bool) : List T → T
  | [] => 0
  | x::w => feature d x ||| joint d w

private theorem memberOn {x w d p} (hw : x ∈ w) (hv : bit p (feature d x) = true) :
    bit p (joint d w) = true := by
  induction w with
  | nil => simp at hw
  | cons y ys ih =>
    have hOr (a b : T) : bit p (a ||| b) = (bit p a || bit p b) := by simp [bit]
    rw [joint,hOr,Bool.or_eq_true]; rcases List.mem_cons.mp hw with rfl | hm
    · exact Or.inl hv
    · exact Or.inr (ih hm)

private def viable (n : Nat) (w : List T) : Bool :=
  decide (w.toFinset.card ≤ n+1) &&
  (joint (decide (n < w.toFinset.card)) w &&& target == target)

private theorem cutBits : ∀ p : Fin (2*K), bit p target = decide (p.val < K) := by decide +kernel

private theorem fits {n w} (h : Need n w.toFinset) : viable n w = true := by
  obtain ⟨hc,ha,hd⟩ := bound h
  simp only [viable,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  refine ⟨hc,?_⟩
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let p : Fin (2*K) := ⟨i,hi⟩
  have hb (a b : T) : bit p (a &&& b) = (bit p a && bit p b) := by simp [bit]
  change bit p (_ &&& target) = bit p target
  rw [hb]
  by_cases hp : i < K
  · let q : Fin (2*K) := ⟨i+K, by omega⟩
    have htp : bit p target = true := by simpa [p,hp] using cutBits p
    have htq : bit q target = false := by simpa [q] using cutBits q
    have shifted (x : T) : bit p (x >>> K) = bit q x := by
      change (x >>> K)[i] = x[i+K]
      simp only [BitVec.getElem_ushiftRight,Nat.add_comm K i]
      exact BitVec.getLsbD_eq_getElem q.isLt
    let d := decide (n < w.toFinset.card)
    have H : ∃ x ∈ w.toFinset, bit p (feature d x) = true := by
      by_cases hs : n < w.toFinset.card
      · obtain ⟨x,hx,htrue,hfalse⟩ := hd.resolve_left (by omega) p q ⟨htp,htq⟩
        refine ⟨x,hx,?_⟩
        change bit p (feature (decide (n < w.toFinset.card)) x) = true
        simp only [feature,hs,decide_true,ite_true,hb]
        have hnot : bit p (~~~(x >>> K)) = !(bit p (x >>> K)) := by simp [bit]
        simp [hnot,shifted,htrue,hfalse]
      · obtain ⟨x,hx,hne⟩ := ha p q ⟨htp,htq⟩
        refine ⟨x,hx,?_⟩
        change bit p (feature (decide (n < w.toFinset.card)) x) = true
        have hxor : bit p (x ^^^ (x >>> K)) = Bool.xor (bit p x) (bit p (x >>> K)) := by simp [bit]
        simp only [feature,hs,decide_false,ite_false,hxor,shifted]
        change bit p x ≠ bit q x at hne
        cases a : bit p x <;> cases b : bit q x <;> simp_all
    obtain ⟨x,hx,hh⟩ := H
    have hh' := memberOn (List.mem_toFinset.mp hx) hh
    change (bit p (joint d w) && bit p target) = bit p target
    simp [hh']
  · have htp : bit p target = false := by simpa [p,hp] using cutBits p
    simp [htp]
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
private def wire0 : T := (0x0 : T)
private def wire2 : T := (0x3f80 : T)
private def wire4 : T := (0x1fc000 : T)
private def wire8 : T := (0xfe00000 : T)
private def wire16 : T := (((0x7 : T) <<< 32) ||| 0xf0000000)
private def wire32 : T := (((0x3f8 : T) <<< 32) ||| 0x0)
private def wire55 : T := (((0x3ff : T) <<< 32) ||| 0xf01fffff)
private def wire59 : T := (((0x3ff : T) <<< 32) ||| 0xffe03fff)
private def wire63 : T := (((0x3ff : T) <<< 32) ||| 0xffffffff)
private def wire128 : T := (((0x1fc00 : T) <<< 32) ||| 0x0)
private def wire191 : T := (((0x1ffff : T) <<< 32) ||| 0xffffffff)
private def wire256 : T := (((0xfe0000 : T) <<< 32) ||| 0x0)
private def wire258 : T := (((0xfe0000 : T) <<< 32) ||| 0x3f80)
private def wire264 : T := (((0xfe0000 : T) <<< 32) ||| 0xfe00000)
private def wire319 : T := (((0xfe03ff : T) <<< 32) ||| 0xffffffff)
private def wire384 : T := (((0xfffc00 : T) <<< 32) ||| 0x0)
private def wire447 : T := (((0xffffff : T) <<< 32) ||| 0xffffffff)
private def wire512 : T := (((0x7f000000 : T) <<< 32) ||| 0x0)
private def wire575 : T := (((0x7f0003ff : T) <<< 32) ||| 0xffffffff)
private def wire768 : T := (((0x7ffe0000 : T) <<< 32) ||| 0x0)
private def wire831 : T := (((0x7ffe03ff : T) <<< 32) ||| 0xffffffff)
private def wire1024 : T := (((((0x3f : T) <<< 32) ||| 0x80000000) <<< 32) ||| 0x0)
private def wire1087 : T := (((((0x3f : T) <<< 32) ||| 0x800003ff) <<< 32) ||| 0xffffffff)
private def wire1280 : T := (((((0x3f : T) <<< 32) ||| 0x80fe0000) <<< 32) ||| 0x0)
private def wire1343 : T := (((((0x3f : T) <<< 32) ||| 0x80fe03ff) <<< 32) ||| 0xffffffff)
private def wire1536 : T := (((((0x3f : T) <<< 32) ||| 0xff000000) <<< 32) ||| 0x0)
private def wire1599 : T := (((((0x3f : T) <<< 32) ||| 0xff0003ff) <<< 32) ||| 0xffffffff)
private def wire1602 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xff000000) <<< 32) ||| 0x3f80)
private def wire1728 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xff01fc00) <<< 32) ||| 0x0)
private def wire1730 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xff01fc00) <<< 32) ||| 0x3f80)
private def wire1783 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xff01ffff) <<< 32) ||| 0xf01fffff)
private def wire1791 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xff01ffff) <<< 32) ||| 0xffffffff)
private def wire1858 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffe0000) <<< 32) ||| 0x3f80)
private def wire1984 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x0)
private def wire1986 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x3f80)
private def wire1990 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x1fff80)
private def wire1994 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0xfe03f80)
private def wire2002 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc07) <<< 32) ||| 0xf0003f80)
private def wire2018 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffff8) <<< 32) ||| 0x3f80)
private def wire2047 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x3f) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire4096 : T := (((((0xfe000 : T) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire4159 : T := (((((0xfe000 : T) <<< 32) ||| 0x3ff) <<< 32) ||| 0xffffffff)
private def wire4352 : T := (((((0xfe000 : T) <<< 32) ||| 0xfe0000) <<< 32) ||| 0x0)
private def wire4415 : T := (((((0xfe000 : T) <<< 32) ||| 0xfe03ff) <<< 32) ||| 0xffffffff)
private def wire6082 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0xfe03f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x3f80)
private def wire8192 : T := (((((0x7f00000 : T) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire8255 : T := (((((0x7f00000 : T) <<< 32) ||| 0x3ff) <<< 32) ||| 0xffffffff)
private def wire8320 : T := (((((0x7f00000 : T) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x0)
private def wire8383 : T := (((((0x7f00000 : T) <<< 32) ||| 0x1ffff) <<< 32) ||| 0xffffffff)
private def wire10178 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810204) <<< 32) ||| 0x7f0003f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x3f80)
private def wire14468 : T := (((((0x7ffffc0 : T) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x1fc000)
private def wire14527 : T := (((((0x7ffffc0 : T) <<< 32) ||| 0x1ffff) <<< 32) ||| 0xffffffff)
private def wire16384 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x0) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire16447 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff) <<< 32) ||| 0xffffffff)
private def wire18370 : T := (((((((((((0x60c18306 : T) <<< 32) ||| 0xc183060) <<< 32) ||| 0xc183060c) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x3f80)
private def wire26756 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7f01fc0) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x1fc000)
private def wire28358 : T := (((((((((((0x60c18306 : T) <<< 32) ||| 0xc183060) <<< 32) ||| 0xc183060c) <<< 32) ||| 0x7f01fff) <<< 32) ||| 0xff01fc00) <<< 32) ||| 0x1fff80)
private def wire30848 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x0)
private def wire30852 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x1fc000)
private def wire30854 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x1fff80)
private def wire30860 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fc00) <<< 32) ||| 0xfffc000)
private def wire30868 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fc07) <<< 32) ||| 0xf01fc000)
private def wire30884 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fff8) <<< 32) ||| 0x1fc000)
private def wire30911 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1ffff) <<< 32) ||| 0xffffffff)
private def wire31108 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0xfffc00) <<< 32) ||| 0x1fc000)
private def wire31110 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0xfffc00) <<< 32) ||| 0x1fff80)
private def wire31116 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0xfffc00) <<< 32) ||| 0xfffc000)
private def wire31167 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0xffffff) <<< 32) ||| 0xffffffff)
private def wire31364 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x7f01fc00) <<< 32) ||| 0x1fc000)
private def wire31620 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x7ffffc00) <<< 32) ||| 0x1fc000)
private def wire31876 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0x8001fc00) <<< 32) ||| 0x1fc000)
private def wire32132 : T := (((((((((((0x40810204 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0x80fffc00) <<< 32) ||| 0x1fc000)
private def wire32454 : T := (((((((((((0x60c18306 : T) <<< 32) ||| 0xc183060) <<< 32) ||| 0xc183060c) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0xff01fc00) <<< 32) ||| 0x1fff80)
private def wire32710 : T := (((((((((((0x60c18306 : T) <<< 32) ||| 0xc183060) <<< 32) ||| 0xc183060c) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x1fff80)
private def wire32767 : T := (((((((((((0x60c18306 : T) <<< 32) ||| 0xc183060) <<< 32) ||| 0xc183060c) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire39375 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810207) <<< 32) ||| 0xf80fffc0) <<< 32) ||| 0xfffc00) <<< 32) ||| 0xfffffff)
private def wire40911 : T := (((((((((((0x20408102 : T) <<< 32) ||| 0x4081020) <<< 32) ||| 0x40810207) <<< 32) ||| 0xf80fffff) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0xfffffff)
private def wire65536 : T := (((((((((((0x81020408 : T) <<< 32) ||| 0x10204081) <<< 32) ||| 0x2040810) <<< 32) ||| 0x0) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire65599 : T := (((((((((((0x81020408 : T) <<< 32) ||| 0x10204081) <<< 32) ||| 0x2040810) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff) <<< 32) ||| 0xffffffff)
private def wire65792 : T := (((((((((((0x81020408 : T) <<< 32) ||| 0x10204081) <<< 32) ||| 0x2040810) <<< 32) ||| 0x0) <<< 32) ||| 0xfe0000) <<< 32) ||| 0x0)
private def wire66048 : T := (((((((((((0x81020408 : T) <<< 32) ||| 0x10204081) <<< 32) ||| 0x2040810) <<< 32) ||| 0x0) <<< 32) ||| 0x7f000000) <<< 32) ||| 0x0)
private def wire67522 : T := (((((((((((0xa142850a : T) <<< 32) ||| 0x142850a1) <<< 32) ||| 0x42850a14) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x3f80)
private def wire96388 : T := (((((((((((0xc183060c : T) <<< 32) ||| 0x183060c1) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x1fc000)
private def wire102664 : T := (((((((((((0x81020408 : T) <<< 32) ||| 0x10204081) <<< 32) ||| 0x2040813) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe00000)
private def wire131072 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x2040810) <<< 32) ||| 0x20408102) <<< 32) ||| 0x4081020) <<< 32) ||| 0x0) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire131135 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x2040810) <<< 32) ||| 0x20408102) <<< 32) ||| 0x4081020) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff) <<< 32) ||| 0xffffffff)
private def wire131328 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x2040810) <<< 32) ||| 0x20408102) <<< 32) ||| 0x4081020) <<< 32) ||| 0x0) <<< 32) ||| 0xfe0000) <<< 32) ||| 0x0)
private def wire133058 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x22448912) <<< 32) ||| 0x24489122) <<< 32) ||| 0x44891224) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x3f80)
private def wire161924 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x42850a14) <<< 32) ||| 0x2850a142) <<< 32) ||| 0x850a1428) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x1fc000)
private def wire162180 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x42850a14) <<< 32) ||| 0x2850a142) <<< 32) ||| 0x850a1428) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0xfffc00) <<< 32) ||| 0x1fc000)
private def wire168200 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x2040810) <<< 32) ||| 0x20408102) <<< 32) ||| 0x4081023) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe00000)
private def wire194956 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x42850a14) <<< 32) ||| 0x2850a142) <<< 32) ||| 0x850a142b) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0xfffc00) <<< 32) ||| 0xfffc000)
private def wire198144 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1830) <<< 32) ||| 0x3f) <<< 32) ||| 0xff000000) <<< 32) ||| 0x0)
private def wire229640 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf8000000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe00000)
private def wire233728 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0x0)
private def wire233736 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe00000)
private def wire233738 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe03f80)
private def wire233740 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfffc000)
private def wire233752 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0007) <<< 32) ||| 0xffe00000)
private def wire233768 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe03f8) <<< 32) ||| 0xfe00000)
private def wire233791 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe03ff) <<< 32) ||| 0xffffffff)
private def wire233864 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfffc00) <<< 32) ||| 0xfe00000)
private def wire234248 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0x7ffe0000) <<< 32) ||| 0xfe00000)
private def wire234760 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xf80fe03f) <<< 32) ||| 0x80fe0000) <<< 32) ||| 0xfe00000)
private def wire235466 : T := (((((((((((((0x1 : T) <<< 32) ||| 0xa3468d1a) <<< 32) ||| 0x3468d1a3) <<< 32) ||| 0x468d1a37) <<< 32) ||| 0xf80fe03f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0xfe03f80)
private def wire235519 : T := (((((((((((((0x1 : T) <<< 32) ||| 0xa3468d1a) <<< 32) ||| 0x3468d1a3) <<< 32) ||| 0x468d1a37) <<< 32) ||| 0xf80fe03f) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire241928 : T := (((((((((((((0x1 : T) <<< 32) ||| 0x83060c18) <<< 32) ||| 0x3060c183) <<< 32) ||| 0x60c1833) <<< 32) ||| 0xffffe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe00000)
private def wire250120 : T := (((((((((((((0x1 : T) <<< 32) ||| 0xc3870e1c) <<< 32) ||| 0x3870e1c3) <<< 32) ||| 0x870e1c3b) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe00000)
private def wire260492 : T := (((((((((((((0x1 : T) <<< 32) ||| 0xc3870e1c) <<< 32) ||| 0x3870e1c3) <<< 32) ||| 0x870e1c3b) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0xfffc00) <<< 32) ||| 0xfffc000)
private def wire260543 : T := (((((((((((((0x1 : T) <<< 32) ||| 0xc3870e1c) <<< 32) ||| 0x3870e1c3) <<< 32) ||| 0x870e1c3b) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0xffffff) <<< 32) ||| 0xffffffff)
private def wire262094 : T := (((((((((((((0x1 : T) <<< 32) ||| 0xe3c78f1e) <<< 32) ||| 0x3c78f1e3) <<< 32) ||| 0xc78f1e3f) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0xfffff80)
private def wire273111 : T := (((((((((((((0x2 : T) <<< 32) ||| 0x24489122) <<< 32) ||| 0x44891224) <<< 32) ||| 0x48912244) <<< 32) ||| 0x7f01fc0) <<< 32) ||| 0x7f01fc07) <<< 32) ||| 0xf01fffff)
private def wire336400 : T := (((((((((((((0x2 : T) <<< 32) ||| 0x850a1428) <<< 32) ||| 0x50a14285) <<< 32) ||| 0xa142850) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xf0000000)
private def wire361307 : T := (((((((((((((0x2 : T) <<< 32) ||| 0xa54a952a) <<< 32) ||| 0x54a952a5) <<< 32) ||| 0x4a952a57) <<< 32) ||| 0xf8000000) <<< 32) ||| 0x7ffe0007) <<< 32) ||| 0xffe03fff)
private def wire375519 : T := (((((((((((((0x2 : T) <<< 32) ||| 0xa54a952a) <<< 32) ||| 0x54a952a5) <<< 32) ||| 0x4a952a57) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x7f01fc07) <<< 32) ||| 0xffffffff)
private def wire375744 : T := (((((((((((((0x2 : T) <<< 32) ||| 0xa54a952a) <<< 32) ||| 0x54a952a5) <<< 32) ||| 0x4a952a57) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x7ffffc00) <<< 32) ||| 0x0)
private def wire375775 : T := (((((((((((((0x2 : T) <<< 32) ||| 0xa54a952a) <<< 32) ||| 0x54a952a5) <<< 32) ||| 0x4a952a57) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x7ffffc07) <<< 32) ||| 0xffffffff)
private def wire375807 : T := (((((((((((((0x2 : T) <<< 32) ||| 0xa54a952a) <<< 32) ||| 0x54a952a5) <<< 32) ||| 0x4a952a57) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xffffffff)
private def wire524288 : T := (((((((((((((0x4 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x10204080) <<< 32) ||| 0x0) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire524351 : T := (((((((((((((0x4 : T) <<< 32) ||| 0x8102040) <<< 32) ||| 0x81020408) <<< 32) ||| 0x10204080) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff) <<< 32) ||| 0xffffffff)
private def wire526274 : T := (((((((((((((0x4 : T) <<< 32) ||| 0x2850a142) <<< 32) ||| 0x850a1428) <<< 32) ||| 0x50a14284) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x3f80)
private def wire555140 : T := (((((((((((((0x4 : T) <<< 32) ||| 0x48912244) <<< 32) ||| 0x89122448) <<< 32) ||| 0x91224488) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x1fc00) <<< 32) ||| 0x1fc000)
private def wire758024 : T := (((((((((((((0x5 : T) <<< 32) ||| 0x8b162c58) <<< 32) ||| 0xb162c58b) <<< 32) ||| 0x162c58b3) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe00000)
private def wire852496 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x0) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xf0000000)
private def wire860672 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f000000) <<< 32) ||| 0x0)
private def wire860688 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xf0000000)
private def wire860690 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xf0003f80)
private def wire860692 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xf01fc000)
private def wire860696 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xffe00000)
private def wire860720 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f0003ff) <<< 32) ||| 0xf0000000)
private def wire860735 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f0003ff) <<< 32) ||| 0xffffffff)
private def wire860816 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f01fc07) <<< 32) ||| 0xf0000000)
private def wire860944 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7ffe0007) <<< 32) ||| 0xf0000000)
private def wire860946 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7ffe0007) <<< 32) ||| 0xf0003f80)
private def wire860952 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7ffe0007) <<< 32) ||| 0xffe00000)
private def wire860991 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7ffe03ff) <<< 32) ||| 0xffffffff)
private def wire861072 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7ffffc07) <<< 32) ||| 0xf0000000)
private def wire861712 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f0003f) <<< 32) ||| 0xff000007) <<< 32) ||| 0xf0000000)
private def wire861968 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7f0003f) <<< 32) ||| 0xfffe0007) <<< 32) ||| 0xf0000000)
private def wire862162 : T := (((((((((((((0x6 : T) <<< 32) ||| 0xad5ab56a) <<< 32) ||| 0xd5ab56ad) <<< 32) ||| 0x5ab56ad4) <<< 32) ||| 0x7f0003f) <<< 32) ||| 0xfffffc07) <<< 32) ||| 0xf0003f80)
private def wire864784 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7ffe000) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xf0000000)
private def wire865040 : T := (((((((((((((0x6 : T) <<< 32) ||| 0x8d1a3468) <<< 32) ||| 0xd1a3468d) <<< 32) ||| 0x1a3468d0) <<< 32) ||| 0x7ffe000) <<< 32) ||| 0x7ffe0007) <<< 32) ||| 0xf0000000)
private def wire877072 : T := (((((((((((((0x6 : T) <<< 32) ||| 0xcd9b366c) <<< 32) ||| 0xd9b366cd) <<< 32) ||| 0x9b366cd8) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xf0000000)
private def wire883348 : T := (((((((((((((0x6 : T) <<< 32) ||| 0xcd9b366c) <<< 32) ||| 0xd9b366cd) <<< 32) ||| 0x9b366cd8) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x7f01fc07) <<< 32) ||| 0xf01fc000)
private def wire883391 : T := (((((((((((((0x6 : T) <<< 32) ||| 0xcd9b366c) <<< 32) ||| 0xd9b366cd) <<< 32) ||| 0x9b366cd8) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x7f01ffff) <<< 32) ||| 0xffffffff)
private def wire883604 : T := (((((((((((((0x6 : T) <<< 32) ||| 0xcd9b366c) <<< 32) ||| 0xd9b366cd) <<< 32) ||| 0x9b366cd8) <<< 32) ||| 0x7ffffc0) <<< 32) ||| 0x7ffffc07) <<< 32) ||| 0xf01fc000)
private def wire900063 : T := (((((((((((((0x6 : T) <<< 32) ||| 0xad5ab56a) <<< 32) ||| 0xd5ab56ad) <<< 32) ||| 0x5ab56ad7) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x7ffffc07) <<< 32) ||| 0xffffffff)
private def wire991760 : T := (((((((((((((0x7 : T) <<< 32) ||| 0x8f1e3c78) <<< 32) ||| 0xf1e3c78f) <<< 32) ||| 0x1e3c78f0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7f000007) <<< 32) ||| 0xf0000000)
private def wire992016 : T := (((((((((((((0x7 : T) <<< 32) ||| 0x8f1e3c78) <<< 32) ||| 0xf1e3c78f) <<< 32) ||| 0x1e3c78f0) <<< 32) ||| 0x7f00000) <<< 32) ||| 0x7ffe0007) <<< 32) ||| 0xf0000000)
private def wire1028888 : T := (((((((((((((0x7 : T) <<< 32) ||| 0x8f1e3c78) <<< 32) ||| 0xf1e3c78f) <<< 32) ||| 0x1e3c78f3) <<< 32) ||| 0xffffe000) <<< 32) ||| 0x7ffe0007) <<< 32) ||| 0xffe00000)
private def wire1028927 : T := (((((((((((((0x7 : T) <<< 32) ||| 0x8f1e3c78) <<< 32) ||| 0xf1e3c78f) <<< 32) ||| 0x1e3c78f3) <<< 32) ||| 0xffffe000) <<< 32) ||| 0x7ffe03ff) <<< 32) ||| 0xffffffff)
private def wire1047452 : T := (((((((((((((0x7 : T) <<< 32) ||| 0xcf9f3e7c) <<< 32) ||| 0xf9f3e7cf) <<< 32) ||| 0x9f3e7cfb) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x7ffffc07) <<< 32) ||| 0xffffc000)
private def wire1068263 : T := (((((((((((((0x8 : T) <<< 32) ||| 0x70e1c387) <<< 32) ||| 0xe1c3870) <<< 32) ||| 0xe1c3870c) <<< 32) ||| 0x1fff) <<< 32) ||| 0x8001fff8) <<< 32) ||| 0x1fffff)
private def wire1197088 : T := (((((((((((((0x9 : T) <<< 32) ||| 0x52a54a95) <<< 32) ||| 0x2a54a952) <<< 32) ||| 0xa54a9528) <<< 32) ||| 0x3f) <<< 32) ||| 0x800003f8) <<< 32) ||| 0x0)
private def wire1213803 : T := (((((((((((((0x9 : T) <<< 32) ||| 0x3264c993) <<< 32) ||| 0x264c9932) <<< 32) ||| 0x64c99327) <<< 32) ||| 0xf800003f) <<< 32) ||| 0x80fe03f8) <<< 32) ||| 0xfe03fff)
private def wire1236207 : T := (((((((((((((0x9 : T) <<< 32) ||| 0x72e5cb97) <<< 32) ||| 0x2e5cb972) <<< 32) ||| 0xe5cb972f) <<< 32) ||| 0xf80fffff) <<< 32) ||| 0x8001fff8) <<< 32) ||| 0xfffffff)
private def wire1236416 : T := (((((((((((((0x9 : T) <<< 32) ||| 0x72e5cb97) <<< 32) ||| 0x2e5cb972) <<< 32) ||| 0xe5cb972f) <<< 32) ||| 0xf80fffff) <<< 32) ||| 0x80fffc00) <<< 32) ||| 0x0)
private def wire1236463 : T := (((((((((((((0x9 : T) <<< 32) ||| 0x72e5cb97) <<< 32) ||| 0x2e5cb972) <<< 32) ||| 0xe5cb972f) <<< 32) ||| 0xf80fffff) <<< 32) ||| 0x80fffff8) <<< 32) ||| 0xfffffff)
private def wire1236479 : T := (((((((((((((0x9 : T) <<< 32) ||| 0x72e5cb97) <<< 32) ||| 0x2e5cb972) <<< 32) ||| 0xe5cb972f) <<< 32) ||| 0xf80fffff) <<< 32) ||| 0x80ffffff) <<< 32) ||| 0xffffffff)
private def wire1244655 : T := (((((((((((((0x9 : T) <<< 32) ||| 0x72e5cb97) <<< 32) ||| 0x2e5cb972) <<< 32) ||| 0xe5cb972f) <<< 32) ||| 0xffffffff) <<< 32) ||| 0x80fffff8) <<< 32) ||| 0xfffffff)
private def wire1721344 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x80000000) <<< 32) ||| 0x0)
private def wire1721376 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x800003f8) <<< 32) ||| 0x0)
private def wire1721378 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x800003f8) <<< 32) ||| 0x3f80)
private def wire1721380 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x800003f8) <<< 32) ||| 0x1fc000)
private def wire1721384 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x800003f8) <<< 32) ||| 0xfe00000)
private def wire1721392 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x800003ff) <<< 32) ||| 0xf0000000)
private def wire1721407 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x800003ff) <<< 32) ||| 0xffffffff)
private def wire1721504 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x8001fff8) <<< 32) ||| 0x0)
private def wire1721632 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x80fe03f8) <<< 32) ||| 0x0)
private def wire1721634 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x80fe03f8) <<< 32) ||| 0x3f80)
private def wire1721640 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x80fe03f8) <<< 32) ||| 0xfe00000)
private def wire1721663 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x80fe03ff) <<< 32) ||| 0xffffffff)
private def wire1721760 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0x80fffff8) <<< 32) ||| 0x0)
private def wire1721888 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0xff0003f8) <<< 32) ||| 0x0)
private def wire1722144 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffe03f8) <<< 32) ||| 0x0)
private def wire1722338 : T := (((((((((((((0xd : T) <<< 32) ||| 0x7af5ebd7) <<< 32) ||| 0xaf5ebd7a) <<< 32) ||| 0xf5ebd7ac) <<< 32) ||| 0x3f) <<< 32) ||| 0xfffffff8) <<< 32) ||| 0x3f80)
private def wire1725472 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0xfe03f) <<< 32) ||| 0x800003f8) <<< 32) ||| 0x0)
private def wire1729568 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x7f0003f) <<< 32) ||| 0x800003f8) <<< 32) ||| 0x0)
private def wire1735844 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0x8001fff8) <<< 32) ||| 0x1fc000)
private def wire1735871 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0x8001ffff) <<< 32) ||| 0xffffffff)
private def wire1736100 : T := (((((((((((((0xd : T) <<< 32) ||| 0x5ab56ad5) <<< 32) ||| 0xab56ad5a) <<< 32) ||| 0xb56ad5a8) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0x80fffff8) <<< 32) ||| 0x1fc000)
private def wire1760751 : T := (((((((((((((0xd : T) <<< 32) ||| 0x7af5ebd7) <<< 32) ||| 0xaf5ebd7a) <<< 32) ||| 0xf5ebd7af) <<< 32) ||| 0xf80fffff) <<< 32) ||| 0x80fffff8) <<< 32) ||| 0xfffffff)
private def wire1786912 : T := (((((((((((((0xd : T) <<< 32) ||| 0xdbb76edd) <<< 32) ||| 0xbb76eddb) <<< 32) ||| 0xb76eddb8) <<< 32) ||| 0x3f) <<< 32) ||| 0x800003f8) <<< 32) ||| 0x0)
private def wire1787168 : T := (((((((((((((0xd : T) <<< 32) ||| 0xdbb76edd) <<< 32) ||| 0xbb76eddb) <<< 32) ||| 0xb76eddb8) <<< 32) ||| 0x3f) <<< 32) ||| 0x80fe03f8) <<< 32) ||| 0x0)
private def wire1787424 : T := (((((((((((((0xd : T) <<< 32) ||| 0xdbb76edd) <<< 32) ||| 0xbb76eddb) <<< 32) ||| 0xb76eddb8) <<< 32) ||| 0x3f) <<< 32) ||| 0xff0003f8) <<< 32) ||| 0x0)
private def wire1824040 : T := (((((((((((((0xd : T) <<< 32) ||| 0xdbb76edd) <<< 32) ||| 0xbb76eddb) <<< 32) ||| 0xb76eddbb) <<< 32) ||| 0xf80fe03f) <<< 32) ||| 0x80fe03f8) <<< 32) ||| 0xfe00000)
private def wire1824063 : T := (((((((((((((0xd : T) <<< 32) ||| 0xdbb76edd) <<< 32) ||| 0xbb76eddb) <<< 32) ||| 0xb76eddbb) <<< 32) ||| 0xf80fe03f) <<< 32) ||| 0x80fe03ff) <<< 32) ||| 0xffffffff)
private def wire1834412 : T := (((((((((((((0xd : T) <<< 32) ||| 0xdbb76edd) <<< 32) ||| 0xbb76eddb) <<< 32) ||| 0xb76eddbb) <<< 32) ||| 0xffffffff) <<< 32) ||| 0x80fffff8) <<< 32) ||| 0xfffc000)
private def wire1836659 : T := (((((((((((((0xe : T) <<< 32) ||| 0x3c78f1e3) <<< 32) ||| 0xc78f1e3c) <<< 32) ||| 0x78f1e3c4) <<< 32) ||| 0x3f) <<< 32) ||| 0xff0003ff) <<< 32) ||| 0xf0003fff)
private def wire1861685 : T := (((((((((((((0xe : T) <<< 32) ||| 0x5cb972e5) <<< 32) ||| 0xcb972e5c) <<< 32) ||| 0xb972e5c8) <<< 32) ||| 0x7f01fc0) <<< 32) ||| 0x3ff) <<< 32) ||| 0xf01fc07f)
private def wire1863360 : T := (((((((((((((0xe : T) <<< 32) ||| 0x7cf9f3e7) <<< 32) ||| 0xcf9f3e7c) <<< 32) ||| 0xf9f3e7cc) <<< 32) ||| 0x7f01fff) <<< 32) ||| 0xff01fc00) <<< 32) ||| 0x0)
private def wire1863415 : T := (((((((((((((0xe : T) <<< 32) ||| 0x7cf9f3e7) <<< 32) ||| 0xcf9f3e7c) <<< 32) ||| 0xf9f3e7cc) <<< 32) ||| 0x7f01fff) <<< 32) ||| 0xff01ffff) <<< 32) ||| 0xf01fffff)
private def wire1863423 : T := (((((((((((((0xe : T) <<< 32) ||| 0x7cf9f3e7) <<< 32) ||| 0xcf9f3e7c) <<< 32) ||| 0xf9f3e7cc) <<< 32) ||| 0x7f01fff) <<< 32) ||| 0xff01ffff) <<< 32) ||| 0xffffffff)
private def wire1867511 : T := (((((((((((((0xe : T) <<< 32) ||| 0x7cf9f3e7) <<< 32) ||| 0xcf9f3e7c) <<< 32) ||| 0xf9f3e7cc) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0xff01ffff) <<< 32) ||| 0xf01fffff)
private def wire1928951 : T := (((((((((((((0xe : T) <<< 32) ||| 0xfdfbf7ef) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdc) <<< 32) ||| 0x7f01fff) <<< 32) ||| 0xff01ffff) <<< 32) ||| 0xf01fffff)
private def wire1994487 : T := (((((((((((((0xf : T) <<< 32) ||| 0x7efdfbf7) <<< 32) ||| 0xefdfbf7e) <<< 32) ||| 0xfdfbf7ec) <<< 32) ||| 0x7f01fff) <<< 32) ||| 0xff01ffff) <<< 32) ||| 0xf01fffff)
private def wire2049584 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdf8) <<< 32) ||| 0x3f) <<< 32) ||| 0xff0003ff) <<< 32) ||| 0xf0000000)
private def wire2057776 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdf8) <<< 32) ||| 0x7f0003f) <<< 32) ||| 0xff0003ff) <<< 32) ||| 0xf0000000)
private def wire2057791 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdf8) <<< 32) ||| 0x7f0003f) <<< 32) ||| 0xff0003ff) <<< 32) ||| 0xffffffff)
private def wire2058032 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdf8) <<< 32) ||| 0x7f0003f) <<< 32) ||| 0xfffe03ff) <<< 32) ||| 0xf0000000)
private def wire2064052 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdf8) <<< 32) ||| 0x7ffffff) <<< 32) ||| 0xff01ffff) <<< 32) ||| 0xf01fc000)
private def wire2064441 : T := (((((((((((((0xf : T) <<< 32) ||| 0x9f3e7cf9) <<< 32) ||| 0xf3e7cf9f) <<< 32) ||| 0x3e7cf9f3) <<< 32) ||| 0xf8000000) <<< 32) ||| 0x3ff) <<< 32) ||| 0xffe0007f)
private def wire2066043 : T := (((((((((((((0xf : T) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xf7efdfbf) <<< 32) ||| 0x7efdfbf7) <<< 32) ||| 0xf800003f) <<< 32) ||| 0xff0003ff) <<< 32) ||| 0xffe03fff)
private def wire2066240 : T := (((((((((((((0xf : T) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xf7efdfbf) <<< 32) ||| 0x7efdfbf7) <<< 32) ||| 0xf800003f) <<< 32) ||| 0xfffe0000) <<< 32) ||| 0x0)
private def wire2066299 : T := (((((((((((((0xf : T) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xf7efdfbf) <<< 32) ||| 0x7efdfbf7) <<< 32) ||| 0xf800003f) <<< 32) ||| 0xfffe03ff) <<< 32) ||| 0xffe03fff)
private def wire2066303 : T := (((((((((((((0xf : T) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xf7efdfbf) <<< 32) ||| 0x7efdfbf7) <<< 32) ||| 0xf800003f) <<< 32) ||| 0xfffe03ff) <<< 32) ||| 0xffffffff)
private def wire2068793 : T := (((((((((((((0xf : T) <<< 32) ||| 0x9f3e7cf9) <<< 32) ||| 0xf3e7cf9f) <<< 32) ||| 0x3e7cf9f3) <<< 32) ||| 0xf80fe000) <<< 32) ||| 0xfe03ff) <<< 32) ||| 0xffe0007f)
private def wire2070395 : T := (((((((((((((0xf : T) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xf7efdfbf) <<< 32) ||| 0x7efdfbf7) <<< 32) ||| 0xf80fe03f) <<< 32) ||| 0xfffe03ff) <<< 32) ||| 0xffe03fff)
private def wire2082683 : T := (((((((((((((0xf : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xf800003f) <<< 32) ||| 0xfffe03ff) <<< 32) ||| 0xffe03fff)
private def wire2094904 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xffffe03f) <<< 32) ||| 0xfffe03ff) <<< 32) ||| 0xffe00000)
private def wire2095104 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire2095165 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x3ff) <<< 32) ||| 0xffffc07f)
private def wire2095167 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x3ff) <<< 32) ||| 0xffffffff)
private def wire2095293 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0x1ffff) <<< 32) ||| 0xffffc07f)
private def wire2095368 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0xfe0000) <<< 32) ||| 0xfe00000)
private def wire2095421 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0xfe03ff) <<< 32) ||| 0xffffc07f)
private def wire2095423 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0xfe03ff) <<< 32) ||| 0xffffffff)
private def wire2095549 : T := (((((((((((((0xf : T) <<< 32) ||| 0xdfbf7efd) <<< 32) ||| 0xfbf7efdf) <<< 32) ||| 0xbf7efdfb) <<< 32) ||| 0xffffffc0) <<< 32) ||| 0xffffff) <<< 32) ||| 0xffffc07f)
private def wire2096832 : T := (((((((((((((0xf : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xff01fc00) <<< 32) ||| 0x0)
private def wire2096895 : T := (((((((((((((0xf : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xff01ffff) <<< 32) ||| 0xffffffff)
private def wire2097088 : T := (((((((((((((0xf : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x0)
private def wire2097092 : T := (((((((((((((0xf : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0x1fc000)
private def wire2097096 : T := (((((((((((((0xf : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xfffffc00) <<< 32) ||| 0xfe00000)
private def wire2097151 : T := (((((((((((((0xf : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)

-- Every listed set is checked against every possible next output and every reuse of its inputs.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def layer2 : List (List T) := []
private theorem good2 (w : List T) (h : w ∈ layer2) : ¬ Need 2 w.toFinset := by simp [layer2] at h
private def chunk3_0 : List (List T) := [[wire1599,wire30852,wire39375,wire1028888]]
private def pool3_0 : List (List (List T)) := []
private theorem checked3_0 : ∀ w ∈ chunk3_0, ¬ Need 3 w.toFinset := by
  have h : chunk3_0.all (routes 2 pool3_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_0] at hv
#print axioms checked3_0
private def chunk4_0 : List (List T) := [[wire63,wire1536,wire30852,wire39375,wire1028888],
  [wire63,wire1858,wire233736,wire2049584],
  [wire63,wire1986,wire260492,wire1787424],
  [wire63,wire1986,wire260492,wire2049584]]
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
private def chunk4_1 : List (List T) := [[wire63,wire10178,wire260492,wire2057776],
  [wire63,wire30852,wire40911,wire860688,wire1824040],
  [wire63,wire30852,wire40911,wire860688,wire2094904],
  [wire63,wire30852,wire40911,wire1028888,wire1721376]]
private def pool4_1 : List (List (List T)) := []
private theorem checked4_1 : ∀ w ∈ chunk4_1, ¬ Need 4 w.toFinset := by
  have h : chunk4_1.all (routes 3 pool4_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_1] at hv
private def chunk4_2 : List (List T) := [[wire63,wire30852,wire40911,wire1028888,wire2057776],
  [wire63,wire32454,wire883348,wire1721376],
  [wire63,wire32710,wire883348,wire1721632],
  [wire63,wire32710,wire883604,wire1721376]]
private def pool4_2 : List (List (List T)) := []
private theorem checked4_2 : ∀ w ∈ chunk4_2, ¬ Need 4 w.toFinset := by
  have h : chunk4_2.all (routes 3 pool4_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_2] at hv
private def chunk4_3 : List (List T) := [[wire63,wire198144,wire260492,wire1721376],
  [wire63,wire235466,wire260492,wire1787424],
  [wire319,wire32710,wire883348,wire1721376],
  [wire1599,wire30852,wire39375,wire233736,wire860688]]
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
private def chunk4_4 : List (List T) := [[wire1599,wire30852,wire1028888,wire2057776],
  [wire1599,wire30852,wire1824040,wire2057776],
  [wire1730,wire30911,wire860735,wire1721376],
  [wire1730,wire30911,wire883348,wire1721376]]
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
private def chunk4_5 : List (List T) := [[wire1783,wire30911,wire860688,wire1721376],
  [wire1791,wire30852,wire860688,wire1721407],
  [wire1791,wire30852,wire860735,wire1721376],
  [wire1791,wire30911,wire860688,wire1721376]]
private def pool4_5 : List (List (List T)) := []
private theorem checked4_5 : ∀ w ∈ chunk4_5, ¬ Need 4 w.toFinset := by
  have h : chunk4_5.all (routes 3 pool4_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_5] at hv
private def chunk4_6 : List (List T) := [[wire1986,wire8255,wire260492,wire2057776],
  [wire1986,wire8383,wire233736,wire2057776],
  [wire1986,wire14527,wire233736,wire2057776],
  [wire1986,wire30911,wire250120,wire2057776]]
private def pool4_6 : List (List (List T)) := []
private theorem checked4_6 : ∀ w ∈ chunk4_6, ¬ Need 4 w.toFinset := by
  have h : chunk4_6.all (routes 3 pool4_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_6] at hv
private def chunk4_7 : List (List T) := [[wire1986,wire30911,wire860735,wire1721632],
  [wire1986,wire30911,wire860991,wire1721376],
  [wire1986,wire30911,wire883348,wire1721632],
  [wire1986,wire30911,wire883604,wire1721376]]
private def pool4_7 : List (List (List T)) := []
private theorem checked4_7 : ∀ w ∈ chunk4_7, ¬ Need 4 w.toFinset := by
  have h : chunk4_7.all (routes 3 pool4_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_7] at hv
private def chunk4_8 : List (List T) := [[wire1986,wire30911,wire1028927,wire2057776],
  [wire1986,wire30911,wire1028927,wire2057791],
  [wire1986,wire31167,wire860735,wire1721376],
  [wire1986,wire31167,wire860991,wire1721376]]
private def pool4_8 : List (List (List T)) := []
private theorem checked4_8 : ∀ w ∈ chunk4_8, ¬ Need 4 w.toFinset := by
  have h : chunk4_8.all (routes 3 pool4_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_8] at hv
private def chunk4_9 : List (List T) := [[wire1986,wire31167,wire883348,wire1721376],
  [wire1986,wire31167,wire883604,wire1721376],
  [wire2047,wire30852,wire860688,wire1721663],
  [wire2047,wire30852,wire860735,wire1721632]]
private def pool4_9 : List (List (List T)) := []
private theorem checked4_9 : ∀ w ∈ chunk4_9, ¬ Need 4 w.toFinset := by
  have h : chunk4_9.all (routes 3 pool4_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_9] at hv
private def chunk4_10 : List (List T) := [[wire2047,wire30852,wire860735,wire1721640],
  [wire2047,wire30852,wire860944,wire1721407],
  [wire2047,wire30852,wire860952,wire1721407],
  [wire2047,wire30852,wire860991,wire1721376]]
private def pool4_10 : List (List (List T)) := []
private theorem checked4_10 : ∀ w ∈ chunk4_10, ¬ Need 4 w.toFinset := by
  have h : chunk4_10.all (routes 3 pool4_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_10] at hv
private def chunk4_11 : List (List T) := [[wire2047,wire30852,wire1028888,wire2057791],
  [wire2047,wire30852,wire1028927,wire2057776],
  [wire2047,wire30852,wire1028927,wire2057791],
  [wire2047,wire30852,wire1824040,wire2057791]]
private def pool4_11 : List (List (List T)) := []
private theorem checked4_11 : ∀ w ∈ chunk4_11, ¬ Need 4 w.toFinset := by
  have h : chunk4_11.all (routes 3 pool4_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_11] at hv
private def chunk4_12 : List (List T) := [[wire2047,wire30852,wire1824063,wire2057776],
  [wire2047,wire30852,wire1824063,wire2057791],
  [wire2047,wire30911,wire860688,wire1721632],
  [wire2047,wire30911,wire860688,wire1721640]]
private def pool4_12 : List (List (List T)) := []
private theorem checked4_12 : ∀ w ∈ chunk4_12, ¬ Need 4 w.toFinset := by
  have h : chunk4_12.all (routes 3 pool4_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_12] at hv
private def chunk4_13 : List (List T) := [[wire2047,wire30911,wire860944,wire1721376],
  [wire2047,wire30911,wire860952,wire1721376],
  [wire2047,wire30911,wire1028888,wire2057776],
  [wire2047,wire30911,wire1824040,wire2057776]]
private def pool4_13 : List (List (List T)) := []
private theorem checked4_13 : ∀ w ∈ chunk4_13, ¬ Need 4 w.toFinset := by
  have h : chunk4_13.all (routes 3 pool4_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_13] at hv
private def chunk4_14 : List (List T) := [[wire2047,wire31108,wire860688,wire1721407],
  [wire2047,wire31108,wire860735,wire1721376],
  [wire2047,wire31116,wire860688,wire1721407],
  [wire2047,wire31116,wire860735,wire1721376]]
private def pool4_14 : List (List (List T)) := []
private theorem checked4_14 : ∀ w ∈ chunk4_14, ¬ Need 4 w.toFinset := by
  have h : chunk4_14.all (routes 3 pool4_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_14] at hv
private def chunk4_15 : List (List T) := [[wire2047,wire31167,wire860688,wire1721376],
  [wire4415,wire32710,wire883348,wire1721376],
  [wire18370,wire30911,wire233736,wire2057776],
  [wire28358,wire30911,wire860688,wire1721376]]
private def pool4_15 : List (List (List T)) := []
private theorem checked4_15 : ∀ w ∈ chunk4_15, ¬ Need 4 w.toFinset := by
  have h : chunk4_15.all (routes 3 pool4_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_15] at hv
private def chunk4_16 : List (List T) := [[wire30852,wire198144,wire233791,wire1721376],
  [wire30852,wire233791,wire235466,wire1787424],
  [wire30911,wire32454,wire860688,wire1721376],
  [wire30911,wire32710,wire860688,wire1721632]]
private def pool4_16 : List (List (List T)) := []
private theorem checked4_16 : ∀ w ∈ chunk4_16, ¬ Need 4 w.toFinset := by
  have h : chunk4_16.all (routes 3 pool4_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_16] at hv
private def chunk4_17 : List (List T) := [[wire30911,wire32710,wire860944,wire1721376],
  [wire30911,wire32710,wire865040,wire1721376],
  [wire30911,wire32710,wire1028888,wire2057776],
  [wire30911,wire32710,wire1824040,wire2057776]]
private def pool4_17 : List (List (List T)) := []
private theorem checked4_17 : ∀ w ∈ chunk4_17, ¬ Need 4 w.toFinset := by
  have h : chunk4_17.all (routes 3 pool4_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_17] at hv
private def chunk4_18 : List (List T) := [[wire30911,wire860688,wire1721376,wire2068793],
  [wire30911,wire860688,wire1721376,wire2095368],
  [wire30911,wire860735,wire1721376,wire2095421],
  [wire30911,wire883348,wire1721376,wire2095421]]
private def pool4_18 : List (List (List T)) := []
private theorem checked4_18 : ∀ w ∈ chunk4_18, ¬ Need 4 w.toFinset := by
  have h : chunk4_18.all (routes 3 pool4_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_18] at hv
private def chunk4_19 : List (List T) := [[wire31167,wire32710,wire860688,wire1721376],
  [wire32767,wire233791,wire883348,wire1721376],
  [wire32767,wire233791,wire883391,wire1721376],
  [wire32767,wire260492,wire860735,wire1721376]]
private def pool4_19 : List (List (List T)) := []
private theorem checked4_19 : ∀ w ∈ chunk4_19, ¬ Need 4 w.toFinset := by
  have h : chunk4_19.all (routes 3 pool4_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_19] at hv
private def chunk4_20 : List (List T) := [[wire32767,wire260492,wire883391,wire1721376],
  [wire32767,wire260543,wire860735,wire1721376],
  [wire32767,wire260543,wire883348,wire1721376]]
private def pool4_20 : List (List (List T)) := []
private theorem checked4_20 : ∀ w ∈ chunk4_20, ¬ Need 4 w.toFinset := by
  have h : chunk4_20.all (routes 3 pool4_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_20] at hv
#print axioms checked4_20
private def chunk5_0 : List (List T) := [[wire55,wire1730,wire30852,wire860688,wire1721376],
  [wire63,wire256,wire32710,wire883348,wire1721376],
  [wire63,wire1536,wire30852,wire39375,wire233736,wire860688],
  [wire63,wire1536,wire30852,wire1028888,wire2057776]]
private def pool5_0 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_3, chunk4_4]
private theorem checked5_0 : ∀ w ∈ chunk5_0, ¬ Need 5 w.toFinset := by
  have h : chunk5_0.all (routes 4 pool5_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
private def chunk5_1 : List (List T) := [[wire63,wire1536,wire30852,wire1824040,wire2057776],
  [wire63,wire1602,wire30852,wire860688,wire1721376],
  [wire63,wire1728,wire30852,wire860688,wire1721376],
  [wire63,wire1730,wire26756,wire860688,wire1721376]]
private def pool5_1 : List (List (List T)) := [chunk4_4]
private theorem checked5_1 : ∀ w ∈ chunk5_1, ¬ Need 5 w.toFinset := by
  have h : chunk5_1.all (routes 4 pool5_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_4 _ hm
private def chunk5_2 : List (List T) := [[wire63,wire1730,wire30852,wire375775,wire860688],
  [wire63,wire1730,wire30852,wire860688,wire1721376],
  [wire63,wire1730,wire30852,wire860688,wire1721407],
  [wire63,wire1730,wire30852,wire860688,wire2057776]]
private def pool5_2 : List (List (List T)) := [chunk4_5]
private theorem checked5_2 : ∀ w ∈ chunk5_2, ¬ Need 5 w.toFinset := by
  have h : chunk5_2.all (routes 4 pool5_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_5 _ hm
private def chunk5_3 : List (List T) := [[wire63,wire1730,wire30852,wire860735,wire1721376],
  [wire63,wire1730,wire30852,wire883348,wire1721376],
  [wire63,wire1730,wire30852,wire1236463,wire1721376],
  [wire63,wire1730,wire30852,wire1721376,wire2057776]]
private def pool5_3 : List (List (List T)) := [chunk4_2, chunk4_4, chunk4_5]
private theorem checked5_3 : ∀ w ∈ chunk5_3, ¬ Need 5 w.toFinset := by
  have h : chunk5_3.all (routes 4 pool5_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
private def chunk5_4 : List (List T) := [[wire63,wire1730,wire30911,wire860688,wire1721376],
  [wire63,wire1730,wire860688,wire1721376,wire1735844],
  [wire63,wire1730,wire860688,wire1721376,wire2066299],
  [wire63,wire1783,wire30852,wire860688,wire1721376]]
private def pool5_4 : List (List (List T)) := [chunk4_4, chunk4_5]
private theorem checked5_4 : ∀ w ∈ chunk5_4, ¬ Need 5 w.toFinset := by
  have h : chunk5_4.all (routes 4 pool5_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
private def chunk5_5 : List (List T) := [[wire63,wire1791,wire30852,wire860688,wire1721376],
  [wire63,wire1858,wire233736,wire852496,wire1721376],
  [wire63,wire1986,wire8192,wire260492,wire2057776],
  [wire63,wire1986,wire8320,wire233736,wire2057776]]
private def pool5_5 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_5, chunk4_6]
private theorem checked5_5 : ∀ w ∈ chunk5_5, ¬ Need 5 w.toFinset := by
  have h : chunk5_5.all (routes 4 pool5_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
private def chunk5_6 : List (List T) := [[wire63,wire1986,wire14468,wire233736,wire2057776],
  [wire63,wire1986,wire30852,wire39375,wire860688,wire1824040],
  [wire63,wire1986,wire30852,wire39375,wire860688,wire2094904],
  [wire63,wire1986,wire30852,wire39375,wire1028888]]
private def pool5_6 : List (List (List T)) := [chunk4_1, chunk4_6]
private theorem checked5_6 : ∀ w ∈ chunk5_6, ¬ Need 5 w.toFinset := by
  have h : chunk5_6.all (routes 4 pool5_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_6 _ hm
private def chunk5_7 : List (List T) := [[wire63,wire1986,wire30852,wire39375,wire1028888,wire1721376],
  [wire63,wire1986,wire30852,wire39375,wire1028888,wire2057776],
  [wire63,wire1986,wire30852,wire39375,wire1824040],
  [wire63,wire1986,wire30852,wire233736,wire1787424]]
private def pool5_7 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_2]
private theorem checked5_7 : ∀ w ∈ chunk5_7, ¬ Need 5 w.toFinset := by
  have h : chunk5_7.all (routes 4 pool5_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
private def chunk5_8 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire2049584],
  [wire63,wire1986,wire30852,wire241928,wire2057776],
  [wire63,wire1986,wire30852,wire250120,wire2057776],
  [wire63,wire1986,wire30852,wire273111,wire2057776]]
private def pool5_8 : List (List (List T)) := [chunk4_0, chunk4_6]
private theorem checked5_8 : ∀ w ∈ chunk5_8, ¬ Need 5 w.toFinset := by
  have h : chunk5_8.all (routes 4 pool5_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_6 _ hm
private def chunk5_9 : List (List T) := [[wire63,wire1986,wire30852,wire375519,wire860688],
  [wire63,wire1986,wire30852,wire375775,wire860944],
  [wire63,wire1986,wire30852,wire860688,wire1721632],
  [wire63,wire1986,wire30852,wire860688,wire1721634]]
private def pool5_9 : List (List (List T)) := []
private theorem checked5_9 : ∀ w ∈ chunk5_9, ¬ Need 5 w.toFinset := by
  have h : chunk5_9.all (routes 4 pool5_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_9] at hv
private def chunk5_10 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1721640],
  [wire63,wire1986,wire30852,wire860688,wire1721663],
  [wire63,wire1986,wire30852,wire860688,wire1721760],
  [wire63,wire1986,wire30852,wire860688,wire1722144]]
private def pool5_10 : List (List (List T)) := [chunk4_9]
private theorem checked5_10 : ∀ w ∈ chunk5_10, ¬ Need 5 w.toFinset := by
  have h : chunk5_10.all (routes 4 pool5_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_9 _ hm
private def chunk5_11 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1787168],
  [wire63,wire1986,wire30852,wire860688,wire2058032],
  [wire63,wire1986,wire30852,wire860735,wire1721632],
  [wire63,wire1986,wire30852,wire860944,wire1721376]]
private def pool5_11 : List (List (List T)) := [chunk4_7, chunk4_9]
private theorem checked5_11 : ∀ w ∈ chunk5_11, ¬ Need 5 w.toFinset := by
  have h : chunk5_11.all (routes 4 pool5_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_9 _ hm
private def chunk5_12 : List (List T) := [[wire63,wire1986,wire30852,wire860944,wire1721407],
  [wire63,wire1986,wire30852,wire860944,wire1721632],
  [wire63,wire1986,wire30852,wire860944,wire2057776],
  [wire63,wire1986,wire30852,wire860944,wire2058032]]
private def pool5_12 : List (List (List T)) := [chunk4_10]
private theorem checked5_12 : ∀ w ∈ chunk5_12, ¬ Need 5 w.toFinset := by
  have h : chunk5_12.all (routes 4 pool5_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_10 _ hm
private def chunk5_13 : List (List T) := [[wire63,wire1986,wire30852,wire860946,wire1721376],
  [wire63,wire1986,wire30852,wire860952,wire1721376],
  [wire63,wire1986,wire30852,wire860991,wire1721376],
  [wire63,wire1986,wire30852,wire861072,wire1721376]]
private def pool5_13 : List (List (List T)) := [chunk4_7, chunk4_10]
private theorem checked5_13 : ∀ w ∈ chunk5_13, ¬ Need 5 w.toFinset := by
  have h : chunk5_13.all (routes 4 pool5_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_10 _ hm
private def chunk5_14 : List (List T) := [[wire63,wire1986,wire30852,wire861968,wire1721376],
  [wire63,wire1986,wire30852,wire865040,wire1721376],
  [wire63,wire1986,wire30852,wire883348,wire1721632],
  [wire63,wire1986,wire30852,wire883604,wire1721376]]
private def pool5_14 : List (List (List T)) := [chunk4_2, chunk4_7]
private theorem checked5_14 : ∀ w ∈ chunk5_14, ¬ Need 5 w.toFinset := by
  have h : chunk5_14.all (routes 4 pool5_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_7 _ hm
private def chunk5_15 : List (List T) := [[wire63,wire1986,wire30852,wire992016,wire1721376],
  [wire63,wire1986,wire30852,wire1028888,wire2057776],
  [wire63,wire1986,wire30852,wire1028888,wire2057791],
  [wire63,wire1986,wire30852,wire1028927,wire2057776]]
private def pool5_15 : List (List (List T)) := [chunk4_8, chunk4_11]
private theorem checked5_15 : ∀ w ∈ chunk5_15, ¬ Need 5 w.toFinset := by
  have h : chunk5_15.all (routes 4 pool5_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_11 _ hm
private def chunk5_16 : List (List T) := [[wire63,wire1986,wire30852,wire1028927,wire2057791],
  [wire63,wire1986,wire30852,wire1068263,wire2057776],
  [wire63,wire1986,wire30852,wire1236207,wire1721376],
  [wire63,wire1986,wire30852,wire1236463,wire1721632]]
private def pool5_16 : List (List (List T)) := [chunk4_8, chunk4_11]
private theorem checked5_16 : ∀ w ∈ chunk5_16, ¬ Need 5 w.toFinset := by
  have h : chunk5_16.all (routes 4 pool5_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_11 _ hm
private def chunk5_17 : List (List T) := [[wire63,wire1986,wire30852,wire1721376,wire2058032],
  [wire63,wire1986,wire30852,wire1721632,wire2057776],
  [wire63,wire1986,wire30852,wire1721632,wire2058032],
  [wire63,wire1986,wire30852,wire1824040,wire2057776]]
private def pool5_17 : List (List (List T)) := []
private theorem checked5_17 : ∀ w ∈ chunk5_17, ¬ Need 5 w.toFinset := by
  have h : chunk5_17.all (routes 4 pool5_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_17] at hv
private def chunk5_18 : List (List T) := [[wire63,wire1986,wire30852,wire1824040,wire2057791],
  [wire63,wire1986,wire30852,wire1824063,wire2057776],
  [wire63,wire1986,wire30852,wire1824063,wire2057791],
  [wire63,wire1986,wire30911,wire860688,wire1721632]]
private def pool5_18 : List (List (List T)) := [chunk4_7, chunk4_11, chunk4_12]
private theorem checked5_18 : ∀ w ∈ chunk5_18, ¬ Need 5 w.toFinset := by
  have h : chunk5_18.all (routes 4 pool5_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
private def chunk5_19 : List (List T) := [[wire63,wire1986,wire30911,wire860944,wire1721376],
  [wire63,wire1986,wire30911,wire1028888,wire2057776],
  [wire63,wire1986,wire30911,wire1824040,wire2057776],
  [wire63,wire1986,wire31108,wire375775,wire860688]]
private def pool5_19 : List (List (List T)) := [chunk4_7, chunk4_8, chunk4_13]
private theorem checked5_19 : ∀ w ∈ chunk5_19, ¬ Need 5 w.toFinset := by
  have h : chunk5_19.all (routes 4 pool5_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_13 _ hm
private def chunk5_20 : List (List T) := [[wire63,wire1986,wire31108,wire860688,wire1721376],
  [wire63,wire1986,wire31108,wire860688,wire1721407],
  [wire63,wire1986,wire31108,wire860688,wire1721632],
  [wire63,wire1986,wire31108,wire860688,wire2057776]]
private def pool5_20 : List (List (List T)) := [chunk4_14]
private theorem checked5_20 : ∀ w ∈ chunk5_20, ¬ Need 5 w.toFinset := by
  have h : chunk5_20.all (routes 4 pool5_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_14 _ hm
private def chunk5_21 : List (List T) := [[wire63,wire1986,wire31108,wire860735,wire1721376],
  [wire63,wire1986,wire31108,wire860944,wire1721376],
  [wire63,wire1986,wire31108,wire883348,wire1721376],
  [wire63,wire1986,wire31108,wire883604,wire1721376]]
private def pool5_21 : List (List (List T)) := [chunk4_2, chunk4_8, chunk4_9, chunk4_14]
private theorem checked5_21 : ∀ w ∈ chunk5_21, ¬ Need 5 w.toFinset := by
  have h : chunk5_21.all (routes 4 pool5_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_14 _ hm
private def chunk5_22 : List (List T) := [[wire63,wire1986,wire31108,wire1236463,wire1721376],
  [wire63,wire1986,wire31108,wire1721376,wire2057776],
  [wire63,wire1986,wire31110,wire860688,wire1721376],
  [wire63,wire1986,wire31116,wire860688,wire1721376]]
private def pool5_22 : List (List (List T)) := []
private theorem checked5_22 : ∀ w ∈ chunk5_22, ¬ Need 5 w.toFinset := by
  have h : chunk5_22.all (routes 4 pool5_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_22] at hv
private def chunk5_23 : List (List T) := [[wire63,wire1986,wire31167,wire860688,wire1721376],
  [wire63,wire1986,wire31620,wire860688,wire1721376],
  [wire63,wire1986,wire32132,wire860688,wire1721376],
  [wire63,wire1986,wire66048,wire260492,wire1721376]]
private def pool5_23 : List (List (List T)) := [chunk4_0, chunk4_8, chunk4_15]
private theorem checked5_23 : ∀ w ∈ chunk5_23, ¬ Need 5 w.toFinset := by
  have h : chunk5_23.all (routes 4 pool5_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_8 _ hm
  · exact checked4_15 _ hm
private def chunk5_24 : List (List T) := [[wire63,wire1986,wire162180,wire860688,wire1721376],
  [wire63,wire1986,wire194956,wire860688,wire1721376],
  [wire63,wire1986,wire194956,wire1236463,wire1721376],
  [wire63,wire1986,wire233736,wire2049584,wire2066299]]
private def pool5_24 : List (List (List T)) := [chunk4_0]
private theorem checked5_24 : ∀ w ∈ chunk5_24, ¬ Need 5 w.toFinset := by
  have h : chunk5_24.all (routes 4 pool5_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_0 _ hm
private def chunk5_25 : List (List T) := [[wire63,wire1986,wire233736,wire2057776,wire2082683],
  [wire63,wire1986,wire260492,wire852496,wire1721376],
  [wire63,wire1986,wire260492,wire860688,wire1729568],
  [wire63,wire1986,wire260492,wire860688,wire1786912]]
private def pool5_25 : List (List (List T)) := [chunk4_0]
private theorem checked5_25 : ∀ w ∈ chunk5_25, ¬ Need 5 w.toFinset := by
  have h : chunk5_25.all (routes 4 pool5_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_0 _ hm
private def chunk5_26 : List (List T) := [[wire63,wire1986,wire260492,wire1244655,wire1721376],
  [wire63,wire1986,wire260492,wire1824040,wire2057776],
  [wire63,wire1986,wire860688,wire1721376,wire1736100],
  [wire63,wire1986,wire860688,wire1721376,wire2066043]]
private def pool5_26 : List (List (List T)) := []
private theorem checked5_26 : ∀ w ∈ chunk5_26, ¬ Need 5 w.toFinset := by
  have h : chunk5_26.all (routes 4 pool5_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_26] at hv
private def chunk5_27 : List (List T) := [[wire63,wire1986,wire860688,wire1721632,wire1735844],
  [wire63,wire1986,wire860688,wire1721632,wire1736100],
  [wire63,wire1986,wire860688,wire1721632,wire2066299],
  [wire63,wire1986,wire860944,wire1721376,wire1735844]]
private def pool5_27 : List (List (List T)) := []
private theorem checked5_27 : ∀ w ∈ chunk5_27, ¬ Need 5 w.toFinset := by
  have h : chunk5_27.all (routes 4 pool5_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_27] at hv
private def chunk5_28 : List (List T) := [[wire63,wire1986,wire860944,wire1721376,wire2066299],
  [wire63,wire1986,wire1028888,wire2057776,wire2066299],
  [wire63,wire1986,wire1735844,wire1824040,wire2057776],
  [wire63,wire1986,wire1824040,wire1834412,wire2057776]]
private def pool5_28 : List (List (List T)) := []
private theorem checked5_28 : ∀ w ∈ chunk5_28, ¬ Need 5 w.toFinset := by
  have h : chunk5_28.all (routes 4 pool5_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_28] at hv
private def chunk5_29 : List (List T) := [[wire63,wire1986,wire1824040,wire2057776,wire2066299],
  [wire63,wire2047,wire30852,wire860688,wire1721632],
  [wire63,wire2047,wire30852,wire860688,wire1721640],
  [wire63,wire2047,wire30852,wire860944,wire1721376]]
private def pool5_29 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_12, chunk4_13]
private theorem checked5_29 : ∀ w ∈ chunk5_29, ¬ Need 5 w.toFinset := by
  have h : chunk5_29.all (routes 4 pool5_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
private def chunk5_30 : List (List T) := [[wire63,wire2047,wire30852,wire860952,wire1721376],
  [wire63,wire2047,wire30852,wire1028888,wire2057776],
  [wire63,wire2047,wire30852,wire1824040,wire2057776],
  [wire63,wire2047,wire31108,wire860688,wire1721376]]
private def pool5_30 : List (List (List T)) := [chunk4_10, chunk4_11, chunk4_12, chunk4_13, chunk4_14, chunk4_15]
private theorem checked5_30 : ∀ w ∈ chunk5_30, ¬ Need 5 w.toFinset := by
  have h : chunk5_30.all (routes 4 pool5_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
private def chunk5_31 : List (List T) := [[wire63,wire2047,wire31116,wire860688,wire1721376],
  [wire63,wire4352,wire32710,wire883348,wire1721376],
  [wire63,wire10178,wire30852,wire233736,wire2057776],
  [wire63,wire10178,wire260492,wire860688,wire1721376]]
private def pool5_31 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_14, chunk4_15]
private theorem checked5_31 : ∀ w ∈ chunk5_31, ¬ Need 5 w.toFinset := by
  have h : chunk5_31.all (routes 4 pool5_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
private def chunk5_32 : List (List T) := [[wire63,wire18370,wire30852,wire233736,wire2057776],
  [wire63,wire28358,wire30852,wire860688,wire1721376],
  [wire63,wire30852,wire32454,wire860688,wire1721376],
  [wire63,wire30852,wire32710,wire860688,wire1721632]]
private def pool5_32 : List (List (List T)) := [chunk4_2, chunk4_15, chunk4_16]
private theorem checked5_32 : ∀ w ∈ chunk5_32, ¬ Need 5 w.toFinset := by
  have h : chunk5_32.all (routes 4 pool5_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
private def chunk5_33 : List (List T) := [[wire63,wire30852,wire32710,wire860944,wire1721376],
  [wire63,wire30852,wire32710,wire865040,wire1721376],
  [wire63,wire30852,wire32710,wire1028888,wire2057776],
  [wire63,wire30852,wire32710,wire1824040,wire2057776]]
private def pool5_33 : List (List (List T)) := [chunk4_2, chunk4_17]
private theorem checked5_33 : ∀ w ∈ chunk5_33, ¬ Need 5 w.toFinset := by
  have h : chunk5_33.all (routes 4 pool5_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_17 _ hm
private def chunk5_34 : List (List T) := [[wire63,wire30852,wire40911,wire233736,wire860688,wire1721376],
  [wire63,wire30852,wire40911,wire233736,wire860688,wire2057776],
  [wire63,wire30852,wire198144,wire233736,wire1721376],
  [wire63,wire30852,wire233736,wire235466,wire1787424]]
private def pool5_34 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_3, chunk4_16]
private theorem checked5_34 : ∀ w ∈ chunk5_34, ¬ Need 5 w.toFinset := by
  have h : chunk5_34.all (routes 4 pool5_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_16 _ hm
private def chunk5_35 : List (List T) := [[wire63,wire30852,wire375775,wire860688,wire2095421],
  [wire63,wire30852,wire860688,wire1721376,wire2068793],
  [wire63,wire30852,wire860688,wire1721376,wire2095368],
  [wire63,wire30852,wire860688,wire1721376,wire2095421]]
private def pool5_35 : List (List (List T)) := [chunk4_18]
private theorem checked5_35 : ∀ w ∈ chunk5_35, ¬ Need 5 w.toFinset := by
  have h : chunk5_35.all (routes 4 pool5_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_18 _ hm
private def chunk5_36 : List (List T) := [[wire63,wire30852,wire860688,wire1721376,wire2095423],
  [wire63,wire30852,wire860688,wire1721376,wire2095549],
  [wire63,wire30852,wire860688,wire1721407,wire2095421],
  [wire63,wire30852,wire860688,wire1721632,wire2095165]]
private def pool5_36 : List (List (List T)) := []
private theorem checked5_36 : ∀ w ∈ chunk5_36, ¬ Need 5 w.toFinset := by
  have h : chunk5_36.all (routes 4 pool5_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_36] at hv
private def chunk5_37 : List (List T) := [[wire63,wire30852,wire860688,wire2057776,wire2095421],
  [wire63,wire30852,wire860735,wire1721376,wire2095421],
  [wire63,wire30852,wire860944,wire1721376,wire2095165],
  [wire63,wire30852,wire883348,wire1721376,wire2095421]]
private def pool5_37 : List (List (List T)) := [chunk4_18]
private theorem checked5_37 : ∀ w ∈ chunk5_37, ¬ Need 5 w.toFinset := by
  have h : chunk5_37.all (routes 4 pool5_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_18 _ hm
private def chunk5_38 : List (List T) := [[wire63,wire30852,wire1028888,wire2057776,wire2095165],
  [wire63,wire30852,wire1236463,wire1721376,wire2095421],
  [wire63,wire30852,wire1721376,wire2057776,wire2095421],
  [wire63,wire30852,wire1824040,wire2057776,wire2095165]]
private def pool5_38 : List (List (List T)) := []
private theorem checked5_38 : ∀ w ∈ chunk5_38, ¬ Need 5 w.toFinset := by
  have h : chunk5_38.all (routes 4 pool5_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_38] at hv
private def chunk5_39 : List (List T) := [[wire63,wire30911,wire860688,wire1721376,wire2095421],
  [wire63,wire31108,wire32710,wire860688,wire1721376],
  [wire63,wire31108,wire860688,wire1721376,wire2095165],
  [wire63,wire32710,wire233736,wire375775,wire883348]]
private def pool5_39 : List (List (List T)) := [chunk4_2, chunk4_18, chunk4_19]
private theorem checked5_39 : ∀ w ∈ chunk5_39, ¬ Need 5 w.toFinset := by
  have h : chunk5_39.all (routes 4 pool5_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
private def chunk5_40 : List (List T) := [[wire63,wire32710,wire233736,wire883348,wire1721376],
  [wire63,wire32710,wire233736,wire883348,wire1721407],
  [wire63,wire32710,wire233736,wire883391,wire1721376],
  [wire63,wire32710,wire233736,wire1213803,wire1721376]]
private def pool5_40 : List (List (List T)) := []
private theorem checked5_40 : ∀ w ∈ chunk5_40, ¬ Need 5 w.toFinset := by
  have h : chunk5_40.all (routes 4 pool5_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_40] at hv
private def chunk5_41 : List (List T) := [[wire63,wire32710,wire233791,wire883348,wire1721376],
  [wire63,wire32710,wire260492,wire375775,wire860688],
  [wire63,wire32710,wire260492,wire860688,wire1721376],
  [wire63,wire32710,wire260492,wire860688,wire1721407]]
private def pool5_41 : List (List (List T)) := [chunk4_19]
private theorem checked5_41 : ∀ w ∈ chunk5_41, ¬ Need 5 w.toFinset := by
  have h : chunk5_41.all (routes 4 pool5_41.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_41,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_19 _ hm
private def chunk5_42 : List (List T) := [[wire63,wire32710,wire260492,wire860688,wire2057776],
  [wire63,wire32710,wire260492,wire860735,wire1721376],
  [wire63,wire32710,wire260492,wire883348,wire1721376],
  [wire63,wire32710,wire260492,wire1236463,wire1721376]]
private def pool5_42 : List (List (List T)) := [chunk4_19]
private theorem checked5_42 : ∀ w ∈ chunk5_42, ¬ Need 5 w.toFinset := by
  have h : chunk5_42.all (routes 4 pool5_42.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_42,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_19 _ hm
private def chunk5_43 : List (List T) := [[wire63,wire32710,wire260492,wire1721376,wire2057776],
  [wire63,wire32710,wire260543,wire860688,wire1721376],
  [wire63,wire32710,wire860688,wire1047452,wire1721376],
  [wire63,wire32710,wire860688,wire1721376,wire1836659]]
private def pool5_43 : List (List (List T)) := []
private theorem checked5_43 : ∀ w ∈ chunk5_43, ¬ Need 5 w.toFinset := by
  have h : chunk5_43.all (routes 4 pool5_43.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_43] at hv
private def chunk5_44 : List (List T) := [[wire63,wire32710,wire883348,wire1028888,wire1721376],
  [wire63,wire32710,wire883348,wire1047452,wire1721376],
  [wire63,wire32710,wire883348,wire1721376,wire1824040],
  [wire63,wire32710,wire883348,wire1721376,wire1863415]]
private def pool5_44 : List (List (List T)) := []
private theorem checked5_44 : ∀ w ∈ chunk5_44, ¬ Need 5 w.toFinset := by
  have h : chunk5_44.all (routes 4 pool5_44.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_44] at hv
private def chunk5_45 : List (List T) := [[wire63,wire32767,wire233736,wire883348,wire1721376],
  [wire63,wire32767,wire233736,wire883391,wire1721376],
  [wire63,wire32767,wire260492,wire860688,wire1721376],
  [wire63,wire32767,wire260543,wire860688,wire1721376]]
private def pool5_45 : List (List (List T)) := [chunk4_19, chunk4_20]
private theorem checked5_45 : ∀ w ∈ chunk5_45, ¬ Need 5 w.toFinset := by
  have h : chunk5_45.all (routes 4 pool5_45.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_45,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_19 _ hm
  · exact checked4_20 _ hm
private def chunk5_46 : List (List T) := [[wire63,wire66048,wire235466,wire260492,wire1721376],
  [wire63,wire67522,wire260492,wire860688,wire1721376],
  [wire63,wire233736,wire883348,wire1721376,wire2064441],
  [wire63,wire235466,wire260492,wire375775,wire860688]]
private def pool5_46 : List (List (List T)) := [chunk4_3]
private theorem checked5_46 : ∀ w ∈ chunk5_46, ¬ Need 5 w.toFinset := by
  have h : chunk5_46.all (routes 4 pool5_46.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_46,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_3 _ hm
private def chunk5_47 : List (List T) := [[wire63,wire235466,wire260492,wire860688,wire1721376],
  [wire63,wire235466,wire260492,wire860688,wire1721407],
  [wire63,wire235466,wire260492,wire860688,wire2057776],
  [wire63,wire235466,wire260492,wire860735,wire1721376]]
private def pool5_47 : List (List (List T)) := []
private theorem checked5_47 : ∀ w ∈ chunk5_47, ¬ Need 5 w.toFinset := by
  have h : chunk5_47.all (routes 4 pool5_47.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_47] at hv
private def chunk5_48 : List (List T) := [[wire63,wire235466,wire260492,wire1236463,wire1721376],
  [wire63,wire235466,wire260492,wire1721376,wire2057776],
  [wire63,wire235466,wire260543,wire860688,wire1721376],
  [wire63,wire235466,wire860688,wire1721376,wire1836659]]
private def pool5_48 : List (List (List T)) := [chunk4_3]
private theorem checked5_48 : ∀ w ∈ chunk5_48, ¬ Need 5 w.toFinset := by
  have h : chunk5_48.all (routes 4 pool5_48.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_48,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_3 _ hm
private def chunk5_49 : List (List T) := [[wire63,wire235519,wire260492,wire860688,wire1721376],
  [wire63,wire235519,wire260543,wire860688,wire1721376],
  [wire63,wire260492,wire860688,wire1721376,wire1861685],
  [wire63,wire260492,wire860688,wire1721376,wire2064441]]
private def pool5_49 : List (List (List T)) := []
private theorem checked5_49 : ∀ w ∈ chunk5_49, ¬ Need 5 w.toFinset := by
  have h : chunk5_49.all (routes 4 pool5_49.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_49] at hv
private def chunk5_50 : List (List T) := [[wire63,wire860688,wire1721376,wire1735844,wire2095421],
  [wire63,wire860688,wire1721376,wire2066299,wire2095421],
  [wire256,wire1986,wire30911,wire860735,wire1721376],
  [wire256,wire1986,wire30911,wire883348,wire1721376]]
private def pool5_50 : List (List (List T)) := [chunk4_7, chunk4_8, chunk4_9]
private theorem checked5_50 : ∀ w ∈ chunk5_50, ¬ Need 5 w.toFinset := by
  have h : chunk5_50.all (routes 4 pool5_50.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_50,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
private def chunk5_51 : List (List T) := [[wire256,wire2047,wire30852,wire860688,wire1721407],
  [wire256,wire2047,wire30852,wire860735,wire1721376],
  [wire256,wire2047,wire30911,wire860688,wire1721376],
  [wire256,wire30911,wire32710,wire860688,wire1721376]]
private def pool5_51 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_12, chunk4_13, chunk4_14, chunk4_15, chunk4_16, chunk4_17, chunk4_19]
private theorem checked5_51 : ∀ w ∈ chunk5_51, ¬ Need 5 w.toFinset := by
  have h : chunk5_51.all (routes 4 pool5_51.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_51,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
  · exact checked4_17 _ hm
  · exact checked4_19 _ hm
private def chunk5_52 : List (List T) := [[wire264,wire2047,wire30852,wire860688,wire1721407],
  [wire264,wire2047,wire30852,wire860735,wire1721376],
  [wire264,wire2047,wire30911,wire860688,wire1721376],
  [wire319,wire1986,wire30852,wire375775,wire860688]]
private def pool5_52 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_12, chunk4_13, chunk4_14, chunk4_15]
private theorem checked5_52 : ∀ w ∈ chunk5_52, ¬ Need 5 w.toFinset := by
  have h : chunk5_52.all (routes 4 pool5_52.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_52,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
private def chunk5_53 : List (List T) := [[wire319,wire1986,wire30852,wire860688,wire1721376],
  [wire319,wire1986,wire30852,wire860688,wire1721407],
  [wire319,wire1986,wire30852,wire860688,wire1721632],
  [wire319,wire1986,wire30852,wire860688,wire1721663]]
private def pool5_53 : List (List (List T)) := [chunk4_9]
private theorem checked5_53 : ∀ w ∈ chunk5_53, ¬ Need 5 w.toFinset := by
  have h : chunk5_53.all (routes 4 pool5_53.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_53,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_9 _ hm
private def chunk5_54 : List (List T) := [[wire319,wire1986,wire30852,wire860688,wire2057776],
  [wire319,wire1986,wire30852,wire860735,wire1721376],
  [wire319,wire1986,wire30852,wire860944,wire1721376],
  [wire319,wire1986,wire30852,wire860991,wire1721376]]
private def pool5_54 : List (List (List T)) := [chunk4_8, chunk4_10]
private theorem checked5_54 : ∀ w ∈ chunk5_54, ¬ Need 5 w.toFinset := by
  have h : chunk5_54.all (routes 4 pool5_54.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_54,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_10 _ hm
private def chunk5_55 : List (List T) := [[wire319,wire1986,wire30852,wire883348,wire1721376],
  [wire319,wire1986,wire30852,wire1236463,wire1721376],
  [wire319,wire1986,wire30852,wire1721376,wire2057776],
  [wire319,wire1986,wire30911,wire860688,wire1721376]]
private def pool5_55 : List (List (List T)) := [chunk4_3, chunk4_7, chunk4_9]
private theorem checked5_55 : ∀ w ∈ chunk5_55, ¬ Need 5 w.toFinset := by
  have h : chunk5_55.all (routes 4 pool5_55.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_55,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_7 _ hm
  · exact checked4_9 _ hm
private def chunk5_56 : List (List T) := [[wire319,wire1986,wire31108,wire860688,wire1721376],
  [wire319,wire1986,wire31167,wire860688,wire1721376],
  [wire319,wire1986,wire860688,wire1721376,wire1735844],
  [wire319,wire1986,wire860688,wire1721376,wire2066299]]
private def pool5_56 : List (List (List T)) := [chunk4_8, chunk4_15]
private theorem checked5_56 : ∀ w ∈ chunk5_56, ¬ Need 5 w.toFinset := by
  have h : chunk5_56.all (routes 4 pool5_56.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_56,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_15 _ hm
private def chunk5_57 : List (List T) := [[wire319,wire2047,wire30852,wire860688,wire1721376],
  [wire319,wire30852,wire32710,wire860688,wire1721376],
  [wire319,wire30852,wire860688,wire1721376,wire2095165],
  [wire447,wire1986,wire30852,wire860688,wire1721376]]
private def pool5_57 : List (List (List T)) := [chunk4_3, chunk4_9, chunk4_10, chunk4_15, chunk4_19]
private theorem checked5_57 : ∀ w ∈ chunk5_57, ¬ Need 5 w.toFinset := by
  have h : chunk5_57.all (routes 4 pool5_57.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_57,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_15 _ hm
  · exact checked4_19 _ hm
private def chunk5_58 : List (List T) := [[wire831,wire1986,wire30852,wire860688,wire1721376],
  [wire1343,wire1986,wire30852,wire860688,wire1721376],
  [wire1599,wire30852,wire233736,wire860688,wire1721376],
  [wire1599,wire30852,wire233736,wire860688,wire2057776]]
private def pool5_58 : List (List (List T)) := [chunk4_3, chunk4_4]
private theorem checked5_58 : ∀ w ∈ chunk5_58, ¬ Need 5 w.toFinset := by
  have h : chunk5_58.all (routes 4 pool5_58.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_58,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
private def chunk5_59 : List (List T) := [[wire1599,wire30852,wire233736,wire1721376,wire2057776],
  [wire1730,wire30852,wire30911,wire860688,wire1721376],
  [wire1730,wire30852,wire860688,wire1721376,wire2097088],
  [wire1986,wire4415,wire30852,wire860688,wire1721376]]
private def pool5_59 : List (List (List T)) := [chunk4_4, chunk4_16]
private theorem checked5_59 : ∀ w ∈ chunk5_59, ¬ Need 5 w.toFinset := by
  have h : chunk5_59.all (routes 4 pool5_59.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_59,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_16 _ hm
private def chunk5_60 : List (List T) := [[wire1986,wire8255,wire30852,wire233736,wire2057776],
  [wire1986,wire8255,wire260492,wire860688,wire1721376],
  [wire1986,wire8383,wire233736,wire860688,wire1721376],
  [wire1986,wire14527,wire233736,wire375775,wire860688]]
private def pool5_60 : List (List (List T)) := [chunk4_6]
private theorem checked5_60 : ∀ w ∈ chunk5_60, ¬ Need 5 w.toFinset := by
  have h : chunk5_60.all (routes 4 pool5_60.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_60,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_6 _ hm
private def chunk5_61 : List (List T) := [[wire1986,wire14527,wire233736,wire860688,wire1721376],
  [wire1986,wire16384,wire30911,wire233736,wire2057776],
  [wire1986,wire16447,wire30852,wire233736,wire2057776],
  [wire1986,wire30852,wire30911,wire860688,wire1721632]]
private def pool5_61 : List (List (List T)) := [chunk4_6, chunk4_7, chunk4_15, chunk4_16]
private theorem checked5_61 : ∀ w ∈ chunk5_61, ¬ Need 5 w.toFinset := by
  have h : chunk5_61.all (routes 4 pool5_61.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_61,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
private def chunk5_62 : List (List T) := [[wire1986,wire30852,wire30911,wire860944,wire1721376],
  [wire1986,wire30852,wire30911,wire1028888,wire2057776],
  [wire1986,wire30852,wire30911,wire1824040,wire2057776],
  [wire1986,wire30852,wire31167,wire860688,wire1721376]]
private def pool5_62 : List (List (List T)) := [chunk4_7, chunk4_9, chunk4_17, chunk4_19]
private theorem checked5_62 : ∀ w ∈ chunk5_62, ¬ Need 5 w.toFinset := by
  have h : chunk5_62.all (routes 4 pool5_62.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_62,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_9 _ hm
  · exact checked4_17 _ hm
  · exact checked4_19 _ hm
private def chunk5_63 : List (List T) := [[wire1986,wire30852,wire233791,wire860735,wire1721407],
  [wire1986,wire30852,wire860688,wire1721376,wire2096832],
  [wire1986,wire30852,wire860688,wire1721632,wire2097088],
  [wire1986,wire30852,wire860944,wire1721376,wire2097088]]
private def pool5_63 : List (List (List T)) := []
private theorem checked5_63 : ∀ w ∈ chunk5_63, ¬ Need 5 w.toFinset := by
  have h : chunk5_63.all (routes 4 pool5_63.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_63] at hv
private def chunk5_64 : List (List T) := [[wire1986,wire30852,wire1028888,wire2057776,wire2097088],
  [wire1986,wire30852,wire1824040,wire2057776,wire2097088],
  [wire1986,wire30911,wire31108,wire860688,wire1721376],
  [wire1986,wire30911,wire233736,wire375775,wire860735]]
private def pool5_64 : List (List (List T)) := [chunk4_7]
private theorem checked5_64 : ∀ w ∈ chunk5_64, ¬ Need 5 w.toFinset := by
  have h : chunk5_64.all (routes 4 pool5_64.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_64,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_7 _ hm
private def chunk5_65 : List (List T) := [[wire1986,wire30911,wire233736,wire375775,wire883348],
  [wire1986,wire30911,wire233736,wire375807,wire860688],
  [wire1986,wire30911,wire233736,wire860688,wire1721344],
  [wire1986,wire30911,wire233736,wire860720,wire1721376]]
private def pool5_65 : List (List (List T)) := []
private theorem checked5_65 : ∀ w ∈ chunk5_65, ¬ Need 5 w.toFinset := by
  have h : chunk5_65.all (routes 4 pool5_65.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_65] at hv
private def chunk5_66 : List (List T) := [[wire1986,wire30911,wire233736,wire860735,wire1721376],
  [wire1986,wire30911,wire233736,wire860735,wire1721407],
  [wire1986,wire30911,wire233736,wire860735,wire2057776],
  [wire1986,wire30911,wire233736,wire860735,wire2057791]]
private def pool5_66 : List (List (List T)) := [chunk4_8]
private theorem checked5_66 : ∀ w ∈ chunk5_66, ¬ Need 5 w.toFinset := by
  have h : chunk5_66.all (routes 4 pool5_66.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_66,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_8 _ hm
private def chunk5_67 : List (List T) := [[wire1986,wire30911,wire233736,wire877072,wire1721376],
  [wire1986,wire30911,wire233736,wire883348,wire1721376],
  [wire1986,wire30911,wire233736,wire1213803,wire1721376],
  [wire1986,wire30911,wire233736,wire1236416,wire1721376]]
private def pool5_67 : List (List (List T)) := []
private theorem checked5_67 : ∀ w ∈ chunk5_67, ¬ Need 5 w.toFinset := by
  have h : chunk5_67.all (routes 4 pool5_67.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_67] at hv
private def chunk5_68 : List (List T) := [[wire1986,wire30911,wire233768,wire860688,wire1721376],
  [wire1986,wire30911,wire233791,wire375775,wire860688],
  [wire1986,wire30911,wire233791,wire860688,wire1721376],
  [wire1986,wire30911,wire233791,wire860688,wire1721407]]
private def pool5_68 : List (List (List T)) := []
private theorem checked5_68 : ∀ w ∈ chunk5_68, ¬ Need 5 w.toFinset := by
  have h : chunk5_68.all (routes 4 pool5_68.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_68] at hv
private def chunk5_69 : List (List T) := [[wire1986,wire30911,wire233791,wire860688,wire2057776],
  [wire1986,wire30911,wire233791,wire860735,wire1721376],
  [wire1986,wire30911,wire233791,wire883348,wire1721376],
  [wire1986,wire30911,wire233791,wire883391,wire1721376]]
private def pool5_69 : List (List (List T)) := [chunk4_8, chunk4_19]
private theorem checked5_69 : ∀ w ∈ chunk5_69, ¬ Need 5 w.toFinset := by
  have h : chunk5_69.all (routes 4 pool5_69.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_69,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_19 _ hm
private def chunk5_70 : List (List T) := [[wire1986,wire30911,wire233791,wire1236463,wire1721376],
  [wire1986,wire30911,wire233791,wire1721376,wire2057776],
  [wire1986,wire30911,wire250120,wire860688,wire1721376],
  [wire1986,wire30911,wire260492,wire375775,wire860688]]
private def pool5_70 : List (List (List T)) := [chunk4_6]
private theorem checked5_70 : ∀ w ∈ chunk5_70, ¬ Need 5 w.toFinset := by
  have h : chunk5_70.all (routes 4 pool5_70.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_70,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_6 _ hm
private def chunk5_71 : List (List T) := [[wire1986,wire30911,wire260492,wire860688,wire1721376],
  [wire1986,wire30911,wire260492,wire860688,wire2057776],
  [wire1986,wire30911,wire260492,wire860735,wire1721376],
  [wire1986,wire30911,wire260492,wire883348,wire1721376]]
private def pool5_71 : List (List (List T)) := [chunk4_19]
private theorem checked5_71 : ∀ w ∈ chunk5_71, ¬ Need 5 w.toFinset := by
  have h : chunk5_71.all (routes 4 pool5_71.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_71,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_19 _ hm
private def chunk5_72 : List (List T) := [[wire1986,wire30911,wire260492,wire883391,wire1721376],
  [wire1986,wire30911,wire260492,wire1236463,wire1721376],
  [wire1986,wire30911,wire260492,wire1721376,wire2057776],
  [wire1986,wire30911,wire260543,wire860735,wire1721376]]
private def pool5_72 : List (List (List T)) := [chunk4_20]
private theorem checked5_72 : ∀ w ∈ chunk5_72, ¬ Need 5 w.toFinset := by
  have h : chunk5_72.all (routes 4 pool5_72.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_72,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_20 _ hm
private def chunk5_73 : List (List T) := [[wire1986,wire30911,wire260543,wire883348,wire1721376],
  [wire1986,wire30911,wire860688,wire1028927,wire1721376],
  [wire1986,wire30911,wire860688,wire1047452,wire1721376],
  [wire1986,wire30911,wire860688,wire1721376,wire1836659]]
private def pool5_73 : List (List (List T)) := [chunk4_8, chunk4_20]
private theorem checked5_73 : ∀ w ∈ chunk5_73, ¬ Need 5 w.toFinset := by
  have h : chunk5_73.all (routes 4 pool5_73.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_73,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_20 _ hm
private def chunk5_74 : List (List T) := [[wire1986,wire30911,wire860688,wire1721376,wire1863360],
  [wire1986,wire30911,wire860735,wire1028888,wire1721376],
  [wire1986,wire30911,wire860735,wire1028927,wire1721376],
  [wire1986,wire30911,wire860735,wire1721376,wire1824040]]
private def pool5_74 : List (List (List T)) := [chunk4_8]
private theorem checked5_74 : ∀ w ∈ chunk5_74, ¬ Need 5 w.toFinset := by
  have h : chunk5_74.all (routes 4 pool5_74.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_74,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_8 _ hm
private def chunk5_75 : List (List T) := [[wire1986,wire30911,wire860735,wire1721376,wire1863415],
  [wire1986,wire30911,wire883348,wire1028888,wire1721376],
  [wire1986,wire30911,wire883348,wire1047452,wire1721376],
  [wire1986,wire30911,wire883348,wire1721376,wire1824040]]
private def pool5_75 : List (List (List T)) := [chunk4_4]
private theorem checked5_75 : ∀ w ∈ chunk5_75, ¬ Need 5 w.toFinset := by
  have h : chunk5_75.all (routes 4 pool5_75.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_75,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_4 _ hm
private def chunk5_76 : List (List T) := [[wire1986,wire30911,wire883348,wire1721376,wire1863415],
  [wire1986,wire31108,wire31167,wire860688,wire1721376],
  [wire1986,wire31108,wire860688,wire1721376,wire2097088],
  [wire1986,wire65599,wire260492,wire860688,wire1721376]]
private def pool5_76 : List (List (List T)) := [chunk4_4, chunk4_9, chunk4_19]
private theorem checked5_76 : ∀ w ∈ chunk5_76, ¬ Need 5 w.toFinset := by
  have h : chunk5_76.all (routes 4 pool5_76.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_76,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_9 _ hm
  · exact checked4_19 _ hm
private def chunk5_77 : List (List T) := [[wire1986,wire233736,wire860735,wire1721376,wire2066240],
  [wire1986,wire233736,wire883348,wire1721376,wire2066240],
  [wire1986,wire233791,wire260492,wire375775,wire860688],
  [wire1986,wire233791,wire260492,wire860688,wire1721376]]
private def pool5_77 : List (List (List T)) := []
private theorem checked5_77 : ∀ w ∈ chunk5_77, ¬ Need 5 w.toFinset := by
  have h : chunk5_77.all (routes 4 pool5_77.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_77] at hv
private def chunk5_78 : List (List T) := [[wire1986,wire233791,wire260492,wire860688,wire2057776],
  [wire1986,wire233791,wire260492,wire1236463,wire1721376],
  [wire1986,wire233791,wire260492,wire1721376,wire2057776],
  [wire1986,wire233791,wire860688,wire1721376,wire1836659]]
private def pool5_78 : List (List (List T)) := []
private theorem checked5_78 : ∀ w ∈ chunk5_78, ¬ Need 5 w.toFinset := by
  have h : chunk5_78.all (routes 4 pool5_78.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_78] at hv
private def chunk5_79 : List (List T) := [[wire1986,wire233791,wire860688,wire1721376,wire2066240],
  [wire1986,wire260492,wire860688,wire1721376,wire1863360],
  [wire1986,wire260492,wire860688,wire1721376,wire2066240],
  [wire2018,wire30911,wire233736,wire860688,wire1721376]]
private def pool5_79 : List (List (List T)) := []
private theorem checked5_79 : ∀ w ∈ chunk5_79, ¬ Need 5 w.toFinset := by
  have h : chunk5_79.all (routes 4 pool5_79.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_79] at hv
private def chunk5_80 : List (List T) := [[wire2047,wire30852,wire233736,wire375744,wire860688],
  [wire2047,wire30852,wire233736,wire375775,wire860735],
  [wire2047,wire30852,wire233736,wire860688,wire1721407],
  [wire2047,wire30852,wire233736,wire860688,wire2057791]]
private def pool5_80 : List (List (List T)) := [chunk4_11]
private theorem checked5_80 : ∀ w ∈ chunk5_80, ¬ Need 5 w.toFinset := by
  have h : chunk5_80.all (routes 4 pool5_80.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_80,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_11 _ hm
private def chunk5_81 : List (List T) := [[wire2047,wire30852,wire233736,wire860735,wire1721376],
  [wire2047,wire30852,wire233736,wire860735,wire1721407],
  [wire2047,wire30852,wire233736,wire860735,wire2057776],
  [wire2047,wire30852,wire233736,wire860735,wire2057791]]
private def pool5_81 : List (List (List T)) := [chunk4_11]
private theorem checked5_81 : ∀ w ∈ chunk5_81, ¬ Need 5 w.toFinset := by
  have h : chunk5_81.all (routes 4 pool5_81.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_81,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_11 _ hm
private def chunk5_82 : List (List T) := [[wire2047,wire30852,wire233736,wire883348,wire1721407],
  [wire2047,wire30852,wire233736,wire883391,wire1721376],
  [wire2047,wire30852,wire233736,wire1236416,wire1721376],
  [wire2047,wire30852,wire233736,wire1236463,wire1721407]]
private def pool5_82 : List (List (List T)) := []
private theorem checked5_82 : ∀ w ∈ chunk5_82, ¬ Need 5 w.toFinset := by
  have h : chunk5_82.all (routes 4 pool5_82.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_82] at hv
private def chunk5_83 : List (List T) := [[wire2047,wire30852,wire233736,wire1721376,wire2057791],
  [wire2047,wire30852,wire233736,wire1721407,wire2057776],
  [wire2047,wire30852,wire233736,wire1721407,wire2057791],
  [wire2047,wire30852,wire233791,wire375775,wire860688]]
private def pool5_83 : List (List (List T)) := [chunk4_11, chunk4_12]
private theorem checked5_83 : ∀ w ∈ chunk5_83, ¬ Need 5 w.toFinset := by
  have h : chunk5_83.all (routes 4 pool5_83.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_83,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
private def chunk5_84 : List (List T) := [[wire2047,wire30852,wire233791,wire860688,wire1721376],
  [wire2047,wire30852,wire233791,wire860688,wire1721407],
  [wire2047,wire30852,wire233791,wire860688,wire2057776],
  [wire2047,wire30852,wire233791,wire860735,wire1721376]]
private def pool5_84 : List (List (List T)) := [chunk4_11]
private theorem checked5_84 : ∀ w ∈ chunk5_84, ¬ Need 5 w.toFinset := by
  have h : chunk5_84.all (routes 4 pool5_84.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_84,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_11 _ hm
private def chunk5_85 : List (List T) := [[wire2047,wire30852,wire233791,wire883348,wire1721376],
  [wire2047,wire30852,wire233791,wire1236463,wire1721376],
  [wire2047,wire30852,wire233791,wire1721376,wire2057776],
  [wire2047,wire30852,wire260492,wire860688,wire1721407]]
private def pool5_85 : List (List (List T)) := [chunk4_12, chunk4_19]
private theorem checked5_85 : ∀ w ∈ chunk5_85, ¬ Need 5 w.toFinset := by
  have h : chunk5_85.all (routes 4 pool5_85.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_85,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_12 _ hm
  · exact checked4_19 _ hm
private def chunk5_86 : List (List T) := [[wire2047,wire30852,wire260492,wire860735,wire1721376],
  [wire2047,wire30852,wire260543,wire860688,wire1721376],
  [wire2047,wire30852,wire860688,wire1028888,wire1721407],
  [wire2047,wire30852,wire860688,wire1028927,wire1721376]]
private def pool5_86 : List (List (List T)) := [chunk4_11, chunk4_19]
private theorem checked5_86 : ∀ w ∈ chunk5_86, ¬ Need 5 w.toFinset := by
  have h : chunk5_86.all (routes 4 pool5_86.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_86,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_19 _ hm
private def chunk5_87 : List (List T) := [[wire2047,wire30852,wire860688,wire1721376,wire1824063],
  [wire2047,wire30852,wire860688,wire1721376,wire1863360],
  [wire2047,wire30852,wire860688,wire1721407,wire1824040],
  [wire2047,wire30852,wire860688,wire1721407,wire1824063]]
private def pool5_87 : List (List (List T)) := [chunk4_11, chunk4_12]
private theorem checked5_87 : ∀ w ∈ chunk5_87, ¬ Need 5 w.toFinset := by
  have h : chunk5_87.all (routes 4 pool5_87.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_87,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
private def chunk5_88 : List (List T) := [[wire2047,wire30852,wire860688,wire1721407,wire1863415],
  [wire2047,wire30852,wire860735,wire1028888,wire1721376],
  [wire2047,wire30852,wire860735,wire1028927,wire1721376],
  [wire2047,wire30852,wire860735,wire1721376,wire1824040]]
private def pool5_88 : List (List (List T)) := [chunk4_11]
private theorem checked5_88 : ∀ w ∈ chunk5_88, ¬ Need 5 w.toFinset := by
  have h : chunk5_88.all (routes 4 pool5_88.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_88,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_11 _ hm
private def chunk5_89 : List (List T) := [[wire2047,wire30852,wire860735,wire1721376,wire1863415],
  [wire2047,wire30911,wire233736,wire375775,wire860688],
  [wire2047,wire30911,wire233736,wire860688,wire1721376],
  [wire2047,wire30911,wire233736,wire860688,wire1721407]]
private def pool5_89 : List (List (List T)) := []
private theorem checked5_89 : ∀ w ∈ chunk5_89, ¬ Need 5 w.toFinset := by
  have h : chunk5_89.all (routes 4 pool5_89.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_89] at hv
private def chunk5_90 : List (List T) := [[wire2047,wire30911,wire233736,wire860688,wire2057776],
  [wire2047,wire30911,wire233736,wire860735,wire1721376],
  [wire2047,wire30911,wire233736,wire883348,wire1721376],
  [wire2047,wire30911,wire233736,wire883391,wire1721376]]
private def pool5_90 : List (List (List T)) := [chunk4_13]
private theorem checked5_90 : ∀ w ∈ chunk5_90, ¬ Need 5 w.toFinset := by
  have h : chunk5_90.all (routes 4 pool5_90.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_90,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_13 _ hm
private def chunk5_91 : List (List T) := [[wire2047,wire30911,wire233736,wire1236463,wire1721376],
  [wire2047,wire30911,wire233736,wire1721376,wire2057776],
  [wire2047,wire30911,wire233791,wire860688,wire1721376],
  [wire2047,wire30911,wire260492,wire860688,wire1721376]]
private def pool5_91 : List (List (List T)) := [chunk4_13]
private theorem checked5_91 : ∀ w ∈ chunk5_91, ¬ Need 5 w.toFinset := by
  have h : chunk5_91.all (routes 4 pool5_91.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_91,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_13 _ hm
private def chunk5_92 : List (List T) := [[wire2047,wire30911,wire260543,wire860688,wire1721376],
  [wire2047,wire30911,wire860688,wire1028888,wire1721376],
  [wire2047,wire30911,wire860688,wire1721376,wire1824040],
  [wire2047,wire30911,wire860688,wire1721376,wire1863415]]
private def pool5_92 : List (List (List T)) := [chunk4_5, chunk4_13]
private theorem checked5_92 : ∀ w ∈ chunk5_92, ¬ Need 5 w.toFinset := by
  have h : chunk5_92.all (routes 4 pool5_92.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_92,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_13 _ hm
private def chunk5_93 : List (List T) := [[wire2047,wire233736,wire260492,wire860688,wire1721407],
  [wire2047,wire233736,wire260492,wire860735,wire1721376],
  [wire2047,wire233736,wire260543,wire860688,wire1721376],
  [wire2047,wire233736,wire860688,wire1721376,wire1735871]]
private def pool5_93 : List (List (List T)) := []
private theorem checked5_93 : ∀ w ∈ chunk5_93, ¬ Need 5 w.toFinset := by
  have h : chunk5_93.all (routes 4 pool5_93.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_93] at hv
private def chunk5_94 : List (List T) := [[wire2047,wire233736,wire860688,wire1721376,wire2066240],
  [wire2047,wire233736,wire860688,wire1721407,wire1735844],
  [wire2047,wire233736,wire860688,wire1721407,wire1735871],
  [wire2047,wire233736,wire860688,wire1721407,wire2066299]]
private def pool5_94 : List (List (List T)) := []
private theorem checked5_94 : ∀ w ∈ chunk5_94, ¬ Need 5 w.toFinset := by
  have h : chunk5_94.all (routes 4 pool5_94.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_94] at hv
private def chunk5_95 : List (List T) := [[wire2047,wire233736,wire860735,wire1721376,wire1735844],
  [wire2047,wire233736,wire860735,wire1721376,wire2066299],
  [wire2047,wire233791,wire260492,wire860688,wire1721376],
  [wire2047,wire233791,wire260543,wire860688,wire1721376]]
private def pool5_95 : List (List (List T)) := []
private theorem checked5_95 : ∀ w ∈ chunk5_95, ¬ Need 5 w.toFinset := by
  have h : chunk5_95.all (routes 4 pool5_95.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_95] at hv
private def chunk5_96 : List (List T) := [[wire2047,wire233791,wire860688,wire1721376,wire1735844],
  [wire2047,wire233791,wire860688,wire1721376,wire2066299],
  [wire4352,wire30911,wire32710,wire860688,wire1721376],
  [wire4415,wire30852,wire32710,wire860688,wire1721376]]
private def pool5_96 : List (List (List T)) := [chunk4_15, chunk4_17, chunk4_19]
private theorem checked5_96 : ∀ w ∈ chunk5_96, ¬ Need 5 w.toFinset := by
  have h : chunk5_96.all (routes 4 pool5_96.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_96,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_15 _ hm
  · exact checked4_17 _ hm
  · exact checked4_19 _ hm
private def chunk5_97 : List (List T) := [[wire18370,wire30911,wire233736,wire860688,wire1721376],
  [wire30852,wire30911,wire860688,wire1721376,wire2095421],
  [wire30852,wire32767,wire233736,wire860735,wire1721376],
  [wire30852,wire32767,wire233736,wire883391,wire1721376]]
private def pool5_97 : List (List (List T)) := [chunk4_15, chunk4_18, chunk4_19, chunk4_20]
private theorem checked5_97 : ∀ w ∈ chunk5_97, ¬ Need 5 w.toFinset := by
  have h : chunk5_97.all (routes 4 pool5_97.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_97,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_15 _ hm
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
  · exact checked4_20 _ hm
private def chunk5_98 : List (List T) := [[wire30852,wire32767,wire233791,wire860688,wire1721376],
  [wire30852,wire32767,wire260543,wire860688,wire1721376],
  [wire30852,wire66048,wire233791,wire235466,wire1721376],
  [wire30852,wire233736,wire860688,wire1721407,wire2095104]]
private def pool5_98 : List (List (List T)) := [chunk4_16, chunk4_19, chunk4_20]
private theorem checked5_98 : ∀ w ∈ chunk5_98, ¬ Need 5 w.toFinset := by
  have h : chunk5_98.all (routes 4 pool5_98.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_98,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_16 _ hm
  · exact checked4_19 _ hm
  · exact checked4_20 _ hm
private def chunk5_99 : List (List T) := [[wire30852,wire233736,wire860735,wire1721376,wire2095104],
  [wire30852,wire233791,wire235466,wire375775,wire860688],
  [wire30852,wire233791,wire235466,wire860688,wire1721376],
  [wire30852,wire233791,wire235466,wire860688,wire2057776]]
private def pool5_99 : List (List (List T)) := []
private theorem checked5_99 : ∀ w ∈ chunk5_99, ¬ Need 5 w.toFinset := by
  have h : chunk5_99.all (routes 4 pool5_99.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_99] at hv
private def chunk5_100 : List (List T) := [[wire30852,wire233791,wire235466,wire883348,wire1721376],
  [wire30852,wire233791,wire235466,wire1236463,wire1721376],
  [wire30852,wire233791,wire235466,wire1721376,wire2057776],
  [wire30852,wire233791,wire262094,wire860688,wire1721376]]
private def pool5_100 : List (List (List T)) := [chunk4_16]
private theorem checked5_100 : ∀ w ∈ chunk5_100, ¬ Need 5 w.toFinset := by
  have h : chunk5_100.all (routes 4 pool5_100.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_100,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_16 _ hm
private def chunk5_101 : List (List T) := [[wire30852,wire233791,wire860688,wire1721376,wire1861685],
  [wire30852,wire233791,wire860688,wire1721376,wire2095104],
  [wire30852,wire235466,wire260543,wire860688,wire1721376],
  [wire30852,wire235466,wire860688,wire1721376,wire1863360]]
private def pool5_101 : List (List (List T)) := []
private theorem checked5_101 : ∀ w ∈ chunk5_101, ¬ Need 5 w.toFinset := by
  have h : chunk5_101.all (routes 4 pool5_101.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_101] at hv
private def chunk5_102 : List (List T) := [[wire30852,wire260543,wire262094,wire860688,wire1721376],
  [wire30852,wire860688,wire1721376,wire2095421,wire2097088],
  [wire30911,wire32710,wire233736,wire375775,wire860688],
  [wire30911,wire32710,wire233736,wire860688,wire1721376]]
private def pool5_102 : List (List (List T)) := []
private theorem checked5_102 : ∀ w ∈ chunk5_102, ¬ Need 5 w.toFinset := by
  have h : chunk5_102.all (routes 4 pool5_102.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_102] at hv
private def chunk5_103 : List (List T) := [[wire30911,wire32710,wire233736,wire860688,wire2057776],
  [wire30911,wire32710,wire233736,wire860735,wire1721376],
  [wire30911,wire32710,wire233736,wire883348,wire1721376],
  [wire30911,wire32710,wire233736,wire883391,wire1721376]]
private def pool5_103 : List (List (List T)) := [chunk4_17]
private theorem checked5_103 : ∀ w ∈ chunk5_103, ¬ Need 5 w.toFinset := by
  have h : chunk5_103.all (routes 4 pool5_103.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_103,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_17 _ hm
private def chunk5_104 : List (List T) := [[wire30911,wire32710,wire233736,wire1236463,wire1721376],
  [wire30911,wire32710,wire233736,wire1721376,wire2057776],
  [wire30911,wire32710,wire233791,wire860688,wire1721376],
  [wire30911,wire32710,wire260492,wire860688,wire1721376]]
private def pool5_104 : List (List (List T)) := [chunk4_17]
private theorem checked5_104 : ∀ w ∈ chunk5_104, ¬ Need 5 w.toFinset := by
  have h : chunk5_104.all (routes 4 pool5_104.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_104,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_17 _ hm
private def chunk5_105 : List (List T) := [[wire30911,wire32710,wire260543,wire860688,wire1721376],
  [wire30911,wire32710,wire860688,wire1028888,wire1721376],
  [wire30911,wire32710,wire860688,wire1721376,wire1824040],
  [wire30911,wire32710,wire860688,wire1721376,wire1863415]]
private def pool5_105 : List (List (List T)) := [chunk4_15, chunk4_17]
private theorem checked5_105 : ∀ w ∈ chunk5_105, ¬ Need 5 w.toFinset := by
  have h : chunk5_105.all (routes 4 pool5_105.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_105,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_15 _ hm
  · exact checked4_17 _ hm
private def chunk5_106 : List (List T) := [[wire30911,wire32767,wire233736,wire860735,wire1721376],
  [wire30911,wire32767,wire233736,wire883348,wire1721376],
  [wire30911,wire32767,wire233791,wire860688,wire1721376],
  [wire30911,wire32767,wire260492,wire860688,wire1721376]]
private def pool5_106 : List (List (List T)) := [chunk4_19, chunk4_20]
private theorem checked5_106 : ∀ w ∈ chunk5_106, ¬ Need 5 w.toFinset := by
  have h : chunk5_106.all (routes 4 pool5_106.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_106,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_19 _ hm
  · exact checked4_20 _ hm
private def chunk5_107 : List (List T) := [[wire30911,wire233736,wire235466,wire860735,wire1721376],
  [wire30911,wire233736,wire235466,wire883348,wire1721376],
  [wire30911,wire233736,wire235519,wire860688,wire1721376],
  [wire30911,wire233736,wire262094,wire860688,wire1721376]]
private def pool5_107 : List (List (List T)) := []
private theorem checked5_107 : ∀ w ∈ chunk5_107, ¬ Need 5 w.toFinset := by
  have h : chunk5_107.all (routes 4 pool5_107.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_107] at hv
private def chunk5_108 : List (List T) := [[wire30911,wire233736,wire860688,wire1721376,wire2064441],
  [wire30911,wire233736,wire860688,wire1721376,wire2095104],
  [wire30911,wire233736,wire860735,wire1721376,wire2095165],
  [wire30911,wire233736,wire883348,wire1721376,wire2095165]]
private def pool5_108 : List (List (List T)) := [chunk4_18]
private theorem checked5_108 : ∀ w ∈ chunk5_108, ¬ Need 5 w.toFinset := by
  have h : chunk5_108.all (routes 4 pool5_108.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_108,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_18 _ hm
private def chunk5_109 : List (List T) := [[wire30911,wire233791,wire235466,wire860688,wire1721376],
  [wire30911,wire233791,wire235519,wire860688,wire1721376],
  [wire30911,wire233791,wire860688,wire1721376,wire2095165],
  [wire30911,wire235466,wire260492,wire860688,wire1721376]]
private def pool5_109 : List (List (List T)) := []
private theorem checked5_109 : ∀ w ∈ chunk5_109, ¬ Need 5 w.toFinset := by
  have h : chunk5_109.all (routes 4 pool5_109.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_109] at hv
private def chunk5_110 : List (List T) := [[wire30911,wire260492,wire262094,wire860688,wire1721376],
  [wire30911,wire260492,wire860688,wire1721376,wire2095165],
  [wire32710,wire233736,wire233791,wire883348,wire1721376],
  [wire32710,wire233736,wire260543,wire860688,wire1721376]]
private def pool5_110 : List (List (List T)) := []
private theorem checked5_110 : ∀ w ∈ chunk5_110, ¬ Need 5 w.toFinset := by
  have h : chunk5_110.all (routes 4 pool5_110.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_110] at hv
private def chunk5_111 : List (List T) := [[wire32710,wire233736,wire860688,wire1721376,wire2066240],
  [wire32710,wire233736,wire883348,wire1721376,wire2097088],
  [wire32710,wire233791,wire260492,wire860688,wire1721376],
  [wire32710,wire260492,wire260543,wire860688,wire1721376]]
private def pool5_111 : List (List (List T)) := []
private theorem checked5_111 : ∀ w ∈ chunk5_111, ¬ Need 5 w.toFinset := by
  have h : chunk5_111.all (routes 4 pool5_111.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_111] at hv
private def chunk5_112 : List (List T) := [[wire32710,wire260492,wire860688,wire1721376,wire2097088],
  [wire233736,wire235519,wire260543,wire860688,wire1721376],
  [wire233736,wire260543,wire262094,wire860688,wire1721376],
  [wire233791,wire235466,wire260492,wire860688,wire1721376]]
private def pool5_112 : List (List (List T)) := []
private theorem checked5_112 : ∀ w ∈ chunk5_112, ¬ Need 5 w.toFinset := by
  have h : chunk5_112.all (routes 4 pool5_112.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_112] at hv
private def chunk5_113 : List (List T) := [[wire233791,wire235466,wire260543,wire860688,wire1721376],
  [wire233791,wire235466,wire860688,wire1721376,wire1735844],
  [wire233791,wire235466,wire860688,wire1721376,wire2066299],
  [wire233791,wire235519,wire260492,wire860688,wire1721376]]
private def pool5_113 : List (List (List T)) := []
private theorem checked5_113 : ∀ w ∈ chunk5_113, ¬ Need 5 w.toFinset := by
  have h : chunk5_113.all (routes 4 pool5_113.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_113] at hv
private def chunk5_114 : List (List T) := [[wire233791,wire260492,wire262094,wire860688,wire1721376],
  [wire233791,wire260492,wire860688,wire1721376,wire2095165],
  [wire235466,wire260492,wire260543,wire860688,wire1721376],
  [wire235466,wire260492,wire860688,wire1721376,wire2097088]]
private def pool5_114 : List (List (List T)) := []
private theorem checked5_114 : ∀ w ∈ chunk5_114, ¬ Need 5 w.toFinset := by
  have h : chunk5_114.all (routes 4 pool5_114.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_114] at hv
#print axioms checked5_114
private def chunk6_0 : List (List T) := [[wire32,wire1986,wire30911,wire233736,wire860688,wire1721376],
  [wire55,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire55,wire1986,wire30852,wire860688,wire1721376,wire1863415],
  [wire59,wire1986,wire30852,wire233736,wire860688,wire1721376]]
private def pool6_0 : List (List (List T)) := [chunk5_0, chunk5_65, chunk5_68, chunk5_79]
private theorem checked6_0 : ∀ w ∈ chunk6_0, ¬ Need 6 w.toFinset := by
  have h : chunk6_0.all (routes 5 pool6_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_65 _ hm
  · exact checked5_68 _ hm
  · exact checked5_79 _ hm
private def chunk6_1 : List (List T) := [[wire59,wire1986,wire233736,wire860688,wire1721376,wire2066299],
  [wire63,wire256,wire1986,wire30852,wire375775,wire860688],
  [wire63,wire256,wire1986,wire30852,wire860688,wire1721376],
  [wire63,wire256,wire1986,wire30852,wire860688,wire1721407]]
private def pool6_1 : List (List (List T)) := [chunk5_9, chunk5_10, chunk5_11, chunk5_12, chunk5_19, chunk5_20, chunk5_51, chunk5_52, chunk5_53]
private theorem checked6_1 : ∀ w ∈ chunk6_1, ¬ Need 6 w.toFinset := by
  have h : chunk6_1.all (routes 5 pool6_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_53 _ hm
private def chunk6_2 : List (List T) := [[wire63,wire256,wire1986,wire30852,wire860688,wire1721632],
  [wire63,wire256,wire1986,wire30852,wire860688,wire2057776],
  [wire63,wire256,wire1986,wire30852,wire860735,wire1721376],
  [wire63,wire256,wire1986,wire30852,wire860944,wire1721376]]
private def pool6_2 : List (List (List T)) := [chunk5_9, chunk5_11, chunk5_12, chunk5_13, chunk5_20, chunk5_21, chunk5_50, chunk5_51, chunk5_53, chunk5_54]
private theorem checked6_2 : ∀ w ∈ chunk6_2, ¬ Need 6 w.toFinset := by
  have h : chunk6_2.all (routes 5 pool6_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_50 _ hm
  · exact checked5_51 _ hm
  · exact checked5_53 _ hm
  · exact checked5_54 _ hm
private def chunk6_3 : List (List T) := [[wire63,wire256,wire1986,wire30852,wire883348,wire1721376],
  [wire63,wire256,wire1986,wire30852,wire1236463,wire1721376],
  [wire63,wire256,wire1986,wire30852,wire1721376,wire2057776],
  [wire63,wire256,wire1986,wire30911,wire860688,wire1721376]]
private def pool6_3 : List (List (List T)) := [chunk5_0, chunk5_14, chunk5_16, chunk5_17, chunk5_18, chunk5_19, chunk5_21, chunk5_22, chunk5_23, chunk5_50, chunk5_51, chunk5_55]
private theorem checked6_3 : ∀ w ∈ chunk6_3, ¬ Need 6 w.toFinset := by
  have h : chunk6_3.all (routes 5 pool6_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_14 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_50 _ hm
  · exact checked5_51 _ hm
  · exact checked5_55 _ hm
private def chunk6_4 : List (List T) := [[wire63,wire256,wire1986,wire31108,wire860688,wire1721376],
  [wire63,wire256,wire1986,wire860688,wire1721376,wire1735844],
  [wire63,wire256,wire1986,wire860688,wire1721376,wire2066299],
  [wire63,wire256,wire2047,wire30852,wire860688,wire1721376]]
private def pool6_4 : List (List (List T)) := [chunk5_20, chunk5_21, chunk5_26, chunk5_27, chunk5_28, chunk5_29, chunk5_30, chunk5_51, chunk5_56, chunk5_57]
private theorem checked6_4 : ∀ w ∈ chunk6_4, ¬ Need 6 w.toFinset := by
  have h : chunk6_4.all (routes 5 pool6_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_51 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
private def chunk6_5 : List (List T) := [[wire63,wire256,wire30852,wire32710,wire860688,wire1721376],
  [wire63,wire256,wire30852,wire860688,wire1721376,wire2095165],
  [wire63,wire258,wire1986,wire30852,wire860688,wire1721376],
  [wire63,wire264,wire1986,wire30852,wire860688,wire1721376]]
private def pool6_5 : List (List (List T)) := [chunk5_0, chunk5_9, chunk5_10, chunk5_13, chunk5_22, chunk5_32, chunk5_33, chunk5_35, chunk5_36, chunk5_37, chunk5_39, chunk5_51, chunk5_53, chunk5_57]
private theorem checked6_5 : ∀ w ∈ chunk6_5, ¬ Need 6 w.toFinset := by
  have h : chunk6_5.all (routes 5 pool6_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_13 _ hm
  · exact checked5_22 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_39 _ hm
  · exact checked5_51 _ hm
  · exact checked5_53 _ hm
  · exact checked5_57 _ hm
private def chunk6_6 : List (List T) := [[wire63,wire264,wire2047,wire30852,wire860688,wire1721376],
  [wire63,wire319,wire1986,wire30852,wire860688,wire1721376],
  [wire63,wire384,wire1986,wire30852,wire860688,wire1721376],
  [wire63,wire768,wire1986,wire30852,wire860688,wire1721376]]
private def pool6_6 : List (List (List T)) := [chunk5_10, chunk5_11, chunk5_13, chunk5_20, chunk5_23, chunk5_29, chunk5_30, chunk5_31, chunk5_52, chunk5_53, chunk5_54, chunk5_55, chunk5_57, chunk5_58]
private theorem checked6_6 : ∀ w ∈ chunk6_6, ¬ Need 6 w.toFinset := by
  have h : chunk6_6.all (routes 5 pool6_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_10 _ hm
  · exact checked5_11 _ hm
  · exact checked5_13 _ hm
  · exact checked5_20 _ hm
  · exact checked5_23 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_52 _ hm
  · exact checked5_53 _ hm
  · exact checked5_54 _ hm
  · exact checked5_55 _ hm
  · exact checked5_57 _ hm
  · exact checked5_58 _ hm
private def chunk6_7 : List (List T) := [[wire63,wire1280,wire1986,wire30852,wire860688,wire1721376],
  [wire63,wire1536,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1536,wire30852,wire233736,wire860688,wire2057776],
  [wire63,wire1536,wire30852,wire233736,wire1721376,wire2057776]]
private def pool6_7 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_9, chunk5_14, chunk5_23, chunk5_58, chunk5_59]
private theorem checked6_7 : ∀ w ∈ chunk6_7, ¬ Need 6 w.toFinset := by
  have h : chunk6_7.all (routes 5 pool6_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_9 _ hm
  · exact checked5_14 _ hm
  · exact checked5_23 _ hm
  · exact checked5_58 _ hm
  · exact checked5_59 _ hm
private def chunk6_8 : List (List T) := [[wire63,wire1730,wire1986,wire30852,wire860688,wire1721376],
  [wire63,wire1730,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1730,wire30852,wire860688,wire1721376],
  [wire63,wire1730,wire30852,wire860688,wire1721376,wire1863415]]
private def pool6_8 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_2, chunk5_3, chunk5_4, chunk5_5, chunk5_32, chunk5_35, chunk5_59]
private theorem checked6_8 : ∀ w ∈ chunk6_8, ¬ Need 6 w.toFinset := by
  have h : chunk6_8.all (routes 5 pool6_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_5 _ hm
  · exact checked5_32 _ hm
  · exact checked5_35 _ hm
  · exact checked5_59 _ hm
private def chunk6_9 : List (List T) := [[wire63,wire1858,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1858,wire233736,wire860688,wire1721376,wire2066299],
  [wire63,wire1984,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire4352,wire30852,wire860688,wire1721376]]
private def pool6_9 : List (List (List T)) := [chunk5_5, chunk5_14, chunk5_20, chunk5_59]
private theorem checked6_9 : ∀ w ∈ chunk6_9, ¬ Need 6 w.toFinset := by
  have h : chunk6_9.all (routes 5 pool6_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_14 _ hm
  · exact checked5_20 _ hm
  · exact checked5_59 _ hm
private def chunk6_10 : List (List T) := [[wire63,wire1986,wire8192,wire30852,wire233736,wire2057776],
  [wire63,wire1986,wire8192,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire8320,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire14468,wire233736,wire375775,wire860688]]
private def pool6_10 : List (List (List T)) := [chunk5_5, chunk5_8, chunk5_25, chunk5_31, chunk5_60]
private theorem checked6_10 : ∀ w ∈ chunk6_10, ¬ Need 6 w.toFinset := by
  have h : chunk6_10.all (routes 5 pool6_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_8 _ hm
  · exact checked5_25 _ hm
  · exact checked5_31 _ hm
  · exact checked5_60 _ hm
private def chunk6_11 : List (List T) := [[wire63,wire1986,wire14468,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire16384,wire30852,wire233736,wire2057776],
  [wire63,wire1986,wire26756,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire26756,wire860688,wire1721376,wire1863415]]
private def pool6_11 : List (List (List T)) := [chunk5_1, chunk5_6, chunk5_8, chunk5_32, chunk5_61]
private theorem checked6_11 : ∀ w ∈ chunk6_11, ¬ Need 6 w.toFinset := by
  have h : chunk6_11.all (routes 5 pool6_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_6 _ hm
  · exact checked5_8 _ hm
  · exact checked5_32 _ hm
  · exact checked5_61 _ hm
private def chunk6_12 : List (List T) := [[wire63,wire1986,wire30848,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire31108,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire39375,wire233736,wire860688],
  [wire63,wire1986,wire30852,wire39375,wire233736,wire860688,wire1721376]]
private def pool6_12 : List (List (List T)) := [chunk5_6, chunk5_7, chunk5_14, chunk5_20, chunk5_21, chunk5_34, chunk5_39, chunk5_62, chunk5_64]
private theorem checked6_12 : ∀ w ∈ chunk6_12, ¬ Need 6 w.toFinset := by
  have h : chunk6_12.all (routes 5 pool6_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_14 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_34 _ hm
  · exact checked5_39 _ hm
  · exact checked5_62 _ hm
  · exact checked5_64 _ hm
private def chunk6_13 : List (List T) := [[wire63,wire1986,wire30852,wire39375,wire233736,wire860688,wire2057776],
  [wire63,wire1986,wire30852,wire39375,wire233736,wire1721376],
  [wire63,wire1986,wire30852,wire65792,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire66048,wire233736,wire1721376]]
private def pool6_13 : List (List (List T)) := [chunk5_0, chunk5_6, chunk5_7, chunk5_11, chunk5_23, chunk5_34]
private theorem checked6_13 : ∀ w ∈ chunk6_13, ¬ Need 6 w.toFinset := by
  have h : chunk6_13.all (routes 5 pool6_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_11 _ hm
  · exact checked5_23 _ hm
  · exact checked5_34 _ hm
private def chunk6_14 : List (List T) := [[wire63,wire1986,wire30852,wire102664,wire375775,wire860688],
  [wire63,wire1986,wire30852,wire102664,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire131328,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire168200,wire860688,wire1721376]]
private def pool6_14 : List (List (List T)) := [chunk5_9, chunk5_15, chunk5_24]
private theorem checked6_14 : ∀ w ∈ chunk6_14, ¬ Need 6 w.toFinset := by
  have h : chunk6_14.all (routes 5 pool6_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_15 _ hm
  · exact checked5_24 _ hm
private def chunk6_15 : List (List T) := [[wire63,wire1986,wire30852,wire168200,wire1236463,wire1721376],
  [wire63,wire1986,wire30852,wire229640,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233728,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire336400,wire375775]]
private def pool6_15 : List (List (List T)) := [chunk5_24]
private theorem checked6_15 : ∀ w ∈ chunk6_15, ¬ Need 6 w.toFinset := by
  have h : chunk6_15.all (routes 5 pool6_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_24 _ hm
private def chunk6_16 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire336400,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire375744,wire860688],
  [wire63,wire1986,wire30852,wire233736,wire375775,wire860688],
  [wire63,wire1986,wire30852,wire233736,wire375775,wire860735]]
private def pool6_16 : List (List (List T)) := [chunk5_64, chunk5_80]
private theorem checked6_16 : ∀ w ∈ chunk6_16, ¬ Need 6 w.toFinset := by
  have h : chunk6_16.all (routes 5 pool6_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_64 _ hm
  · exact checked5_80 _ hm
private def chunk6_17 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire375775,wire883348],
  [wire63,wire1986,wire30852,wire233736,wire375775,wire1236463],
  [wire63,wire1986,wire30852,wire233736,wire375775,wire2057776],
  [wire63,wire1986,wire30852,wire233736,wire375807,wire860688]]
private def pool6_17 : List (List (List T)) := [chunk5_6, chunk5_39, chunk5_65]
private theorem checked6_17 : ∀ w ∈ chunk6_17, ¬ Need 6 w.toFinset := by
  have h : chunk6_17.all (routes 5 pool6_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_39 _ hm
  · exact checked5_65 _ hm
private def chunk6_18 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire852496,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860672,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire900063],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1197088]]
private def pool6_18 : List (List (List T)) := [chunk5_8, chunk5_25]
private theorem checked6_18 : ∀ w ∈ chunk6_18, ¬ Need 6 w.toFinset := by
  have h : chunk6_18.all (routes 5 pool6_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_25 _ hm
private def chunk6_19 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1721344],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721378],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721380]]
private def pool6_19 : List (List (List T)) := [chunk5_65]
private theorem checked6_19 : ∀ w ∈ chunk6_19, ¬ Need 6 w.toFinset := by
  have h : chunk6_19.all (routes 5 pool6_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_65 _ hm
private def chunk6_20 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1721384],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721392],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721407],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721504]]
private def pool6_20 : List (List (List T)) := [chunk5_80]
private theorem checked6_20 : ∀ w ∈ chunk6_20, ¬ Need 6 w.toFinset := by
  have h : chunk6_20.all (routes 5 pool6_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_80 _ hm
private def chunk6_21 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1721632],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721888],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1725472],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1729568]]
private def pool6_21 : List (List (List T)) := [chunk5_25]
private theorem checked6_21 : ∀ w ∈ chunk6_21, ¬ Need 6 w.toFinset := by
  have h : chunk6_21.all (routes 5 pool6_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_25 _ hm
private def chunk6_22 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1786912],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire2057776],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire2057791],
  [wire63,wire1986,wire30852,wire233736,wire860690,wire1721376]]
private def pool6_22 : List (List (List T)) := [chunk5_15, chunk5_25, chunk5_80]
private theorem checked6_22 : ∀ w ∈ chunk6_22, ¬ Need 6 w.toFinset := by
  have h : chunk6_22.all (routes 5 pool6_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_25 _ hm
  · exact checked5_80 _ hm
private def chunk6_23 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860692,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860696,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860720,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860735,wire1721376]]
private def pool6_23 : List (List (List T)) := [chunk5_65, chunk5_66, chunk5_81]
private theorem checked6_23 : ∀ w ∈ chunk6_23, ¬ Need 6 w.toFinset := by
  have h : chunk6_23.all (routes 5 pool6_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
  · exact checked5_81 _ hm
private def chunk6_24 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860735,wire1721407],
  [wire63,wire1986,wire30852,wire233736,wire860735,wire2057776],
  [wire63,wire1986,wire30852,wire233736,wire860735,wire2057791],
  [wire63,wire1986,wire30852,wire233736,wire860816,wire1721376]]
private def pool6_24 : List (List (List T)) := [chunk5_15, chunk5_16, chunk5_63, chunk5_66, chunk5_81]
private theorem checked6_24 : ∀ w ∈ chunk6_24, ¬ Need 6 w.toFinset := by
  have h : chunk6_24.all (routes 5 pool6_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_63 _ hm
  · exact checked5_66 _ hm
  · exact checked5_81 _ hm
private def chunk6_25 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860944,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire861712,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire862162,wire2057776],
  [wire63,wire1986,wire30852,wire233736,wire864784,wire1721376]]
private def pool6_25 : List (List (List T)) := [chunk5_5]
private theorem checked6_25 : ∀ w ∈ chunk6_25, ¬ Need 6 w.toFinset := by
  have h : chunk6_25.all (routes 5 pool6_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_5 _ hm
private def chunk6_26 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire877072,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire883348,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire883348,wire1721407],
  [wire63,wire1986,wire30852,wire233736,wire883391,wire1721376]]
private def pool6_26 : List (List (List T)) := [chunk5_40, chunk5_67, chunk5_82]
private theorem checked6_26 : ∀ w ∈ chunk6_26, ¬ Need 6 w.toFinset := by
  have h : chunk6_26.all (routes 5 pool6_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_40 _ hm
  · exact checked5_67 _ hm
  · exact checked5_82 _ hm
private def chunk6_27 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire991760,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire1028888,wire2057776],
  [wire63,wire1986,wire30852,wire233736,wire1197088,wire1236463],
  [wire63,wire1986,wire30852,wire233736,wire1213803,wire1721376]]
private def pool6_27 : List (List (List T)) := [chunk5_15, chunk5_40, chunk5_67]
private theorem checked6_27 : ∀ w ∈ chunk6_27, ¬ Need 6 w.toFinset := by
  have h : chunk6_27.all (routes 5 pool6_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_40 _ hm
  · exact checked5_67 _ hm
private def chunk6_28 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire1236416,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire1236463,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire1236463,wire1721407],
  [wire63,wire1986,wire30852,wire233736,wire1236463,wire2057776]]
private def pool6_28 : List (List (List T)) := [chunk5_67, chunk5_82]
private theorem checked6_28 : ∀ w ∈ chunk6_28, ¬ Need 6 w.toFinset := by
  have h : chunk6_28.all (routes 5 pool6_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_67 _ hm
  · exact checked5_82 _ hm
private def chunk6_29 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire1236479,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire1244655,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire1721376,wire1760751],
  [wire63,wire1986,wire30852,wire233736,wire1721376,wire2057776]]
private def pool6_29 : List (List (List T)) := [chunk5_17, chunk5_26]
private theorem checked6_29 : ∀ w ∈ chunk6_29, ¬ Need 6 w.toFinset := by
  have h : chunk6_29.all (routes 5 pool6_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_17 _ hm
  · exact checked5_26 _ hm
private def chunk6_30 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire1721376,wire2057791],
  [wire63,wire1986,wire30852,wire233736,wire1721376,wire2064052],
  [wire63,wire1986,wire30852,wire233736,wire1721407,wire2057776],
  [wire63,wire1986,wire30852,wire233736,wire1721407,wire2057791]]
private def pool6_30 : List (List (List T)) := [chunk5_18, chunk5_83]
private theorem checked6_30 : ∀ w ∈ chunk6_30, ¬ Need 6 w.toFinset := by
  have h : chunk6_30.all (routes 5 pool6_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_18 _ hm
  · exact checked5_83 _ hm
private def chunk6_31 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire1722338,wire2057776],
  [wire63,wire1986,wire30852,wire233736,wire1824040,wire2057776],
  [wire63,wire1986,wire30852,wire233738,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233740,wire860688,wire1721376]]
private def pool6_31 : List (List (List T)) := [chunk5_17, chunk5_26]
private theorem checked6_31 : ∀ w ∈ chunk6_31, ¬ Need 6 w.toFinset := by
  have h : chunk6_31.all (routes 5 pool6_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_17 _ hm
  · exact checked5_26 _ hm
private def chunk6_32 : List (List T) := [[wire63,wire1986,wire30852,wire233752,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233768,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233791,wire375775,wire860688],
  [wire63,wire1986,wire30852,wire233791,wire860688,wire1721376]]
private def pool6_32 : List (List (List T)) := [chunk5_68, chunk5_83, chunk5_84]
private theorem checked6_32 : ∀ w ∈ chunk6_32, ¬ Need 6 w.toFinset := by
  have h : chunk6_32.all (routes 5 pool6_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_68 _ hm
  · exact checked5_83 _ hm
  · exact checked5_84 _ hm
private def chunk6_33 : List (List T) := [[wire63,wire1986,wire30852,wire233791,wire860688,wire1721407],
  [wire63,wire1986,wire30852,wire233791,wire860688,wire2057776],
  [wire63,wire1986,wire30852,wire233791,wire860735,wire1721376],
  [wire63,wire1986,wire30852,wire233791,wire883348,wire1721376]]
private def pool6_33 : List (List (List T)) := [chunk5_15, chunk5_41, chunk5_63, chunk5_68, chunk5_69, chunk5_84, chunk5_85]
private theorem checked6_33 : ∀ w ∈ chunk6_33, ¬ Need 6 w.toFinset := by
  have h : chunk6_33.all (routes 5 pool6_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_41 _ hm
  · exact checked5_63 _ hm
  · exact checked5_68 _ hm
  · exact checked5_69 _ hm
  · exact checked5_84 _ hm
  · exact checked5_85 _ hm
private def chunk6_34 : List (List T) := [[wire63,wire1986,wire30852,wire233791,wire1236463,wire1721376],
  [wire63,wire1986,wire30852,wire233791,wire1721376,wire2057776],
  [wire63,wire1986,wire30852,wire233864,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire234248,wire860688,wire1721376]]
private def pool6_34 : List (List (List T)) := [chunk5_18, chunk5_70, chunk5_85]
private theorem checked6_34 : ∀ w ∈ chunk6_34, ¬ Need 6 w.toFinset := by
  have h : chunk6_34.all (routes 5 pool6_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_18 _ hm
  · exact checked5_70 _ hm
  · exact checked5_85 _ hm
private def chunk6_35 : List (List T) := [[wire63,wire1986,wire30852,wire234760,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire241928,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire250120,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire260492,wire375775,wire860688]]
private def pool6_35 : List (List (List T)) := [chunk5_8, chunk5_41, chunk5_70]
private theorem checked6_35 : ∀ w ∈ chunk6_35, ¬ Need 6 w.toFinset := by
  have h : chunk6_35.all (routes 5 pool6_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_41 _ hm
  · exact checked5_70 _ hm
private def chunk6_36 : List (List T) := [[wire63,wire1986,wire30852,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire260492,wire860688,wire1721407],
  [wire63,wire1986,wire30852,wire260492,wire860688,wire2057776],
  [wire63,wire1986,wire30852,wire260492,wire860735,wire1721376]]
private def pool6_36 : List (List (List T)) := [chunk5_5, chunk5_41, chunk5_42, chunk5_71, chunk5_85, chunk5_86]
private theorem checked6_36 : ∀ w ∈ chunk6_36, ¬ Need 6 w.toFinset := by
  have h : chunk6_36.all (routes 5 pool6_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_36,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_71 _ hm
  · exact checked5_85 _ hm
  · exact checked5_86 _ hm
private def chunk6_37 : List (List T) := [[wire63,wire1986,wire30852,wire260492,wire883348,wire1721376],
  [wire63,wire1986,wire30852,wire260492,wire1236463,wire1721376],
  [wire63,wire1986,wire30852,wire260492,wire1721376,wire2057776],
  [wire63,wire1986,wire30852,wire260543,wire860688,wire1721376]]
private def pool6_37 : List (List (List T)) := [chunk5_26, chunk5_42, chunk5_43, chunk5_71, chunk5_72, chunk5_86]
private theorem checked6_37 : ∀ w ∈ chunk6_37, ¬ Need 6 w.toFinset := by
  have h : chunk6_37.all (routes 5 pool6_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_26 _ hm
  · exact checked5_42 _ hm
  · exact checked5_43 _ hm
  · exact checked5_71 _ hm
  · exact checked5_72 _ hm
  · exact checked5_86 _ hm
private def chunk6_38 : List (List T) := [[wire63,wire1986,wire30852,wire273111,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire375775,wire860688,wire1028888],
  [wire63,wire1986,wire30852,wire375775,wire860688,wire1824040],
  [wire63,wire1986,wire30852,wire375775,wire860688,wire1863415]]
private def pool6_38 : List (List (List T)) := [chunk5_2, chunk5_8]
private theorem checked6_38 : ∀ w ∈ chunk6_38, ¬ Need 6 w.toFinset := by
  have h : chunk6_38.all (routes 5 pool6_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_38,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_8 _ hm
private def chunk6_39 : List (List T) := [[wire63,wire1986,wire30852,wire758024,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire860688,wire860944,wire1721376],
  [wire63,wire1986,wire30852,wire860688,wire1028888,wire1721376],
  [wire63,wire1986,wire30852,wire860688,wire1028888,wire1721407]]
private def pool6_39 : List (List (List T)) := [chunk5_11, chunk5_12, chunk5_15, chunk5_86]
private theorem checked6_39 : ∀ w ∈ chunk6_39, ¬ Need 6 w.toFinset := by
  have h : chunk6_39.all (routes 5 pool6_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_15 _ hm
  · exact checked5_86 _ hm
private def chunk6_40 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1028888,wire2057776],
  [wire63,wire1986,wire30852,wire860688,wire1028927,wire1721376],
  [wire63,wire1986,wire30852,wire860688,wire1047452,wire1721376],
  [wire63,wire1986,wire30852,wire860688,wire1068263,wire1721376]]
private def pool6_40 : List (List (List T)) := [chunk5_15, chunk5_16, chunk5_43, chunk5_73, chunk5_86]
private theorem checked6_40 : ∀ w ∈ chunk6_40, ¬ Need 6 w.toFinset := by
  have h : chunk6_40.all (routes 5 pool6_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_40,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_43 _ hm
  · exact checked5_73 _ hm
  · exact checked5_86 _ hm
private def chunk6_41 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1721376,wire1721632],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1824040],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1824063],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1834412]]
private def pool6_41 : List (List (List T)) := [chunk5_9, chunk5_17, chunk5_18, chunk5_26, chunk5_27, chunk5_87]
private theorem checked6_41 : ∀ w ∈ chunk6_41, ¬ Need 6 w.toFinset := by
  have h : chunk6_41.all (routes 5 pool6_41.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_41,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_87 _ hm
private def chunk6_42 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1721376,wire1836659],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1863360],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1863415],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1863423]]
private def pool6_42 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_43, chunk5_73, chunk5_74, chunk5_87]
private theorem checked6_42 : ∀ w ∈ chunk6_42, ¬ Need 6 w.toFinset := by
  have h : chunk6_42.all (routes 5 pool6_42.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_42,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_43 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_87 _ hm
private def chunk6_43 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1721376,wire1867511],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1928951],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1994487],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire2094904]]
private def pool6_43 : List (List (List T)) := [chunk5_2]
private theorem checked6_43 : ∀ w ∈ chunk6_43, ¬ Need 6 w.toFinset := by
  have h : chunk6_43.all (routes 5 pool6_43.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_43,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_2 _ hm
private def chunk6_44 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1721376,wire2095421],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire2096895],
  [wire63,wire1986,wire30852,wire860688,wire1721407,wire1824040],
  [wire63,wire1986,wire30852,wire860688,wire1721407,wire1824063]]
private def pool6_44 : List (List (List T)) := [chunk5_2, chunk5_18, chunk5_87]
private theorem checked6_44 : ∀ w ∈ chunk6_44, ¬ Need 6 w.toFinset := by
  have h : chunk6_44.all (routes 5 pool6_44.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_44,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_18 _ hm
  · exact checked5_87 _ hm
private def chunk6_45 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1721407,wire1863415],
  [wire63,wire1986,wire30852,wire860688,wire1721632],
  [wire63,wire1986,wire30852,wire860688,wire1722338,wire1824040],
  [wire63,wire1986,wire30852,wire860688,wire1824040,wire2057776]]
private def pool6_45 : List (List (List T)) := [chunk5_2, chunk5_6, chunk5_9, chunk5_10, chunk5_11, chunk5_14, chunk5_16, chunk5_17, chunk5_18, chunk5_27, chunk5_29, chunk5_32, chunk5_36, chunk5_61, chunk5_63, chunk5_88]
private theorem checked6_45 : ∀ w ∈ chunk6_45, ¬ Need 6 w.toFinset := by
  have h : chunk6_45.all (routes 5 pool6_45.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_45,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_6 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_11 _ hm
  · exact checked5_14 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_27 _ hm
  · exact checked5_29 _ hm
  · exact checked5_32 _ hm
  · exact checked5_36 _ hm
  · exact checked5_61 _ hm
  · exact checked5_63 _ hm
  · exact checked5_88 _ hm
private def chunk6_46 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1863415,wire2057776],
  [wire63,wire1986,wire30852,wire860688,wire2057776,wire2094904],
  [wire63,wire1986,wire30852,wire860735,wire1028888,wire1721376],
  [wire63,wire1986,wire30852,wire860735,wire1028927,wire1721376]]
private def pool6_46 : List (List (List T)) := [chunk5_2, chunk5_6, chunk5_15, chunk5_16, chunk5_74, chunk5_88]
private theorem checked6_46 : ∀ w ∈ chunk6_46, ¬ Need 6 w.toFinset := by
  have h : chunk6_46.all (routes 5 pool6_46.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_46,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_6 _ hm
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_74 _ hm
  · exact checked5_88 _ hm
private def chunk6_47 : List (List T) := [[wire63,wire1986,wire30852,wire860735,wire1721376,wire1824040],
  [wire63,wire1986,wire30852,wire860735,wire1721376,wire1863415],
  [wire63,wire1986,wire30852,wire860944,wire1721376],
  [wire63,wire1986,wire30852,wire862162,wire1028888,wire1721376]]
private def pool6_47 : List (List (List T)) := [chunk5_3, chunk5_9, chunk5_11, chunk5_12, chunk5_13, chunk5_14, chunk5_16, chunk5_17, chunk5_18, chunk5_19, chunk5_27, chunk5_28, chunk5_29, chunk5_33, chunk5_37, chunk5_62, chunk5_63, chunk5_74, chunk5_75, chunk5_88, chunk5_89]
private theorem checked6_47 : ∀ w ∈ chunk6_47, ¬ Need 6 w.toFinset := by
  have h : chunk6_47.all (routes 5 pool6_47.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_47,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_9 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_33 _ hm
  · exact checked5_37 _ hm
  · exact checked5_62 _ hm
  · exact checked5_63 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
  · exact checked5_88 _ hm
  · exact checked5_89 _ hm
private def chunk6_48 : List (List T) := [[wire63,wire1986,wire30852,wire883348,wire1028888,wire1721376],
  [wire63,wire1986,wire30852,wire883348,wire1047452,wire1721376],
  [wire63,wire1986,wire30852,wire883348,wire1721376,wire1824040],
  [wire63,wire1986,wire30852,wire883348,wire1721376,wire1863415]]
private def pool6_48 : List (List (List T)) := [chunk5_3, chunk5_44, chunk5_75, chunk5_76]
private theorem checked6_48 : ∀ w ∈ chunk6_48, ¬ Need 6 w.toFinset := by
  have h : chunk6_48.all (routes 5 pool6_48.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_48,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_44 _ hm
  · exact checked5_75 _ hm
  · exact checked5_76 _ hm
private def chunk6_49 : List (List T) := [[wire63,wire1986,wire30852,wire1028888,wire1236463,wire1721376],
  [wire63,wire1986,wire30852,wire1028888,wire1721376,wire2057776],
  [wire63,wire1986,wire30852,wire1028888,wire2057776],
  [wire63,wire1986,wire30852,wire1236463,wire1721376,wire1824040]]
private def pool6_49 : List (List (List T)) := [chunk5_0, chunk5_6, chunk5_7, chunk5_15, chunk5_16, chunk5_19, chunk5_28, chunk5_30, chunk5_33, chunk5_38, chunk5_62, chunk5_64]
private theorem checked6_49 : ∀ w ∈ chunk6_49, ¬ Need 6 w.toFinset := by
  have h : chunk6_49.all (routes 5 pool6_49.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_49,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_19 _ hm
  · exact checked5_28 _ hm
  · exact checked5_30 _ hm
  · exact checked5_33 _ hm
  · exact checked5_38 _ hm
  · exact checked5_62 _ hm
  · exact checked5_64 _ hm
private def chunk6_50 : List (List T) := [[wire63,wire1986,wire30852,wire1236463,wire1721376,wire1863415],
  [wire63,wire1986,wire30852,wire1721376,wire1824040,wire2057776],
  [wire63,wire1986,wire30852,wire1721376,wire1863415,wire2057776],
  [wire63,wire1986,wire30852,wire1721376,wire2057776,wire2094904]]
private def pool6_50 : List (List (List T)) := [chunk5_3, chunk5_17, chunk5_28]
private theorem checked6_50 : ∀ w ∈ chunk6_50, ¬ Need 6 w.toFinset := by
  have h : chunk6_50.all (routes 5 pool6_50.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_50,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_17 _ hm
  · exact checked5_28 _ hm
private def chunk6_51 : List (List T) := [[wire63,wire1986,wire30852,wire1824040,wire2057776],
  [wire63,wire1986,wire30854,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30860,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30868,wire233736,wire860688,wire1721376]]
private def pool6_51 : List (List (List T)) := [chunk5_1, chunk5_7, chunk5_8, chunk5_17, chunk5_18, chunk5_19, chunk5_28, chunk5_29, chunk5_30, chunk5_33, chunk5_38, chunk5_62, chunk5_64]
private theorem checked6_51 : ∀ w ∈ chunk6_51, ¬ Need 6 w.toFinset := by
  have h : chunk6_51.all (routes 5 pool6_51.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_51,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_33 _ hm
  · exact checked5_38 _ hm
  · exact checked5_62 _ hm
  · exact checked5_64 _ hm
private def chunk6_52 : List (List T) := [[wire63,wire1986,wire30884,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30911,wire233736,wire375775,wire860688],
  [wire63,wire1986,wire30911,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30911,wire233736,wire860688,wire1721407]]
private def pool6_52 : List (List (List T)) := [chunk5_64, chunk5_65, chunk5_66, chunk5_68, chunk5_89]
private theorem checked6_52 : ∀ w ∈ chunk6_52, ¬ Need 6 w.toFinset := by
  have h : chunk6_52.all (routes 5 pool6_52.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_52,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
  · exact checked5_68 _ hm
  · exact checked5_89 _ hm
private def chunk6_53 : List (List T) := [[wire63,wire1986,wire30911,wire233736,wire860688,wire2057776],
  [wire63,wire1986,wire30911,wire233736,wire860735,wire1721376],
  [wire63,wire1986,wire30911,wire233736,wire883348,wire1721376],
  [wire63,wire1986,wire30911,wire233736,wire883391,wire1721376]]
private def pool6_53 : List (List (List T)) := [chunk5_19, chunk5_45, chunk5_66, chunk5_67, chunk5_69, chunk5_90]
private theorem checked6_53 : ∀ w ∈ chunk6_53, ¬ Need 6 w.toFinset := by
  have h : chunk6_53.all (routes 5 pool6_53.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_53,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_19 _ hm
  · exact checked5_45 _ hm
  · exact checked5_66 _ hm
  · exact checked5_67 _ hm
  · exact checked5_69 _ hm
  · exact checked5_90 _ hm
private def chunk6_54 : List (List T) := [[wire63,wire1986,wire30911,wire233736,wire1236463,wire1721376],
  [wire63,wire1986,wire30911,wire233736,wire1721376,wire2057776],
  [wire63,wire1986,wire30911,wire233791,wire860688,wire1721376],
  [wire63,wire1986,wire30911,wire260492,wire860688,wire1721376]]
private def pool6_54 : List (List (List T)) := [chunk5_19, chunk5_45, chunk5_68, chunk5_69, chunk5_70, chunk5_71, chunk5_91]
private theorem checked6_54 : ∀ w ∈ chunk6_54, ¬ Need 6 w.toFinset := by
  have h : chunk6_54.all (routes 5 pool6_54.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_54,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_19 _ hm
  · exact checked5_45 _ hm
  · exact checked5_68 _ hm
  · exact checked5_69 _ hm
  · exact checked5_70 _ hm
  · exact checked5_71 _ hm
  · exact checked5_91 _ hm
private def chunk6_55 : List (List T) := [[wire63,wire1986,wire30911,wire260543,wire860688,wire1721376],
  [wire63,wire1986,wire30911,wire860688,wire1028888,wire1721376],
  [wire63,wire1986,wire30911,wire860688,wire1721376,wire1824040],
  [wire63,wire1986,wire30911,wire860688,wire1721376,wire1863415]]
private def pool6_55 : List (List (List T)) := [chunk5_4, chunk5_19, chunk5_45, chunk5_72, chunk5_73, chunk5_74, chunk5_75, chunk5_92]
private theorem checked6_55 : ∀ w ∈ chunk6_55, ¬ Need 6 w.toFinset := by
  have h : chunk6_55.all (routes 5 pool6_55.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_55,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_19 _ hm
  · exact checked5_45 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
  · exact checked5_92 _ hm
private def chunk6_56 : List (List T) := [[wire63,wire1986,wire31108,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire31108,wire860688,wire1721376],
  [wire63,wire1986,wire31364,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire31876,wire233736,wire860688,wire1721376]]
private def pool6_56 : List (List (List T)) := [chunk5_19, chunk5_20, chunk5_21, chunk5_22, chunk5_23, chunk5_26, chunk5_30, chunk5_39, chunk5_76]
private theorem checked6_56 : ∀ w ∈ chunk6_56, ¬ Need 6 w.toFinset := by
  have h : chunk6_56.all (routes 5 pool6_56.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_56,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_26 _ hm
  · exact checked5_30 _ hm
  · exact checked5_39 _ hm
  · exact checked5_76 _ hm
private def chunk6_57 : List (List T) := [[wire63,wire1986,wire32710,wire233736,wire883348,wire1721376],
  [wire63,wire1986,wire32710,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire65536,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire96388,wire233736,wire860688,wire1721376]]
private def pool6_57 : List (List (List T)) := [chunk5_0, chunk5_20, chunk5_25, chunk5_40, chunk5_41, chunk5_46, chunk5_76]
private theorem checked6_57 : ∀ w ∈ chunk6_57, ¬ Need 6 w.toFinset := by
  have h : chunk6_57.all (routes 5 pool6_57.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_57,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_20 _ hm
  · exact checked5_25 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_46 _ hm
  · exact checked5_76 _ hm
private def chunk6_58 : List (List T) := [[wire63,wire1986,wire161924,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire229640,wire860688,wire1721376,wire2066299],
  [wire63,wire1986,wire233736,wire260492,wire375775,wire860688],
  [wire63,wire1986,wire233736,wire260492,wire860688,wire1721376]]
private def pool6_58 : List (List (List T)) := [chunk5_46, chunk5_47, chunk5_77]
private theorem checked6_58 : ∀ w ∈ chunk6_58, ¬ Need 6 w.toFinset := by
  have h : chunk6_58.all (routes 5 pool6_58.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_58,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_46 _ hm
  · exact checked5_47 _ hm
  · exact checked5_77 _ hm
private def chunk6_59 : List (List T) := [[wire63,wire1986,wire233736,wire260492,wire860688,wire1721407],
  [wire63,wire1986,wire233736,wire260492,wire860688,wire2057776],
  [wire63,wire1986,wire233736,wire260492,wire860735,wire1721376],
  [wire63,wire1986,wire233736,wire260492,wire1236463,wire1721376]]
private def pool6_59 : List (List (List T)) := [chunk5_47, chunk5_48, chunk5_78, chunk5_93]
private theorem checked6_59 : ∀ w ∈ chunk6_59, ¬ Need 6 w.toFinset := by
  have h : chunk6_59.all (routes 5 pool6_59.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_59,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_47 _ hm
  · exact checked5_48 _ hm
  · exact checked5_78 _ hm
  · exact checked5_93 _ hm
private def chunk6_60 : List (List T) := [[wire63,wire1986,wire233736,wire260492,wire1721376,wire2057776],
  [wire63,wire1986,wire233736,wire260543,wire860688,wire1721376],
  [wire63,wire1986,wire233736,wire361307,wire860688,wire1721376],
  [wire63,wire1986,wire233736,wire375775,wire860688,wire1735844]]
private def pool6_60 : List (List (List T)) := [chunk5_26, chunk5_48, chunk5_78, chunk5_93]
private theorem checked6_60 : ∀ w ∈ chunk6_60, ¬ Need 6 w.toFinset := by
  have h : chunk6_60.all (routes 5 pool6_60.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_60,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_26 _ hm
  · exact checked5_48 _ hm
  · exact checked5_78 _ hm
  · exact checked5_93 _ hm
private def chunk6_61 : List (List T) := [[wire63,wire1986,wire233736,wire375775,wire860688,wire2066299],
  [wire63,wire1986,wire233736,wire555140,wire860688,wire1721376],
  [wire63,wire1986,wire233736,wire852496,wire1721376,wire2066299],
  [wire63,wire1986,wire233736,wire860688,wire1721376,wire1735844]]
private def pool6_61 : List (List (List T)) := [chunk5_5, chunk5_24]
private theorem checked6_61 : ∀ w ∈ chunk6_61, ¬ Need 6 w.toFinset := by
  have h : chunk6_61.all (routes 5 pool6_61.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_61,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_24 _ hm
private def chunk6_62 : List (List T) := [[wire63,wire1986,wire233736,wire860688,wire1721376,wire1735871],
  [wire63,wire1986,wire233736,wire860688,wire1721376,wire1834412],
  [wire63,wire1986,wire233736,wire860688,wire1721376,wire1836659],
  [wire63,wire1986,wire233736,wire860688,wire1721376,wire2066240]]
private def pool6_62 : List (List (List T)) := [chunk5_48, chunk5_77, chunk5_78, chunk5_79, chunk5_93, chunk5_94]
private theorem checked6_62 : ∀ w ∈ chunk6_62, ¬ Need 6 w.toFinset := by
  have h : chunk6_62.all (routes 5 pool6_62.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_62,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_48 _ hm
  · exact checked5_77 _ hm
  · exact checked5_78 _ hm
  · exact checked5_79 _ hm
  · exact checked5_93 _ hm
  · exact checked5_94 _ hm
private def chunk6_63 : List (List T) := [[wire63,wire1986,wire233736,wire860688,wire1721376,wire2066299],
  [wire63,wire1986,wire233736,wire860688,wire1721376,wire2066303],
  [wire63,wire1986,wire233736,wire860688,wire1721376,wire2070395],
  [wire63,wire1986,wire233736,wire860688,wire1721376,wire2082683]]
private def pool6_63 : List (List (List T)) := [chunk5_25]
private theorem checked6_63 : ∀ w ∈ chunk6_63, ¬ Need 6 w.toFinset := by
  have h : chunk6_63.all (routes 5 pool6_63.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_63,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_25 _ hm
private def chunk6_64 : List (List T) := [[wire63,wire1986,wire233736,wire860688,wire1721407,wire1735844],
  [wire63,wire1986,wire233736,wire860688,wire1721407,wire1735871],
  [wire63,wire1986,wire233736,wire860688,wire1721407,wire2066299],
  [wire63,wire1986,wire233736,wire860688,wire1722338,wire1735844]]
private def pool6_64 : List (List (List T)) := [chunk5_94]
private theorem checked6_64 : ∀ w ∈ chunk6_64, ¬ Need 6 w.toFinset := by
  have h : chunk6_64.all (routes 5 pool6_64.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_64,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_94 _ hm
private def chunk6_65 : List (List T) := [[wire63,wire1986,wire233736,wire860688,wire2057776,wire2066299],
  [wire63,wire1986,wire233736,wire860735,wire1721376,wire1735844],
  [wire63,wire1986,wire233736,wire860735,wire1721376,wire2066299],
  [wire63,wire1986,wire233736,wire883348,wire1721376,wire1735844]]
private def pool6_65 : List (List (List T)) := [chunk5_28, chunk5_95]
private theorem checked6_65 : ∀ w ∈ chunk6_65, ¬ Need 6 w.toFinset := by
  have h : chunk6_65.all (routes 5 pool6_65.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_65,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_28 _ hm
  · exact checked5_95 _ hm
private def chunk6_66 : List (List T) := [[wire63,wire1986,wire233736,wire883348,wire1721376,wire2066299],
  [wire63,wire1986,wire233736,wire1236463,wire1721376,wire1735844],
  [wire63,wire1986,wire233736,wire1236463,wire1721376,wire2066299],
  [wire63,wire1986,wire233736,wire1721376,wire1735844,wire2057776]]
private def pool6_66 : List (List (List T)) := [chunk5_28]
private theorem checked6_66 : ∀ w ∈ chunk6_66, ¬ Need 6 w.toFinset := by
  have h : chunk6_66.all (routes 5 pool6_66.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_66,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_28 _ hm
private def chunk6_67 : List (List T) := [[wire63,wire1986,wire233736,wire1721376,wire1735844,wire2064052],
  [wire63,wire1986,wire233736,wire1721376,wire2057776,wire2066299],
  [wire63,wire1986,wire233791,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire233791,wire260543,wire860688,wire1721376]]
private def pool6_67 : List (List (List T)) := [chunk5_25, chunk5_29, chunk5_49, chunk5_77, chunk5_95]
private theorem checked6_67 : ∀ w ∈ chunk6_67, ¬ Need 6 w.toFinset := by
  have h : chunk6_67.all (routes 5 pool6_67.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_67,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_25 _ hm
  · exact checked5_29 _ hm
  · exact checked5_49 _ hm
  · exact checked5_77 _ hm
  · exact checked5_95 _ hm
private def chunk6_68 : List (List T) := [[wire63,wire1986,wire233791,wire860688,wire1721376,wire1735844],
  [wire63,wire1986,wire233791,wire860688,wire1721376,wire2066299],
  [wire63,wire1986,wire235466,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire260492,wire860688,wire1721376,wire1735844]]
private def pool6_68 : List (List (List T)) := [chunk5_23, chunk5_47, chunk5_96]
private theorem checked6_68 : ∀ w ∈ chunk6_68, ¬ Need 6 w.toFinset := by
  have h : chunk6_68.all (routes 5 pool6_68.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_68,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_23 _ hm
  · exact checked5_47 _ hm
  · exact checked5_96 _ hm
private def chunk6_69 : List (List T) := [[wire63,wire1986,wire260492,wire860688,wire1721376,wire1824040],
  [wire63,wire1986,wire260492,wire860688,wire1721376,wire1863415],
  [wire63,wire1986,wire260492,wire860688,wire1721376,wire2066299],
  [wire63,wire1986,wire860688,wire1028888,wire1721376,wire1735844]]
private def pool6_69 : List (List (List T)) := [chunk5_25, chunk5_26]
private theorem checked6_69 : ∀ w ∈ chunk6_69, ¬ Need 6 w.toFinset := by
  have h : chunk6_69.all (routes 5 pool6_69.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_69,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_25 _ hm
  · exact checked5_26 _ hm
private def chunk6_70 : List (List T) := [[wire63,wire1986,wire860688,wire1028888,wire1721376,wire2066299],
  [wire63,wire1986,wire860688,wire1721376,wire1735844,wire1824040],
  [wire63,wire1986,wire860688,wire1721376,wire1735844,wire1834412],
  [wire63,wire1986,wire860688,wire1721376,wire1735844,wire1863415]]
private def pool6_70 : List (List (List T)) := [chunk5_4, chunk5_28]
private theorem checked6_70 : ∀ w ∈ chunk6_70, ¬ Need 6 w.toFinset := by
  have h : chunk6_70.all (routes 5 pool6_70.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_70,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_28 _ hm
private def chunk6_71 : List (List T) := [[wire63,wire1986,wire860688,wire1721376,wire1824040,wire1834412],
  [wire63,wire1986,wire860688,wire1721376,wire1824040,wire2066299],
  [wire63,wire1986,wire860688,wire1721376,wire1863415,wire2066299],
  [wire63,wire1990,wire30852,wire233736,wire860688,wire1721376]]
private def pool6_71 : List (List (List T)) := [chunk5_4, chunk5_28, chunk5_29]
private theorem checked6_71 : ∀ w ∈ chunk6_71, ¬ Need 6 w.toFinset := by
  have h : chunk6_71.all (routes 5 pool6_71.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_71,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
private def chunk6_72 : List (List T) := [[wire63,wire1994,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire2002,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire2018,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire2047,wire30852,wire233736,wire375775,wire860688]]
private def pool6_72 : List (List (List T)) := [chunk5_79, chunk5_80, chunk5_83, chunk5_89]
private theorem checked6_72 : ∀ w ∈ chunk6_72, ¬ Need 6 w.toFinset := by
  have h : chunk6_72.all (routes 5 pool6_72.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_72,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_79 _ hm
  · exact checked5_80 _ hm
  · exact checked5_83 _ hm
  · exact checked5_89 _ hm
private def chunk6_73 : List (List T) := [[wire63,wire2047,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire2047,wire30852,wire233736,wire860688,wire1721407],
  [wire63,wire2047,wire30852,wire233736,wire860688,wire2057776],
  [wire63,wire2047,wire30852,wire233736,wire860735,wire1721376]]
private def pool6_73 : List (List (List T)) := [chunk5_30, chunk5_80, chunk5_81, chunk5_84, chunk5_89, chunk5_90]
private theorem checked6_73 : ∀ w ∈ chunk6_73, ¬ Need 6 w.toFinset := by
  have h : chunk6_73.all (routes 5 pool6_73.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_73,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_30 _ hm
  · exact checked5_80 _ hm
  · exact checked5_81 _ hm
  · exact checked5_84 _ hm
  · exact checked5_89 _ hm
  · exact checked5_90 _ hm
private def chunk6_74 : List (List T) := [[wire63,wire2047,wire30852,wire233736,wire883348,wire1721376],
  [wire63,wire2047,wire30852,wire233736,wire1236463,wire1721376],
  [wire63,wire2047,wire30852,wire233736,wire1721376,wire2057776],
  [wire63,wire2047,wire30852,wire233791,wire860688,wire1721376]]
private def pool6_74 : List (List (List T)) := [chunk5_30, chunk5_45, chunk5_82, chunk5_83, chunk5_84, chunk5_85, chunk5_90, chunk5_91]
private theorem checked6_74 : ∀ w ∈ chunk6_74, ¬ Need 6 w.toFinset := by
  have h : chunk6_74.all (routes 5 pool6_74.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_74,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_30 _ hm
  · exact checked5_45 _ hm
  · exact checked5_82 _ hm
  · exact checked5_83 _ hm
  · exact checked5_84 _ hm
  · exact checked5_85 _ hm
  · exact checked5_90 _ hm
  · exact checked5_91 _ hm
private def chunk6_75 : List (List T) := [[wire63,wire2047,wire30852,wire260492,wire860688,wire1721376],
  [wire63,wire2047,wire30852,wire860688,wire1028888,wire1721376],
  [wire63,wire2047,wire30852,wire860688,wire1721376,wire1824040],
  [wire63,wire2047,wire30852,wire860688,wire1721376,wire1863415]]
private def pool6_75 : List (List (List T)) := [chunk5_4, chunk5_30, chunk5_45, chunk5_85, chunk5_86, chunk5_87, chunk5_88, chunk5_89, chunk5_91, chunk5_92]
private theorem checked6_75 : ∀ w ∈ chunk6_75, ¬ Need 6 w.toFinset := by
  have h : chunk6_75.all (routes 5 pool6_75.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_75,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_30 _ hm
  · exact checked5_45 _ hm
  · exact checked5_85 _ hm
  · exact checked5_86 _ hm
  · exact checked5_87 _ hm
  · exact checked5_88 _ hm
  · exact checked5_89 _ hm
  · exact checked5_91 _ hm
  · exact checked5_92 _ hm
private def chunk6_76 : List (List T) := [[wire63,wire2047,wire30911,wire233736,wire860688,wire1721376],
  [wire63,wire2047,wire233736,wire260492,wire860688,wire1721376],
  [wire63,wire2047,wire233736,wire860688,wire1721376,wire1735844],
  [wire63,wire2047,wire233736,wire860688,wire1721376,wire2066299]]
private def pool6_76 : List (List (List T)) := [chunk5_49, chunk5_89, chunk5_90, chunk5_91, chunk5_93, chunk5_94, chunk5_95, chunk5_96]
private theorem checked6_76 : ∀ w ∈ chunk6_76, ¬ Need 6 w.toFinset := by
  have h : chunk6_76.all (routes 5 pool6_76.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_76,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_49 _ hm
  · exact checked5_89 _ hm
  · exact checked5_90 _ hm
  · exact checked5_91 _ hm
  · exact checked5_93 _ hm
  · exact checked5_94 _ hm
  · exact checked5_95 _ hm
  · exact checked5_96 _ hm
private def chunk6_77 : List (List T) := [[wire63,wire4352,wire30852,wire32710,wire860688,wire1721376],
  [wire63,wire6082,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire10178,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire18370,wire30852,wire233736,wire860688,wire1721376]]
private def pool6_77 : List (List (List T)) := [chunk5_31, chunk5_32, chunk5_33, chunk5_39, chunk5_96, chunk5_97]
private theorem checked6_77 : ∀ w ∈ chunk6_77, ¬ Need 6 w.toFinset := by
  have h : chunk6_77.all (routes 5 pool6_77.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_77,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_39 _ hm
  · exact checked5_96 _ hm
  · exact checked5_97 _ hm
private def chunk6_78 : List (List T) := [[wire63,wire30852,wire32710,wire233736,wire375775,wire860688],
  [wire63,wire30852,wire32710,wire233736,wire860688,wire1721376],
  [wire63,wire30852,wire32710,wire233736,wire860688,wire1721407],
  [wire63,wire30852,wire32710,wire233736,wire860688,wire2057776]]
private def pool6_78 : List (List (List T)) := [chunk5_33, chunk5_39, chunk5_40, chunk5_41, chunk5_42, chunk5_102, chunk5_103]
private theorem checked6_78 : ∀ w ∈ chunk6_78, ¬ Need 6 w.toFinset := by
  have h : chunk6_78.all (routes 5 pool6_78.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_78,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_102 _ hm
  · exact checked5_103 _ hm
private def chunk6_79 : List (List T) := [[wire63,wire30852,wire32710,wire233736,wire860735,wire1721376],
  [wire63,wire30852,wire32710,wire233736,wire883348,wire1721376],
  [wire63,wire30852,wire32710,wire233736,wire1236463,wire1721376],
  [wire63,wire30852,wire32710,wire233736,wire1721376,wire2057776]]
private def pool6_79 : List (List (List T)) := [chunk5_33, chunk5_40, chunk5_42, chunk5_43, chunk5_97, chunk5_103, chunk5_104]
private theorem checked6_79 : ∀ w ∈ chunk6_79, ¬ Need 6 w.toFinset := by
  have h : chunk6_79.all (routes 5 pool6_79.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_79,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_40 _ hm
  · exact checked5_42 _ hm
  · exact checked5_43 _ hm
  · exact checked5_97 _ hm
  · exact checked5_103 _ hm
  · exact checked5_104 _ hm
private def chunk6_80 : List (List T) := [[wire63,wire30852,wire32710,wire233791,wire860688,wire1721376],
  [wire63,wire30852,wire32710,wire260492,wire860688,wire1721376],
  [wire63,wire30852,wire32710,wire860688,wire1028888,wire1721376],
  [wire63,wire30852,wire32710,wire860688,wire1721376,wire1824040]]
private def pool6_80 : List (List (List T)) := [chunk5_33, chunk5_41, chunk5_42, chunk5_43, chunk5_44, chunk5_98, chunk5_104, chunk5_105]
private theorem checked6_80 : ∀ w ∈ chunk6_80, ¬ Need 6 w.toFinset := by
  have h : chunk6_80.all (routes 5 pool6_80.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_80,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_33 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_43 _ hm
  · exact checked5_44 _ hm
  · exact checked5_98 _ hm
  · exact checked5_104 _ hm
  · exact checked5_105 _ hm
private def chunk6_81 : List (List T) := [[wire63,wire30852,wire32710,wire860688,wire1721376,wire1863415],
  [wire63,wire30852,wire32767,wire233736,wire860688,wire1721376],
  [wire63,wire30852,wire66048,wire233736,wire235466,wire1721376],
  [wire63,wire30852,wire67522,wire233736,wire860688,wire1721376]]
private def pool6_81 : List (List (List T)) := [chunk5_32, chunk5_34, chunk5_44, chunk5_45, chunk5_46, chunk5_97, chunk5_98, chunk5_105]
private theorem checked6_81 : ∀ w ∈ chunk6_81, ¬ Need 6 w.toFinset := by
  have h : chunk6_81.all (routes 5 pool6_81.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_81,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_32 _ hm
  · exact checked5_34 _ hm
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
  · exact checked5_46 _ hm
  · exact checked5_97 _ hm
  · exact checked5_98 _ hm
  · exact checked5_105 _ hm
private def chunk6_82 : List (List T) := [[wire63,wire30852,wire133058,wire233736,wire860688,wire1721376],
  [wire63,wire30852,wire233736,wire235466,wire375775,wire860688],
  [wire63,wire30852,wire233736,wire235466,wire860688,wire1721376],
  [wire63,wire30852,wire233736,wire235466,wire860688,wire1721407]]
private def pool6_82 : List (List (List T)) := [chunk5_46, chunk5_47, chunk5_99]
private theorem checked6_82 : ∀ w ∈ chunk6_82, ¬ Need 6 w.toFinset := by
  have h : chunk6_82.all (routes 5 pool6_82.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_82,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_46 _ hm
  · exact checked5_47 _ hm
  · exact checked5_99 _ hm
private def chunk6_83 : List (List T) := [[wire63,wire30852,wire233736,wire235466,wire860688,wire2057776],
  [wire63,wire30852,wire233736,wire235466,wire860735,wire1721376],
  [wire63,wire30852,wire233736,wire235466,wire883348,wire1721376],
  [wire63,wire30852,wire233736,wire235466,wire1236463,wire1721376]]
private def pool6_83 : List (List (List T)) := [chunk5_47, chunk5_48, chunk5_99, chunk5_100, chunk5_107]
private theorem checked6_83 : ∀ w ∈ chunk6_83, ¬ Need 6 w.toFinset := by
  have h : chunk6_83.all (routes 5 pool6_83.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_83,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_47 _ hm
  · exact checked5_48 _ hm
  · exact checked5_99 _ hm
  · exact checked5_100 _ hm
  · exact checked5_107 _ hm
private def chunk6_84 : List (List T) := [[wire63,wire30852,wire233736,wire235466,wire1721376,wire2057776],
  [wire63,wire30852,wire233736,wire235519,wire860688,wire1721376],
  [wire63,wire30852,wire233736,wire262094,wire860688,wire1721376],
  [wire63,wire30852,wire233736,wire375775,wire860688,wire2095165]]
private def pool6_84 : List (List (List T)) := [chunk5_34, chunk5_35, chunk5_48, chunk5_49, chunk5_100, chunk5_107]
private theorem checked6_84 : ∀ w ∈ chunk6_84, ¬ Need 6 w.toFinset := by
  have h : chunk6_84.all (routes 5 pool6_84.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_84,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_34 _ hm
  · exact checked5_35 _ hm
  · exact checked5_48 _ hm
  · exact checked5_49 _ hm
  · exact checked5_100 _ hm
  · exact checked5_107 _ hm
private def chunk6_85 : List (List T) := [[wire63,wire30852,wire233736,wire526274,wire860688,wire1721376],
  [wire63,wire30852,wire233736,wire860688,wire1721376,wire1861685],
  [wire63,wire30852,wire233736,wire860688,wire1721376,wire2064441],
  [wire63,wire30852,wire233736,wire860688,wire1721376,wire2095104]]
private def pool6_85 : List (List (List T)) := [chunk5_35, chunk5_46, chunk5_49, chunk5_98, chunk5_99, chunk5_101, chunk5_108]
private theorem checked6_85 : ∀ w ∈ chunk6_85, ¬ Need 6 w.toFinset := by
  have h : chunk6_85.all (routes 5 pool6_85.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_85,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_35 _ hm
  · exact checked5_46 _ hm
  · exact checked5_49 _ hm
  · exact checked5_98 _ hm
  · exact checked5_99 _ hm
  · exact checked5_101 _ hm
  · exact checked5_108 _ hm
private def chunk6_86 : List (List T) := [[wire63,wire30852,wire233736,wire860688,wire1721376,wire2095165],
  [wire63,wire30852,wire233736,wire860688,wire1721376,wire2095167],
  [wire63,wire30852,wire233736,wire860688,wire1721376,wire2095293],
  [wire63,wire30852,wire233736,wire860688,wire1721376,wire2095421]]
private def pool6_86 : List (List (List T)) := [chunk5_35, chunk5_36]
private theorem checked6_86 : ∀ w ∈ chunk6_86, ¬ Need 6 w.toFinset := by
  have h : chunk6_86.all (routes 5 pool6_86.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_86,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
private def chunk6_87 : List (List T) := [[wire63,wire30852,wire233736,wire860688,wire1721407,wire2095165],
  [wire63,wire30852,wire233736,wire860688,wire2057776,wire2095165],
  [wire63,wire30852,wire233736,wire860735,wire1721376,wire2095165],
  [wire63,wire30852,wire233736,wire883348,wire1721376,wire2095165]]
private def pool6_87 : List (List (List T)) := [chunk5_36, chunk5_37, chunk5_38, chunk5_108]
private theorem checked6_87 : ∀ w ∈ chunk6_87, ¬ Need 6 w.toFinset := by
  have h : chunk6_87.all (routes 5 pool6_87.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_87,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_38 _ hm
  · exact checked5_108 _ hm
private def chunk6_88 : List (List T) := [[wire63,wire30852,wire233736,wire1236463,wire1721376,wire2095165],
  [wire63,wire30852,wire233736,wire1721376,wire2057776,wire2095165],
  [wire63,wire30852,wire233791,wire235466,wire860688,wire1721376],
  [wire63,wire30852,wire233791,wire235519,wire860688,wire1721376]]
private def pool6_88 : List (List (List T)) := [chunk5_38, chunk5_48, chunk5_49, chunk5_99, chunk5_109]
private theorem checked6_88 : ∀ w ∈ chunk6_88, ¬ Need 6 w.toFinset := by
  have h : chunk6_88.all (routes 5 pool6_88.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_88,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_38 _ hm
  · exact checked5_48 _ hm
  · exact checked5_49 _ hm
  · exact checked5_99 _ hm
  · exact checked5_109 _ hm
private def chunk6_89 : List (List T) := [[wire63,wire30852,wire233791,wire860688,wire1721376,wire2095165],
  [wire63,wire30852,wire235466,wire260492,wire860688,wire1721376],
  [wire63,wire30852,wire235466,wire860688,wire1721376,wire1863415],
  [wire63,wire30852,wire260492,wire262094,wire860688,wire1721376]]
private def pool6_89 : List (List (List T)) := [chunk5_2, chunk5_36, chunk5_47, chunk5_101, chunk5_102, chunk5_109, chunk5_110]
private theorem checked6_89 : ∀ w ∈ chunk6_89, ¬ Need 6 w.toFinset := by
  have h : chunk6_89.all (routes 5 pool6_89.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_89,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_36 _ hm
  · exact checked5_47 _ hm
  · exact checked5_101 _ hm
  · exact checked5_102 _ hm
  · exact checked5_109 _ hm
  · exact checked5_110 _ hm
private def chunk6_90 : List (List T) := [[wire63,wire30852,wire260492,wire860688,wire1721376,wire2095165],
  [wire63,wire30852,wire860688,wire1028888,wire1721376,wire2095165],
  [wire63,wire30852,wire860688,wire1721376,wire1824040,wire2095165],
  [wire63,wire30852,wire860688,wire1721376,wire1863415,wire2095165]]
private def pool6_90 : List (List (List T)) := [chunk5_36, chunk5_38, chunk5_110]
private theorem checked6_90 : ∀ w ∈ chunk6_90, ¬ Need 6 w.toFinset := by
  have h : chunk6_90.all (routes 5 pool6_90.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_90,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_36 _ hm
  · exact checked5_38 _ hm
  · exact checked5_110 _ hm
private def chunk6_91 : List (List T) := [[wire63,wire30852,wire860688,wire1721376,wire2095165,wire2095421],
  [wire63,wire30852,wire860688,wire1721376,wire2095421],
  [wire63,wire30911,wire32710,wire233736,wire860688,wire1721376],
  [wire63,wire30911,wire32767,wire233736,wire860688,wire1721376]]
private def pool6_91 : List (List (List T)) := [chunk5_2, chunk5_35, chunk5_36, chunk5_37, chunk5_38, chunk5_39, chunk5_40, chunk5_43, chunk5_45, chunk5_50, chunk5_97, chunk5_102, chunk5_103, chunk5_104, chunk5_106]
private theorem checked6_91 : ∀ w ∈ chunk6_91, ¬ Need 6 w.toFinset := by
  have h : chunk6_91.all (routes 5 pool6_91.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_91,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_38 _ hm
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_43 _ hm
  · exact checked5_45 _ hm
  · exact checked5_50 _ hm
  · exact checked5_97 _ hm
  · exact checked5_102 _ hm
  · exact checked5_103 _ hm
  · exact checked5_104 _ hm
  · exact checked5_106 _ hm
private def chunk6_92 : List (List T) := [[wire63,wire30911,wire233736,wire235466,wire860688,wire1721376],
  [wire63,wire30911,wire233736,wire860688,wire1721376,wire2095165],
  [wire63,wire32710,wire233736,wire260492,wire860688,wire1721376],
  [wire63,wire32710,wire233736,wire860688,wire883348,wire1721376]]
private def pool6_92 : List (List (List T)) := [chunk5_39, chunk5_40, chunk5_41, chunk5_43, chunk5_44, chunk5_48, chunk5_107, chunk5_108, chunk5_109, chunk5_110, chunk5_111]
private theorem checked6_92 : ∀ w ∈ chunk6_92, ¬ Need 6 w.toFinset := by
  have h : chunk6_92.all (routes 5 pool6_92.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_92,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_43 _ hm
  · exact checked5_44 _ hm
  · exact checked5_48 _ hm
  · exact checked5_107 _ hm
  · exact checked5_108 _ hm
  · exact checked5_109 _ hm
  · exact checked5_110 _ hm
  · exact checked5_111 _ hm
private def chunk6_93 : List (List T) := [[wire63,wire32710,wire233736,wire860688,wire1721376,wire2066299],
  [wire63,wire32710,wire233736,wire883348,wire1721376],
  [wire63,wire32710,wire260492,wire860688,wire1721376],
  [wire63,wire233736,wire235466,wire260492,wire860688,wire1721376]]
private def pool6_93 : List (List (List T)) := [chunk5_31, chunk5_39, chunk5_40, chunk5_41, chunk5_42, chunk5_43, chunk5_44, chunk5_45, chunk5_46, chunk5_47, chunk5_49, chunk5_110, chunk5_111, chunk5_112]
private theorem checked6_93 : ∀ w ∈ chunk6_93, ¬ Need 6 w.toFinset := by
  have h : chunk6_93.all (routes 5 pool6_93.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_93,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_31 _ hm
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_43 _ hm
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
  · exact checked5_46 _ hm
  · exact checked5_47 _ hm
  · exact checked5_49 _ hm
  · exact checked5_110 _ hm
  · exact checked5_111 _ hm
  · exact checked5_112 _ hm
private def chunk6_94 : List (List T) := [[wire63,wire233736,wire235466,wire860688,wire1721376,wire1735844],
  [wire63,wire233736,wire235466,wire860688,wire1721376,wire2066299],
  [wire63,wire233736,wire260492,wire262094,wire860688,wire1721376],
  [wire63,wire233736,wire260492,wire860688,wire1721376,wire2095165]]
private def pool6_94 : List (List (List T)) := [chunk5_112, chunk5_113, chunk5_114]
private theorem checked6_94 : ∀ w ∈ chunk6_94, ¬ Need 6 w.toFinset := by
  have h : chunk6_94.all (routes 5 pool6_94.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_94,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_112 _ hm
  · exact checked5_113 _ hm
  · exact checked5_114 _ hm
private def chunk6_95 : List (List T) := [[wire63,wire233736,wire860688,wire1721376,wire1735844,wire2095165],
  [wire63,wire233736,wire860688,wire1721376,wire2066299,wire2095165],
  [wire63,wire235466,wire260492,wire860688,wire1721376],
  [wire191,wire1986,wire30852,wire233736,wire860688,wire1721376]]
private def pool6_95 : List (List (List T)) := [chunk5_46, chunk5_47, chunk5_48, chunk5_49, chunk5_50, chunk5_114]
private theorem checked6_95 : ∀ w ∈ chunk6_95, ¬ Need 6 w.toFinset := by
  have h : chunk6_95.all (routes 5 pool6_95.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_95,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_46 _ hm
  · exact checked5_47 _ hm
  · exact checked5_48 _ hm
  · exact checked5_49 _ hm
  · exact checked5_50 _ hm
  · exact checked5_114 _ hm
private def chunk6_96 : List (List T) := [[wire256,wire319,wire1986,wire30852,wire860688,wire1721376],
  [wire256,wire1986,wire30852,wire30911,wire860688,wire1721376],
  [wire256,wire1986,wire30852,wire860688,wire1721376,wire2097088],
  [wire319,wire1986,wire30852,wire233736,wire860688,wire1721376]]
private def pool6_96 : List (List (List T)) := [chunk5_50, chunk5_51, chunk5_53, chunk5_54, chunk5_56, chunk5_61, chunk5_62, chunk5_63, chunk5_64, chunk5_76]
private theorem checked6_96 : ∀ w ∈ chunk6_96, ¬ Need 6 w.toFinset := by
  have h : chunk6_96.all (routes 5 pool6_96.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_96,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_50 _ hm
  · exact checked5_51 _ hm
  · exact checked5_53 _ hm
  · exact checked5_54 _ hm
  · exact checked5_56 _ hm
  · exact checked5_61 _ hm
  · exact checked5_62 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_76 _ hm
private def chunk6_97 : List (List T) := [[wire319,wire1986,wire30852,wire860688,wire1721376],
  [wire575,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire1087,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire1984,wire30852,wire233736,wire860688,wire1721376,wire2097088]]
private def pool6_97 : List (List (List T)) := [chunk5_52, chunk5_53, chunk5_54, chunk5_55, chunk5_56, chunk5_57, chunk5_62, chunk5_63]
private theorem checked6_97 : ∀ w ∈ chunk6_97, ¬ Need 6 w.toFinset := by
  have h : chunk6_97.all (routes 5 pool6_97.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_97,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_52 _ hm
  · exact checked5_53 _ hm
  · exact checked5_54 _ hm
  · exact checked5_55 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
  · exact checked5_62 _ hm
  · exact checked5_63 _ hm
private def chunk6_98 : List (List T) := [[wire1986,wire2047,wire30852,wire233736,wire860688,wire1721407],
  [wire1986,wire2047,wire30852,wire233736,wire860735,wire1721376],
  [wire1986,wire2047,wire30852,wire233791,wire860688,wire1721376],
  [wire1986,wire2047,wire30911,wire233736,wire860688,wire1721376]]
private def pool6_98 : List (List (List T)) := [chunk5_51, chunk5_53, chunk5_80, chunk5_81, chunk5_84, chunk5_89]
private theorem checked6_98 : ∀ w ∈ chunk6_98, ¬ Need 6 w.toFinset := by
  have h : chunk6_98.all (routes 5 pool6_98.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_98,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_53 _ hm
  · exact checked5_80 _ hm
  · exact checked5_81 _ hm
  · exact checked5_84 _ hm
  · exact checked5_89 _ hm
private def chunk6_99 : List (List T) := [[wire1986,wire4159,wire30852,wire233736,wire860688,wire1721376],
  [wire1986,wire8255,wire30852,wire233736,wire860688,wire1721376],
  [wire1986,wire16384,wire30911,wire233736,wire860688,wire1721376],
  [wire1986,wire16447,wire30852,wire233736,wire860688,wire1721376]]
private def pool6_99 : List (List (List T)) := [chunk5_60, chunk5_61, chunk5_67, chunk5_70, chunk5_97]
private theorem checked6_99 : ∀ w ∈ chunk6_99, ¬ Need 6 w.toFinset := by
  have h : chunk6_99.all (routes 5 pool6_99.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_99,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_60 _ hm
  · exact checked5_61 _ hm
  · exact checked5_67 _ hm
  · exact checked5_70 _ hm
  · exact checked5_97 _ hm
private def chunk6_100 : List (List T) := [[wire1986,wire30848,wire233736,wire860688,wire1721376,wire2097088],
  [wire1986,wire30852,wire30911,wire233736,wire375775,wire860688],
  [wire1986,wire30852,wire30911,wire233736,wire860688,wire1721376],
  [wire1986,wire30852,wire30911,wire233736,wire860688,wire2057776]]
private def pool6_100 : List (List (List T)) := [chunk5_62, chunk5_65, chunk5_67, chunk5_70, chunk5_71, chunk5_102, chunk5_103]
private theorem checked6_100 : ∀ w ∈ chunk6_100, ¬ Need 6 w.toFinset := by
  have h : chunk6_100.all (routes 5 pool6_100.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_100,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_62 _ hm
  · exact checked5_65 _ hm
  · exact checked5_67 _ hm
  · exact checked5_70 _ hm
  · exact checked5_71 _ hm
  · exact checked5_102 _ hm
  · exact checked5_103 _ hm
private def chunk6_101 : List (List T) := [[wire1986,wire30852,wire30911,wire233736,wire860735,wire1721376],
  [wire1986,wire30852,wire30911,wire233736,wire883348,wire1721376],
  [wire1986,wire30852,wire30911,wire233736,wire883391,wire1721376],
  [wire1986,wire30852,wire30911,wire233736,wire1236463,wire1721376]]
private def pool6_101 : List (List (List T)) := [chunk5_66, chunk5_67, chunk5_71, chunk5_72, chunk5_97, chunk5_103, chunk5_104]
private theorem checked6_101 : ∀ w ∈ chunk6_101, ¬ Need 6 w.toFinset := by
  have h : chunk6_101.all (routes 5 pool6_101.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_101,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_66 _ hm
  · exact checked5_67 _ hm
  · exact checked5_71 _ hm
  · exact checked5_72 _ hm
  · exact checked5_97 _ hm
  · exact checked5_103 _ hm
  · exact checked5_104 _ hm
private def chunk6_102 : List (List T) := [[wire1986,wire30852,wire30911,wire233736,wire1721376,wire2057776],
  [wire1986,wire30852,wire30911,wire233791,wire860688,wire1721376],
  [wire1986,wire30852,wire30911,wire260492,wire860688,wire1721376],
  [wire1986,wire30852,wire30911,wire260543,wire860688,wire1721376]]
private def pool6_102 : List (List (List T)) := [chunk5_61, chunk5_62, chunk5_68, chunk5_69, chunk5_71, chunk5_72, chunk5_73, chunk5_98, chunk5_104, chunk5_105]
private theorem checked6_102 : ∀ w ∈ chunk6_102, ¬ Need 6 w.toFinset := by
  have h : chunk6_102.all (routes 5 pool6_102.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_102,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_61 _ hm
  · exact checked5_62 _ hm
  · exact checked5_68 _ hm
  · exact checked5_69 _ hm
  · exact checked5_71 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_98 _ hm
  · exact checked5_104 _ hm
  · exact checked5_105 _ hm
private def chunk6_103 : List (List T) := [[wire1986,wire30852,wire30911,wire860688,wire1028888,wire1721376],
  [wire1986,wire30852,wire30911,wire860688,wire1721376,wire1824040],
  [wire1986,wire30852,wire30911,wire860688,wire1721376,wire1863415],
  [wire1986,wire30852,wire65599,wire233736,wire860688,wire1721376]]
private def pool6_103 : List (List (List T)) := [chunk5_59, chunk5_62, chunk5_73, chunk5_75, chunk5_76, chunk5_105]
private theorem checked6_103 : ∀ w ∈ chunk6_103, ¬ Need 6 w.toFinset := by
  have h : chunk6_103.all (routes 5 pool6_103.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_103,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_59 _ hm
  · exact checked5_62 _ hm
  · exact checked5_73 _ hm
  · exact checked5_75 _ hm
  · exact checked5_76 _ hm
  · exact checked5_105 _ hm
private def chunk6_104 : List (List T) := [[wire1986,wire30852,wire131135,wire233736,wire860688,wire1721376],
  [wire1986,wire30852,wire233728,wire860688,wire1721376,wire2097088],
  [wire1986,wire30852,wire233736,wire233791,wire375775,wire860688],
  [wire1986,wire30852,wire233736,wire233791,wire860688,wire1721376]]
private def pool6_104 : List (List (List T)) := [chunk5_77, chunk5_99]
private theorem checked6_104 : ∀ w ∈ chunk6_104, ¬ Need 6 w.toFinset := by
  have h : chunk6_104.all (routes 5 pool6_104.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_104,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_77 _ hm
  · exact checked5_99 _ hm
private def chunk6_105 : List (List T) := [[wire1986,wire30852,wire233736,wire233791,wire860688,wire2057776],
  [wire1986,wire30852,wire233736,wire233791,wire883348,wire1721376],
  [wire1986,wire30852,wire233736,wire233791,wire1236463,wire1721376],
  [wire1986,wire30852,wire233736,wire233791,wire1721376,wire2057776]]
private def pool6_105 : List (List (List T)) := [chunk5_78, chunk5_99, chunk5_100, chunk5_110]
private theorem checked6_105 : ∀ w ∈ chunk6_105, ¬ Need 6 w.toFinset := by
  have h : chunk6_105.all (routes 5 pool6_105.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_105,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_78 _ hm
  · exact checked5_99 _ hm
  · exact checked5_100 _ hm
  · exact checked5_110 _ hm
private def chunk6_106 : List (List T) := [[wire1986,wire30852,wire233736,wire260543,wire860688,wire1721376],
  [wire1986,wire30852,wire233736,wire375775,wire860688,wire2097088],
  [wire1986,wire30852,wire233736,wire524351,wire860688,wire1721376],
  [wire1986,wire30852,wire233736,wire860672,wire1721376,wire2097088]]
private def pool6_106 : List (List (List T)) := [chunk5_101, chunk5_110]
private theorem checked6_106 : ∀ w ∈ chunk6_106, ¬ Need 6 w.toFinset := by
  have h : chunk6_106.all (routes 5 pool6_106.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_106,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_101 _ hm
  · exact checked5_110 _ hm
private def chunk6_107 : List (List T) := [[wire1986,wire30852,wire233736,wire860688,wire1721344,wire2097088],
  [wire1986,wire30852,wire233736,wire860688,wire1721376,wire1863360],
  [wire1986,wire30852,wire233736,wire860688,wire1721376,wire2066240],
  [wire1986,wire30852,wire233736,wire860688,wire1721376,wire2097088]]
private def pool6_107 : List (List (List T)) := [chunk5_77, chunk5_79, chunk5_101, chunk5_111]
private theorem checked6_107 : ∀ w ∈ chunk6_107, ¬ Need 6 w.toFinset := by
  have h : chunk6_107.all (routes 5 pool6_107.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_107,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_77 _ hm
  · exact checked5_79 _ hm
  · exact checked5_101 _ hm
  · exact checked5_111 _ hm
private def chunk6_108 : List (List T) := [[wire1986,wire30852,wire233736,wire860688,wire1721376,wire2097092],
  [wire1986,wire30852,wire233736,wire860688,wire1721376,wire2097096],
  [wire1986,wire30852,wire233736,wire860688,wire1721407,wire2097088],
  [wire1986,wire30852,wire233736,wire860688,wire2057776,wire2097088]]
private def pool6_108 : List (List (List T)) := [chunk5_64]
private theorem checked6_108 : ∀ w ∈ chunk6_108, ¬ Need 6 w.toFinset := by
  have h : chunk6_108.all (routes 5 pool6_108.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_108,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_64 _ hm
private def chunk6_109 : List (List T) := [[wire1986,wire30852,wire233736,wire860735,wire1721376,wire2097088],
  [wire1986,wire30852,wire233736,wire883348,wire1721376,wire2097088],
  [wire1986,wire30852,wire233736,wire1236463,wire1721376,wire2097088],
  [wire1986,wire30852,wire233736,wire1721376,wire2057776,wire2097088]]
private def pool6_109 : List (List (List T)) := [chunk5_64, chunk5_111]
private theorem checked6_109 : ∀ w ∈ chunk6_109, ¬ Need 6 w.toFinset := by
  have h : chunk6_109.all (routes 5 pool6_109.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_109,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_64 _ hm
  · exact checked5_111 _ hm
private def chunk6_110 : List (List T) := [[wire1986,wire30852,wire233791,wire235466,wire860688,wire1721376],
  [wire1986,wire30852,wire233791,wire260492,wire860688,wire1721376],
  [wire1986,wire30852,wire233791,wire860688,wire1721376,wire1863415],
  [wire1986,wire30852,wire233791,wire860688,wire1721376,wire2097088]]
private def pool6_110 : List (List (List T)) := [chunk5_77, chunk5_99, chunk5_100, chunk5_111]
private theorem checked6_110 : ∀ w ∈ chunk6_110, ¬ Need 6 w.toFinset := by
  have h : chunk6_110.all (routes 5 pool6_110.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_110,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_77 _ hm
  · exact checked5_99 _ hm
  · exact checked5_100 _ hm
  · exact checked5_111 _ hm
private def chunk6_111 : List (List T) := [[wire1986,wire30852,wire260492,wire260543,wire860688,wire1721376],
  [wire1986,wire30852,wire260492,wire860688,wire1721376,wire2097088],
  [wire1986,wire30852,wire860688,wire1028888,wire1721376,wire2097088],
  [wire1986,wire30852,wire860688,wire1721376,wire1824040,wire2097088]]
private def pool6_111 : List (List (List T)) := [chunk5_64, chunk5_102, chunk5_111, chunk5_112]
private theorem checked6_111 : ∀ w ∈ chunk6_111, ¬ Need 6 w.toFinset := by
  have h : chunk6_111.all (routes 5 pool6_111.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_111,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_64 _ hm
  · exact checked5_102 _ hm
  · exact checked5_111 _ hm
  · exact checked5_112 _ hm
private def chunk6_112 : List (List T) := [[wire1986,wire30852,wire860688,wire1721376,wire1863415,wire2097088],
  [wire1986,wire30911,wire32710,wire233736,wire860688,wire1721376],
  [wire1986,wire30911,wire233736,wire233791,wire860688,wire1721376],
  [wire1986,wire30911,wire233736,wire260492,wire860688,wire1721376]]
private def pool6_112 : List (List (List T)) := [chunk5_51, chunk5_59, chunk5_68, chunk5_71, chunk5_102, chunk5_107, chunk5_109]
private theorem checked6_112 : ∀ w ∈ chunk6_112, ¬ Need 6 w.toFinset := by
  have h : chunk6_112.all (routes 5 pool6_112.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_112,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_59 _ hm
  · exact checked5_68 _ hm
  · exact checked5_71 _ hm
  · exact checked5_102 _ hm
  · exact checked5_107 _ hm
  · exact checked5_109 _ hm
private def chunk6_113 : List (List T) := [[wire1986,wire30911,wire233736,wire860688,wire860735,wire1721376],
  [wire1986,wire30911,wire233736,wire860688,wire883348,wire1721376],
  [wire1986,wire30911,wire233736,wire860688,wire1721376,wire2066299],
  [wire1986,wire30911,wire233736,wire860688,wire1721376,wire2097088]]
private def pool6_113 : List (List (List T)) := [chunk5_65, chunk5_66, chunk5_67, chunk5_73, chunk5_74, chunk5_75]
private theorem checked6_113 : ∀ w ∈ chunk6_113, ¬ Need 6 w.toFinset := by
  have h : chunk6_113.all (routes 5 pool6_113.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_113,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
  · exact checked5_67 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
private def chunk6_114 : List (List T) := [[wire1986,wire30911,wire233736,wire860735,wire1721376],
  [wire1986,wire30911,wire233736,wire883348,wire1721376],
  [wire1986,wire30911,wire233791,wire860688,wire1721376],
  [wire1986,wire30911,wire260492,wire860688,wire1721376]]
private def pool6_114 : List (List (List T)) := [chunk5_50, chunk5_64, chunk5_65, chunk5_66, chunk5_67, chunk5_68, chunk5_69, chunk5_70, chunk5_71, chunk5_72, chunk5_73, chunk5_74, chunk5_75, chunk5_76, chunk5_77, chunk5_79, chunk5_106, chunk5_107, chunk5_108, chunk5_109, chunk5_110]
private theorem checked6_114 : ∀ w ∈ chunk6_114, ¬ Need 6 w.toFinset := by
  have h : chunk6_114.all (routes 5 pool6_114.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_114,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_50 _ hm
  · exact checked5_64 _ hm
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
  · exact checked5_67 _ hm
  · exact checked5_68 _ hm
  · exact checked5_69 _ hm
  · exact checked5_70 _ hm
  · exact checked5_71 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
  · exact checked5_76 _ hm
  · exact checked5_77 _ hm
  · exact checked5_79 _ hm
  · exact checked5_106 _ hm
  · exact checked5_107 _ hm
  · exact checked5_108 _ hm
  · exact checked5_109 _ hm
  · exact checked5_110 _ hm
private def chunk6_115 : List (List T) := [[wire1986,wire233736,wire233791,wire260492,wire860688,wire1721376],
  [wire1986,wire233736,wire233791,wire260543,wire860688,wire1721376],
  [wire1986,wire233736,wire233791,wire860688,wire1721376,wire1735844],
  [wire1986,wire233736,wire233791,wire860688,wire1721376,wire2066299]]
private def pool6_115 : List (List (List T)) := [chunk5_77, chunk5_112, chunk5_113]
private theorem checked6_115 : ∀ w ∈ chunk6_115, ¬ Need 6 w.toFinset := by
  have h : chunk6_115.all (routes 5 pool6_115.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_115,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked5_77 _ hm
  · exact checked5_112 _ hm
  · exact checked5_113 _ hm
private def chunk6_116 : List (List T) := [[wire1986,wire233736,wire260492,wire260543,wire860688,wire1721376],
  [wire1986,wire233736,wire260492,wire860688,wire1721376,wire2097088],
  [wire1986,wire233736,wire860688,wire1721376,wire1735844,wire2097088],
  [wire1986,wire233736,wire860688,wire1721376,wire2066299,wire2097088]]
private def pool6_116 : List (List (List T)) := [chunk5_112, chunk5_114]
private theorem checked6_116 : ∀ w ∈ chunk6_116, ¬ Need 6 w.toFinset := by
  have h : chunk6_116.all (routes 5 pool6_116.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_116,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked5_112 _ hm
  · exact checked5_114 _ hm
private def chunk6_117 : List (List T) := [[wire1986,wire233791,wire260492,wire860688,wire1721376],
  [wire2047,wire30852,wire30911,wire233736,wire860688,wire1721376],
  [wire2047,wire30852,wire233736,wire233791,wire860688,wire1721376],
  [wire2047,wire30852,wire233736,wire860688,wire860735,wire1721376]]
private def pool6_117 : List (List (List T)) := [chunk5_77, chunk5_78, chunk5_79, chunk5_80, chunk5_81, chunk5_82, chunk5_84, chunk5_86, chunk5_88, chunk5_89, chunk5_90, chunk5_91, chunk5_93, chunk5_95, chunk5_113, chunk5_114]
private theorem checked6_117 : ∀ w ∈ chunk6_117, ¬ Need 6 w.toFinset := by
  have h : chunk6_117.all (routes 5 pool6_117.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_117,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_77 _ hm
  · exact checked5_78 _ hm
  · exact checked5_79 _ hm
  · exact checked5_80 _ hm
  · exact checked5_81 _ hm
  · exact checked5_82 _ hm
  · exact checked5_84 _ hm
  · exact checked5_86 _ hm
  · exact checked5_88 _ hm
  · exact checked5_89 _ hm
  · exact checked5_90 _ hm
  · exact checked5_91 _ hm
  · exact checked5_93 _ hm
  · exact checked5_95 _ hm
  · exact checked5_113 _ hm
  · exact checked5_114 _ hm
private def chunk6_118 : List (List T) := [[wire2047,wire30852,wire233736,wire860688,wire1721376,wire1721407],
  [wire2047,wire30852,wire233736,wire860688,wire1721376,wire2097088],
  [wire2047,wire30852,wire233736,wire860688,wire1721407],
  [wire2047,wire30852,wire233736,wire860735,wire1721376]]
private def pool6_118 : List (List (List T)) := [chunk5_52, chunk5_80, chunk5_81, chunk5_82, chunk5_83, chunk5_85, chunk5_86, chunk5_87, chunk5_88, chunk5_89, chunk5_93, chunk5_94, chunk5_95, chunk5_97, chunk5_98, chunk5_99]
private theorem checked6_118 : ∀ w ∈ chunk6_118, ¬ Need 6 w.toFinset := by
  have h : chunk6_118.all (routes 5 pool6_118.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_118,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_52 _ hm
  · exact checked5_80 _ hm
  · exact checked5_81 _ hm
  · exact checked5_82 _ hm
  · exact checked5_83 _ hm
  · exact checked5_85 _ hm
  · exact checked5_86 _ hm
  · exact checked5_87 _ hm
  · exact checked5_88 _ hm
  · exact checked5_89 _ hm
  · exact checked5_93 _ hm
  · exact checked5_94 _ hm
  · exact checked5_95 _ hm
  · exact checked5_97 _ hm
  · exact checked5_98 _ hm
  · exact checked5_99 _ hm
private def chunk6_119 : List (List T) := [[wire2047,wire30852,wire233791,wire860688,wire1721376],
  [wire2047,wire30911,wire233736,wire860688,wire1721376],
  [wire30852,wire30911,wire32710,wire233736,wire860688,wire1721376],
  [wire30852,wire30911,wire32767,wire233736,wire860688,wire1721376]]
private def pool6_119 : List (List (List T)) := [chunk5_52, chunk5_57, chunk5_83, chunk5_84, chunk5_85, chunk5_86, chunk5_87, chunk5_89, chunk5_90, chunk5_91, chunk5_92, chunk5_93, chunk5_94, chunk5_95, chunk5_96, chunk5_97, chunk5_98, chunk5_101, chunk5_102, chunk5_103, chunk5_104, chunk5_106, chunk5_107, chunk5_108]
private theorem checked6_119 : ∀ w ∈ chunk6_119, ¬ Need 6 w.toFinset := by
  have h : chunk6_119.all (routes 5 pool6_119.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_119,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_52 _ hm
  · exact checked5_57 _ hm
  · exact checked5_83 _ hm
  · exact checked5_84 _ hm
  · exact checked5_85 _ hm
  · exact checked5_86 _ hm
  · exact checked5_87 _ hm
  · exact checked5_89 _ hm
  · exact checked5_90 _ hm
  · exact checked5_91 _ hm
  · exact checked5_92 _ hm
  · exact checked5_93 _ hm
  · exact checked5_94 _ hm
  · exact checked5_95 _ hm
  · exact checked5_96 _ hm
  · exact checked5_97 _ hm
  · exact checked5_98 _ hm
  · exact checked5_101 _ hm
  · exact checked5_102 _ hm
  · exact checked5_103 _ hm
  · exact checked5_104 _ hm
  · exact checked5_106 _ hm
  · exact checked5_107 _ hm
  · exact checked5_108 _ hm
private def chunk6_120 : List (List T) := [[wire30852,wire30911,wire233736,wire235466,wire860688,wire1721376],
  [wire30852,wire30911,wire233736,wire860688,wire1721376,wire2095165],
  [wire30852,wire32710,wire233736,wire233791,wire860688,wire1721376],
  [wire30852,wire32710,wire233736,wire860688,wire1721376,wire2097088]]
private def pool6_120 : List (List (List T)) := [chunk5_97, chunk5_100, chunk5_101, chunk5_107, chunk5_108, chunk5_109, chunk5_110, chunk5_111, chunk5_112]
private theorem checked6_120 : ∀ w ∈ chunk6_120, ¬ Need 6 w.toFinset := by
  have h : chunk6_120.all (routes 5 pool6_120.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_120,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_97 _ hm
  · exact checked5_100 _ hm
  · exact checked5_101 _ hm
  · exact checked5_107 _ hm
  · exact checked5_108 _ hm
  · exact checked5_109 _ hm
  · exact checked5_110 _ hm
  · exact checked5_111 _ hm
  · exact checked5_112 _ hm
private def chunk6_121 : List (List T) := [[wire30852,wire233736,wire233791,wire235466,wire860688,wire1721376],
  [wire30852,wire233736,wire233791,wire235519,wire860688,wire1721376],
  [wire30852,wire233736,wire233791,wire860688,wire1721376,wire2095165],
  [wire30852,wire233736,wire235466,wire860688,wire1721376,wire2097088]]
private def pool6_121 : List (List (List T)) := [chunk5_99, chunk5_112, chunk5_113, chunk5_114]
private theorem checked6_121 : ∀ w ∈ chunk6_121, ¬ Need 6 w.toFinset := by
  have h : chunk6_121.all (routes 5 pool6_121.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_121,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_99 _ hm
  · exact checked5_112 _ hm
  · exact checked5_113 _ hm
  · exact checked5_114 _ hm
private def chunk6_122 : List (List T) := [[wire30852,wire233736,wire860688,wire1721376,wire2095165,wire2097088],
  [wire30852,wire233791,wire235466,wire860688,wire1721376],
  [wire30911,wire32710,wire233736,wire860688,wire1721376]]
private def pool6_122 : List (List (List T)) := [chunk5_96, chunk5_98, chunk5_99, chunk5_100, chunk5_101, chunk5_102, chunk5_103, chunk5_104, chunk5_105, chunk5_107, chunk5_108, chunk5_110, chunk5_111, chunk5_113]
private theorem checked6_122 : ∀ w ∈ chunk6_122, ¬ Need 6 w.toFinset := by
  have h : chunk6_122.all (routes 5 pool6_122.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_122,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_96 _ hm
  · exact checked5_98 _ hm
  · exact checked5_99 _ hm
  · exact checked5_100 _ hm
  · exact checked5_101 _ hm
  · exact checked5_102 _ hm
  · exact checked5_103 _ hm
  · exact checked5_104 _ hm
  · exact checked5_105 _ hm
  · exact checked5_107 _ hm
  · exact checked5_108 _ hm
  · exact checked5_110 _ hm
  · exact checked5_111 _ hm
  · exact checked5_113 _ hm
#print axioms checked6_122
private def chunk7_0 : List (List T) := [[wire0,wire63,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire2,wire63,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire4,wire63,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire8,wire63,wire1986,wire30852,wire233736,wire860688,wire1721376]]
private def pool7_0 : List (List (List T)) := [chunk6_19, chunk6_20, chunk6_22, chunk6_23, chunk6_31, chunk6_51, chunk6_71, chunk6_72]
private theorem checked7_0 : ∀ w ∈ chunk7_0, ¬ Need 7 w.toFinset := by
  have h : chunk7_0.all (routes 6 pool7_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_31 _ hm
  · exact checked6_51 _ hm
  · exact checked6_71 _ hm
  · exact checked6_72 _ hm
private def chunk7_1 : List (List T) := [[wire16,wire63,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire32,wire63,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire128,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire256,wire1986,wire30852,wire233736,wire860688,wire1721376]]
private def pool7_1 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_19, chunk6_20, chunk6_21, chunk6_23, chunk6_24, chunk6_25, chunk6_32, chunk6_34, chunk6_51, chunk6_52, chunk6_56, chunk6_72, chunk6_95, chunk6_96]
private theorem checked7_1 : ∀ w ∈ chunk7_1, ¬ Need 7 w.toFinset := by
  have h : chunk7_1.all (routes 6 pool7_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_21 _ hm
  · exact checked6_23 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_32 _ hm
  · exact checked6_34 _ hm
  · exact checked6_51 _ hm
  · exact checked6_52 _ hm
  · exact checked6_56 _ hm
  · exact checked6_72 _ hm
  · exact checked6_95 _ hm
  · exact checked6_96 _ hm
private def chunk7_2 : List (List T) := [[wire63,wire256,wire1986,wire30852,wire860688,wire1721376],
  [wire63,wire512,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1024,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire2047,wire30852,wire233736,wire860688,wire1721376]]
private def pool7_2 : List (List (List T)) := [chunk6_1, chunk6_2, chunk6_3, chunk6_4, chunk6_5, chunk6_6, chunk6_12, chunk6_19, chunk6_21, chunk6_25, chunk6_34, chunk6_35, chunk6_39, chunk6_41, chunk6_44, chunk6_45, chunk6_47, chunk6_56, chunk6_73, chunk6_96, chunk6_97, chunk6_98]
private theorem checked7_2 : ∀ w ∈ chunk7_2, ¬ Need 7 w.toFinset := by
  have h : chunk7_2.all (routes 6 pool7_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_5 _ hm
  · exact checked6_6 _ hm
  · exact checked6_12 _ hm
  · exact checked6_19 _ hm
  · exact checked6_21 _ hm
  · exact checked6_25 _ hm
  · exact checked6_34 _ hm
  · exact checked6_35 _ hm
  · exact checked6_39 _ hm
  · exact checked6_41 _ hm
  · exact checked6_44 _ hm
  · exact checked6_45 _ hm
  · exact checked6_47 _ hm
  · exact checked6_56 _ hm
  · exact checked6_73 _ hm
  · exact checked6_96 _ hm
  · exact checked6_97 _ hm
  · exact checked6_98 _ hm
private def chunk7_3 : List (List T) := [[wire63,wire1986,wire4096,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire8192,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire16384,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire30911,wire233736,wire860688,wire1721376]]
private def pool7_3 : List (List (List T)) := [chunk6_10, chunk6_11, chunk6_19, chunk6_21, chunk6_25, chunk6_26, chunk6_35, chunk6_37, chunk6_52, chunk6_53, chunk6_54, chunk6_77, chunk6_81, chunk6_91, chunk6_99, chunk6_100, chunk6_101, chunk6_102, chunk6_117]
private theorem checked7_3 : ∀ w ∈ chunk7_3, ¬ Need 7 w.toFinset := by
  have h : chunk7_3.all (routes 6 pool7_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_19 _ hm
  · exact checked6_21 _ hm
  · exact checked6_25 _ hm
  · exact checked6_26 _ hm
  · exact checked6_35 _ hm
  · exact checked6_37 _ hm
  · exact checked6_52 _ hm
  · exact checked6_53 _ hm
  · exact checked6_54 _ hm
  · exact checked6_77 _ hm
  · exact checked6_81 _ hm
  · exact checked6_91 _ hm
  · exact checked6_99 _ hm
  · exact checked6_100 _ hm
  · exact checked6_101 _ hm
  · exact checked6_102 _ hm
  · exact checked6_117 _ hm
private def chunk7_4 : List (List T) := [[wire63,wire1986,wire30852,wire32710,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire65536,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire131072,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire233791,wire860688,wire1721376]]
private def pool7_4 : List (List (List T)) := [chunk6_5, chunk6_9, chunk6_19, chunk6_22, chunk6_27, chunk6_32, chunk6_57, chunk6_58, chunk6_60, chunk6_67, chunk6_78, chunk6_81, chunk6_82, chunk6_84, chunk6_88, chunk6_103, chunk6_104, chunk6_112, chunk6_117]
private theorem checked7_4 : ∀ w ∈ chunk7_4, ¬ Need 7 w.toFinset := by
  have h : chunk7_4.all (routes 6 pool7_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_5 _ hm
  · exact checked6_9 _ hm
  · exact checked6_19 _ hm
  · exact checked6_22 _ hm
  · exact checked6_27 _ hm
  · exact checked6_32 _ hm
  · exact checked6_57 _ hm
  · exact checked6_58 _ hm
  · exact checked6_60 _ hm
  · exact checked6_67 _ hm
  · exact checked6_78 _ hm
  · exact checked6_81 _ hm
  · exact checked6_82 _ hm
  · exact checked6_84 _ hm
  · exact checked6_88 _ hm
  · exact checked6_103 _ hm
  · exact checked6_104 _ hm
  · exact checked6_112 _ hm
  · exact checked6_117 _ hm
private def chunk7_5 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire235466,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire375775,wire860688],
  [wire63,wire1986,wire30852,wire233736,wire375775,wire860688,wire1721376]]
private def pool7_5 : List (List (List T)) := [chunk6_1, chunk6_10, chunk6_11, chunk6_13, chunk6_14, chunk6_15, chunk6_16, chunk6_17, chunk6_18, chunk6_19, chunk6_32, chunk6_35, chunk6_36, chunk6_38, chunk6_52, chunk6_58, chunk6_60, chunk6_61, chunk6_68, chunk6_72, chunk6_78, chunk6_82, chunk6_84, chunk6_89, chunk6_92, chunk6_100, chunk6_104, chunk6_106, chunk6_110, chunk6_112]
private theorem checked7_5 : ∀ w ∈ chunk7_5, ¬ Need 7 w.toFinset := by
  have h : chunk7_5.all (routes 6 pool7_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_13 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_18 _ hm
  · exact checked6_19 _ hm
  · exact checked6_32 _ hm
  · exact checked6_35 _ hm
  · exact checked6_36 _ hm
  · exact checked6_38 _ hm
  · exact checked6_52 _ hm
  · exact checked6_58 _ hm
  · exact checked6_60 _ hm
  · exact checked6_61 _ hm
  · exact checked6_68 _ hm
  · exact checked6_72 _ hm
  · exact checked6_78 _ hm
  · exact checked6_82 _ hm
  · exact checked6_84 _ hm
  · exact checked6_89 _ hm
  · exact checked6_92 _ hm
  · exact checked6_100 _ hm
  · exact checked6_104 _ hm
  · exact checked6_106 _ hm
  · exact checked6_110 _ hm
  · exact checked6_112 _ hm
private def chunk7_6 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire524288,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire860735,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire862162,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire883348,wire1721376]]
private def pool7_6 : List (List (List T)) := [chunk6_10, chunk6_13, chunk6_19, chunk6_22, chunk6_23, chunk6_24, chunk6_25, chunk6_26, chunk6_39, chunk6_40, chunk6_46, chunk6_47, chunk6_48, chunk6_61, chunk6_85, chunk6_92, chunk6_106, chunk6_113, chunk6_117]
private theorem checked7_6 : ∀ w ∈ chunk7_6, ¬ Need 7 w.toFinset := by
  have h : chunk7_6.all (routes 6 pool7_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_10 _ hm
  · exact checked6_13 _ hm
  · exact checked6_19 _ hm
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_26 _ hm
  · exact checked6_39 _ hm
  · exact checked6_40 _ hm
  · exact checked6_46 _ hm
  · exact checked6_47 _ hm
  · exact checked6_48 _ hm
  · exact checked6_61 _ hm
  · exact checked6_85 _ hm
  · exact checked6_92 _ hm
  · exact checked6_106 _ hm
  · exact checked6_113 _ hm
  · exact checked6_117 _ hm
private def chunk7_7 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1028888,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1236463,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire1721407]]
private def pool7_7 : List (List (List T)) := [chunk6_1, chunk6_14, chunk6_16, chunk6_18, chunk6_19, chunk6_20, chunk6_22, chunk6_23, chunk6_26, chunk6_27, chunk6_28, chunk6_29, chunk6_30, chunk6_32, chunk6_36, chunk6_39, chunk6_41, chunk6_42, chunk6_44, chunk6_49, chunk6_52, chunk6_58, chunk6_61, chunk6_62, chunk6_63, chunk6_64, chunk6_73, chunk6_78, chunk6_82, chunk6_86, chunk6_100, chunk6_104, chunk6_107, chunk6_118]
private theorem checked7_7 : ∀ w ∈ chunk7_7, ¬ Need 7 w.toFinset := by
  have h : chunk7_7.all (routes 6 pool7_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_14 _ hm
  · exact checked6_16 _ hm
  · exact checked6_18 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_26 _ hm
  · exact checked6_27 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_30 _ hm
  · exact checked6_32 _ hm
  · exact checked6_36 _ hm
  · exact checked6_39 _ hm
  · exact checked6_41 _ hm
  · exact checked6_42 _ hm
  · exact checked6_44 _ hm
  · exact checked6_49 _ hm
  · exact checked6_52 _ hm
  · exact checked6_58 _ hm
  · exact checked6_61 _ hm
  · exact checked6_62 _ hm
  · exact checked6_63 _ hm
  · exact checked6_64 _ hm
  · exact checked6_73 _ hm
  · exact checked6_78 _ hm
  · exact checked6_82 _ hm
  · exact checked6_86 _ hm
  · exact checked6_100 _ hm
  · exact checked6_104 _ hm
  · exact checked6_107 _ hm
  · exact checked6_118 _ hm
private def chunk7_8 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire1722338],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire1735844],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire1824040],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire1863415]]
private def pool7_8 : List (List (List T)) := [chunk6_0, chunk6_8, chunk6_11, chunk6_14, chunk6_19, chunk6_30, chunk6_31, chunk6_41, chunk6_42, chunk6_45, chunk6_61, chunk6_62, chunk6_64, chunk6_65, chunk6_68, chunk6_69, chunk6_89, chunk6_110]
private theorem checked7_8 : ∀ w ∈ chunk7_8, ¬ Need 7 w.toFinset := by
  have h : chunk7_8.all (routes 6 pool7_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_8 _ hm
  · exact checked6_11 _ hm
  · exact checked6_14 _ hm
  · exact checked6_19 _ hm
  · exact checked6_30 _ hm
  · exact checked6_31 _ hm
  · exact checked6_41 _ hm
  · exact checked6_42 _ hm
  · exact checked6_45 _ hm
  · exact checked6_61 _ hm
  · exact checked6_62 _ hm
  · exact checked6_64 _ hm
  · exact checked6_65 _ hm
  · exact checked6_68 _ hm
  · exact checked6_69 _ hm
  · exact checked6_89 _ hm
  · exact checked6_110 _ hm
private def chunk7_9 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire2057776],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire2066299],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire2095165],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire2097088]]
private def pool7_9 : List (List (List T)) := [chunk6_0, chunk6_5, chunk6_7, chunk6_9, chunk6_12, chunk6_15, chunk6_18, chunk6_19, chunk6_22, chunk6_29, chunk6_43, chunk6_44, chunk6_45, chunk6_49, chunk6_63, chunk6_66, chunk6_69, chunk6_86, chunk6_93, chunk6_107, chunk6_108, chunk6_109, chunk6_110, chunk6_113, chunk6_118]
private theorem checked7_9 : ∀ w ∈ chunk7_9, ¬ Need 7 w.toFinset := by
  have h : chunk7_9.all (routes 6 pool7_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_5 _ hm
  · exact checked6_7 _ hm
  · exact checked6_9 _ hm
  · exact checked6_12 _ hm
  · exact checked6_15 _ hm
  · exact checked6_18 _ hm
  · exact checked6_19 _ hm
  · exact checked6_22 _ hm
  · exact checked6_29 _ hm
  · exact checked6_43 _ hm
  · exact checked6_44 _ hm
  · exact checked6_45 _ hm
  · exact checked6_49 _ hm
  · exact checked6_63 _ hm
  · exact checked6_66 _ hm
  · exact checked6_69 _ hm
  · exact checked6_86 _ hm
  · exact checked6_93 _ hm
  · exact checked6_107 _ hm
  · exact checked6_108 _ hm
  · exact checked6_109 _ hm
  · exact checked6_110 _ hm
  · exact checked6_113 _ hm
  · exact checked6_118 _ hm
private def chunk7_10 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1721376,wire2097151],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721407],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire2057776],
  [wire63,wire1986,wire30852,wire233736,wire860735,wire1721376]]
private def pool7_10 : List (List (List T)) := [chunk6_1, chunk6_2, chunk6_7, chunk6_10, chunk6_12, chunk6_13, chunk6_16, chunk6_19, chunk6_20, chunk6_22, chunk6_23, chunk6_24, chunk6_25, chunk6_26, chunk6_27, chunk6_28, chunk6_30, chunk6_33, chunk6_36, chunk6_39, chunk6_40, chunk6_44, chunk6_45, chunk6_46, chunk6_47, chunk6_49, chunk6_52, chunk6_53, chunk6_59, chunk6_64, chunk6_65, chunk6_73, chunk6_78, chunk6_79, chunk6_82, chunk6_83, chunk6_87, chunk6_98, chunk6_100, chunk6_101, chunk6_105, chunk6_108, chunk6_109, chunk6_114, chunk6_118]
private theorem checked7_10 : ∀ w ∈ chunk7_10, ¬ Need 7 w.toFinset := by
  have h : chunk7_10.all (routes 6 pool7_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_7 _ hm
  · exact checked6_10 _ hm
  · exact checked6_12 _ hm
  · exact checked6_13 _ hm
  · exact checked6_16 _ hm
  · exact checked6_19 _ hm
  · exact checked6_20 _ hm
  · exact checked6_22 _ hm
  · exact checked6_23 _ hm
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_26 _ hm
  · exact checked6_27 _ hm
  · exact checked6_28 _ hm
  · exact checked6_30 _ hm
  · exact checked6_33 _ hm
  · exact checked6_36 _ hm
  · exact checked6_39 _ hm
  · exact checked6_40 _ hm
  · exact checked6_44 _ hm
  · exact checked6_45 _ hm
  · exact checked6_46 _ hm
  · exact checked6_47 _ hm
  · exact checked6_49 _ hm
  · exact checked6_52 _ hm
  · exact checked6_53 _ hm
  · exact checked6_59 _ hm
  · exact checked6_64 _ hm
  · exact checked6_65 _ hm
  · exact checked6_73 _ hm
  · exact checked6_78 _ hm
  · exact checked6_79 _ hm
  · exact checked6_82 _ hm
  · exact checked6_83 _ hm
  · exact checked6_87 _ hm
  · exact checked6_98 _ hm
  · exact checked6_100 _ hm
  · exact checked6_101 _ hm
  · exact checked6_105 _ hm
  · exact checked6_108 _ hm
  · exact checked6_109 _ hm
  · exact checked6_114 _ hm
  · exact checked6_118 _ hm
private def chunk7_11 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire883348,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire1236463,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire1721376,wire2057776],
  [wire63,wire1986,wire30852,wire233791,wire860688,wire1721376]]
private def pool7_11 : List (List (List T)) := [chunk6_3, chunk6_5, chunk6_7, chunk6_11, chunk6_13, chunk6_15, chunk6_17, chunk6_19, chunk6_26, chunk6_27, chunk6_28, chunk6_29, chunk6_30, chunk6_31, chunk6_32, chunk6_33, chunk6_34, chunk6_37, chunk6_40, chunk6_41, chunk6_42, chunk6_48, chunk6_49, chunk6_50, chunk6_51, chunk6_53, chunk6_54, chunk6_57, chunk6_59, chunk6_60, chunk6_65, chunk6_66, chunk6_67, chunk6_68, chunk6_74, chunk6_79, chunk6_80, chunk6_83, chunk6_84, chunk6_87, chunk6_88, chunk6_89, chunk6_93, chunk6_98, chunk6_101, chunk6_102, chunk6_105, chunk6_109, chunk6_110, chunk6_114, chunk6_119]
private theorem checked7_11 : ∀ w ∈ chunk7_11, ¬ Need 7 w.toFinset := by
  have h : chunk7_11.all (routes 6 pool7_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_3 _ hm
  · exact checked6_5 _ hm
  · exact checked6_7 _ hm
  · exact checked6_11 _ hm
  · exact checked6_13 _ hm
  · exact checked6_15 _ hm
  · exact checked6_17 _ hm
  · exact checked6_19 _ hm
  · exact checked6_26 _ hm
  · exact checked6_27 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_30 _ hm
  · exact checked6_31 _ hm
  · exact checked6_32 _ hm
  · exact checked6_33 _ hm
  · exact checked6_34 _ hm
  · exact checked6_37 _ hm
  · exact checked6_40 _ hm
  · exact checked6_41 _ hm
  · exact checked6_42 _ hm
  · exact checked6_48 _ hm
  · exact checked6_49 _ hm
  · exact checked6_50 _ hm
  · exact checked6_51 _ hm
  · exact checked6_53 _ hm
  · exact checked6_54 _ hm
  · exact checked6_57 _ hm
  · exact checked6_59 _ hm
  · exact checked6_60 _ hm
  · exact checked6_65 _ hm
  · exact checked6_66 _ hm
  · exact checked6_67 _ hm
  · exact checked6_68 _ hm
  · exact checked6_74 _ hm
  · exact checked6_79 _ hm
  · exact checked6_80 _ hm
  · exact checked6_83 _ hm
  · exact checked6_84 _ hm
  · exact checked6_87 _ hm
  · exact checked6_88 _ hm
  · exact checked6_89 _ hm
  · exact checked6_93 _ hm
  · exact checked6_98 _ hm
  · exact checked6_101 _ hm
  · exact checked6_102 _ hm
  · exact checked6_105 _ hm
  · exact checked6_109 _ hm
  · exact checked6_110 _ hm
  · exact checked6_114 _ hm
  · exact checked6_119 _ hm
private def chunk7_12 : List (List T) := [[wire63,wire1986,wire30852,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire860688,wire1028888,wire1721376],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1824040],
  [wire63,wire1986,wire30852,wire860688,wire1721376,wire1863415]]
private def pool7_12 : List (List (List T)) := [chunk6_0, chunk6_6, chunk6_7, chunk6_8, chunk6_10, chunk6_11, chunk6_19, chunk6_35, chunk6_36, chunk6_37, chunk6_38, chunk6_39, chunk6_40, chunk6_41, chunk6_42, chunk6_43, chunk6_44, chunk6_45, chunk6_46, chunk6_47, chunk6_48, chunk6_49, chunk6_50, chunk6_51, chunk6_54, chunk6_55, chunk6_57, chunk6_68, chunk6_69, chunk6_70, chunk6_71, chunk6_75, chunk6_80, chunk6_81, chunk6_89, chunk6_90, chunk6_93, chunk6_102, chunk6_103, chunk6_111, chunk6_112, chunk6_114]
private theorem checked7_12 : ∀ w ∈ chunk7_12, ¬ Need 7 w.toFinset := by
  have h : chunk7_12.all (routes 6 pool7_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_19 _ hm
  · exact checked6_35 _ hm
  · exact checked6_36 _ hm
  · exact checked6_37 _ hm
  · exact checked6_38 _ hm
  · exact checked6_39 _ hm
  · exact checked6_40 _ hm
  · exact checked6_41 _ hm
  · exact checked6_42 _ hm
  · exact checked6_43 _ hm
  · exact checked6_44 _ hm
  · exact checked6_45 _ hm
  · exact checked6_46 _ hm
  · exact checked6_47 _ hm
  · exact checked6_48 _ hm
  · exact checked6_49 _ hm
  · exact checked6_50 _ hm
  · exact checked6_51 _ hm
  · exact checked6_54 _ hm
  · exact checked6_55 _ hm
  · exact checked6_57 _ hm
  · exact checked6_68 _ hm
  · exact checked6_69 _ hm
  · exact checked6_70 _ hm
  · exact checked6_71 _ hm
  · exact checked6_75 _ hm
  · exact checked6_80 _ hm
  · exact checked6_81 _ hm
  · exact checked6_89 _ hm
  · exact checked6_90 _ hm
  · exact checked6_93 _ hm
  · exact checked6_102 _ hm
  · exact checked6_103 _ hm
  · exact checked6_111 _ hm
  · exact checked6_112 _ hm
  · exact checked6_114 _ hm
private def chunk7_13 : List (List T) := [[wire63,wire1986,wire30911,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire233736,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire233736,wire860688,wire1721376,wire1735844],
  [wire63,wire1986,wire233736,wire860688,wire1721376,wire2066299]]
private def pool7_13 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_3, chunk6_4, chunk6_9, chunk6_19, chunk6_52, chunk6_53, chunk6_54, chunk6_55, chunk6_57, chunk6_58, chunk6_59, chunk6_60, chunk6_61, chunk6_62, chunk6_63, chunk6_64, chunk6_65, chunk6_66, chunk6_67, chunk6_68, chunk6_69, chunk6_70, chunk6_71, chunk6_76, chunk6_91, chunk6_92, chunk6_93, chunk6_94, chunk6_95, chunk6_98, chunk6_112, chunk6_113, chunk6_114, chunk6_115, chunk6_116, chunk6_117, chunk6_119]
private theorem checked7_13 : ∀ w ∈ chunk7_13, ¬ Need 7 w.toFinset := by
  have h : chunk7_13.all (routes 6 pool7_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_9 _ hm
  · exact checked6_19 _ hm
  · exact checked6_52 _ hm
  · exact checked6_53 _ hm
  · exact checked6_54 _ hm
  · exact checked6_55 _ hm
  · exact checked6_57 _ hm
  · exact checked6_58 _ hm
  · exact checked6_59 _ hm
  · exact checked6_60 _ hm
  · exact checked6_61 _ hm
  · exact checked6_62 _ hm
  · exact checked6_63 _ hm
  · exact checked6_64 _ hm
  · exact checked6_65 _ hm
  · exact checked6_66 _ hm
  · exact checked6_67 _ hm
  · exact checked6_68 _ hm
  · exact checked6_69 _ hm
  · exact checked6_70 _ hm
  · exact checked6_71 _ hm
  · exact checked6_76 _ hm
  · exact checked6_91 _ hm
  · exact checked6_92 _ hm
  · exact checked6_93 _ hm
  · exact checked6_94 _ hm
  · exact checked6_95 _ hm
  · exact checked6_98 _ hm
  · exact checked6_112 _ hm
  · exact checked6_113 _ hm
  · exact checked6_114 _ hm
  · exact checked6_115 _ hm
  · exact checked6_116 _ hm
  · exact checked6_117 _ hm
  · exact checked6_119 _ hm
private def chunk7_14 : List (List T) := [[wire63,wire2047,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire30852,wire32710,wire233736,wire860688,wire1721376],
  [wire63,wire30852,wire233736,wire235466,wire860688,wire1721376],
  [wire63,wire30852,wire233736,wire860688,wire1721376,wire2095165]]
private def pool7_14 : List (List (List T)) := [chunk6_6, chunk6_19, chunk6_72, chunk6_73, chunk6_74, chunk6_75, chunk6_76, chunk6_77, chunk6_78, chunk6_79, chunk6_80, chunk6_81, chunk6_82, chunk6_83, chunk6_84, chunk6_85, chunk6_86, chunk6_87, chunk6_88, chunk6_89, chunk6_90, chunk6_91, chunk6_92, chunk6_93, chunk6_94, chunk6_95, chunk6_117, chunk6_118, chunk6_119, chunk6_120, chunk6_121, chunk6_122]
private theorem checked7_14 : ∀ w ∈ chunk7_14, ¬ Need 7 w.toFinset := by
  have h : chunk7_14.all (routes 6 pool7_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_6 _ hm
  · exact checked6_19 _ hm
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
  · exact checked6_83 _ hm
  · exact checked6_84 _ hm
  · exact checked6_85 _ hm
  · exact checked6_86 _ hm
  · exact checked6_87 _ hm
  · exact checked6_88 _ hm
  · exact checked6_89 _ hm
  · exact checked6_90 _ hm
  · exact checked6_91 _ hm
  · exact checked6_92 _ hm
  · exact checked6_93 _ hm
  · exact checked6_94 _ hm
  · exact checked6_95 _ hm
  · exact checked6_117 _ hm
  · exact checked6_118 _ hm
  · exact checked6_119 _ hm
  · exact checked6_120 _ hm
  · exact checked6_121 _ hm
  · exact checked6_122 _ hm
private def chunk7_15 : List (List T) := [[wire1986,wire30852,wire30911,wire233736,wire860688,wire1721376],
  [wire1986,wire30852,wire233736,wire233791,wire860688,wire1721376],
  [wire1986,wire30852,wire233736,wire860688,wire1721376,wire2097088]]
private def pool7_15 : List (List (List T)) := [chunk6_19, chunk6_96, chunk6_97, chunk6_99, chunk6_100, chunk6_101, chunk6_102, chunk6_103, chunk6_104, chunk6_105, chunk6_106, chunk6_107, chunk6_108, chunk6_109, chunk6_110, chunk6_111, chunk6_112, chunk6_113, chunk6_114, chunk6_115, chunk6_116, chunk6_117, chunk6_119, chunk6_120, chunk6_121, chunk6_122]
private theorem checked7_15 : ∀ w ∈ chunk7_15, ¬ Need 7 w.toFinset := by
  have h : chunk7_15.all (routes 6 pool7_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_19 _ hm
  · exact checked6_96 _ hm
  · exact checked6_97 _ hm
  · exact checked6_99 _ hm
  · exact checked6_100 _ hm
  · exact checked6_101 _ hm
  · exact checked6_102 _ hm
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
  · exact checked6_114 _ hm
  · exact checked6_115 _ hm
  · exact checked6_116 _ hm
  · exact checked6_117 _ hm
  · exact checked6_119 _ hm
  · exact checked6_120 _ hm
  · exact checked6_121 _ hm
  · exact checked6_122 _ hm
#print axioms checked7_15
private def chunk8_0 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1721376]]
private def pool8_0 : List (List (List T)) := [chunk7_0, chunk7_1, chunk7_2, chunk7_3, chunk7_4, chunk7_5, chunk7_6, chunk7_7, chunk7_8, chunk7_9, chunk7_10, chunk7_11, chunk7_12, chunk7_13, chunk7_14, chunk7_15]
private theorem checked8_0 : ∀ w ∈ chunk8_0, ¬ Need 8 w.toFinset := by
  have h : chunk8_0.all (routes 7 pool8_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool8_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked7_0 _ hm
  · exact checked7_1 _ hm
  · exact checked7_2 _ hm
  · exact checked7_3 _ hm
  · exact checked7_4 _ hm
  · exact checked7_5 _ hm
  · exact checked7_6 _ hm
  · exact checked7_7 _ hm
  · exact checked7_8 _ hm
  · exact checked7_9 _ hm
  · exact checked7_10 _ hm
  · exact checked7_11 _ hm
  · exact checked7_12 _ hm
  · exact checked7_13 _ hm
  · exact checked7_14 _ hm
  · exact checked7_15 _ hm
#print axioms checked8_0
private theorem root : safe 8 ins := initial checked8_0 (by decide +kernel)
private def samples : Fin (2*K) → Fin 6 × Fin 6 := ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 5), (0, 5), (0, 5), (0, 5), (0, 5), (0, 5), (0, 5), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 4), (1, 4), (1, 4), (1, 4), (1, 4), (1, 4), (1, 4), (1, 5), (1, 5), (1, 5), (1, 5), (1, 5), (1, 5), (1, 5), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (2, 4), (2, 4), (2, 4), (2, 4), (2, 4), (2, 4), (2, 4), (3, 3), (3, 3), (3, 3), (3, 3), (3, 3), (3, 3), (3, 3), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (1, 1), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
private def inputs (i : Fin (2*K)) :=
  List.ofFn fun k : Fin 6 => decide (k = (samples i).1 ∨ k = (samples i).2)

private theorem tables (C : Circuit)
    (he : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2215743 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :
    ∀ k, (C.gates.foldl step (ins.map (bit k))).getD C.output false = bit k target := by
  intro k
  have hi : ∀ i : Fin (2*K), inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin (2*K), (2215743 : Nat).testBit
      (6 * min (samples i).1.val (samples i).2.val + max (samples i).1.val (samples i).2.val) = bit i target := by decide +kernel
  have h := he (samples k).1 (samples k).2
  change C.eval (inputs k) = _ at h
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using h

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (2215743 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hg,hs,he⟩
  exact exclude C.gates C.output (fun g hm => hg g hm) ins ins
    (fun ⦃_⦄ hx => hx) 8 hs root (tables C he)

#print axioms generalLower

-- Nine gates suffice on all 36 ordered input pairs.
def circuit : Circuit :=
  { gates := [⟨.not,[2]⟩, ⟨.or,[2,3]⟩, ⟨.and,[4,6]⟩, ⟨.or,[8,5]⟩,
              ⟨.not,[9]⟩, ⟨.or,[1,10]⟩, ⟨.or,[7,9]⟩, ⟨.and,[11,12]⟩, ⟨.or,[0,13]⟩], output := 14 }

theorem nine : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (2215743 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms nine
end Graph2215743
