import PEqualNP.Defs.Represents

-- The gate semantics and safety induction adapt the Apache-2.0 proof credited in Mask53Exact.lean.
-- Lewis Watson and Nico Habets developed the earlier gate enumeration.
-- Here the twenty-one table entries are all singleton and pair inputs on six pins.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Graph279104431

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev K := 90
private abbrev T := BitVec (2*K)
private def ins : List T := [(((((((((((0x4104 : T) <<< 32) ||| 0x10410410) <<< 32) ||| 0x41041041) <<< 32) ||| 0x4000000) <<< 32) ||| 0x0) <<< 32) ||| 0x3fffffff), (((((((((((0x8208 : T) <<< 32) ||| 0x20820820) <<< 32) ||| 0x82082082) <<< 32) ||| 0x8000000) <<< 32) ||| 0x3fffff) <<< 32) ||| 0xc0000fc0), (((((((((((0x10410 : T) <<< 32) ||| 0x41041041) <<< 32) ||| 0x4104104) <<< 32) ||| 0x100000ff) <<< 32) ||| 0xffc003f0) <<< 32) ||| 0x3f000), (((((((((((0x20820 : T) <<< 32) ||| 0x82082082) <<< 32) ||| 0x8208208) <<< 32) ||| 0x200fff03) <<< 32) ||| 0xf000fc00) <<< 32) ||| 0xfc0000), (((((((((((0x7df7d : T) <<< 32) ||| 0xf7df7df7) <<< 32) ||| 0xdf7df7df) <<< 32) ||| 0x7ff00000) <<< 32) ||| 0x0) <<< 32) ||| 0x0), (((((((((((0xc30c3 : T) <<< 32) ||| 0xc30c30c) <<< 32) ||| 0x30c30c30) <<< 32) ||| 0xc00fc0fc) <<< 32) ||| 0x3f0000) <<< 32) ||| 0x3f000000)]
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
private def wire63 : T := (((((((((((0x4104 : T) <<< 32) ||| 0x10410410) <<< 32) ||| 0x41041041) <<< 32) ||| 0x4000000) <<< 32) ||| 0x0) <<< 32) ||| 0x3fffffff)
private def wire1986 : T := (((((((((((0x8208 : T) <<< 32) ||| 0x20820820) <<< 32) ||| 0x82082082) <<< 32) ||| 0x8000000) <<< 32) ||| 0x3fffff) <<< 32) ||| 0xc0000fc0)
private def wire2047 : T := (((((((((((0xc30c : T) <<< 32) ||| 0x30c30c30) <<< 32) ||| 0xc30c30c3) <<< 32) ||| 0xc000000) <<< 32) ||| 0x3fffff) <<< 32) ||| 0xffffffff)
private def wire30852 : T := (((((((((((0x10410 : T) <<< 32) ||| 0x41041041) <<< 32) ||| 0x4104104) <<< 32) ||| 0x100000ff) <<< 32) ||| 0xffc003f0) <<< 32) ||| 0x3f000)
private def wire30911 : T := (((((((((((0x14514 : T) <<< 32) ||| 0x51451451) <<< 32) ||| 0x45145145) <<< 32) ||| 0x140000ff) <<< 32) ||| 0xffc003f0) <<< 32) ||| 0x3fffffff)
private def wire32710 : T := (((((((((((0x18618 : T) <<< 32) ||| 0x61861861) <<< 32) ||| 0x86186186) <<< 32) ||| 0x180000ff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc003ffc0)
private def wire32767 : T := (((((((((((0x1c71c : T) <<< 32) ||| 0x71c71c71) <<< 32) ||| 0xc71c71c7) <<< 32) ||| 0x1c0000ff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire74256 : T := (((((((((((0x3cf3c : T) <<< 32) ||| 0xf3cf3cf3) <<< 32) ||| 0xcf3cf3cf) <<< 32) ||| 0x3c000000) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire222768 : T := (((((((((((0x3cf3c : T) <<< 32) ||| 0xf3cf3cf3) <<< 32) ||| 0xcf3cf3cf) <<< 32) ||| 0x3c0fc0fc) <<< 32) ||| 0x3f0000) <<< 32) ||| 0x3f000000)
private def wire233736 : T := (((((((((((0x20820 : T) <<< 32) ||| 0x82082082) <<< 32) ||| 0x8208208) <<< 32) ||| 0x200fff03) <<< 32) ||| 0xf000fc00) <<< 32) ||| 0xfc0000)
private def wire233791 : T := (((((((((((0x24924 : T) <<< 32) ||| 0x92492492) <<< 32) ||| 0x49249249) <<< 32) ||| 0x240fff03) <<< 32) ||| 0xf000fc00) <<< 32) ||| 0x3fffffff)
private def wire235466 : T := (((((((((((0x28a28 : T) <<< 32) ||| 0xa28a28a2) <<< 32) ||| 0x8a28a28a) <<< 32) ||| 0x280fff03) <<< 32) ||| 0xf03fffff) <<< 32) ||| 0xc0fc0fc0)
private def wire235519 : T := (((((((((((0x2cb2c : T) <<< 32) ||| 0xb2cb2cb2) <<< 32) ||| 0xcb2cb2cb) <<< 32) ||| 0x2c0fff03) <<< 32) ||| 0xf03fffff) <<< 32) ||| 0xffffffff)
private def wire260492 : T := (((((((((((0x30c30 : T) <<< 32) ||| 0xc30c30c3) <<< 32) ||| 0xc30c30c) <<< 32) ||| 0x300fffff) <<< 32) ||| 0xffc0fff0) <<< 32) ||| 0xfff000)
private def wire260543 : T := (((((((((((0x34d34 : T) <<< 32) ||| 0xd34d34d3) <<< 32) ||| 0x4d34d34d) <<< 32) ||| 0x340fffff) <<< 32) ||| 0xffc0fff0) <<< 32) ||| 0x3fffffff)
private def wire262094 : T := (((((((((((0x38e38 : T) <<< 32) ||| 0xe38e38e3) <<< 32) ||| 0x8e38e38e) <<< 32) ||| 0x380fffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc0ffffc0)
private def wire262143 : T := (((((((((((0x3cf3c : T) <<< 32) ||| 0xf3cf3cf3) <<< 32) ||| 0xcf3cf3cf) <<< 32) ||| 0x3c0fffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire336400 : T := (((((((((((0x3cf3c : T) <<< 32) ||| 0xf3cf3cf3) <<< 32) ||| 0xcf3cf3cf) <<< 32) ||| 0x3ff00000) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire375775 : T := (((((((((((0x3cf3c : T) <<< 32) ||| 0xf3cf3cf3) <<< 32) ||| 0xcf3cf3cf) <<< 32) ||| 0x3ff03f03) <<< 32) ||| 0xffc0ffff) <<< 32) ||| 0xc0ffffff)
private def wire524288 : T := (((((((((((0x41041 : T) <<< 32) ||| 0x4104104) <<< 32) ||| 0x10410410) <<< 32) ||| 0x40000000) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire524351 : T := (((((((((((0x45145 : T) <<< 32) ||| 0x14514514) <<< 32) ||| 0x51451451) <<< 32) ||| 0x44000000) <<< 32) ||| 0x0) <<< 32) ||| 0x3fffffff)
private def wire526274 : T := (((((((((((0x49249 : T) <<< 32) ||| 0x24924924) <<< 32) ||| 0x92492492) <<< 32) ||| 0x48000000) <<< 32) ||| 0x3fffff) <<< 32) ||| 0xc0000fc0)
private def wire526335 : T := (((((((((((0x4d34d : T) <<< 32) ||| 0x34d34d34) <<< 32) ||| 0xd34d34d3) <<< 32) ||| 0x4c000000) <<< 32) ||| 0x3fffff) <<< 32) ||| 0xffffffff)
private def wire555140 : T := (((((((((((0x51451 : T) <<< 32) ||| 0x45145145) <<< 32) ||| 0x14514514) <<< 32) ||| 0x500000ff) <<< 32) ||| 0xffc003f0) <<< 32) ||| 0x3f000)
private def wire555199 : T := (((((((((((0x55555 : T) <<< 32) ||| 0x55555555) <<< 32) ||| 0x55555555) <<< 32) ||| 0x540000ff) <<< 32) ||| 0xffc003f0) <<< 32) ||| 0x3fffffff)
private def wire556998 : T := (((((((((((0x59659 : T) <<< 32) ||| 0x65965965) <<< 32) ||| 0x96596596) <<< 32) ||| 0x580000ff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc003ffc0)
private def wire557055 : T := (((((((((((0x5d75d : T) <<< 32) ||| 0x75d75d75) <<< 32) ||| 0xd75d75d7) <<< 32) ||| 0x5c0000ff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire758024 : T := (((((((((((0x61861 : T) <<< 32) ||| 0x86186186) <<< 32) ||| 0x18618618) <<< 32) ||| 0x600fff03) <<< 32) ||| 0xf000fc00) <<< 32) ||| 0xfc0000)
private def wire758079 : T := (((((((((((0x65965 : T) <<< 32) ||| 0x96596596) <<< 32) ||| 0x59659659) <<< 32) ||| 0x640fff03) <<< 32) ||| 0xf000fc00) <<< 32) ||| 0x3fffffff)
private def wire759754 : T := (((((((((((0x69a69 : T) <<< 32) ||| 0xa69a69a6) <<< 32) ||| 0x9a69a69a) <<< 32) ||| 0x680fff03) <<< 32) ||| 0xf03fffff) <<< 32) ||| 0xc0fc0fc0)
private def wire759807 : T := (((((((((((0x6db6d : T) <<< 32) ||| 0xb6db6db6) <<< 32) ||| 0xdb6db6db) <<< 32) ||| 0x6c0fff03) <<< 32) ||| 0xf03fffff) <<< 32) ||| 0xffffffff)
private def wire784780 : T := (((((((((((0x71c71 : T) <<< 32) ||| 0xc71c71c7) <<< 32) ||| 0x1c71c71c) <<< 32) ||| 0x700fffff) <<< 32) ||| 0xffc0fff0) <<< 32) ||| 0xfff000)
private def wire784831 : T := (((((((((((0x75d75 : T) <<< 32) ||| 0xd75d75d7) <<< 32) ||| 0x5d75d75d) <<< 32) ||| 0x740fffff) <<< 32) ||| 0xffc0fff0) <<< 32) ||| 0x3fffffff)
private def wire786382 : T := (((((((((((0x79e79 : T) <<< 32) ||| 0xe79e79e7) <<< 32) ||| 0x9e79e79e) <<< 32) ||| 0x780fffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc0ffffc0)
private def wire786431 : T := (((((((((((0x7df7d : T) <<< 32) ||| 0xf7df7df7) <<< 32) ||| 0xdf7df7df) <<< 32) ||| 0x7c0fffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire860688 : T := (((((((((((0x7df7d : T) <<< 32) ||| 0xf7df7df7) <<< 32) ||| 0xdf7df7df) <<< 32) ||| 0x7ff00000) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire1236463 : T := (((((((((((0x82082 : T) <<< 32) ||| 0x8208208) <<< 32) ||| 0x20820820) <<< 32) ||| 0x800fffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire1721376 : T := (((((((((((0xc30c3 : T) <<< 32) ||| 0xc30c30c) <<< 32) ||| 0x30c30c30) <<< 32) ||| 0xc00fc0fc) <<< 32) ||| 0x3f0000) <<< 32) ||| 0x3f000000)
private def wire1721407 : T := (((((((((((0xc71c7 : T) <<< 32) ||| 0x1c71c71c) <<< 32) ||| 0x71c71c71) <<< 32) ||| 0xc40fc0fc) <<< 32) ||| 0x3f0000) <<< 32) ||| 0x3fffffff)
private def wire1722338 : T := (((((((((((0xcb2cb : T) <<< 32) ||| 0x2cb2cb2c) <<< 32) ||| 0xb2cb2cb2) <<< 32) ||| 0xc80fc0fc) <<< 32) ||| 0x3fffff) <<< 32) ||| 0xff000fc0)
private def wire1722367 : T := (((((((((((0xcf3cf : T) <<< 32) ||| 0x3cf3cf3c) <<< 32) ||| 0xf3cf3cf3) <<< 32) ||| 0xcc0fc0fc) <<< 32) ||| 0x3fffff) <<< 32) ||| 0xffffffff)
private def wire1735844 : T := (((((((((((0xd34d3 : T) <<< 32) ||| 0x4d34d34d) <<< 32) ||| 0x34d34d34) <<< 32) ||| 0xd00fc0ff) <<< 32) ||| 0xffff03f0) <<< 32) ||| 0x3f03f000)
private def wire1735871 : T := (((((((((((0xd75d7 : T) <<< 32) ||| 0x5d75d75d) <<< 32) ||| 0x75d75d75) <<< 32) ||| 0xd40fc0ff) <<< 32) ||| 0xffff03f0) <<< 32) ||| 0x3fffffff)
private def wire1736678 : T := (((((((((((0xdb6db : T) <<< 32) ||| 0x6db6db6d) <<< 32) ||| 0xb6db6db6) <<< 32) ||| 0xd80fc0ff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xff03ffc0)
private def wire1736703 : T := (((((((((((0xdf7df : T) <<< 32) ||| 0x7df7df7d) <<< 32) ||| 0xf7df7df7) <<< 32) ||| 0xdc0fc0ff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire1760751 : T := (((((((((((0xc30c3 : T) <<< 32) ||| 0xc30c30c) <<< 32) ||| 0x30c30c30) <<< 32) ||| 0xc00fffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire1824040 : T := (((((((((((0xe38e3 : T) <<< 32) ||| 0x8e38e38e) <<< 32) ||| 0x38e38e38) <<< 32) ||| 0xe00fffff) <<< 32) ||| 0xf03ffc00) <<< 32) ||| 0x3ffc0000)
private def wire1824063 : T := (((((((((((0xe79e7 : T) <<< 32) ||| 0x9e79e79e) <<< 32) ||| 0x79e79e79) <<< 32) ||| 0xe40fffff) <<< 32) ||| 0xf03ffc00) <<< 32) ||| 0x3fffffff)
private def wire1824746 : T := (((((((((((0xebaeb : T) <<< 32) ||| 0xaebaebae) <<< 32) ||| 0xbaebaeba) <<< 32) ||| 0xe80fffff) <<< 32) ||| 0xf03fffff) <<< 32) ||| 0xfffc0fc0)
private def wire1824767 : T := (((((((((((0xefbef : T) <<< 32) ||| 0xbefbefbe) <<< 32) ||| 0xfbefbefb) <<< 32) ||| 0xec0fffff) <<< 32) ||| 0xf03fffff) <<< 32) ||| 0xffffffff)
private def wire1834412 : T := (((((((((((0xf3cf3 : T) <<< 32) ||| 0xcf3cf3cf) <<< 32) ||| 0x3cf3cf3c) <<< 32) ||| 0xf00fffff) <<< 32) ||| 0xfffffff0) <<< 32) ||| 0x3ffff000)
private def wire1834431 : T := (((((((((((0xf7df7 : T) <<< 32) ||| 0xdf7df7df) <<< 32) ||| 0x7df7df7d) <<< 32) ||| 0xf40fffff) <<< 32) ||| 0xfffffff0) <<< 32) ||| 0x3fffffff)
private def wire1834990 : T := (((((((((((0xfbefb : T) <<< 32) ||| 0xefbefbef) <<< 32) ||| 0xbefbefbe) <<< 32) ||| 0xf80fffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffc0)
private def wire1835007 : T := (((((((((((0xfffff : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xfc0fffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)
private def wire1835008 : T := (((((((((((0xc30c3 : T) <<< 32) ||| 0xc30c30c) <<< 32) ||| 0x30c30c30) <<< 32) ||| 0xc3f00000) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire1835057 : T := (((((((((((0xc71c7 : T) <<< 32) ||| 0x1c71c71c) <<< 32) ||| 0x71c71c71) <<< 32) ||| 0xc7f00000) <<< 32) ||| 0x0) <<< 32) ||| 0x3f00003f)
private def wire1836608 : T := (((((((((((0xcb2cb : T) <<< 32) ||| 0x2cb2cb2c) <<< 32) ||| 0xb2cb2cb2) <<< 32) ||| 0xcbf00000) <<< 32) ||| 0x3f000f) <<< 32) ||| 0xc0000000)
private def wire1836659 : T := (((((((((((0xcf3cf : T) <<< 32) ||| 0x3cf3cf3c) <<< 32) ||| 0xf3cf3cf3) <<< 32) ||| 0xcff00000) <<< 32) ||| 0x3f000f) <<< 32) ||| 0xff000fff)
private def wire1861632 : T := (((((((((((0xd34d3 : T) <<< 32) ||| 0x4d34d34d) <<< 32) ||| 0x34d34d34) <<< 32) ||| 0xd3f000fc) <<< 32) ||| 0xfc00000) <<< 32) ||| 0x0)
private def wire1861685 : T := (((((((((((0xd75d7 : T) <<< 32) ||| 0x5d75d75d) <<< 32) ||| 0x75d75d75) <<< 32) ||| 0xd7f000fc) <<< 32) ||| 0xfc00000) <<< 32) ||| 0x3f03f03f)
private def wire1863360 : T := (((((((((((0xdb6db : T) <<< 32) ||| 0x6db6db6d) <<< 32) ||| 0xb6db6db6) <<< 32) ||| 0xdbf000fc) <<< 32) ||| 0xfff03ff) <<< 32) ||| 0xc0000000)
private def wire1863415 : T := (((((((((((0xdf7df : T) <<< 32) ||| 0x7df7df7d) <<< 32) ||| 0xf7df7df7) <<< 32) ||| 0xdff000fc) <<< 32) ||| 0xfff03ff) <<< 32) ||| 0xff03ffff)
private def wire2057776 : T := (((((((((((0xfffff : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffc0fc) <<< 32) ||| 0x3f0000) <<< 32) ||| 0x3f000000)
private def wire2064384 : T := (((((((((((0xe38e3 : T) <<< 32) ||| 0x8e38e38e) <<< 32) ||| 0x38e38e38) <<< 32) ||| 0xe3ffff00) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire2064441 : T := (((((((((((0xe79e7 : T) <<< 32) ||| 0x9e79e79e) <<< 32) ||| 0x79e79e79) <<< 32) ||| 0xe7ffff00) <<< 32) ||| 0x0) <<< 32) ||| 0x3ffc003f)
private def wire2066240 : T := (((((((((((0xebaeb : T) <<< 32) ||| 0xaebaebae) <<< 32) ||| 0xbaebaeba) <<< 32) ||| 0xebffff00) <<< 32) ||| 0x3ffc0f) <<< 32) ||| 0xc0000000)
private def wire2066299 : T := (((((((((((0xefbef : T) <<< 32) ||| 0xbefbefbe) <<< 32) ||| 0xfbefbefb) <<< 32) ||| 0xefffff00) <<< 32) ||| 0x3ffc0f) <<< 32) ||| 0xfffc0fff)
private def wire2095104 : T := (((((((((((0xf3cf3 : T) <<< 32) ||| 0xcf3cf3cf) <<< 32) ||| 0x3cf3cf3c) <<< 32) ||| 0xf3ffffff) <<< 32) ||| 0xffc00000) <<< 32) ||| 0x0)
private def wire2095165 : T := (((((((((((0xf7df7 : T) <<< 32) ||| 0xdf7df7df) <<< 32) ||| 0x7df7df7d) <<< 32) ||| 0xf7ffffff) <<< 32) ||| 0xffc00000) <<< 32) ||| 0x3ffff03f)
private def wire2097088 : T := (((((((((((0xfbefb : T) <<< 32) ||| 0xefbefbef) <<< 32) ||| 0xbefbefbe) <<< 32) ||| 0xfbffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc0000000)

-- Every listed set is checked against every possible next output and every reuse of its inputs.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def layer1 : List (List T) := []
private theorem good1 (w : List T) (h : w ∈ layer1) : ¬ Need 1 w.toFinset := by simp [layer1] at h
private def chunk2_0 : List (List T) := [[wire222768,wire1721376],
  [wire262143,wire336400],
  [wire262143,wire1760751],
  [wire786431,wire860688]]
private def pool2_0 : List (List (List T)) := []
private theorem checked2_0 : ∀ w ∈ chunk2_0, ¬ Need 2 w.toFinset := by
  have h : chunk2_0.all (routes 1 pool2_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool2_0] at hv
#print axioms checked2_0
private def chunk3_0 : List (List T) := [[wire63,wire262094,wire336400],
  [wire63,wire262094,wire1760751],
  [wire63,wire786382,wire860688],
  [wire1986,wire260543,wire336400]]
private def pool3_0 : List (List (List T)) := [chunk2_0]
private theorem checked3_0 : ∀ w ∈ chunk3_0, ¬ Need 3 w.toFinset := by
  have h : chunk3_0.all (routes 2 pool3_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
private def chunk3_1 : List (List T) := [[wire1986,wire260543,wire1760751],
  [wire1986,wire784831,wire860688],
  [wire2047,wire260492,wire336400],
  [wire2047,wire260492,wire1760751]]
private def pool3_1 : List (List (List T)) := [chunk2_0]
private theorem checked3_1 : ∀ w ∈ chunk3_1, ¬ Need 3 w.toFinset := by
  have h : chunk3_1.all (routes 2 pool3_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
private def chunk3_2 : List (List T) := [[wire2047,wire784780,wire860688],
  [wire30852,wire235519,wire336400],
  [wire30852,wire235519,wire1760751],
  [wire30852,wire759807,wire860688]]
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
private def chunk3_3 : List (List T) := [[wire30911,wire235466,wire336400],
  [wire30911,wire235466,wire1760751],
  [wire30911,wire759754,wire860688],
  [wire32710,wire233791,wire336400]]
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
private def chunk3_4 : List (List T) := [[wire32710,wire233791,wire1760751],
  [wire32710,wire758079,wire860688],
  [wire32767,wire233736,wire336400],
  [wire32767,wire233736,wire1760751]]
private def pool3_4 : List (List (List T)) := [chunk2_0]
private theorem checked3_4 : ∀ w ∈ chunk3_4, ¬ Need 3 w.toFinset := by
  have h : chunk3_4.all (routes 2 pool3_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
private def chunk3_5 : List (List T) := [[wire32767,wire758024,wire860688],
  [wire74256,wire262143,wire1721376],
  [wire233736,wire557055,wire860688],
  [wire233791,wire556998,wire860688]]
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
private def chunk3_6 : List (List T) := [[wire235466,wire555199,wire860688],
  [wire235519,wire555140,wire860688],
  [wire260492,wire526335,wire860688],
  [wire260543,wire526274,wire860688]]
private def pool3_6 : List (List (List T)) := [chunk2_0]
private theorem checked3_6 : ∀ w ∈ chunk3_6, ¬ Need 3 w.toFinset := by
  have h : chunk3_6.all (routes 2 pool3_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
private def chunk3_7 : List (List T) := [[wire262094,wire524351,wire860688],
  [wire262143,wire375775,wire860688],
  [wire262143,wire524288,wire860688],
  [wire262143,wire860688,wire1721376]]
private def pool3_7 : List (List (List T)) := [chunk2_0]
private theorem checked3_7 : ∀ w ∈ chunk3_7, ¬ Need 3 w.toFinset := by
  have h : chunk3_7.all (routes 2 pool3_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
private def chunk3_8 : List (List T) := [[wire262143,wire860688,wire1721407],
  [wire262143,wire860688,wire1722338],
  [wire262143,wire860688,wire1722367],
  [wire262143,wire860688,wire1735844]]
private def pool3_8 : List (List (List T)) := []
private theorem checked3_8 : ∀ w ∈ chunk3_8, ¬ Need 3 w.toFinset := by
  have h : chunk3_8.all (routes 2 pool3_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_8] at hv
private def chunk3_9 : List (List T) := [[wire262143,wire860688,wire1735871],
  [wire262143,wire860688,wire1736678],
  [wire262143,wire860688,wire1736703],
  [wire262143,wire860688,wire1824040]]
private def pool3_9 : List (List (List T)) := []
private theorem checked3_9 : ∀ w ∈ chunk3_9, ¬ Need 3 w.toFinset := by
  have h : chunk3_9.all (routes 2 pool3_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_9] at hv
private def chunk3_10 : List (List T) := [[wire262143,wire860688,wire1824063],
  [wire262143,wire860688,wire1824746],
  [wire262143,wire860688,wire1824767],
  [wire262143,wire860688,wire1834412]]
private def pool3_10 : List (List (List T)) := []
private theorem checked3_10 : ∀ w ∈ chunk3_10, ¬ Need 3 w.toFinset := by
  have h : chunk3_10.all (routes 2 pool3_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_10] at hv
private def chunk3_11 : List (List T) := [[wire262143,wire860688,wire1834431],
  [wire262143,wire860688,wire1834990],
  [wire262143,wire860688,wire1835007],
  [wire262143,wire1236463,wire1721376]]
private def pool3_11 : List (List (List T)) := [chunk2_0]
private theorem checked3_11 : ∀ w ∈ chunk3_11, ¬ Need 3 w.toFinset := by
  have h : chunk3_11.all (routes 2 pool3_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
private def chunk3_12 : List (List T) := [[wire262143,wire1721376,wire2057776],
  [wire860688,wire1721376,wire1835008]]
private def pool3_12 : List (List (List T)) := [chunk2_0]
private theorem checked3_12 : ∀ w ∈ chunk3_12, ¬ Need 3 w.toFinset := by
  have h : chunk3_12.all (routes 2 pool3_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_0 _ hm
#print axioms checked3_12
private def chunk4_0 : List (List T) := [[wire63,wire1986,wire260492,wire336400],
  [wire63,wire1986,wire260492,wire1760751],
  [wire63,wire1986,wire784780,wire860688],
  [wire63,wire30852,wire235466,wire336400]]
private def pool4_0 : List (List (List T)) := [chunk3_0, chunk3_1, chunk3_2, chunk3_3]
private theorem checked4_0 : ∀ w ∈ chunk4_0, ¬ Need 4 w.toFinset := by
  have h : chunk4_0.all (routes 3 pool4_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_1 _ hm
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
private def chunk4_1 : List (List T) := [[wire63,wire30852,wire235466,wire1760751],
  [wire63,wire30852,wire759754,wire860688],
  [wire63,wire32710,wire233736,wire336400],
  [wire63,wire32710,wire233736,wire1760751]]
private def pool4_1 : List (List (List T)) := [chunk3_0, chunk3_2, chunk3_3, chunk3_4]
private theorem checked4_1 : ∀ w ∈ chunk4_1, ¬ Need 4 w.toFinset := by
  have h : chunk4_1.all (routes 3 pool4_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
  · exact checked3_4 _ hm
private def chunk4_2 : List (List T) := [[wire63,wire32710,wire758024,wire860688],
  [wire63,wire233736,wire556998,wire860688],
  [wire63,wire235466,wire555140,wire860688],
  [wire63,wire260492,wire526274,wire860688]]
private def pool4_2 : List (List (List T)) := [chunk3_0, chunk3_4, chunk3_5, chunk3_6]
private theorem checked4_2 : ∀ w ∈ chunk4_2, ¬ Need 4 w.toFinset := by
  have h : chunk4_2.all (routes 3 pool4_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
private def chunk4_3 : List (List T) := [[wire63,wire262094,wire375775,wire860688],
  [wire63,wire262094,wire524288,wire860688],
  [wire63,wire262094,wire860688,wire1721376],
  [wire63,wire262094,wire860688,wire1721407]]
private def pool4_3 : List (List (List T)) := [chunk3_0, chunk3_7, chunk3_8]
private theorem checked4_3 : ∀ w ∈ chunk4_3, ¬ Need 4 w.toFinset := by
  have h : chunk4_3.all (routes 3 pool4_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_7 _ hm
  · exact checked3_8 _ hm
private def chunk4_4 : List (List T) := [[wire63,wire262094,wire860688,wire1722338],
  [wire63,wire262094,wire860688,wire1735844],
  [wire63,wire262094,wire860688,wire1736678],
  [wire63,wire262094,wire860688,wire1824040]]
private def pool4_4 : List (List (List T)) := [chunk3_8, chunk3_9]
private theorem checked4_4 : ∀ w ∈ chunk4_4, ¬ Need 4 w.toFinset := by
  have h : chunk4_4.all (routes 3 pool4_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_9 _ hm
private def chunk4_5 : List (List T) := [[wire63,wire262094,wire860688,wire1824746],
  [wire63,wire262094,wire860688,wire1834412],
  [wire63,wire262094,wire860688,wire1834990],
  [wire63,wire262094,wire1236463,wire1721376]]
private def pool4_5 : List (List (List T)) := [chunk3_0, chunk3_10, chunk3_11]
private theorem checked4_5 : ∀ w ∈ chunk4_5, ¬ Need 4 w.toFinset := by
  have h : chunk4_5.all (routes 3 pool4_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_10 _ hm
  · exact checked3_11 _ hm
private def chunk4_6 : List (List T) := [[wire63,wire262094,wire1721376,wire2057776],
  [wire63,wire262143,wire860688,wire1721376],
  [wire63,wire860688,wire1721376,wire1835057],
  [wire1986,wire30852,wire233791,wire336400]]
private def pool4_6 : List (List (List T)) := [chunk3_0, chunk3_2, chunk3_3, chunk3_7, chunk3_8, chunk3_12]
private theorem checked4_6 : ∀ w ∈ chunk4_6, ¬ Need 4 w.toFinset := by
  have h : chunk4_6.all (routes 3 pool4_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
  · exact checked3_7 _ hm
  · exact checked3_8 _ hm
  · exact checked3_12 _ hm
private def chunk4_7 : List (List T) := [[wire1986,wire30852,wire233791,wire1760751],
  [wire1986,wire30852,wire758079,wire860688],
  [wire1986,wire30911,wire233736,wire336400],
  [wire1986,wire30911,wire233736,wire1760751]]
private def pool4_7 : List (List (List T)) := [chunk3_0, chunk3_1, chunk3_2, chunk3_3, chunk3_4]
private theorem checked4_7 : ∀ w ∈ chunk4_7, ¬ Need 4 w.toFinset := by
  have h : chunk4_7.all (routes 3 pool4_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_1 _ hm
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
  · exact checked3_4 _ hm
private def chunk4_8 : List (List T) := [[wire1986,wire30911,wire758024,wire860688],
  [wire1986,wire233736,wire555199,wire860688],
  [wire1986,wire233791,wire555140,wire860688],
  [wire1986,wire260492,wire524351,wire860688]]
private def pool4_8 : List (List (List T)) := [chunk3_1, chunk3_3, chunk3_5, chunk3_6, chunk3_7]
private theorem checked4_8 : ∀ w ∈ chunk4_8, ¬ Need 4 w.toFinset := by
  have h : chunk4_8.all (routes 3 pool4_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_1 _ hm
  · exact checked3_3 _ hm
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
private def chunk4_9 : List (List T) := [[wire1986,wire260543,wire375775,wire860688],
  [wire1986,wire260543,wire524288,wire860688],
  [wire1986,wire260543,wire860688,wire1721376],
  [wire1986,wire260543,wire860688,wire1721407]]
private def pool4_9 : List (List (List T)) := [chunk3_0, chunk3_1, chunk3_6, chunk3_7, chunk3_8]
private theorem checked4_9 : ∀ w ∈ chunk4_9, ¬ Need 4 w.toFinset := by
  have h : chunk4_9.all (routes 3 pool4_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_1 _ hm
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
  · exact checked3_8 _ hm
private def chunk4_10 : List (List T) := [[wire1986,wire260543,wire860688,wire1722338],
  [wire1986,wire260543,wire860688,wire1735844],
  [wire1986,wire260543,wire860688,wire1735871],
  [wire1986,wire260543,wire860688,wire1824040]]
private def pool4_10 : List (List (List T)) := [chunk3_8, chunk3_9]
private theorem checked4_10 : ∀ w ∈ chunk4_10, ¬ Need 4 w.toFinset := by
  have h : chunk4_10.all (routes 3 pool4_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_9 _ hm
private def chunk4_11 : List (List T) := [[wire1986,wire260543,wire860688,wire1824063],
  [wire1986,wire260543,wire860688,wire1834412],
  [wire1986,wire260543,wire860688,wire1834431],
  [wire1986,wire260543,wire1236463,wire1721376]]
private def pool4_11 : List (List (List T)) := [chunk3_1, chunk3_10, chunk3_11]
private theorem checked4_11 : ∀ w ∈ chunk4_11, ¬ Need 4 w.toFinset := by
  have h : chunk4_11.all (routes 3 pool4_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_1 _ hm
  · exact checked3_10 _ hm
  · exact checked3_11 _ hm
private def chunk4_12 : List (List T) := [[wire1986,wire260543,wire1721376,wire2057776],
  [wire1986,wire262143,wire860688,wire1721376],
  [wire1986,wire860688,wire1721376,wire1836608],
  [wire2047,wire30852,wire233736,wire336400]]
private def pool4_12 : List (List (List T)) := [chunk3_1, chunk3_2, chunk3_4, chunk3_7, chunk3_8, chunk3_12]
private theorem checked4_12 : ∀ w ∈ chunk4_12, ¬ Need 4 w.toFinset := by
  have h : chunk4_12.all (routes 3 pool4_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_1 _ hm
  · exact checked3_2 _ hm
  · exact checked3_4 _ hm
  · exact checked3_7 _ hm
  · exact checked3_8 _ hm
  · exact checked3_12 _ hm
private def chunk4_13 : List (List T) := [[wire2047,wire30852,wire233736,wire1760751],
  [wire2047,wire30852,wire758024,wire860688],
  [wire2047,wire233736,wire555140,wire860688],
  [wire2047,wire260492,wire375775,wire860688]]
private def pool4_13 : List (List (List T)) := [chunk3_1, chunk3_2, chunk3_4, chunk3_5, chunk3_6, chunk3_7]
private theorem checked4_13 : ∀ w ∈ chunk4_13, ¬ Need 4 w.toFinset := by
  have h : chunk4_13.all (routes 3 pool4_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_1 _ hm
  · exact checked3_2 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
private def chunk4_14 : List (List T) := [[wire2047,wire260492,wire524288,wire860688],
  [wire2047,wire260492,wire860688,wire1721376],
  [wire2047,wire260492,wire860688,wire1721407],
  [wire2047,wire260492,wire860688,wire1722338]]
private def pool4_14 : List (List (List T)) := [chunk3_2, chunk3_6, chunk3_7, chunk3_8]
private theorem checked4_14 : ∀ w ∈ chunk4_14, ¬ Need 4 w.toFinset := by
  have h : chunk4_14.all (routes 3 pool4_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
  · exact checked3_8 _ hm
private def chunk4_15 : List (List T) := [[wire2047,wire260492,wire860688,wire1722367],
  [wire2047,wire260492,wire860688,wire1735844],
  [wire2047,wire260492,wire860688,wire1824040],
  [wire2047,wire260492,wire860688,wire1834412]]
private def pool4_15 : List (List (List T)) := [chunk3_8, chunk3_9, chunk3_10]
private theorem checked4_15 : ∀ w ∈ chunk4_15, ¬ Need 4 w.toFinset := by
  have h : chunk4_15.all (routes 3 pool4_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_9 _ hm
  · exact checked3_10 _ hm
private def chunk4_16 : List (List T) := [[wire2047,wire260492,wire1236463,wire1721376],
  [wire2047,wire260492,wire1721376,wire2057776],
  [wire2047,wire260543,wire860688,wire1721376],
  [wire2047,wire262094,wire860688,wire1721376]]
private def pool4_16 : List (List (List T)) := [chunk3_1, chunk3_7, chunk3_11, chunk3_12]
private theorem checked4_16 : ∀ w ∈ chunk4_16, ¬ Need 4 w.toFinset := by
  have h : chunk4_16.all (routes 3 pool4_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_1 _ hm
  · exact checked3_7 _ hm
  · exact checked3_11 _ hm
  · exact checked3_12 _ hm
private def chunk4_17 : List (List T) := [[wire2047,wire262143,wire860688,wire1721376],
  [wire2047,wire860688,wire1721376,wire1836659],
  [wire30852,wire233736,wire526335,wire860688],
  [wire30852,wire233791,wire526274,wire860688]]
private def pool4_17 : List (List (List T)) := [chunk3_2, chunk3_5, chunk3_6, chunk3_7, chunk3_8]
private theorem checked4_17 : ∀ w ∈ chunk4_17, ¬ Need 4 w.toFinset := by
  have h : chunk4_17.all (routes 3 pool4_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
  · exact checked3_8 _ hm
private def chunk4_18 : List (List T) := [[wire30852,wire235466,wire524351,wire860688],
  [wire30852,wire235519,wire375775,wire860688],
  [wire30852,wire235519,wire524288,wire860688],
  [wire30852,wire235519,wire860688,wire1721376]]
private def pool4_18 : List (List (List T)) := [chunk3_2, chunk3_6, chunk3_7]
private theorem checked4_18 : ∀ w ∈ chunk4_18, ¬ Need 4 w.toFinset := by
  have h : chunk4_18.all (routes 3 pool4_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
private def chunk4_19 : List (List T) := [[wire30852,wire235519,wire860688,wire1721407],
  [wire30852,wire235519,wire860688,wire1722338],
  [wire30852,wire235519,wire860688,wire1722367],
  [wire30852,wire235519,wire860688,wire1735844]]
private def pool4_19 : List (List (List T)) := [chunk3_8]
private theorem checked4_19 : ∀ w ∈ chunk4_19, ¬ Need 4 w.toFinset := by
  have h : chunk4_19.all (routes 3 pool4_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_8 _ hm
private def chunk4_20 : List (List T) := [[wire30852,wire235519,wire860688,wire1824040],
  [wire30852,wire235519,wire860688,wire1824063],
  [wire30852,wire235519,wire860688,wire1824746],
  [wire30852,wire235519,wire860688,wire1824767]]
private def pool4_20 : List (List (List T)) := [chunk3_9, chunk3_10]
private theorem checked4_20 : ∀ w ∈ chunk4_20, ¬ Need 4 w.toFinset := by
  have h : chunk4_20.all (routes 3 pool4_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_9 _ hm
  · exact checked3_10 _ hm
private def chunk4_21 : List (List T) := [[wire30852,wire235519,wire1236463,wire1721376],
  [wire30852,wire235519,wire1721376,wire2057776],
  [wire30852,wire262143,wire860688,wire1721376],
  [wire30852,wire860688,wire1721376,wire1861632]]
private def pool4_21 : List (List (List T)) := [chunk3_2, chunk3_7, chunk3_8, chunk3_11, chunk3_12]
private theorem checked4_21 : ∀ w ∈ chunk4_21, ¬ Need 4 w.toFinset := by
  have h : chunk4_21.all (routes 3 pool4_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_7 _ hm
  · exact checked3_8 _ hm
  · exact checked3_11 _ hm
  · exact checked3_12 _ hm
private def chunk4_22 : List (List T) := [[wire30911,wire233736,wire526274,wire860688],
  [wire30911,wire235466,wire375775,wire860688],
  [wire30911,wire235466,wire524288,wire860688],
  [wire30911,wire235466,wire860688,wire1721376]]
private def pool4_22 : List (List (List T)) := [chunk3_3, chunk3_5, chunk3_6, chunk3_7]
private theorem checked4_22 : ∀ w ∈ chunk4_22, ¬ Need 4 w.toFinset := by
  have h : chunk4_22.all (routes 3 pool4_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_3 _ hm
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
private def chunk4_23 : List (List T) := [[wire30911,wire235466,wire860688,wire1721407],
  [wire30911,wire235466,wire860688,wire1722338],
  [wire30911,wire235466,wire860688,wire1735844],
  [wire30911,wire235466,wire860688,wire1735871]]
private def pool4_23 : List (List (List T)) := [chunk3_8, chunk3_9]
private theorem checked4_23 : ∀ w ∈ chunk4_23, ¬ Need 4 w.toFinset := by
  have h : chunk4_23.all (routes 3 pool4_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_9 _ hm
private def chunk4_24 : List (List T) := [[wire30911,wire235466,wire860688,wire1824040],
  [wire30911,wire235466,wire860688,wire1824746],
  [wire30911,wire235466,wire1236463,wire1721376],
  [wire30911,wire235466,wire1721376,wire2057776]]
private def pool4_24 : List (List (List T)) := [chunk3_3, chunk3_9, chunk3_10, chunk3_11, chunk3_12]
private theorem checked4_24 : ∀ w ∈ chunk4_24, ¬ Need 4 w.toFinset := by
  have h : chunk4_24.all (routes 3 pool4_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_3 _ hm
  · exact checked3_9 _ hm
  · exact checked3_10 _ hm
  · exact checked3_11 _ hm
  · exact checked3_12 _ hm
private def chunk4_25 : List (List T) := [[wire30911,wire235519,wire860688,wire1721376],
  [wire30911,wire262094,wire860688,wire1721376],
  [wire30911,wire262143,wire860688,wire1721376],
  [wire30911,wire860688,wire1721376,wire1861685]]
private def pool4_25 : List (List (List T)) := [chunk3_7, chunk3_9]
private theorem checked4_25 : ∀ w ∈ chunk4_25, ¬ Need 4 w.toFinset := by
  have h : chunk4_25.all (routes 3 pool4_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_9 _ hm
private def chunk4_26 : List (List T) := [[wire32710,wire233736,wire524351,wire860688],
  [wire32710,wire233791,wire375775,wire860688],
  [wire32710,wire233791,wire524288,wire860688],
  [wire32710,wire233791,wire860688,wire1721376]]
private def pool4_26 : List (List (List T)) := [chunk3_3, chunk3_4, chunk3_5, chunk3_7]
private theorem checked4_26 : ∀ w ∈ chunk4_26, ¬ Need 4 w.toFinset := by
  have h : chunk4_26.all (routes 3 pool4_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_3 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
  · exact checked3_7 _ hm
private def chunk4_27 : List (List T) := [[wire32710,wire233791,wire860688,wire1721407],
  [wire32710,wire233791,wire860688,wire1722338],
  [wire32710,wire233791,wire860688,wire1735844],
  [wire32710,wire233791,wire860688,wire1736678]]
private def pool4_27 : List (List (List T)) := [chunk3_8, chunk3_9]
private theorem checked4_27 : ∀ w ∈ chunk4_27, ¬ Need 4 w.toFinset := by
  have h : chunk4_27.all (routes 3 pool4_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_9 _ hm
private def chunk4_28 : List (List T) := [[wire32710,wire233791,wire860688,wire1824040],
  [wire32710,wire233791,wire860688,wire1824063],
  [wire32710,wire233791,wire1236463,wire1721376],
  [wire32710,wire233791,wire1721376,wire2057776]]
private def pool4_28 : List (List (List T)) := [chunk3_4, chunk3_9, chunk3_10, chunk3_11, chunk3_12]
private theorem checked4_28 : ∀ w ∈ chunk4_28, ¬ Need 4 w.toFinset := by
  have h : chunk4_28.all (routes 3 pool4_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_4 _ hm
  · exact checked3_9 _ hm
  · exact checked3_10 _ hm
  · exact checked3_11 _ hm
  · exact checked3_12 _ hm
private def chunk4_29 : List (List T) := [[wire32710,wire235519,wire860688,wire1721376],
  [wire32710,wire260543,wire860688,wire1721376],
  [wire32710,wire262143,wire860688,wire1721376],
  [wire32710,wire860688,wire1721376,wire1863360]]
private def pool4_29 : List (List (List T)) := [chunk3_7, chunk3_9]
private theorem checked4_29 : ∀ w ∈ chunk4_29, ¬ Need 4 w.toFinset := by
  have h : chunk4_29.all (routes 3 pool4_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_9 _ hm
private def chunk4_30 : List (List T) := [[wire32767,wire233736,wire375775,wire860688],
  [wire32767,wire233736,wire524288,wire860688],
  [wire32767,wire233736,wire860688,wire1721376],
  [wire32767,wire233736,wire860688,wire1721407]]
private def pool4_30 : List (List (List T)) := [chunk3_4, chunk3_5, chunk3_7, chunk3_8]
private theorem checked4_30 : ∀ w ∈ chunk4_30, ¬ Need 4 w.toFinset := by
  have h : chunk4_30.all (routes 3 pool4_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
  · exact checked3_7 _ hm
  · exact checked3_8 _ hm
private def chunk4_31 : List (List T) := [[wire32767,wire233736,wire860688,wire1722338],
  [wire32767,wire233736,wire860688,wire1722367],
  [wire32767,wire233736,wire860688,wire1735844],
  [wire32767,wire233736,wire860688,wire1735871]]
private def pool4_31 : List (List (List T)) := [chunk3_8, chunk3_9]
private theorem checked4_31 : ∀ w ∈ chunk4_31, ¬ Need 4 w.toFinset := by
  have h : chunk4_31.all (routes 3 pool4_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_9 _ hm
private def chunk4_32 : List (List T) := [[wire32767,wire233736,wire860688,wire1736678],
  [wire32767,wire233736,wire860688,wire1736703],
  [wire32767,wire233736,wire860688,wire1824040],
  [wire32767,wire233736,wire1236463,wire1721376]]
private def pool4_32 : List (List (List T)) := [chunk3_4, chunk3_9, chunk3_11]
private theorem checked4_32 : ∀ w ∈ chunk4_32, ¬ Need 4 w.toFinset := by
  have h : chunk4_32.all (routes 3 pool4_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_4 _ hm
  · exact checked3_9 _ hm
  · exact checked3_11 _ hm
private def chunk4_33 : List (List T) := [[wire32767,wire233736,wire1721376,wire2057776],
  [wire32767,wire233791,wire860688,wire1721376],
  [wire32767,wire235466,wire860688,wire1721376],
  [wire32767,wire235519,wire860688,wire1721376]]
private def pool4_33 : List (List (List T)) := [chunk3_7, chunk3_12]
private theorem checked4_33 : ∀ w ∈ chunk4_33, ¬ Need 4 w.toFinset := by
  have h : chunk4_33.all (routes 3 pool4_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_12 _ hm
private def chunk4_34 : List (List T) := [[wire32767,wire260492,wire860688,wire1721376],
  [wire32767,wire260543,wire860688,wire1721376],
  [wire32767,wire262094,wire860688,wire1721376],
  [wire32767,wire262143,wire860688,wire1721376]]
private def pool4_34 : List (List (List T)) := [chunk3_7, chunk3_9]
private theorem checked4_34 : ∀ w ∈ chunk4_34, ¬ Need 4 w.toFinset := by
  have h : chunk4_34.all (routes 3 pool4_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_9 _ hm
private def chunk4_35 : List (List T) := [[wire32767,wire860688,wire1721376,wire1863415],
  [wire233736,wire262143,wire860688,wire1721376],
  [wire233736,wire860688,wire1721376,wire2064384],
  [wire233791,wire262094,wire860688,wire1721376]]
private def pool4_35 : List (List (List T)) := [chunk3_7, chunk3_9]
private theorem checked4_35 : ∀ w ∈ chunk4_35, ¬ Need 4 w.toFinset := by
  have h : chunk4_35.all (routes 3 pool4_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_9 _ hm
private def chunk4_36 : List (List T) := [[wire233791,wire262143,wire860688,wire1721376],
  [wire233791,wire860688,wire1721376,wire2064441],
  [wire235466,wire260543,wire860688,wire1721376],
  [wire235466,wire262143,wire860688,wire1721376]]
private def pool4_36 : List (List (List T)) := [chunk3_7, chunk3_10]
private theorem checked4_36 : ∀ w ∈ chunk4_36, ¬ Need 4 w.toFinset := by
  have h : chunk4_36.all (routes 3 pool4_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_36,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_10 _ hm
private def chunk4_37 : List (List T) := [[wire235466,wire860688,wire1721376,wire2066240],
  [wire235519,wire260492,wire860688,wire1721376],
  [wire235519,wire260543,wire860688,wire1721376],
  [wire235519,wire262094,wire860688,wire1721376]]
private def pool4_37 : List (List (List T)) := [chunk3_7]
private theorem checked4_37 : ∀ w ∈ chunk4_37, ¬ Need 4 w.toFinset := by
  have h : chunk4_37.all (routes 3 pool4_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_7 _ hm
private def chunk4_38 : List (List T) := [[wire235519,wire262143,wire860688,wire1721376],
  [wire235519,wire860688,wire1721376,wire2066299],
  [wire260492,wire262143,wire860688,wire1721376],
  [wire260492,wire860688,wire1721376,wire2095104]]
private def pool4_38 : List (List (List T)) := [chunk3_7, chunk3_10]
private theorem checked4_38 : ∀ w ∈ chunk4_38, ¬ Need 4 w.toFinset := by
  have h : chunk4_38.all (routes 3 pool4_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_38,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_10 _ hm
private def chunk4_39 : List (List T) := [[wire260543,wire262094,wire860688,wire1721376],
  [wire260543,wire262143,wire860688,wire1721376],
  [wire260543,wire860688,wire1721376,wire2095165],
  [wire262094,wire262143,wire860688,wire1721376]]
private def pool4_39 : List (List (List T)) := [chunk3_7, chunk3_11]
private theorem checked4_39 : ∀ w ∈ chunk4_39, ¬ Need 4 w.toFinset := by
  have h : chunk4_39.all (routes 3 pool4_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_11 _ hm
private def chunk4_40 : List (List T) := [[wire262094,wire860688,wire1721376,wire2097088],
  [wire262143,wire860688,wire1721376]]
private def pool4_40 : List (List (List T)) := [chunk3_5, chunk3_7, chunk3_11, chunk3_12]
private theorem checked4_40 : ∀ w ∈ chunk4_40, ¬ Need 4 w.toFinset := by
  have h : chunk4_40.all (routes 3 pool4_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_40,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_5 _ hm
  · exact checked3_7 _ hm
  · exact checked3_11 _ hm
  · exact checked3_12 _ hm
#print axioms checked4_40
private def chunk5_0 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire336400],
  [wire63,wire1986,wire30852,wire233736,wire1760751],
  [wire63,wire1986,wire30852,wire758024,wire860688],
  [wire63,wire1986,wire233736,wire555140,wire860688]]
private def pool5_0 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_2, chunk4_6, chunk4_7, chunk4_8, chunk4_12, chunk4_13]
private theorem checked5_0 : ∀ w ∈ chunk5_0, ¬ Need 5 w.toFinset := by
  have h : chunk5_0.all (routes 4 pool5_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
private def chunk5_1 : List (List T) := [[wire63,wire1986,wire260492,wire375775,wire860688],
  [wire63,wire1986,wire260492,wire524288,wire860688],
  [wire63,wire1986,wire260492,wire860688,wire1721376],
  [wire63,wire1986,wire260492,wire860688,wire1721407]]
private def pool5_1 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_3, chunk4_8, chunk4_9, chunk4_13, chunk4_14]
private theorem checked5_1 : ∀ w ∈ chunk5_1, ¬ Need 5 w.toFinset := by
  have h : chunk5_1.all (routes 4 pool5_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
private def chunk5_2 : List (List T) := [[wire63,wire1986,wire260492,wire860688,wire1722338],
  [wire63,wire1986,wire260492,wire860688,wire1735844],
  [wire63,wire1986,wire260492,wire860688,wire1824040],
  [wire63,wire1986,wire260492,wire860688,wire1834412]]
private def pool5_2 : List (List (List T)) := [chunk4_4, chunk4_5, chunk4_10, chunk4_11, chunk4_14, chunk4_15]
private theorem checked5_2 : ∀ w ∈ chunk5_2, ¬ Need 5 w.toFinset := by
  have h : chunk5_2.all (routes 4 pool5_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
private def chunk5_3 : List (List T) := [[wire63,wire1986,wire260492,wire1236463,wire1721376],
  [wire63,wire1986,wire260492,wire1721376,wire2057776],
  [wire63,wire1986,wire260543,wire860688,wire1721376],
  [wire63,wire1986,wire262094,wire860688,wire1721376]]
private def pool5_3 : List (List (List T)) := [chunk4_0, chunk4_3, chunk4_4, chunk4_5, chunk4_6, chunk4_9, chunk4_11, chunk4_12, chunk4_16]
private theorem checked5_3 : ∀ w ∈ chunk5_3, ¬ Need 5 w.toFinset := by
  have h : chunk5_3.all (routes 4 pool5_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_9 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_16 _ hm
private def chunk5_4 : List (List T) := [[wire63,wire1986,wire860688,wire1721376,wire1836659],
  [wire63,wire2047,wire260492,wire860688,wire1721376],
  [wire63,wire30852,wire233736,wire526274,wire860688],
  [wire63,wire30852,wire235466,wire375775,wire860688]]
private def pool5_4 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_2, chunk4_3, chunk4_6, chunk4_14, chunk4_16, chunk4_17, chunk4_18, chunk4_22]
private theorem checked5_4 : ∀ w ∈ chunk5_4, ¬ Need 5 w.toFinset := by
  have h : chunk5_4.all (routes 4 pool5_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_6 _ hm
  · exact checked4_14 _ hm
  · exact checked4_16 _ hm
  · exact checked4_17 _ hm
  · exact checked4_18 _ hm
  · exact checked4_22 _ hm
private def chunk5_5 : List (List T) := [[wire63,wire30852,wire235466,wire524288,wire860688],
  [wire63,wire30852,wire235466,wire860688,wire1721376],
  [wire63,wire30852,wire235466,wire860688,wire1721407],
  [wire63,wire30852,wire235466,wire860688,wire1722338]]
private def pool5_5 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_3, chunk4_4, chunk4_18, chunk4_19, chunk4_22, chunk4_23]
private theorem checked5_5 : ∀ w ∈ chunk5_5, ¬ Need 5 w.toFinset := by
  have h : chunk5_5.all (routes 4 pool5_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
  · exact checked4_22 _ hm
  · exact checked4_23 _ hm
private def chunk5_6 : List (List T) := [[wire63,wire30852,wire235466,wire860688,wire1735844],
  [wire63,wire30852,wire235466,wire860688,wire1824040],
  [wire63,wire30852,wire235466,wire860688,wire1824746],
  [wire63,wire30852,wire235466,wire1236463,wire1721376]]
private def pool5_6 : List (List (List T)) := [chunk4_1, chunk4_4, chunk4_5, chunk4_19, chunk4_20, chunk4_21, chunk4_23, chunk4_24]
private theorem checked5_6 : ∀ w ∈ chunk5_6, ¬ Need 5 w.toFinset := by
  have h : chunk5_6.all (routes 4 pool5_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_19 _ hm
  · exact checked4_20 _ hm
  · exact checked4_21 _ hm
  · exact checked4_23 _ hm
  · exact checked4_24 _ hm
private def chunk5_7 : List (List T) := [[wire63,wire30852,wire235466,wire1721376,wire2057776],
  [wire63,wire30852,wire235519,wire860688,wire1721376],
  [wire63,wire30852,wire262094,wire860688,wire1721376],
  [wire63,wire30852,wire860688,wire1721376,wire1861685]]
private def pool5_7 : List (List (List T)) := [chunk4_3, chunk4_4, chunk4_6, chunk4_18, chunk4_19, chunk4_21, chunk4_24, chunk4_25]
private theorem checked5_7 : ∀ w ∈ chunk5_7, ¬ Need 5 w.toFinset := by
  have h : chunk5_7.all (routes 4 pool5_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_6 _ hm
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
  · exact checked4_21 _ hm
  · exact checked4_24 _ hm
  · exact checked4_25 _ hm
private def chunk5_8 : List (List T) := [[wire63,wire30911,wire235466,wire860688,wire1721376],
  [wire63,wire32710,wire233736,wire375775,wire860688],
  [wire63,wire32710,wire233736,wire524288,wire860688],
  [wire63,wire32710,wire233736,wire860688,wire1721376]]
private def pool5_8 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_3, chunk4_6, chunk4_22, chunk4_23, chunk4_25, chunk4_26, chunk4_30]
private theorem checked5_8 : ∀ w ∈ chunk5_8, ¬ Need 5 w.toFinset := by
  have h : chunk5_8.all (routes 4 pool5_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_6 _ hm
  · exact checked4_22 _ hm
  · exact checked4_23 _ hm
  · exact checked4_25 _ hm
  · exact checked4_26 _ hm
  · exact checked4_30 _ hm
private def chunk5_9 : List (List T) := [[wire63,wire32710,wire233736,wire860688,wire1721407],
  [wire63,wire32710,wire233736,wire860688,wire1722338],
  [wire63,wire32710,wire233736,wire860688,wire1735844],
  [wire63,wire32710,wire233736,wire860688,wire1736678]]
private def pool5_9 : List (List (List T)) := [chunk4_3, chunk4_4, chunk4_27, chunk4_30, chunk4_31, chunk4_32]
private theorem checked5_9 : ∀ w ∈ chunk5_9, ¬ Need 5 w.toFinset := by
  have h : chunk5_9.all (routes 4 pool5_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_27 _ hm
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
  · exact checked4_32 _ hm
private def chunk5_10 : List (List T) := [[wire63,wire32710,wire233736,wire860688,wire1824040],
  [wire63,wire32710,wire233736,wire1236463,wire1721376],
  [wire63,wire32710,wire233736,wire1721376,wire2057776],
  [wire63,wire32710,wire233791,wire860688,wire1721376]]
private def pool5_10 : List (List (List T)) := [chunk4_1, chunk4_4, chunk4_5, chunk4_6, chunk4_26, chunk4_27, chunk4_28, chunk4_32, chunk4_33]
private theorem checked5_10 : ∀ w ∈ chunk5_10, ¬ Need 5 w.toFinset := by
  have h : chunk5_10.all (routes 4 pool5_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_26 _ hm
  · exact checked4_27 _ hm
  · exact checked4_28 _ hm
  · exact checked4_32 _ hm
  · exact checked4_33 _ hm
private def chunk5_11 : List (List T) := [[wire63,wire32710,wire235466,wire860688,wire1721376],
  [wire63,wire32710,wire260492,wire860688,wire1721376],
  [wire63,wire32710,wire262094,wire860688,wire1721376],
  [wire63,wire32710,wire860688,wire1721376,wire1863415]]
private def pool5_11 : List (List (List T)) := [chunk4_3, chunk4_4, chunk4_29, chunk4_33, chunk4_34, chunk4_35]
private theorem checked5_11 : ∀ w ∈ chunk5_11, ¬ Need 5 w.toFinset := by
  have h : chunk5_11.all (routes 4 pool5_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_29 _ hm
  · exact checked4_33 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
private def chunk5_12 : List (List T) := [[wire63,wire32767,wire233736,wire860688,wire1721376],
  [wire63,wire233736,wire262094,wire860688,wire1721376],
  [wire63,wire233736,wire860688,wire1721376,wire2064441],
  [wire63,wire235466,wire260492,wire860688,wire1721376]]
private def pool5_12 : List (List (List T)) := [chunk4_3, chunk4_4, chunk4_6, chunk4_30, chunk4_33, chunk4_35, chunk4_36, chunk4_37]
private theorem checked5_12 : ∀ w ∈ chunk5_12, ¬ Need 5 w.toFinset := by
  have h : chunk5_12.all (routes 4 pool5_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_6 _ hm
  · exact checked4_30 _ hm
  · exact checked4_33 _ hm
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
private def chunk5_13 : List (List T) := [[wire63,wire235466,wire262094,wire860688,wire1721376],
  [wire63,wire235466,wire860688,wire1721376,wire2066299],
  [wire63,wire260492,wire262094,wire860688,wire1721376],
  [wire63,wire260492,wire860688,wire1721376,wire2095165]]
private def pool5_13 : List (List (List T)) := [chunk4_3, chunk4_5, chunk4_36, chunk4_37, chunk4_38, chunk4_39]
private theorem checked5_13 : ∀ w ∈ chunk5_13, ¬ Need 5 w.toFinset := by
  have h : chunk5_13.all (routes 4 pool5_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_5 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
  · exact checked4_38 _ hm
  · exact checked4_39 _ hm
private def chunk5_14 : List (List T) := [[wire63,wire262094,wire860688,wire1721376],
  [wire1986,wire2047,wire260492,wire860688,wire1721376],
  [wire1986,wire30852,wire233736,wire524351,wire860688],
  [wire1986,wire30852,wire233791,wire375775,wire860688]]
private def pool5_14 : List (List (List T)) := [chunk4_3, chunk4_5, chunk4_6, chunk4_7, chunk4_8, chunk4_9, chunk4_12, chunk4_14, chunk4_16, chunk4_17, chunk4_18, chunk4_26, chunk4_39, chunk4_40]
private theorem checked5_14 : ∀ w ∈ chunk5_14, ¬ Need 5 w.toFinset := by
  have h : chunk5_14.all (routes 4 pool5_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_5 _ hm
  · exact checked4_6 _ hm
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_12 _ hm
  · exact checked4_14 _ hm
  · exact checked4_16 _ hm
  · exact checked4_17 _ hm
  · exact checked4_18 _ hm
  · exact checked4_26 _ hm
  · exact checked4_39 _ hm
  · exact checked4_40 _ hm
private def chunk5_15 : List (List T) := [[wire1986,wire30852,wire233791,wire524288,wire860688],
  [wire1986,wire30852,wire233791,wire860688,wire1721376],
  [wire1986,wire30852,wire233791,wire860688,wire1721407],
  [wire1986,wire30852,wire233791,wire860688,wire1722338]]
private def pool5_15 : List (List (List T)) := [chunk4_7, chunk4_8, chunk4_9, chunk4_10, chunk4_17, chunk4_18, chunk4_19, chunk4_26, chunk4_27]
private theorem checked5_15 : ∀ w ∈ chunk5_15, ¬ Need 5 w.toFinset := by
  have h : chunk5_15.all (routes 4 pool5_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_17 _ hm
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
  · exact checked4_26 _ hm
  · exact checked4_27 _ hm
private def chunk5_16 : List (List T) := [[wire1986,wire30852,wire233791,wire860688,wire1735844],
  [wire1986,wire30852,wire233791,wire860688,wire1824040],
  [wire1986,wire30852,wire233791,wire860688,wire1824063],
  [wire1986,wire30852,wire233791,wire1236463,wire1721376]]
private def pool5_16 : List (List (List T)) := [chunk4_7, chunk4_10, chunk4_11, chunk4_19, chunk4_20, chunk4_21, chunk4_27, chunk4_28]
private theorem checked5_16 : ∀ w ∈ chunk5_16, ¬ Need 5 w.toFinset := by
  have h : chunk5_16.all (routes 4 pool5_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_19 _ hm
  · exact checked4_20 _ hm
  · exact checked4_21 _ hm
  · exact checked4_27 _ hm
  · exact checked4_28 _ hm
private def chunk5_17 : List (List T) := [[wire1986,wire30852,wire233791,wire1721376,wire2057776],
  [wire1986,wire30852,wire235519,wire860688,wire1721376],
  [wire1986,wire30852,wire260543,wire860688,wire1721376],
  [wire1986,wire30852,wire860688,wire1721376,wire1863360]]
private def pool5_17 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_12, chunk4_18, chunk4_19, chunk4_21, chunk4_28, chunk4_29]
private theorem checked5_17 : ∀ w ∈ chunk5_17, ¬ Need 5 w.toFinset := by
  have h : chunk5_17.all (routes 4 pool5_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
  · exact checked4_21 _ hm
  · exact checked4_28 _ hm
  · exact checked4_29 _ hm
private def chunk5_18 : List (List T) := [[wire1986,wire30911,wire233736,wire375775,wire860688],
  [wire1986,wire30911,wire233736,wire524288,wire860688],
  [wire1986,wire30911,wire233736,wire860688,wire1721376],
  [wire1986,wire30911,wire233736,wire860688,wire1721407]]
private def pool5_18 : List (List (List T)) := [chunk4_7, chunk4_8, chunk4_9, chunk4_22, chunk4_23, chunk4_30]
private theorem checked5_18 : ∀ w ∈ chunk5_18, ¬ Need 5 w.toFinset := by
  have h : chunk5_18.all (routes 4 pool5_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_9 _ hm
  · exact checked4_22 _ hm
  · exact checked4_23 _ hm
  · exact checked4_30 _ hm
private def chunk5_19 : List (List T) := [[wire1986,wire30911,wire233736,wire860688,wire1722338],
  [wire1986,wire30911,wire233736,wire860688,wire1735844],
  [wire1986,wire30911,wire233736,wire860688,wire1735871],
  [wire1986,wire30911,wire233736,wire860688,wire1824040]]
private def pool5_19 : List (List (List T)) := [chunk4_10, chunk4_23, chunk4_24, chunk4_31, chunk4_32]
private theorem checked5_19 : ∀ w ∈ chunk5_19, ¬ Need 5 w.toFinset := by
  have h : chunk5_19.all (routes 4 pool5_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_23 _ hm
  · exact checked4_24 _ hm
  · exact checked4_31 _ hm
  · exact checked4_32 _ hm
private def chunk5_20 : List (List T) := [[wire1986,wire30911,wire233736,wire1236463,wire1721376],
  [wire1986,wire30911,wire233736,wire1721376,wire2057776],
  [wire1986,wire30911,wire233791,wire860688,wire1721376],
  [wire1986,wire30911,wire235466,wire860688,wire1721376]]
private def pool5_20 : List (List (List T)) := [chunk4_7, chunk4_9, chunk4_11, chunk4_12, chunk4_22, chunk4_23, chunk4_24, chunk4_25, chunk4_32, chunk4_33]
private theorem checked5_20 : ∀ w ∈ chunk5_20, ¬ Need 5 w.toFinset := by
  have h : chunk5_20.all (routes 4 pool5_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_9 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_22 _ hm
  · exact checked4_23 _ hm
  · exact checked4_24 _ hm
  · exact checked4_25 _ hm
  · exact checked4_32 _ hm
  · exact checked4_33 _ hm
private def chunk5_21 : List (List T) := [[wire1986,wire30911,wire260492,wire860688,wire1721376],
  [wire1986,wire30911,wire260543,wire860688,wire1721376],
  [wire1986,wire30911,wire860688,wire1721376,wire1863415],
  [wire1986,wire32710,wire233791,wire860688,wire1721376]]
private def pool5_21 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_12, chunk4_25, chunk4_26, chunk4_27, chunk4_29, chunk4_34, chunk4_35]
private theorem checked5_21 : ∀ w ∈ chunk5_21, ¬ Need 5 w.toFinset := by
  have h : chunk5_21.all (routes 4 pool5_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
  · exact checked4_25 _ hm
  · exact checked4_26 _ hm
  · exact checked4_27 _ hm
  · exact checked4_29 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
private def chunk5_22 : List (List T) := [[wire1986,wire32767,wire233736,wire860688,wire1721376],
  [wire1986,wire233736,wire260543,wire860688,wire1721376],
  [wire1986,wire233736,wire860688,wire1721376,wire2066240],
  [wire1986,wire233791,wire260492,wire860688,wire1721376]]
private def pool5_22 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_12, chunk4_30, chunk4_31, chunk4_33, chunk4_35, chunk4_36, chunk4_37]
private theorem checked5_22 : ∀ w ∈ chunk5_22, ¬ Need 5 w.toFinset := by
  have h : chunk5_22.all (routes 4 pool5_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_12 _ hm
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
  · exact checked4_33 _ hm
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
private def chunk5_23 : List (List T) := [[wire1986,wire233791,wire260543,wire860688,wire1721376],
  [wire1986,wire233791,wire860688,wire1721376,wire2066299],
  [wire1986,wire260492,wire260543,wire860688,wire1721376],
  [wire1986,wire260492,wire860688,wire1721376,wire2097088]]
private def pool5_23 : List (List (List T)) := [chunk4_9, chunk4_11, chunk4_36, chunk4_37, chunk4_38, chunk4_39, chunk4_40]
private theorem checked5_23 : ∀ w ∈ chunk5_23, ¬ Need 5 w.toFinset := by
  have h : chunk5_23.all (routes 4 pool5_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_11 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
  · exact checked4_38 _ hm
  · exact checked4_39 _ hm
  · exact checked4_40 _ hm
private def chunk5_24 : List (List T) := [[wire1986,wire260543,wire860688,wire1721376],
  [wire2047,wire30852,wire233736,wire375775,wire860688],
  [wire2047,wire30852,wire233736,wire524288,wire860688],
  [wire2047,wire30852,wire233736,wire860688,wire1721376]]
private def pool5_24 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_11, chunk4_12, chunk4_13, chunk4_14, chunk4_17, chunk4_18, chunk4_30, chunk4_39, chunk4_40]
private theorem checked5_24 : ∀ w ∈ chunk5_24, ¬ Need 5 w.toFinset := by
  have h : chunk5_24.all (routes 4 pool5_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
  · exact checked4_17 _ hm
  · exact checked4_18 _ hm
  · exact checked4_30 _ hm
  · exact checked4_39 _ hm
  · exact checked4_40 _ hm
private def chunk5_25 : List (List T) := [[wire2047,wire30852,wire233736,wire860688,wire1721407],
  [wire2047,wire30852,wire233736,wire860688,wire1722338],
  [wire2047,wire30852,wire233736,wire860688,wire1722367],
  [wire2047,wire30852,wire233736,wire860688,wire1735844]]
private def pool5_25 : List (List (List T)) := [chunk4_14, chunk4_15, chunk4_19, chunk4_30, chunk4_31]
private theorem checked5_25 : ∀ w ∈ chunk5_25, ¬ Need 5 w.toFinset := by
  have h : chunk5_25.all (routes 4 pool5_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
  · exact checked4_19 _ hm
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
private def chunk5_26 : List (List T) := [[wire2047,wire30852,wire233736,wire860688,wire1824040],
  [wire2047,wire30852,wire233736,wire1236463,wire1721376],
  [wire2047,wire30852,wire233736,wire1721376,wire2057776],
  [wire2047,wire30852,wire233791,wire860688,wire1721376]]
private def pool5_26 : List (List (List T)) := [chunk4_13, chunk4_15, chunk4_16, chunk4_18, chunk4_20, chunk4_21, chunk4_32, chunk4_33]
private theorem checked5_26 : ∀ w ∈ chunk5_26, ¬ Need 5 w.toFinset := by
  have h : chunk5_26.all (routes 4 pool5_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
  · exact checked4_18 _ hm
  · exact checked4_20 _ hm
  · exact checked4_21 _ hm
  · exact checked4_32 _ hm
  · exact checked4_33 _ hm
private def chunk5_27 : List (List T) := [[wire2047,wire30852,wire235466,wire860688,wire1721376],
  [wire2047,wire30852,wire235519,wire860688,wire1721376],
  [wire2047,wire30852,wire260492,wire860688,wire1721376],
  [wire2047,wire30852,wire860688,wire1721376,wire1863415]]
private def pool5_27 : List (List (List T)) := [chunk4_14, chunk4_15, chunk4_16, chunk4_17, chunk4_18, chunk4_19, chunk4_21, chunk4_33, chunk4_34, chunk4_35]
private theorem checked5_27 : ∀ w ∈ chunk5_27, ¬ Need 5 w.toFinset := by
  have h : chunk5_27.all (routes 4 pool5_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
  · exact checked4_17 _ hm
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
  · exact checked4_21 _ hm
  · exact checked4_33 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
private def chunk5_28 : List (List T) := [[wire2047,wire30911,wire233736,wire860688,wire1721376],
  [wire2047,wire32710,wire233736,wire860688,wire1721376],
  [wire2047,wire32767,wire233736,wire860688,wire1721376],
  [wire2047,wire233736,wire260492,wire860688,wire1721376]]
private def pool5_28 : List (List (List T)) := [chunk4_14, chunk4_15, chunk4_16, chunk4_17, chunk4_25, chunk4_29, chunk4_30, chunk4_31, chunk4_33, chunk4_35, chunk4_37]
private theorem checked5_28 : ∀ w ∈ chunk5_28, ¬ Need 5 w.toFinset := by
  have h : chunk5_28.all (routes 4 pool5_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
  · exact checked4_17 _ hm
  · exact checked4_25 _ hm
  · exact checked4_29 _ hm
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
  · exact checked4_33 _ hm
  · exact checked4_35 _ hm
  · exact checked4_37 _ hm
private def chunk5_29 : List (List T) := [[wire2047,wire233736,wire860688,wire1721376,wire2066299],
  [wire2047,wire260492,wire860688,wire1721376],
  [wire30852,wire30911,wire235466,wire860688,wire1721376],
  [wire30852,wire32710,wire233791,wire860688,wire1721376]]
private def pool5_29 : List (List (List T)) := [chunk4_13, chunk4_14, chunk4_15, chunk4_16, chunk4_17, chunk4_21, chunk4_22, chunk4_23, chunk4_25, chunk4_26, chunk4_27, chunk4_29, chunk4_38, chunk4_40]
private theorem checked5_29 : ∀ w ∈ chunk5_29, ¬ Need 5 w.toFinset := by
  have h : chunk5_29.all (routes 4 pool5_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
  · exact checked4_17 _ hm
  · exact checked4_21 _ hm
  · exact checked4_22 _ hm
  · exact checked4_23 _ hm
  · exact checked4_25 _ hm
  · exact checked4_26 _ hm
  · exact checked4_27 _ hm
  · exact checked4_29 _ hm
  · exact checked4_38 _ hm
  · exact checked4_40 _ hm
private def chunk5_30 : List (List T) := [[wire30852,wire32767,wire233736,wire860688,wire1721376],
  [wire30852,wire233736,wire235519,wire860688,wire1721376],
  [wire30852,wire233736,wire860688,wire1721376,wire2095104],
  [wire30852,wire233791,wire235466,wire860688,wire1721376]]
private def pool5_30 : List (List (List T)) := [chunk4_18, chunk4_20, chunk4_21, chunk4_30, chunk4_31, chunk4_34, chunk4_35, chunk4_36, chunk4_37, chunk4_38]
private theorem checked5_30 : ∀ w ∈ chunk5_30, ¬ Need 5 w.toFinset := by
  have h : chunk5_30.all (routes 4 pool5_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_18 _ hm
  · exact checked4_20 _ hm
  · exact checked4_21 _ hm
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
  · exact checked4_38 _ hm
private def chunk5_31 : List (List T) := [[wire30852,wire233791,wire235519,wire860688,wire1721376],
  [wire30852,wire233791,wire860688,wire1721376,wire2095165],
  [wire30852,wire235466,wire235519,wire860688,wire1721376],
  [wire30852,wire235466,wire860688,wire1721376,wire2097088]]
private def pool5_31 : List (List (List T)) := [chunk4_18, chunk4_20, chunk4_36, chunk4_37, chunk4_39, chunk4_40]
private theorem checked5_31 : ∀ w ∈ chunk5_31, ¬ Need 5 w.toFinset := by
  have h : chunk5_31.all (routes 4 pool5_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_18 _ hm
  · exact checked4_20 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
  · exact checked4_39 _ hm
  · exact checked4_40 _ hm
private def chunk5_32 : List (List T) := [[wire30852,wire235519,wire860688,wire1721376],
  [wire30911,wire32710,wire233736,wire860688,wire1721376],
  [wire30911,wire32767,wire233736,wire860688,wire1721376],
  [wire30911,wire233736,wire235466,wire860688,wire1721376]]
private def pool5_32 : List (List (List T)) := [chunk4_18, chunk4_19, chunk4_20, chunk4_21, chunk4_22, chunk4_24, chunk4_25, chunk4_29, chunk4_30, chunk4_31, chunk4_34, chunk4_35, chunk4_36, chunk4_38, chunk4_40]
private theorem checked5_32 : ∀ w ∈ chunk5_32, ¬ Need 5 w.toFinset := by
  have h : chunk5_32.all (routes 4 pool5_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
  · exact checked4_20 _ hm
  · exact checked4_21 _ hm
  · exact checked4_22 _ hm
  · exact checked4_24 _ hm
  · exact checked4_25 _ hm
  · exact checked4_29 _ hm
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_38 _ hm
  · exact checked4_40 _ hm
private def chunk5_33 : List (List T) := [[wire30911,wire233736,wire860688,wire1721376,wire2095165],
  [wire30911,wire235466,wire860688,wire1721376],
  [wire32710,wire32767,wire233736,wire860688,wire1721376],
  [wire32710,wire233736,wire233791,wire860688,wire1721376]]
private def pool5_33 : List (List (List T)) := [chunk4_22, chunk4_23, chunk4_24, chunk4_25, chunk4_26, chunk4_28, chunk4_29, chunk4_30, chunk4_32, chunk4_34, chunk4_35, chunk4_36, chunk4_37, chunk4_39, chunk4_40]
private theorem checked5_33 : ∀ w ∈ chunk5_33, ¬ Need 5 w.toFinset := by
  have h : chunk5_33.all (routes 4 pool5_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_22 _ hm
  · exact checked4_23 _ hm
  · exact checked4_24 _ hm
  · exact checked4_25 _ hm
  · exact checked4_26 _ hm
  · exact checked4_28 _ hm
  · exact checked4_29 _ hm
  · exact checked4_30 _ hm
  · exact checked4_32 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
  · exact checked4_39 _ hm
  · exact checked4_40 _ hm
private def chunk5_34 : List (List T) := [[wire32710,wire233736,wire860688,wire1721376,wire2097088],
  [wire32710,wire233791,wire860688,wire1721376],
  [wire32767,wire233736,wire860688,wire1721376]]
private def pool5_34 : List (List (List T)) := [chunk4_26, chunk4_27, chunk4_28, chunk4_29, chunk4_30, chunk4_32, chunk4_33, chunk4_34, chunk4_35, chunk4_36, chunk4_40]
private theorem checked5_34 : ∀ w ∈ chunk5_34, ¬ Need 5 w.toFinset := by
  have h : chunk5_34.all (routes 4 pool5_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_26 _ hm
  · exact checked4_27 _ hm
  · exact checked4_28 _ hm
  · exact checked4_29 _ hm
  · exact checked4_30 _ hm
  · exact checked4_32 _ hm
  · exact checked4_33 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_40 _ hm
#print axioms checked5_34
private def chunk6_0 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire375775,wire860688],
  [wire63,wire1986,wire30852,wire233736,wire524288,wire860688],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1721407]]
private def pool6_0 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_4, chunk5_5, chunk5_8, chunk5_9, chunk5_14, chunk5_15, chunk5_18, chunk5_24, chunk5_25]
private theorem checked6_0 : ∀ w ∈ chunk6_0, ¬ Need 6 w.toFinset := by
  have h : chunk6_0.all (routes 5 pool6_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_4 _ hm
  · exact checked5_5 _ hm
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_18 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
private def chunk6_1 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1722338],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1735844],
  [wire63,wire1986,wire30852,wire233736,wire860688,wire1824040],
  [wire63,wire1986,wire30852,wire233736,wire1236463,wire1721376]]
private def pool6_1 : List (List (List T)) := [chunk5_0, chunk5_2, chunk5_3, chunk5_5, chunk5_6, chunk5_9, chunk5_10, chunk5_15, chunk5_16, chunk5_19, chunk5_20, chunk5_25, chunk5_26]
private theorem checked6_1 : ∀ w ∈ chunk6_1, ¬ Need 6 w.toFinset := by
  have h : chunk6_1.all (routes 5 pool6_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_25 _ hm
  · exact checked5_26 _ hm
private def chunk6_2 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire1721376,wire2057776],
  [wire63,wire1986,wire30852,wire233791,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire235466,wire860688,wire1721376],
  [wire63,wire1986,wire30852,wire260492,wire860688,wire1721376]]
private def pool6_2 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_3, chunk5_5, chunk5_7, chunk5_10, chunk5_11, chunk5_15, chunk5_17, chunk5_20, chunk5_21, chunk5_26, chunk5_27]
private theorem checked6_2 : ∀ w ∈ chunk6_2, ¬ Need 6 w.toFinset := by
  have h : chunk6_2.all (routes 5 pool6_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_5 _ hm
  · exact checked5_7 _ hm
  · exact checked5_10 _ hm
  · exact checked5_11 _ hm
  · exact checked5_15 _ hm
  · exact checked5_17 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
private def chunk6_3 : List (List T) := [[wire63,wire1986,wire30852,wire860688,wire1721376,wire1863415],
  [wire63,wire1986,wire30911,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire32710,wire233736,wire860688,wire1721376],
  [wire63,wire1986,wire233736,wire260492,wire860688,wire1721376]]
private def pool6_3 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_3, chunk5_8, chunk5_9, chunk5_11, chunk5_12, chunk5_18, chunk5_20, chunk5_21, chunk5_22, chunk5_27, chunk5_28]
private theorem checked6_3 : ∀ w ∈ chunk6_3, ¬ Need 6 w.toFinset := by
  have h : chunk6_3.all (routes 5 pool6_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_18 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
private def chunk6_4 : List (List T) := [[wire63,wire1986,wire233736,wire860688,wire1721376,wire2066299],
  [wire63,wire1986,wire260492,wire860688,wire1721376],
  [wire63,wire2047,wire30852,wire233736,wire860688,wire1721376],
  [wire63,wire30852,wire32710,wire233736,wire860688,wire1721376]]
private def pool6_4 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_3, chunk5_4, chunk5_7, chunk5_8, chunk5_9, chunk5_11, chunk5_12, chunk5_13, chunk5_14, chunk5_23, chunk5_24, chunk5_25, chunk5_26, chunk5_28, chunk5_29, chunk5_30, chunk5_32]
private theorem checked6_4 : ∀ w ∈ chunk6_4, ¬ Need 6 w.toFinset := by
  have h : chunk6_4.all (routes 5 pool6_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_26 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_32 _ hm
private def chunk6_5 : List (List T) := [[wire63,wire30852,wire233736,wire235466,wire860688,wire1721376],
  [wire63,wire30852,wire233736,wire860688,wire1721376,wire2095165],
  [wire63,wire30852,wire235466,wire860688,wire1721376],
  [wire63,wire32710,wire233736,wire860688,wire1721376]]
private def pool6_5 : List (List (List T)) := [chunk5_4, chunk5_5, chunk5_6, chunk5_7, chunk5_8, chunk5_9, chunk5_10, chunk5_11, chunk5_12, chunk5_13, chunk5_14, chunk5_29, chunk5_30, chunk5_31, chunk5_32, chunk5_33, chunk5_34]
private theorem checked6_5 : ∀ w ∈ chunk6_5, ¬ Need 6 w.toFinset := by
  have h : chunk6_5.all (routes 5 pool6_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
private def chunk6_6 : List (List T) := [[wire1986,wire2047,wire30852,wire233736,wire860688,wire1721376],
  [wire1986,wire30852,wire30911,wire233736,wire860688,wire1721376],
  [wire1986,wire30852,wire233736,wire233791,wire860688,wire1721376],
  [wire1986,wire30852,wire233736,wire860688,wire1721376,wire2097088]]
private def pool6_6 : List (List (List T)) := [chunk5_14, chunk5_15, chunk5_16, chunk5_17, chunk5_18, chunk5_19, chunk5_21, chunk5_22, chunk5_23, chunk5_24, chunk5_25, chunk5_27, chunk5_28, chunk5_29, chunk5_30, chunk5_31, chunk5_32, chunk5_33, chunk5_34]
private theorem checked6_6 : ∀ w ∈ chunk6_6, ¬ Need 6 w.toFinset := by
  have h : chunk6_6.all (routes 5 pool6_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
private def chunk6_7 : List (List T) := [[wire1986,wire30852,wire233791,wire860688,wire1721376],
  [wire1986,wire30911,wire233736,wire860688,wire1721376],
  [wire2047,wire30852,wire233736,wire860688,wire1721376]]
private def pool6_7 : List (List (List T)) := [chunk5_14, chunk5_15, chunk5_16, chunk5_17, chunk5_18, chunk5_19, chunk5_20, chunk5_21, chunk5_22, chunk5_23, chunk5_24, chunk5_25, chunk5_26, chunk5_27, chunk5_28, chunk5_29, chunk5_30, chunk5_31, chunk5_32, chunk5_33, chunk5_34]
private theorem checked6_7 : ∀ w ∈ chunk6_7, ¬ Need 6 w.toFinset := by
  have h : chunk6_7.all (routes 5 pool6_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_29 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
#print axioms checked6_7
private def chunk7_0 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1721376]]
private def pool7_0 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_3, chunk6_4, chunk6_5, chunk6_6, chunk6_7]
private theorem checked7_0 : ∀ w ∈ chunk7_0, ¬ Need 7 w.toFinset := by
  have h : chunk7_0.all (routes 6 pool7_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_4 _ hm
  · exact checked6_5 _ hm
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
#print axioms checked7_0
private theorem root : safe 7 ins := initial checked7_0 (by decide +kernel)
private def samples : Fin (2*K) → Fin 6 × Fin 6 := ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 5), (0, 5), (0, 5), (0, 5), (0, 5), (0, 5), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 5), (1, 5), (1, 5), (1, 5), (1, 5), (1, 5), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (2, 5), (2, 5), (2, 5), (2, 5), (2, 5), (2, 5), (3, 3), (3, 3), (3, 3), (3, 3), (3, 3), (3, 3), (3, 5), (3, 5), (3, 5), (3, 5), (3, 5), (3, 5), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5), (0, 4), (1, 4), (2, 4), (3, 4), (4, 5), (5, 5)]
private def inputs (i : Fin (2*K)) :=
  List.ofFn fun k : Fin 6 => decide (k = (samples i).1 ∨ k = (samples i).2)

private theorem tables (C : Circuit)
    (he : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (279104431 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :
    ∀ k, (C.gates.foldl step (ins.map (bit k))).getD C.output false = bit k target := by
  intro k
  have hi : ∀ i : Fin (2*K), inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin (2*K), (279104431 : Nat).testBit
      (6 * min (samples i).1.val (samples i).2.val + max (samples i).1.val (samples i).2.val) = bit i target := by decide +kernel
  have h := he (samples k).1 (samples k).2
  change C.eval (inputs k) = _ at h
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using h

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (279104431 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hg,hs,he⟩
  exact exclude C.gates C.output (fun g hm => hg g hm) ins ins
    (fun ⦃_⦄ hx => hx) 7 hs root (tables C he)

#print axioms generalLower

-- A witness on all 36 ordered input pairs.
def circuit : Circuit :=
  { gates := [⟨.or,[1,0]⟩, ⟨.or,[2,6]⟩, ⟨.or,[3,7]⟩, ⟨.not,[8]⟩, ⟨.and,[4,8]⟩, ⟨.and,[9,5]⟩, ⟨.or,[11,10]⟩, ⟨.not,[12]⟩], output := 13 }

theorem upper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (279104431 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms upper
end Graph279104431
