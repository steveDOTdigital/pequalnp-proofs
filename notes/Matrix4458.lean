import PEqualNP.Defs.Represents

-- The gate semantics and safety induction adapt the Apache-2.0 proof credited in Mask53Exact.lean.
-- Lewis Watson and Nico Habets developed the earlier gate enumeration.
-- The samples are one-row, one-column inputs of the four-by-four matrix.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Matrix4458

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev K := 60
private abbrev T := BitVec (2*K)
private def ins : List T := [(((((((0xc030 : T) <<< 32) ||| 0xc0300c0) <<< 32) ||| 0x30000000) <<< 32) ||| 0xfffff), (((((((0x300c0 : T) <<< 32) ||| 0x300c0300) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xfff00000), (((((((0x1c0701 : T) <<< 32) ||| 0xc0701c07) <<< 32) ||| 0x3ff00) <<< 32) ||| 0x0), (((((((0xe0380e : T) <<< 32) ||| 0x380e038) <<< 32) ||| 0xffc0000) <<< 32) ||| 0x0), (((((((0x14050 : T) <<< 32) ||| 0x14050140) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0), (((((((0x240902 : T) <<< 32) ||| 0x40902409) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff003ff), (((((((0x489224 : T) <<< 32) ||| 0x89224892) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc0000000), (((((((0x922489 : T) <<< 32) ||| 0x22489224) <<< 32) ||| 0x80000000) <<< 32) ||| 0xffc00)]
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
private def wire1 : T := (((((((0x4010 : T) <<< 32) ||| 0x4010040) <<< 32) ||| 0x10000000) <<< 32) ||| 0x0)
private def wire2 : T := (0x3ff : T)
private def wire3 : T := (((((((0x4010 : T) <<< 32) ||| 0x4010040) <<< 32) ||| 0x10000000) <<< 32) ||| 0x3ff)
private def wire4 : T := (((((((0x8020 : T) <<< 32) ||| 0x8020080) <<< 32) ||| 0x20000000) <<< 32) ||| 0x0)
private def wire5 : T := (((((((0xc030 : T) <<< 32) ||| 0xc0300c0) <<< 32) ||| 0x30000000) <<< 32) ||| 0x0)
private def wire8 : T := (0xffc00 : T)
private def wire10 : T := (0xfffff : T)
private def wire11 : T := (((((((0x4010 : T) <<< 32) ||| 0x4010040) <<< 32) ||| 0x10000000) <<< 32) ||| 0xfffff)
private def wire12 : T := (((((((0x8020 : T) <<< 32) ||| 0x8020080) <<< 32) ||| 0x20000000) <<< 32) ||| 0xffc00)
private def wire13 : T := (((((((0xc030 : T) <<< 32) ||| 0xc0300c0) <<< 32) ||| 0x30000000) <<< 32) ||| 0xffc00)
private def wire15 : T := (((((((0xc030 : T) <<< 32) ||| 0xc0300c0) <<< 32) ||| 0x30000000) <<< 32) ||| 0xfffff)
private def wire16 : T := (((((((0x10040 : T) <<< 32) ||| 0x10040100) <<< 32) ||| 0x40000000) <<< 32) ||| 0x0)
private def wire31 : T := (((((((0x1c070 : T) <<< 32) ||| 0x1c0701c0) <<< 32) ||| 0x70000000) <<< 32) ||| 0xfffff)
private def wire32 : T := (0x3ff00000 : T)
private def wire34 : T := (0x3ff003ff : T)
private def wire47 : T := (((((((0xc030 : T) <<< 32) ||| 0xc0300c0) <<< 32) ||| 0x30000000) <<< 32) ||| 0x3fffffff)
private def wire48 : T := (((((((0x10040 : T) <<< 32) ||| 0x10040100) <<< 32) ||| 0x40000000) <<< 32) ||| 0x3ff00000)
private def wire63 : T := (((((((0x1c070 : T) <<< 32) ||| 0x1c0701c0) <<< 32) ||| 0x70000000) <<< 32) ||| 0x3fffffff)
private def wire64 : T := (((0xff : T) <<< 32) ||| 0xc0000000)
private def wire68 : T := (((((((0x8020 : T) <<< 32) ||| 0x8020080) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc0000000)
private def wire72 : T := (((0xff : T) <<< 32) ||| 0xc00ffc00)
private def wire79 : T := (((((((0xc030 : T) <<< 32) ||| 0xc0300c0) <<< 32) ||| 0x300000ff) <<< 32) ||| 0xc00fffff)
private def wire96 : T := (((0xff : T) <<< 32) ||| 0xfff00000)
private def wire111 : T := (((((((0xc030 : T) <<< 32) ||| 0xc0300c0) <<< 32) ||| 0x300000ff) <<< 32) ||| 0xffffffff)
private def wire112 : T := (((((((0x10040 : T) <<< 32) ||| 0x10040100) <<< 32) ||| 0x400000ff) <<< 32) ||| 0xfff00000)
private def wire116 : T := (((((((0x18060 : T) <<< 32) ||| 0x18060180) <<< 32) ||| 0x600000ff) <<< 32) ||| 0xfff00000)
private def wire119 : T := (((((((0x1c070 : T) <<< 32) ||| 0x1c0701c0) <<< 32) ||| 0x700000ff) <<< 32) ||| 0xfff003ff)
private def wire123 : T := (((((((0x14050 : T) <<< 32) ||| 0x14050140) <<< 32) ||| 0x500000ff) <<< 32) ||| 0xffffffff)
private def wire127 : T := (((((((0x1c070 : T) <<< 32) ||| 0x1c0701c0) <<< 32) ||| 0x700000ff) <<< 32) ||| 0xffffffff)
private def wire128 : T := (((((((0x20080 : T) <<< 32) ||| 0x20080200) <<< 32) ||| 0x80000000) <<< 32) ||| 0x0)
private def wire132 : T := (((((((0x280a0 : T) <<< 32) ||| 0x280a0280) <<< 32) ||| 0xa0000000) <<< 32) ||| 0x0)
private def wire136 : T := (((((((0x20080 : T) <<< 32) ||| 0x20080200) <<< 32) ||| 0x80000000) <<< 32) ||| 0xffc00)
private def wire139 : T := (((((((0x24090 : T) <<< 32) ||| 0x24090240) <<< 32) ||| 0x90000000) <<< 32) ||| 0xfffff)
private def wire143 : T := (((((((0x2c0b0 : T) <<< 32) ||| 0x2c0b02c0) <<< 32) ||| 0xb0000000) <<< 32) ||| 0xfffff)
private def wire144 : T := (((((((0x300c0 : T) <<< 32) ||| 0x300c0300) <<< 32) ||| 0xc0000000) <<< 32) ||| 0x0)
private def wire159 : T := (((((((0x3c0f0 : T) <<< 32) ||| 0x3c0f03c0) <<< 32) ||| 0xf0000000) <<< 32) ||| 0xfffff)
private def wire187 : T := (((((((0x340d0 : T) <<< 32) ||| 0x340d0340) <<< 32) ||| 0xd0000000) <<< 32) ||| 0x3fffffff)
private def wire192 : T := (((((((0x20080 : T) <<< 32) ||| 0x20080200) <<< 32) ||| 0x800000ff) <<< 32) ||| 0xc0000000)
private def wire207 : T := (((((((0x2c0b0 : T) <<< 32) ||| 0x2c0b02c0) <<< 32) ||| 0xb00000ff) <<< 32) ||| 0xc00fffff)
private def wire208 : T := (((((((0x300c0 : T) <<< 32) ||| 0x300c0300) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xc0000000)
private def wire223 : T := (((((((0x3c0f0 : T) <<< 32) ||| 0x3c0f03c0) <<< 32) ||| 0xf00000ff) <<< 32) ||| 0xc00fffff)
private def wire240 : T := (((((((0x300c0 : T) <<< 32) ||| 0x300c0300) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xfff00000)
private def wire241 : T := (((((((0x340d0 : T) <<< 32) ||| 0x340d0340) <<< 32) ||| 0xd00000ff) <<< 32) ||| 0xfff00000)
private def wire242 : T := (((((((0x300c0 : T) <<< 32) ||| 0x300c0300) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xfff003ff)
private def wire243 : T := (((((((0x340d0 : T) <<< 32) ||| 0x340d0340) <<< 32) ||| 0xd00000ff) <<< 32) ||| 0xfff003ff)
private def wire244 : T := (((((((0x380e0 : T) <<< 32) ||| 0x380e0380) <<< 32) ||| 0xe00000ff) <<< 32) ||| 0xfff00000)
private def wire245 : T := (((((((0x3c0f0 : T) <<< 32) ||| 0x3c0f03c0) <<< 32) ||| 0xf00000ff) <<< 32) ||| 0xfff00000)
private def wire248 : T := (((((((0x300c0 : T) <<< 32) ||| 0x300c0300) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xfffffc00)
private def wire250 : T := (((((((0x300c0 : T) <<< 32) ||| 0x300c0300) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xffffffff)
private def wire251 : T := (((((((0x340d0 : T) <<< 32) ||| 0x340d0340) <<< 32) ||| 0xd00000ff) <<< 32) ||| 0xffffffff)
private def wire252 : T := (((((((0x380e0 : T) <<< 32) ||| 0x380e0380) <<< 32) ||| 0xe00000ff) <<< 32) ||| 0xfffffc00)
private def wire253 : T := (((((((0x3c0f0 : T) <<< 32) ||| 0x3c0f03c0) <<< 32) ||| 0xf00000ff) <<< 32) ||| 0xfffffc00)
private def wire255 : T := (((((((0x3c0f0 : T) <<< 32) ||| 0x3c0f03c0) <<< 32) ||| 0xf00000ff) <<< 32) ||| 0xffffffff)
private def wire256 : T := (((0x3ff00 : T) <<< 32) ||| 0x0)
private def wire512 : T := (((((((0x40100 : T) <<< 32) ||| 0x40100401) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire514 : T := (((((((0x40100 : T) <<< 32) ||| 0x40100401) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff)
private def wire544 : T := (((((((0x40100 : T) <<< 32) ||| 0x40100401) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff00000)
private def wire546 : T := (((((((0x40100 : T) <<< 32) ||| 0x40100401) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff003ff)
private def wire1024 : T := (((((((0x80200 : T) <<< 32) ||| 0x80200802) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire1028 : T := (((((((0x88220 : T) <<< 32) ||| 0x88220882) <<< 32) ||| 0x20000000) <<< 32) ||| 0x0)
private def wire1039 : T := (((((((0x8c230 : T) <<< 32) ||| 0x8c2308c2) <<< 32) ||| 0x30000000) <<< 32) ||| 0xfffff)
private def wire1092 : T := (((((((0x88220 : T) <<< 32) ||| 0x88220882) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc0000000)
private def wire1911 : T := (((((((0xdc370 : T) <<< 32) ||| 0xdc370dc3) <<< 32) ||| 0x7003ffff) <<< 32) ||| 0xfff003ff)
private def wire2048 : T := (((((((0x100401 : T) <<< 32) ||| 0x401004) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire2176 : T := (((((((0x120481 : T) <<< 32) ||| 0x20481204) <<< 32) ||| 0x80000000) <<< 32) ||| 0x0)
private def wire2184 : T := (((((((0x120481 : T) <<< 32) ||| 0x20481204) <<< 32) ||| 0x80000000) <<< 32) ||| 0xffc00)
private def wire2288 : T := (((((((0x1304c1 : T) <<< 32) ||| 0x304c1304) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xfff00000)
private def wire3003 : T := (((((((0x1745d1 : T) <<< 32) ||| 0x745d1745) <<< 32) ||| 0xd003ff00) <<< 32) ||| 0x3fffffff)
private def wire3549 : T := (((((((0x1bc6f1 : T) <<< 32) ||| 0xbc6f1bc6) <<< 32) ||| 0xf003ffff) <<< 32) ||| 0xc00ffc00)
private def wire3840 : T := (((((((0x1c0701 : T) <<< 32) ||| 0xc0701c07) <<< 32) ||| 0x3ff00) <<< 32) ||| 0x0)
private def wire3842 : T := (((((((0x1c0701 : T) <<< 32) ||| 0xc0701c07) <<< 32) ||| 0x3ff00) <<< 32) ||| 0x3ff)
private def wire3844 : T := (((((((0x1c8721 : T) <<< 32) ||| 0xc8721c87) <<< 32) ||| 0x2003ff00) <<< 32) ||| 0x0)
private def wire3855 : T := (((((((0x1cc731 : T) <<< 32) ||| 0xcc731cc7) <<< 32) ||| 0x3003ff00) <<< 32) ||| 0xfffff)
private def wire3872 : T := (((((((0x1c0701 : T) <<< 32) ||| 0xc0701c07) <<< 32) ||| 0x3ff00) <<< 32) ||| 0x3ff00000)
private def wire3968 : T := (((((((0x1e0781 : T) <<< 32) ||| 0xe0781e07) <<< 32) ||| 0x8003ff00) <<< 32) ||| 0x0)
private def wire3972 : T := (((((((0x1e87a1 : T) <<< 32) ||| 0xe87a1e87) <<< 32) ||| 0xa003ff00) <<< 32) ||| 0x0)
private def wire4080 : T := (((((((0x1f07c1 : T) <<< 32) ||| 0xf07c1f07) <<< 32) ||| 0xc003ffff) <<< 32) ||| 0xfff00000)
private def wire4095 : T := (((((((0x1fc7f1 : T) <<< 32) ||| 0xfc7f1fc7) <<< 32) ||| 0xf003ffff) <<< 32) ||| 0xffffffff)
private def wire4096 : T := (((0xffc0000 : T) <<< 32) ||| 0x0)
private def wire4352 : T := (((0xfffff00 : T) <<< 32) ||| 0x0)
private def wire4353 : T := (((((((0x4010 : T) <<< 32) ||| 0x4010040) <<< 32) ||| 0x1fffff00) <<< 32) ||| 0x0)
private def wire4368 : T := (((((((0x10040 : T) <<< 32) ||| 0x10040100) <<< 32) ||| 0x4fffff00) <<< 32) ||| 0x0)
private def wire4369 : T := (((((((0x14050 : T) <<< 32) ||| 0x14050140) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0)
private def wire4371 : T := (((((((0x14050 : T) <<< 32) ||| 0x14050140) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x3ff)
private def wire4373 : T := (((((((0x1c070 : T) <<< 32) ||| 0x1c0701c0) <<< 32) ||| 0x7fffff00) <<< 32) ||| 0x0)
private def wire4377 : T := (((((((0x14050 : T) <<< 32) ||| 0x14050140) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0xffc00)
private def wire4381 : T := (((((((0x1c070 : T) <<< 32) ||| 0x1c0701c0) <<< 32) ||| 0x7fffff00) <<< 32) ||| 0xffc00)
private def wire4383 : T := (((((((0x1c070 : T) <<< 32) ||| 0x1c0701c0) <<< 32) ||| 0x7fffff00) <<< 32) ||| 0xfffff)
private def wire4401 : T := (((((((0x14050 : T) <<< 32) ||| 0x14050140) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x3ff00000)
private def wire4433 : T := (((((((0x14050 : T) <<< 32) ||| 0x14050140) <<< 32) ||| 0x5fffffff) <<< 32) ||| 0xc0000000)
private def wire4497 : T := (((((((0x340d0 : T) <<< 32) ||| 0x340d0340) <<< 32) ||| 0xdfffff00) <<< 32) ||| 0x0)
private def wire4501 : T := (((((((0x3c0f0 : T) <<< 32) ||| 0x3c0f03c0) <<< 32) ||| 0xffffff00) <<< 32) ||| 0x0)
private def wire4561 : T := (((((((0x340d0 : T) <<< 32) ||| 0x340d0340) <<< 32) ||| 0xdfffffff) <<< 32) ||| 0xc0000000)
private def wire4593 : T := (((((((0x340d0 : T) <<< 32) ||| 0x340d0340) <<< 32) ||| 0xdfffffff) <<< 32) ||| 0xfff00000)
private def wire4881 : T := (((((((0x54150 : T) <<< 32) ||| 0x54150541) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0)
private def wire5393 : T := (((((((0x94250 : T) <<< 32) ||| 0x94250942) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0)
private def wire6417 : T := (((((((0x114451 : T) <<< 32) ||| 0x14451144) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0)
private def wire7953 : T := (((((((0x1d4751 : T) <<< 32) ||| 0xd4751d47) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0)
private def wire8192 : T := (((((((0x200802 : T) <<< 32) ||| 0x802008) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire8194 : T := (((((((0x200802 : T) <<< 32) ||| 0x802008) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff)
private def wire8224 : T := (((((((0x200802 : T) <<< 32) ||| 0x802008) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff00000)
private def wire8226 : T := (((((((0x200802 : T) <<< 32) ||| 0x802008) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff003ff)
private def wire8706 : T := (((((((0x240902 : T) <<< 32) ||| 0x40902409) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff)
private def wire8736 : T := (((((((0x240902 : T) <<< 32) ||| 0x40902409) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff00000)
private def wire8738 : T := (((((((0x240902 : T) <<< 32) ||| 0x40902409) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff003ff)
private def wire8739 : T := (((((((0x244912 : T) <<< 32) ||| 0x44912449) <<< 32) ||| 0x10000000) <<< 32) ||| 0x3ff003ff)
private def wire8742 : T := (((((((0x248922 : T) <<< 32) ||| 0x48922489) <<< 32) ||| 0x20000000) <<< 32) ||| 0x3ff003ff)
private def wire8746 : T := (((((((0x240902 : T) <<< 32) ||| 0x40902409) <<< 32) ||| 0x0) <<< 32) ||| 0x3fffffff)
private def wire8751 : T := (((((((0x24c932 : T) <<< 32) ||| 0x4c9324c9) <<< 32) ||| 0x30000000) <<< 32) ||| 0x3fffffff)
private def wire8754 : T := (((((((0x250942 : T) <<< 32) ||| 0x50942509) <<< 32) ||| 0x40000000) <<< 32) ||| 0x3ff003ff)
private def wire8802 : T := (((((((0x240902 : T) <<< 32) ||| 0x40902409) <<< 32) ||| 0xff) <<< 32) ||| 0xfff003ff)
private def wire8810 : T := (((((((0x240902 : T) <<< 32) ||| 0x40902409) <<< 32) ||| 0xff) <<< 32) ||| 0xffffffff)
private def wire8866 : T := (((((((0x260982 : T) <<< 32) ||| 0x60982609) <<< 32) ||| 0x80000000) <<< 32) ||| 0x3ff003ff)
private def wire8946 : T := (((((((0x2709c2 : T) <<< 32) ||| 0x709c2709) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xfff003ff)
private def wire8994 : T := (((((((0x240902 : T) <<< 32) ||| 0x40902409) <<< 32) ||| 0x3ff00) <<< 32) ||| 0x3ff003ff)
private def wire9762 : T := (((((((0x2c0b02 : T) <<< 32) ||| 0xc0b02c0b) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff003ff)
private def wire10786 : T := (((((((0x340d03 : T) <<< 32) ||| 0x40d0340d) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff003ff)
private def wire12066 : T := (((((((0x3c0f03 : T) <<< 32) ||| 0xc0f03c0f) <<< 32) ||| 0x3ff00) <<< 32) ||| 0x3ff003ff)
private def wire12079 : T := (((((((0x3ccf33 : T) <<< 32) ||| 0xccf33ccf) <<< 32) ||| 0x3003ff00) <<< 32) ||| 0x3fffffff)
private def wire12274 : T := (((((((0x3f0fc3 : T) <<< 32) ||| 0xf0fc3f0f) <<< 32) ||| 0xc003ffff) <<< 32) ||| 0xfff003ff)
private def wire12561 : T := (((((((0x214852 : T) <<< 32) ||| 0x14852148) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0)
private def wire12834 : T := (((((((0x240902 : T) <<< 32) ||| 0x40902409) <<< 32) ||| 0xffc0000) <<< 32) ||| 0x3ff003ff)
private def wire13107 : T := (((((((0x254952 : T) <<< 32) ||| 0x54952549) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x3ff003ff)
private def wire13119 : T := (((((((0x25c972 : T) <<< 32) ||| 0x5c9725c9) <<< 32) ||| 0x7fffff00) <<< 32) ||| 0x3fffffff)
private def wire13299 : T := (((((((0x2749d2 : T) <<< 32) ||| 0x749d2749) <<< 32) ||| 0xdfffffff) <<< 32) ||| 0xfff003ff)
private def wire16179 : T := (((((((0x3d4f53 : T) <<< 32) ||| 0xd4f53d4f) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x3ff003ff)
private def wire16384 : T := (((((((0x401004 : T) <<< 32) ||| 0x1004010) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire16388 : T := (((((((0x409024 : T) <<< 32) ||| 0x9024090) <<< 32) ||| 0x20000000) <<< 32) ||| 0x0)
private def wire16399 : T := (((((((0x40d034 : T) <<< 32) ||| 0xd0340d0) <<< 32) ||| 0x30000000) <<< 32) ||| 0xfffff)
private def wire16452 : T := (((((((0x409024 : T) <<< 32) ||| 0x9024090) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc0000000)
private def wire17412 : T := (((((((0x489224 : T) <<< 32) ||| 0x89224892) <<< 32) ||| 0x20000000) <<< 32) ||| 0x0)
private def wire17472 : T := (((((((0x481204 : T) <<< 32) ||| 0x81204812) <<< 32) ||| 0xff) <<< 32) ||| 0xc0000000)
private def wire17476 : T := (((((((0x489224 : T) <<< 32) ||| 0x89224892) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc0000000)
private def wire17477 : T := (((((((0x48d234 : T) <<< 32) ||| 0x8d2348d2) <<< 32) ||| 0x300000ff) <<< 32) ||| 0xc0000000)
private def wire17478 : T := (((((((0x489224 : T) <<< 32) ||| 0x89224892) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc00003ff)
private def wire17484 : T := (((((((0x489224 : T) <<< 32) ||| 0x89224892) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc00ffc00)
private def wire17487 : T := (((((((0x48d234 : T) <<< 32) ||| 0x8d2348d2) <<< 32) ||| 0x300000ff) <<< 32) ||| 0xc00fffff)
private def wire17492 : T := (((((((0x499264 : T) <<< 32) ||| 0x99264992) <<< 32) ||| 0x600000ff) <<< 32) ||| 0xc0000000)
private def wire17508 : T := (((((((0x489224 : T) <<< 32) ||| 0x89224892) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xfff00000)
private def wire17519 : T := (((((((0x48d234 : T) <<< 32) ||| 0x8d2348d2) <<< 32) ||| 0x300000ff) <<< 32) ||| 0xffffffff)
private def wire17524 : T := (((((((0x499264 : T) <<< 32) ||| 0x99264992) <<< 32) ||| 0x600000ff) <<< 32) ||| 0xfff00000)
private def wire17604 : T := (((((((0x4a92a4 : T) <<< 32) ||| 0xa92a4a92) <<< 32) ||| 0xa00000ff) <<< 32) ||| 0xc0000000)
private def wire17615 : T := (((((((0x4ad2b4 : T) <<< 32) ||| 0xad2b4ad2) <<< 32) ||| 0xb00000ff) <<< 32) ||| 0xc00fffff)
private def wire17652 : T := (((((((0x4b92e4 : T) <<< 32) ||| 0xb92e4b92) <<< 32) ||| 0xe00000ff) <<< 32) ||| 0xfff00000)
private def wire17663 : T := (((((((0x4bd2f4 : T) <<< 32) ||| 0xbd2f4bd2) <<< 32) ||| 0xf00000ff) <<< 32) ||| 0xffffffff)
private def wire17732 : T := (((((((0x489224 : T) <<< 32) ||| 0x89224892) <<< 32) ||| 0x2003ffff) <<< 32) ||| 0xc0000000)
private def wire17988 : T := (((((((0x4c9324 : T) <<< 32) ||| 0xc9324c93) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc0000000)
private def wire18020 : T := (((((((0x4c9324 : T) <<< 32) ||| 0xc9324c93) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xfff00000)
private def wire19524 : T := (((((((0x589625 : T) <<< 32) ||| 0x89625896) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc0000000)
private def wire20292 : T := (((((((0x5c9725 : T) <<< 32) ||| 0xc9725c97) <<< 32) ||| 0x2003ffff) <<< 32) ||| 0xc0000000)
private def wire20303 : T := (((((((0x5cd735 : T) <<< 32) ||| 0xcd735cd7) <<< 32) ||| 0x3003ffff) <<< 32) ||| 0xc00fffff)
private def wire20324 : T := (((((((0x5c9725 : T) <<< 32) ||| 0xc9725c97) <<< 32) ||| 0x2003ffff) <<< 32) ||| 0xfff00000)
private def wire20468 : T := (((((((0x5f97e5 : T) <<< 32) ||| 0xf97e5f97) <<< 32) ||| 0xe003ffff) <<< 32) ||| 0xfff00000)
private def wire20753 : T := (((((((0x415054 : T) <<< 32) ||| 0x15054150) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0)
private def wire21572 : T := (((((((0x489224 : T) <<< 32) ||| 0x89224892) <<< 32) ||| 0x2ffc00ff) <<< 32) ||| 0xc0000000)
private def wire21845 : T := (((((((0x49d274 : T) <<< 32) ||| 0x9d2749d2) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xc0000000)
private def wire21855 : T := (((((((0x49d274 : T) <<< 32) ||| 0x9d2749d2) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xc00fffff)
private def wire21877 : T := (((((((0x49d274 : T) <<< 32) ||| 0x9d2749d2) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xfff00000)
private def wire21973 : T := (((((((0x4bd2f4 : T) <<< 32) ||| 0xbd2f4bd2) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc0000000)
private def wire22005 : T := (((((((0x4bd2f4 : T) <<< 32) ||| 0xbd2f4bd2) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xfff00000)
private def wire24405 : T := (((((((0x5dd775 : T) <<< 32) ||| 0xdd775dd7) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xc0000000)
private def wire25122 : T := (((((((0x641906 : T) <<< 32) ||| 0x41906419) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff003ff)
private def wire25668 : T := (((((((0x689a26 : T) <<< 32) ||| 0x89a2689a) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc0000000)
private def wire25700 : T := (((((((0x689a26 : T) <<< 32) ||| 0x89a2689a) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xfff00000)
private def wire26210 : T := (((((((0x6c1b06 : T) <<< 32) ||| 0xc1b06c1b) <<< 32) ||| 0xff) <<< 32) ||| 0xfff003ff)
private def wire26212 : T := (((((((0x6c9b26 : T) <<< 32) ||| 0xc9b26c9b) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xfff00000)
private def wire26214 : T := (((((((0x6c9b26 : T) <<< 32) ||| 0xc9b26c9b) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xfff003ff)
private def wire26223 : T := (((((((0x6cdb36 : T) <<< 32) ||| 0xcdb36cdb) <<< 32) ||| 0x300000ff) <<< 32) ||| 0xffffffff)
private def wire28518 : T := (((((((0x7c9f27 : T) <<< 32) ||| 0xc9f27c9f) <<< 32) ||| 0x2003ffff) <<< 32) ||| 0xfff003ff)
private def wire28791 : T := (((((((0x61d876 : T) <<< 32) ||| 0x1d8761d8) <<< 32) ||| 0x7ffc00ff) <<< 32) ||| 0xfff003ff)
private def wire30471 : T := (((((((0x6cdb36 : T) <<< 32) ||| 0xcdb36cdb) <<< 32) ||| 0x3fffff00) <<< 32) ||| 0x3ff)
private def wire30576 : T := (((((((0x6d1b46 : T) <<< 32) ||| 0xd1b46d1b) <<< 32) ||| 0x4fffffff) <<< 32) ||| 0xfff00000)
private def wire30580 : T := (((((((0x6d9b66 : T) <<< 32) ||| 0xd9b66d9b) <<< 32) ||| 0x6fffffff) <<< 32) ||| 0xfff00000)
private def wire30581 : T := (((((((0x6ddb76 : T) <<< 32) ||| 0xddb76ddb) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xfff00000)
private def wire30583 : T := (((((((0x6ddb76 : T) <<< 32) ||| 0xddb76ddb) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xfff003ff)
private def wire30591 : T := (((((((0x6ddb76 : T) <<< 32) ||| 0xddb76ddb) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xffffffff)
private def wire30711 : T := (((((((0x6fdbf6 : T) <<< 32) ||| 0xfdbf6fdb) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xfff003ff)
private def wire32631 : T := (((((((0x7ddf77 : T) <<< 32) ||| 0xddf77ddf) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xfff003ff)
private def wire32768 : T := (((((((0x802008 : T) <<< 32) ||| 0x2008020) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire32896 : T := (((((((0x822088 : T) <<< 32) ||| 0x22088220) <<< 32) ||| 0x80000000) <<< 32) ||| 0x0)
private def wire32904 : T := (((((((0x822088 : T) <<< 32) ||| 0x22088220) <<< 32) ||| 0x80000000) <<< 32) ||| 0xffc00)
private def wire33008 : T := (((((((0x8320c8 : T) <<< 32) ||| 0x320c8320) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xfff00000)
private def wire34824 : T := (((((((0x902409 : T) <<< 32) ||| 0x2409024) <<< 32) ||| 0x0) <<< 32) ||| 0xffc00)
private def wire34944 : T := (((((((0x922489 : T) <<< 32) ||| 0x22489224) <<< 32) ||| 0x80000000) <<< 32) ||| 0x0)
private def wire34952 : T := (((((((0x922489 : T) <<< 32) ||| 0x22489224) <<< 32) ||| 0x80000000) <<< 32) ||| 0xffc00)
private def wire34953 : T := (((((((0x926499 : T) <<< 32) ||| 0x26499264) <<< 32) ||| 0x90000000) <<< 32) ||| 0xffc00)
private def wire34954 : T := (((((((0x922489 : T) <<< 32) ||| 0x22489224) <<< 32) ||| 0x80000000) <<< 32) ||| 0xfffff)
private def wire34955 : T := (((((((0x926499 : T) <<< 32) ||| 0x26499264) <<< 32) ||| 0x90000000) <<< 32) ||| 0xfffff)
private def wire34956 : T := (((((((0x92a4a9 : T) <<< 32) ||| 0x2a4a92a4) <<< 32) ||| 0xa0000000) <<< 32) ||| 0xffc00)
private def wire34959 : T := (((((((0x92e4b9 : T) <<< 32) ||| 0x2e4b92e4) <<< 32) ||| 0xb0000000) <<< 32) ||| 0xfffff)
private def wire34968 : T := (((((((0x9324c9 : T) <<< 32) ||| 0x324c9324) <<< 32) ||| 0xc0000000) <<< 32) ||| 0xffc00)
private def wire34984 : T := (((((((0x922489 : T) <<< 32) ||| 0x22489224) <<< 32) ||| 0x80000000) <<< 32) ||| 0x3ffffc00)
private def wire35016 : T := (((((((0x922489 : T) <<< 32) ||| 0x22489224) <<< 32) ||| 0x800000ff) <<< 32) ||| 0xc00ffc00)
private def wire35064 : T := (((((((0x9324c9 : T) <<< 32) ||| 0x324c9324) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xfffffc00)
private def wire35066 : T := (((((((0x9324c9 : T) <<< 32) ||| 0x324c9324) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xffffffff)
private def wire35068 : T := (((((((0x93a4e9 : T) <<< 32) ||| 0x3a4e93a4) <<< 32) ||| 0xe00000ff) <<< 32) ||| 0xfffffc00)
private def wire35071 : T := (((((((0x93e4f9 : T) <<< 32) ||| 0x3e4f93e4) <<< 32) ||| 0xf00000ff) <<< 32) ||| 0xffffffff)
private def wire35208 : T := (((((((0x922489 : T) <<< 32) ||| 0x22489224) <<< 32) ||| 0x8003ff00) <<< 32) ||| 0xffc00)
private def wire35464 : T := (((((((0x962589 : T) <<< 32) ||| 0x62589625) <<< 32) ||| 0x80000000) <<< 32) ||| 0xffc00)
private def wire35466 : T := (((((((0x962589 : T) <<< 32) ||| 0x62589625) <<< 32) ||| 0x80000000) <<< 32) ||| 0xfffff)
private def wire35976 : T := (((((((0x9a2689 : T) <<< 32) ||| 0xa2689a26) <<< 32) ||| 0x80000000) <<< 32) ||| 0xffc00)
private def wire36744 : T := (((((((0x9e2789 : T) <<< 32) ||| 0xe2789e27) <<< 32) ||| 0x8003ff00) <<< 32) ||| 0xffc00)
private def wire36746 : T := (((((((0x9e2789 : T) <<< 32) ||| 0xe2789e27) <<< 32) ||| 0x8003ff00) <<< 32) ||| 0xfffff)
private def wire36751 : T := (((((((0x9ee7b9 : T) <<< 32) ||| 0xee7b9ee7) <<< 32) ||| 0xb003ff00) <<< 32) ||| 0xfffff)
private def wire36856 : T := (((((((0x9f27c9 : T) <<< 32) ||| 0xf27c9f27) <<< 32) ||| 0xc003ffff) <<< 32) ||| 0xfffffc00)
private def wire37137 : T := (((((((0x816058 : T) <<< 32) ||| 0x16058160) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0)
private def wire39048 : T := (((((((0x922489 : T) <<< 32) ||| 0x22489224) <<< 32) ||| 0x8ffc0000) <<< 32) ||| 0xffc00)
private def wire39321 : T := (((((((0x9364d9 : T) <<< 32) ||| 0x364d9364) <<< 32) ||| 0xdfffff00) <<< 32) ||| 0xffc00)
private def wire39323 : T := (((((((0x9364d9 : T) <<< 32) ||| 0x364d9364) <<< 32) ||| 0xdfffff00) <<< 32) ||| 0xfffff)
private def wire39325 : T := (((((((0x93e4f9 : T) <<< 32) ||| 0x3e4f93e4) <<< 32) ||| 0xffffff00) <<< 32) ||| 0xffc00)
private def wire39327 : T := (((((((0x93e4f9 : T) <<< 32) ||| 0x3e4f93e4) <<< 32) ||| 0xffffff00) <<< 32) ||| 0xfffff)
private def wire39417 : T := (((((((0x9364d9 : T) <<< 32) ||| 0x364d9364) <<< 32) ||| 0xdfffffff) <<< 32) ||| 0xfffffc00)
private def wire40857 : T := (((((((0x9f67d9 : T) <<< 32) ||| 0xf67d9f67) <<< 32) ||| 0xdfffff00) <<< 32) ||| 0xffc00)
private def wire41506 : T := (((((((0xa4290a : T) <<< 32) ||| 0x4290a429) <<< 32) ||| 0x0) <<< 32) ||| 0x3ff003ff)
private def wire43144 : T := (((((((0xb22c8b : T) <<< 32) ||| 0x22c8b22c) <<< 32) ||| 0x80000000) <<< 32) ||| 0xffc00)
private def wire43146 : T := (((((((0xb22c8b : T) <<< 32) ||| 0x22c8b22c) <<< 32) ||| 0x80000000) <<< 32) ||| 0xfffff)
private def wire43562 : T := (((((((0xb42d0b : T) <<< 32) ||| 0x42d0b42d) <<< 32) ||| 0x0) <<< 32) ||| 0x3fffffff)
private def wire43658 : T := (((((((0xb62d8b : T) <<< 32) ||| 0x62d8b62d) <<< 32) ||| 0x80000000) <<< 32) ||| 0xfffff)
private def wire43690 : T := (((((((0xb62d8b : T) <<< 32) ||| 0x62d8b62d) <<< 32) ||| 0x80000000) <<< 32) ||| 0x3fffffff)
private def wire43770 : T := (((((((0xb72dcb : T) <<< 32) ||| 0x72dcb72d) <<< 32) ||| 0xc00000ff) <<< 32) ||| 0xffffffff)
private def wire44970 : T := (((((((0xbe2f8b : T) <<< 32) ||| 0xe2f8be2f) <<< 32) ||| 0x8003ff00) <<< 32) ||| 0x3fffffff)
private def wire45243 : T := (((((((0xa368da : T) <<< 32) ||| 0x368da368) <<< 32) ||| 0xdffc0000) <<< 32) ||| 0x3fffffff)
private def wire47883 : T := (((((((0xb46d1b : T) <<< 32) ||| 0x46d1b46d) <<< 32) ||| 0x1fffff00) <<< 32) ||| 0xfffff)
private def wire48011 : T := (((((((0xb66d9b : T) <<< 32) ||| 0x66d9b66d) <<< 32) ||| 0x9fffff00) <<< 32) ||| 0xfffff)
private def wire48027 : T := (((((((0xb76ddb : T) <<< 32) ||| 0x76ddb76d) <<< 32) ||| 0xdfffff00) <<< 32) ||| 0xfffff)
private def wire48048 : T := (((((((0xb72dcb : T) <<< 32) ||| 0x72dcb72d) <<< 32) ||| 0xcfffff00) <<< 32) ||| 0x3ff00000)
private def wire48059 : T := (((((((0xb76ddb : T) <<< 32) ||| 0x76ddb76d) <<< 32) ||| 0xdfffff00) <<< 32) ||| 0x3fffffff)
private def wire48063 : T := (((((((0xb7edfb : T) <<< 32) ||| 0x7edfb7ed) <<< 32) ||| 0xffffff00) <<< 32) ||| 0x3fffffff)
private def wire48123 : T := (((((((0xb76ddb : T) <<< 32) ||| 0x76ddb76d) <<< 32) ||| 0xdfffffff) <<< 32) ||| 0xffffffff)
private def wire49083 : T := (((((((0xbf6fdb : T) <<< 32) ||| 0xf6fdbf6f) <<< 32) ||| 0xdfffff00) <<< 32) ||| 0x3fffffff)
private def wire50244 : T := (((((((0xc8b22c : T) <<< 32) ||| 0x8b22c8b2) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xc0000000)
private def wire51336 : T := (((((((0xd2348d : T) <<< 32) ||| 0x2348d234) <<< 32) ||| 0x80000000) <<< 32) ||| 0xffc00)
private def wire52428 : T := (((((((0xdab6ad : T) <<< 32) ||| 0xab6adab6) <<< 32) ||| 0xa00000ff) <<< 32) ||| 0xc00ffc00)
private def wire52431 : T := (((((((0xdaf6bd : T) <<< 32) ||| 0xaf6bdaf6) <<< 32) ||| 0xb00000ff) <<< 32) ||| 0xc00fffff)
private def wire52476 : T := (((((((0xdbb6ed : T) <<< 32) ||| 0xbb6edbb6) <<< 32) ||| 0xe00000ff) <<< 32) ||| 0xfffffc00)
private def wire52479 : T := (((((((0xdbf6fd : T) <<< 32) ||| 0xbf6fdbf6) <<< 32) ||| 0xf00000ff) <<< 32) ||| 0xffffffff)
private def wire53196 : T := (((((((0xdeb7ad : T) <<< 32) ||| 0xeb7adeb7) <<< 32) ||| 0xa003ffff) <<< 32) ||| 0xc00ffc00)
private def wire53469 : T := (((((((0xc3f0fc : T) <<< 32) ||| 0x3f0fc3f0) <<< 32) ||| 0xfffc00ff) <<< 32) ||| 0xc00ffc00)
private def wire56589 : T := (((((((0xd8f63d : T) <<< 32) ||| 0x8f63d8f6) <<< 32) ||| 0x3fffff00) <<< 32) ||| 0xffc00)
private def wire56784 : T := (((((((0xdb36cd : T) <<< 32) ||| 0xb36cdb36) <<< 32) ||| 0xcfffffff) <<< 32) ||| 0xc0000000)
private def wire56797 : T := (((((((0xdbf6fd : T) <<< 32) ||| 0xbf6fdbf6) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc00ffc00)
private def wire56799 : T := (((((((0xdbf6fd : T) <<< 32) ||| 0xbf6fdbf6) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc00fffff)
private def wire56829 : T := (((((((0xdbf6fd : T) <<< 32) ||| 0xbf6fdbf6) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xfffffc00)
private def wire57309 : T := (((((((0xdff7fd : T) <<< 32) ||| 0xff7fdff7) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc00ffc00)
private def wire60942 : T := (((((((0xfcbf2f : T) <<< 32) ||| 0xcbf2fcbf) <<< 32) ||| 0x20000000) <<< 32) ||| 0xfffff)
private def wire60974 : T := (((((((0xfcbf2f : T) <<< 32) ||| 0xcbf2fcbf) <<< 32) ||| 0x20000000) <<< 32) ||| 0x3fffffff)
private def wire61038 : T := (((((((0xfcbf2f : T) <<< 32) ||| 0xcbf2fcbf) <<< 32) ||| 0x200000ff) <<< 32) ||| 0xffffffff)
private def wire61152 : T := (((((((0xfe3f8f : T) <<< 32) ||| 0xe3f8fe3f) <<< 32) ||| 0x800000ff) <<< 32) ||| 0xfff00000)
private def wire61154 : T := (((((((0xfe3f8f : T) <<< 32) ||| 0xe3f8fe3f) <<< 32) ||| 0x800000ff) <<< 32) ||| 0xfff003ff)
private def wire61162 : T := (((((((0xfe3f8f : T) <<< 32) ||| 0xe3f8fe3f) <<< 32) ||| 0x800000ff) <<< 32) ||| 0xffffffff)
private def wire61166 : T := (((((((0xfebfaf : T) <<< 32) ||| 0xebfafebf) <<< 32) ||| 0xa00000ff) <<< 32) ||| 0xffffffff)
private def wire61167 : T := (((((((0xfeffbf : T) <<< 32) ||| 0xeffbfeff) <<< 32) ||| 0xb00000ff) <<< 32) ||| 0xffffffff)
private def wire61182 : T := (((((((0xffbfef : T) <<< 32) ||| 0xfbfeffbf) <<< 32) ||| 0xe00000ff) <<< 32) ||| 0xffffffff)
private def wire61440 : T := (((((((0xe0380e : T) <<< 32) ||| 0x380e038) <<< 32) ||| 0xffc0000) <<< 32) ||| 0x0)
private def wire61442 : T := (((((((0xe0380e : T) <<< 32) ||| 0x380e038) <<< 32) ||| 0xffc0000) <<< 32) ||| 0x3ff)
private def wire61444 : T := (((((((0xe0b82e : T) <<< 32) ||| 0xb82e0b8) <<< 32) ||| 0x2ffc0000) <<< 32) ||| 0x0)
private def wire61455 : T := (((((((0xe0f83e : T) <<< 32) ||| 0xf83e0f8) <<< 32) ||| 0x3ffc0000) <<< 32) ||| 0xfffff)
private def wire61472 : T := (((((((0xe0380e : T) <<< 32) ||| 0x380e038) <<< 32) ||| 0xffc0000) <<< 32) ||| 0x3ff00000)
private def wire61568 : T := (((((((0xe2388e : T) <<< 32) ||| 0x2388e238) <<< 32) ||| 0x8ffc0000) <<< 32) ||| 0x0)
private def wire61572 : T := (((((((0xe2b8ae : T) <<< 32) ||| 0x2b8ae2b8) <<< 32) ||| 0xaffc0000) <<< 32) ||| 0x0)
private def wire61680 : T := (((((((0xe338ce : T) <<< 32) ||| 0x338ce338) <<< 32) ||| 0xcffc00ff) <<< 32) ||| 0xfff00000)
private def wire61695 : T := (((((((0xe3f8fe : T) <<< 32) ||| 0x3f8fe3f8) <<< 32) ||| 0xfffc00ff) <<< 32) ||| 0xffffffff)
private def wire61713 : T := (((((((0xe1785e : T) <<< 32) ||| 0x1785e178) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x0)
private def wire61986 : T := (((((((0xe4390e : T) <<< 32) ||| 0x4390e439) <<< 32) ||| 0xffc0000) <<< 32) ||| 0x3ff003ff)
private def wire61999 : T := (((((((0xe4f93e : T) <<< 32) ||| 0x4f93e4f9) <<< 32) ||| 0x3ffc0000) <<< 32) ||| 0x3fffffff)
private def wire62194 : T := (((((((0xe739ce : T) <<< 32) ||| 0x739ce739) <<< 32) ||| 0xcffc00ff) <<< 32) ||| 0xfff003ff)
private def wire62259 : T := (((((((0xe5795e : T) <<< 32) ||| 0x5795e579) <<< 32) ||| 0x5fffff00) <<< 32) ||| 0x3ff003ff)
private def wire62532 : T := (((((((0xe8ba2e : T) <<< 32) ||| 0x8ba2e8ba) <<< 32) ||| 0x2ffc00ff) <<< 32) ||| 0xc0000000)
private def wire62543 : T := (((((((0xe8fa3e : T) <<< 32) ||| 0x8fa3e8fa) <<< 32) ||| 0x3ffc00ff) <<< 32) ||| 0xc00fffff)
private def wire62564 : T := (((((((0xe8ba2e : T) <<< 32) ||| 0x8ba2e8ba) <<< 32) ||| 0x2ffc00ff) <<< 32) ||| 0xfff00000)
private def wire62708 : T := (((((((0xebbaee : T) <<< 32) ||| 0xbbaeebba) <<< 32) ||| 0xeffc00ff) <<< 32) ||| 0xfff00000)
private def wire62805 : T := (((((((0xe9fa7e : T) <<< 32) ||| 0x9fa7e9fa) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xc0000000)
private def wire63078 : T := (((((((0xecbb2e : T) <<< 32) ||| 0xcbb2ecbb) <<< 32) ||| 0x2ffc00ff) <<< 32) ||| 0xfff003ff)
private def wire63351 : T := (((((((0xedfb7e : T) <<< 32) ||| 0xdfb7edfb) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xfff003ff)
private def wire63624 : T := (((((((0xf23c8f : T) <<< 32) ||| 0x23c8f23c) <<< 32) ||| 0x8ffc0000) <<< 32) ||| 0xffc00)
private def wire63626 : T := (((((((0xf23c8f : T) <<< 32) ||| 0x23c8f23c) <<< 32) ||| 0x8ffc0000) <<< 32) ||| 0xfffff)
private def wire63631 : T := (((((((0xf2fcbf : T) <<< 32) ||| 0x2fcbf2fc) <<< 32) ||| 0xbffc0000) <<< 32) ||| 0xfffff)
private def wire63736 : T := (((((((0xf33ccf : T) <<< 32) ||| 0x33ccf33c) <<< 32) ||| 0xcffc00ff) <<< 32) ||| 0xfffffc00)
private def wire63897 : T := (((((((0xf37cdf : T) <<< 32) ||| 0x37cdf37c) <<< 32) ||| 0xdfffff00) <<< 32) ||| 0xffc00)
private def wire64170 : T := (((((((0xf63d8f : T) <<< 32) ||| 0x63d8f63d) <<< 32) ||| 0x8ffc0000) <<< 32) ||| 0x3fffffff)
private def wire64443 : T := (((((((0xf77ddf : T) <<< 32) ||| 0x77ddf77d) <<< 32) ||| 0xdfffff00) <<< 32) ||| 0x3fffffff)
private def wire64716 : T := (((((((0xfabeaf : T) <<< 32) ||| 0xabeafabe) <<< 32) ||| 0xaffc00ff) <<< 32) ||| 0xc00ffc00)
private def wire64989 : T := (((((((0xfbfeff : T) <<< 32) ||| 0xbfeffbfe) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc00ffc00)
private def wire65280 : T := (((((((0xfc3f0f : T) <<< 32) ||| 0xc3f0fc3f) <<< 32) ||| 0xfffff00) <<< 32) ||| 0x0)
private def wire65282 : T := (((((((0xfc3f0f : T) <<< 32) ||| 0xc3f0fc3f) <<< 32) ||| 0xfffff00) <<< 32) ||| 0x3ff)
private def wire65284 : T := (((((((0xfcbf2f : T) <<< 32) ||| 0xcbf2fcbf) <<< 32) ||| 0x2fffff00) <<< 32) ||| 0x0)
private def wire65291 : T := (((((((0xfc7f1f : T) <<< 32) ||| 0xc7f1fc7f) <<< 32) ||| 0x1fffff00) <<< 32) ||| 0xfffff)
private def wire65293 : T := (((((((0xfcff3f : T) <<< 32) ||| 0xcff3fcff) <<< 32) ||| 0x3fffff00) <<< 32) ||| 0xffc00)
private def wire65295 : T := (((((((0xfcff3f : T) <<< 32) ||| 0xcff3fcff) <<< 32) ||| 0x3fffff00) <<< 32) ||| 0xfffff)
private def wire65312 : T := (((((((0xfc3f0f : T) <<< 32) ||| 0xc3f0fc3f) <<< 32) ||| 0xfffff00) <<< 32) ||| 0x3ff00000)
private def wire65314 : T := (((((((0xfc3f0f : T) <<< 32) ||| 0xc3f0fc3f) <<< 32) ||| 0xfffff00) <<< 32) ||| 0x3ff003ff)
private def wire65327 : T := (((((((0xfcff3f : T) <<< 32) ||| 0xcff3fcff) <<< 32) ||| 0x3fffff00) <<< 32) ||| 0x3fffffff)
private def wire65348 : T := (((((((0xfcbf2f : T) <<< 32) ||| 0xcbf2fcbf) <<< 32) ||| 0x2fffffff) <<< 32) ||| 0xc0000000)
private def wire65380 : T := (((((((0xfcbf2f : T) <<< 32) ||| 0xcbf2fcbf) <<< 32) ||| 0x2fffffff) <<< 32) ||| 0xfff00000)
private def wire65382 : T := (((((((0xfcbf2f : T) <<< 32) ||| 0xcbf2fcbf) <<< 32) ||| 0x2fffffff) <<< 32) ||| 0xfff003ff)
private def wire65392 : T := (((((((0xfd3f4f : T) <<< 32) ||| 0xd3f4fd3f) <<< 32) ||| 0x4fffffff) <<< 32) ||| 0xfff00000)
private def wire65396 : T := (((((((0xfdbf6f : T) <<< 32) ||| 0xdbf6fdbf) <<< 32) ||| 0x6fffffff) <<< 32) ||| 0xfff00000)
private def wire65407 : T := (((((((0xfdff7f : T) <<< 32) ||| 0xdff7fdff) <<< 32) ||| 0x7fffffff) <<< 32) ||| 0xffffffff)
private def wire65408 : T := (((((((0xfe3f8f : T) <<< 32) ||| 0xe3f8fe3f) <<< 32) ||| 0x8fffff00) <<< 32) ||| 0x0)
private def wire65412 : T := (((((((0xfebfaf : T) <<< 32) ||| 0xebfafebf) <<< 32) ||| 0xafffff00) <<< 32) ||| 0x0)
private def wire65416 : T := (((((((0xfe3f8f : T) <<< 32) ||| 0xe3f8fe3f) <<< 32) ||| 0x8fffff00) <<< 32) ||| 0xffc00)
private def wire65418 : T := (((((((0xfe3f8f : T) <<< 32) ||| 0xe3f8fe3f) <<< 32) ||| 0x8fffff00) <<< 32) ||| 0xfffff)
private def wire65419 : T := (((((((0xfe7f9f : T) <<< 32) ||| 0xe7f9fe7f) <<< 32) ||| 0x9fffff00) <<< 32) ||| 0xfffff)
private def wire65423 : T := (((((((0xfeffbf : T) <<< 32) ||| 0xeffbfeff) <<< 32) ||| 0xbfffff00) <<< 32) ||| 0xfffff)
private def wire65450 : T := (((((((0xfe3f8f : T) <<< 32) ||| 0xe3f8fe3f) <<< 32) ||| 0x8fffff00) <<< 32) ||| 0x3fffffff)
private def wire65484 : T := (((((((0xfebfaf : T) <<< 32) ||| 0xebfafebf) <<< 32) ||| 0xafffffff) <<< 32) ||| 0xc00ffc00)
private def wire65488 : T := (((((((0xff3fcf : T) <<< 32) ||| 0xf3fcff3f) <<< 32) ||| 0xcfffffff) <<< 32) ||| 0xc0000000)
private def wire65503 : T := (((((((0xffffff : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xc00fffff)
private def wire65520 : T := (((((((0xff3fcf : T) <<< 32) ||| 0xf3fcff3f) <<< 32) ||| 0xcfffffff) <<< 32) ||| 0xfff00000)
private def wire65522 : T := (((((((0xff3fcf : T) <<< 32) ||| 0xf3fcff3f) <<< 32) ||| 0xcfffffff) <<< 32) ||| 0xfff003ff)
private def wire65524 : T := (((((((0xffbfef : T) <<< 32) ||| 0xfbfeffbf) <<< 32) ||| 0xefffffff) <<< 32) ||| 0xfff00000)
private def wire65531 : T := (((((((0xff7fdf : T) <<< 32) ||| 0xf7fdff7f) <<< 32) ||| 0xdfffffff) <<< 32) ||| 0xffffffff)
private def wire65533 : T := (((((((0xffffff : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xfffffc00)
private def wire65535 : T := (((((((0xffffff : T) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffffffff)

-- Every listed set is checked against every possible next output and every reuse of its inputs.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def layer1 : List (List T) := []
private theorem good1 (w : List T) (h : w ∈ layer1) : ¬ Need 1 w.toFinset := by simp [layer1] at h
private def chunk2_0 : List (List T) := [[wire123,wire4369],
  [wire127,wire4373],
  [wire251,wire4497],
  [wire255,wire4501]]
private def pool2_0 : List (List (List T)) := []
private theorem checked2_0 : ∀ w ∈ chunk2_0, ¬ Need 2 w.toFinset := by
  have h : chunk2_0.all (routes 1 pool2_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool2_0] at hv
private def chunk2_1 : List (List T) := [[wire4369,wire65412],
  [wire4373,wire65408],
  [wire4381,wire65416],
  [wire4383,wire65418]]
private def pool2_1 : List (List (List T)) := []
private theorem checked2_1 : ∀ w ∈ chunk2_1, ¬ Need 2 w.toFinset := by
  have h : chunk2_1.all (routes 1 pool2_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool2_1] at hv
private def chunk2_2 : List (List T) := [[wire4497,wire65284],
  [wire4501,wire65280],
  [wire4561,wire65348],
  [wire4593,wire65380]]
private def pool2_2 : List (List (List T)) := []
private theorem checked2_2 : ∀ w ∈ chunk2_2, ¬ Need 2 w.toFinset := by
  have h : chunk2_2.all (routes 1 pool2_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool2_2] at hv
private def chunk2_3 : List (List T) := [[wire8810,wire52479],
  [wire17519,wire43770],
  [wire26223,wire35066],
  [wire60974,wire65348]]
private def pool2_3 : List (List (List T)) := []
private theorem checked2_3 : ∀ w ∈ chunk2_3, ¬ Need 2 w.toFinset := by
  have h : chunk2_3.all (routes 1 pool2_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool2_3] at hv
private def chunk2_4 : List (List T) := [[wire61154,wire65416]]
private def pool2_4 : List (List (List T)) := []
private theorem checked2_4 : ∀ w ∈ chunk2_4, ¬ Need 2 w.toFinset := by
  have h : chunk2_4.all (routes 1 pool2_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool2_4] at hv
#print axioms checked2_4
private def chunk3_0 : List (List T) := [[wire2,wire4383,wire65416],
  [wire2,wire26223,wire35064],
  [wire4,wire127,wire4369],
  [wire4,wire255,wire4497]]
private def pool3_0 : List (List (List T)) := [chunk2_0, chunk2_1, chunk2_3]
private theorem checked3_0 : ∀ w ∈ chunk3_0, ¬ Need 3 w.toFinset := by
  have h : chunk3_0.all (routes 2 pool3_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked2_0 _ hm
  · exact checked2_1 _ hm
  · exact checked2_3 _ hm
private def chunk3_1 : List (List T) := [[wire4,wire4369,wire65408],
  [wire4,wire4497,wire65280],
  [wire11,wire112,wire4369],
  [wire11,wire240,wire4497]]
private def pool3_1 : List (List (List T)) := [chunk2_0, chunk2_1, chunk2_2]
private theorem checked3_1 : ∀ w ∈ chunk3_1, ¬ Need 3 w.toFinset := by
  have h : chunk3_1.all (routes 2 pool3_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked2_0 _ hm
  · exact checked2_1 _ hm
  · exact checked2_2 _ hm
private def chunk3_2 : List (List T) := [[wire11,wire4369,wire65423],
  [wire11,wire26214,wire35064],
  [wire11,wire35064,wire39321],
  [wire12,wire4369,wire65416]]
private def pool3_2 : List (List (List T)) := [chunk2_1]
private theorem checked3_2 : ∀ w ∈ chunk3_2, ¬ Need 3 w.toFinset := by
  have h : chunk3_2.all (routes 2 pool3_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
private def chunk3_3 : List (List T) := [[wire13,wire4369,wire65416],
  [wire15,wire112,wire4373],
  [wire15,wire116,wire4369],
  [wire15,wire240,wire4501]]
private def pool3_3 : List (List (List T)) := [chunk2_0, chunk2_1]
private theorem checked3_3 : ∀ w ∈ chunk3_3, ¬ Need 3 w.toFinset := by
  have h : chunk3_3.all (routes 2 pool3_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked2_0 _ hm
  · exact checked2_1 _ hm
private def chunk3_4 : List (List T) := [[wire15,wire244,wire4497],
  [wire15,wire4369,wire65418],
  [wire15,wire4369,wire65419],
  [wire15,wire4373,wire65416]]
private def pool3_4 : List (List (List T)) := [chunk2_1]
private theorem checked3_4 : ∀ w ∈ chunk3_4, ¬ Need 3 w.toFinset := by
  have h : chunk3_4.all (routes 2 pool3_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
private def chunk3_5 : List (List T) := [[wire15,wire4373,wire65423],
  [wire15,wire17508,wire43770],
  [wire15,wire26210,wire35064],
  [wire15,wire26214,wire35066]]
private def pool3_5 : List (List (List T)) := [chunk2_3]
private theorem checked3_5 : ∀ w ∈ chunk3_5, ¬ Need 3 w.toFinset := by
  have h : chunk3_5.all (routes 2 pool3_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_3 _ hm
private def chunk3_6 : List (List T) := [[wire15,wire26214,wire35068],
  [wire15,wire35064,wire39325],
  [wire15,wire35066,wire39321],
  [wire15,wire35066,wire39323]]
private def pool3_6 : List (List (List T)) := []
private theorem checked3_6 : ∀ w ∈ chunk3_6, ¬ Need 3 w.toFinset := by
  have h : chunk3_6.all (routes 2 pool3_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_6] at hv
private def chunk3_7 : List (List T) := [[wire15,wire35068,wire39321],
  [wire32,wire4593,wire65348],
  [wire32,wire17487,wire43770],
  [wire47,wire17476,wire43770]]
private def pool3_7 : List (List (List T)) := [chunk2_2, chunk2_3]
private theorem checked3_7 : ∀ w ∈ chunk3_7, ¬ Need 3 w.toFinset := by
  have h : chunk3_7.all (routes 2 pool3_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked2_2 _ hm
  · exact checked2_3 _ hm
private def chunk3_8 : List (List T) := [[wire72,wire8738,wire52479],
  [wire112,wire4369,wire65524],
  [wire112,wire17487,wire21845],
  [wire112,wire17487,wire43690]]
private def pool3_8 : List (List (List T)) := [chunk2_3]
private theorem checked3_8 : ∀ w ∈ chunk3_8, ¬ Need 3 w.toFinset := by
  have h : chunk3_8.all (routes 2 pool3_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_3 _ hm
private def chunk3_9 : List (List T) := [[wire119,wire4383,wire8738],
  [wire128,wire251,wire4369],
  [wire128,wire255,wire4373],
  [wire128,wire4369,wire65284]]
private def pool3_9 : List (List (List T)) := [chunk2_0, chunk2_1, chunk2_2]
private theorem checked3_9 : ∀ w ∈ chunk3_9, ¬ Need 3 w.toFinset := by
  have h : chunk3_9.all (routes 2 pool3_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked2_0 _ hm
  · exact checked2_1 _ hm
  · exact checked2_2 _ hm
private def chunk3_10 : List (List T) := [[wire128,wire4373,wire65280],
  [wire132,wire255,wire4369],
  [wire132,wire4369,wire65280],
  [wire139,wire240,wire4369]]
private def pool3_10 : List (List (List T)) := [chunk2_0, chunk2_1, chunk2_2]
private theorem checked3_10 : ∀ w ∈ chunk3_10, ¬ Need 3 w.toFinset := by
  have h : chunk3_10.all (routes 2 pool3_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked2_0 _ hm
  · exact checked2_1 _ hm
  · exact checked2_2 _ hm
private def chunk3_11 : List (List T) := [[wire143,wire240,wire4373],
  [wire143,wire244,wire4369],
  [wire159,wire4593,wire17476],
  [wire187,wire4593,wire8738]]
private def pool3_11 : List (List (List T)) := []
private theorem checked3_11 : ∀ w ∈ chunk3_11, ¬ Need 3 w.toFinset := by
  have h : chunk3_11.all (routes 2 pool3_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_11] at hv
private def chunk3_12 : List (List T) := [[wire192,wire4369,wire65348],
  [wire208,wire4369,wire65348],
  [wire223,wire4593,wire17476],
  [wire240,wire4369,wire65380]]
private def pool3_12 : List (List (List T)) := [chunk2_2]
private theorem checked3_12 : ∀ w ∈ chunk3_12, ¬ Need 3 w.toFinset := by
  have h : chunk3_12.all (routes 2 pool3_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_2 _ hm
private def chunk3_13 : List (List T) := [[wire240,wire4369,wire65396],
  [wire240,wire4497,wire65348],
  [wire240,wire4497,wire65524],
  [wire240,wire17487,wire21973]]
private def pool3_13 : List (List (List T)) := []
private theorem checked3_13 : ∀ w ∈ chunk3_13, ¬ Need 3 w.toFinset := by
  have h : chunk3_13.all (routes 2 pool3_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_13] at hv
private def chunk3_14 : List (List T) := [[wire240,wire17487,wire43562],
  [wire240,wire17519,wire21845],
  [wire240,wire17519,wire21877],
  [wire240,wire17519,wire43690]]
private def pool3_14 : List (List (List T)) := [chunk2_3]
private theorem checked3_14 : ∀ w ∈ chunk3_14, ¬ Need 3 w.toFinset := by
  have h : chunk3_14.all (routes 2 pool3_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_3 _ hm
private def chunk3_15 : List (List T) := [[wire240,wire17615,wire21845],
  [wire240,wire17615,wire43690],
  [wire240,wire26223,wire34954],
  [wire242,wire26223,wire34952]]
private def pool3_15 : List (List (List T)) := [chunk2_3]
private theorem checked3_15 : ∀ w ∈ chunk3_15, ¬ Need 3 w.toFinset := by
  have h : chunk3_15.all (routes 2 pool3_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_3 _ hm
private def chunk3_16 : List (List T) := [[wire245,wire4383,wire34952],
  [wire253,wire4383,wire34952],
  [wire255,wire4381,wire34952],
  [wire255,wire4383,wire34954]]
private def pool3_16 : List (List (List T)) := []
private theorem checked3_16 : ∀ w ∈ chunk3_16, ¬ Need 3 w.toFinset := by
  have h : chunk3_16.all (routes 2 pool3_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_16] at hv
private def chunk3_17 : List (List T) := [[wire255,wire4561,wire17476],
  [wire255,wire4593,wire17508],
  [wire255,wire13119,wire21845],
  [wire255,wire13119,wire43690]]
private def pool3_17 : List (List (List T)) := []
private theorem checked3_17 : ∀ w ∈ chunk3_17, ¬ Need 3 w.toFinset := by
  have h : chunk3_17.all (routes 2 pool3_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_17] at hv
private def chunk3_18 : List (List T) := [[wire255,wire13299,wire26214],
  [wire255,wire13299,wire39321],
  [wire255,wire17476,wire60974],
  [wire255,wire34952,wire61154]]
private def pool3_18 : List (List (List T)) := []
private theorem checked3_18 : ∀ w ∈ chunk3_18, ¬ Need 3 w.toFinset := by
  have h : chunk3_18.all (routes 2 pool3_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_18] at hv
private def chunk3_19 : List (List T) := [[wire3840,wire4369,wire61572],
  [wire3840,wire4373,wire61568],
  [wire3840,wire4381,wire63624],
  [wire3840,wire4383,wire63626]]
private def pool3_19 : List (List (List T)) := [chunk2_1]
private theorem checked3_19 : ∀ w ∈ chunk3_19, ¬ Need 3 w.toFinset := by
  have h : chunk3_19.all (routes 2 pool3_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
private def chunk3_20 : List (List T) := [[wire3840,wire4497,wire61444],
  [wire3840,wire4501,wire61440],
  [wire3840,wire4561,wire62532],
  [wire3840,wire4593,wire62564]]
private def pool3_20 : List (List (List T)) := [chunk2_2]
private theorem checked3_20 : ∀ w ∈ chunk3_20, ¬ Need 3 w.toFinset := by
  have h : chunk3_20.all (routes 2 pool3_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_2 _ hm
private def chunk3_21 : List (List T) := [[wire3840,wire60974,wire62532],
  [wire3840,wire61154,wire63624],
  [wire3842,wire4383,wire63624],
  [wire3844,wire4369,wire61568]]
private def pool3_21 : List (List (List T)) := [chunk2_1, chunk2_3, chunk2_4]
private theorem checked3_21 : ∀ w ∈ chunk3_21, ¬ Need 3 w.toFinset := by
  have h : chunk3_21.all (routes 2 pool3_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked2_1 _ hm
  · exact checked2_3 _ hm
  · exact checked2_4 _ hm
private def chunk3_22 : List (List T) := [[wire3844,wire4497,wire61440],
  [wire3872,wire4593,wire62532],
  [wire3968,wire4369,wire61444],
  [wire3968,wire4373,wire61440]]
private def pool3_22 : List (List (List T)) := [chunk2_1, chunk2_2]
private theorem checked3_22 : ∀ w ∈ chunk3_22, ¬ Need 3 w.toFinset := by
  have h : chunk3_22.all (routes 2 pool3_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked2_1 _ hm
  · exact checked2_2 _ hm
private def chunk3_23 : List (List T) := [[wire3972,wire4369,wire61440],
  [wire4352,wire8738,wire17487,wire35064],
  [wire4369,wire65327,wire65348],
  [wire4369,wire65416,wire65522]]
private def pool3_23 : List (List (List T)) := [chunk2_1]
private theorem checked3_23 : ∀ w ∈ chunk3_23, ¬ Need 3 w.toFinset := by
  have h : chunk3_23.all (routes 2 pool3_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
private def chunk3_24 : List (List T) := [[wire4369,wire65423,wire65524],
  [wire4381,wire34952,wire65280],
  [wire4381,wire36744,wire61440],
  [wire4383,wire8738,wire65416]]
private def pool3_24 : List (List (List T)) := [chunk2_1]
private theorem checked3_24 : ∀ w ∈ chunk3_24, ¬ Need 3 w.toFinset := by
  have h : chunk3_24.all (routes 2 pool3_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
private def chunk3_25 : List (List T) := [[wire4383,wire12066,wire65416],
  [wire4383,wire21845,wire65416],
  [wire4383,wire34952,wire65282],
  [wire4383,wire34954,wire65280]]
private def pool3_25 : List (List (List T)) := [chunk2_1]
private theorem checked3_25 : ∀ w ∈ chunk3_25, ¬ Need 3 w.toFinset := by
  have h : chunk3_25.all (routes 2 pool3_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
private def chunk3_26 : List (List T) := [[wire4383,wire36744,wire61442],
  [wire4383,wire36746,wire61440],
  [wire4383,wire43690,wire65416],
  [wire4383,wire44970,wire65416]]
private def pool3_26 : List (List (List T)) := [chunk2_1]
private theorem checked3_26 : ∀ w ∈ chunk3_26, ¬ Need 3 w.toFinset := by
  have h : chunk3_26.all (routes 2 pool3_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
private def chunk3_27 : List (List T) := [[wire4383,wire56797,wire65416],
  [wire4383,wire61986,wire65416],
  [wire4383,wire64170,wire65416],
  [wire4383,wire65314,wire65416]]
private def pool3_27 : List (List (List T)) := [chunk2_1]
private theorem checked3_27 : ∀ w ∈ chunk3_27, ¬ Need 3 w.toFinset := by
  have h : chunk3_27.all (routes 2 pool3_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_1 _ hm
private def chunk3_28 : List (List T) := [[wire4383,wire65416,wire65450],
  [wire4561,wire17476,wire65280],
  [wire4561,wire20292,wire61440],
  [wire4593,wire8738,wire65348]]
private def pool3_28 : List (List (List T)) := [chunk2_2]
private theorem checked3_28 : ∀ w ∈ chunk3_28, ¬ Need 3 w.toFinset := by
  have h : chunk3_28.all (routes 2 pool3_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_2 _ hm
private def chunk3_29 : List (List T) := [[wire4593,wire12066,wire65348],
  [wire4593,wire17476,wire65312],
  [wire4593,wire17508,wire65280],
  [wire4593,wire20292,wire61472]]
private def pool3_29 : List (List (List T)) := [chunk2_2]
private theorem checked3_29 : ∀ w ∈ chunk3_29, ¬ Need 3 w.toFinset := by
  have h : chunk3_29.all (routes 2 pool3_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_2 _ hm
private def chunk3_30 : List (List T) := [[wire4593,wire20324,wire61440],
  [wire4593,wire26214,wire65348],
  [wire4593,wire28518,wire65348],
  [wire4593,wire39321,wire65348]]
private def pool3_30 : List (List (List T)) := [chunk2_2]
private theorem checked3_30 : ∀ w ∈ chunk3_30, ¬ Need 3 w.toFinset := by
  have h : chunk3_30.all (routes 2 pool3_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_2 _ hm
private def chunk3_31 : List (List T) := [[wire4593,wire56797,wire65348],
  [wire4593,wire61986,wire65348],
  [wire4593,wire63078,wire65348],
  [wire4593,wire65314,wire65348]]
private def pool3_31 : List (List (List T)) := [chunk2_2]
private theorem checked3_31 : ∀ w ∈ chunk3_31, ¬ Need 3 w.toFinset := by
  have h : chunk3_31.all (routes 2 pool3_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_2 _ hm
private def chunk3_32 : List (List T) := [[wire4593,wire65348,wire65382],
  [wire8738,wire13119,wire65416],
  [wire8738,wire13299,wire65348],
  [wire8738,wire17487,wire30471]]
private def pool3_32 : List (List (List T)) := []
private theorem checked3_32 : ∀ w ∈ chunk3_32, ¬ Need 3 w.toFinset := by
  have h : chunk3_32.all (routes 2 pool3_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_32] at hv
private def chunk3_33 : List (List T) := [[wire8738,wire17487,wire35064],
  [wire8738,wire17487,wire35066],
  [wire8738,wire17519,wire35064],
  [wire8738,wire30471,wire48048]]
private def pool3_33 : List (List (List T)) := [chunk2_3]
private theorem checked3_33 : ∀ w ∈ chunk3_33, ¬ Need 3 w.toFinset := by
  have h : chunk3_33.all (routes 2 pool3_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_3 _ hm
private def chunk3_34 : List (List T) := [[wire8738,wire35064,wire48048],
  [wire8738,wire60942,wire65348],
  [wire8738,wire61152,wire65416],
  [wire8746,wire17487,wire35064]]
private def pool3_34 : List (List (List T)) := [chunk2_3, chunk2_4]
private theorem checked3_34 : ∀ w ∈ chunk3_34, ¬ Need 3 w.toFinset := by
  have h : chunk3_34.all (routes 2 pool3_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked2_3 _ hm
  · exact checked2_4 _ hm
private def chunk3_35 : List (List T) := [[wire8751,wire17476,wire35066],
  [wire8802,wire17487,wire35064],
  [wire8810,wire17487,wire35064],
  [wire8946,wire17519,wire34952]]
private def pool3_35 : List (List (List T)) := [chunk2_3]
private theorem checked3_35 : ∀ w ∈ chunk3_35, ¬ Need 3 w.toFinset := by
  have h : chunk3_35.all (routes 2 pool3_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_3 _ hm
private def chunk3_36 : List (List T) := [[wire13119,wire21845,wire65280],
  [wire13119,wire43690,wire65280],
  [wire13299,wire26214,wire65280],
  [wire13299,wire39321,wire65280]]
private def pool3_36 : List (List (List T)) := []
private theorem checked3_36 : ∀ w ∈ chunk3_36, ¬ Need 3 w.toFinset := by
  have h : chunk3_36.all (routes 2 pool3_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool3_36] at hv
private def chunk3_37 : List (List T) := [[wire17476,wire60974,wire65280],
  [wire17487,wire21845,wire65423],
  [wire17487,wire30471,wire56797],
  [wire17487,wire35064,wire56797]]
private def pool3_37 : List (List (List T)) := [chunk2_3]
private theorem checked3_37 : ∀ w ∈ chunk3_37, ¬ Need 3 w.toFinset := by
  have h : chunk3_37.all (routes 2 pool3_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_3 _ hm
private def chunk3_38 : List (List T) := [[wire17487,wire43562,wire65295],
  [wire17487,wire43690,wire65423],
  [wire20292,wire60974,wire61440],
  [wire26210,wire35064,wire65520]]
private def pool3_38 : List (List (List T)) := [chunk2_3]
private theorem checked3_38 : ∀ w ∈ chunk3_38, ¬ Need 3 w.toFinset := by
  have h : chunk3_38.all (routes 2 pool3_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_38,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_3 _ hm
private def chunk3_39 : List (List T) := [[wire26214,wire35064,wire65524],
  [wire34952,wire61154,wire65280],
  [wire35064,wire39321,wire65524],
  [wire35064,wire48048,wire56797]]
private def pool3_39 : List (List (List T)) := [chunk2_4]
private theorem checked3_39 : ∀ w ∈ chunk3_39, ¬ Need 3 w.toFinset := by
  have h : chunk3_39.all (routes 2 pool3_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_4 _ hm
private def chunk3_40 : List (List T) := [[wire36744,wire61154,wire61440]]
private def pool3_40 : List (List (List T)) := [chunk2_4]
private theorem checked3_40 : ∀ w ∈ chunk3_40, ¬ Need 3 w.toFinset := by
  have h : chunk3_40.all (routes 2 pool3_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool3_40,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked2_4 _ hm
#print axioms checked3_40
private def chunk4_0 : List (List T) := [[wire0,wire8738,wire17487,wire35064],
  [wire1,wire8738,wire17487,wire35064],
  [wire2,wire15,wire4369,wire65416],
  [wire2,wire15,wire26214,wire35064]]
private def pool4_0 : List (List (List T)) := [chunk3_0, chunk3_4, chunk3_5, chunk3_33]
private theorem checked4_0 : ∀ w ∈ chunk4_0, ¬ Need 4 w.toFinset := by
  have h : chunk4_0.all (routes 3 pool4_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
  · exact checked3_33 _ hm
private def chunk4_1 : List (List T) := [[wire2,wire15,wire35064,wire39321],
  [wire2,wire240,wire26223,wire34952],
  [wire2,wire255,wire4383,wire34952],
  [wire2,wire3840,wire4383,wire63624]]
private def pool4_1 : List (List (List T)) := [chunk3_0, chunk3_6, chunk3_15, chunk3_16, chunk3_19, chunk3_21]
private theorem checked4_1 : ∀ w ∈ chunk4_1, ¬ Need 4 w.toFinset := by
  have h : chunk4_1.all (routes 3 pool4_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_6 _ hm
  · exact checked3_15 _ hm
  · exact checked3_16 _ hm
  · exact checked3_19 _ hm
  · exact checked3_21 _ hm
private def chunk4_2 : List (List T) := [[wire2,wire4383,wire34952,wire65280],
  [wire2,wire4383,wire36744,wire61440],
  [wire2,wire8738,wire17487,wire35064],
  [wire2,wire8751,wire17476,wire35064]]
private def pool4_2 : List (List (List T)) := [chunk3_0, chunk3_25, chunk3_26, chunk3_33, chunk3_35]
private theorem checked4_2 : ∀ w ∈ chunk4_2, ¬ Need 4 w.toFinset := by
  have h : chunk4_2.all (routes 3 pool4_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_25 _ hm
  · exact checked3_26 _ hm
  · exact checked3_33 _ hm
  · exact checked3_35 _ hm
private def chunk4_3 : List (List T) := [[wire4,wire15,wire112,wire4369],
  [wire4,wire15,wire240,wire4497],
  [wire4,wire15,wire4369,wire65416],
  [wire4,wire15,wire4369,wire65423]]
private def pool4_3 : List (List (List T)) := [chunk3_0, chunk3_3, chunk3_4, chunk3_5]
private theorem checked4_3 : ∀ w ∈ chunk4_3, ¬ Need 4 w.toFinset := by
  have h : chunk4_3.all (routes 3 pool4_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_3 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
private def chunk4_4 : List (List T) := [[wire4,wire15,wire26214,wire35064],
  [wire4,wire15,wire35064,wire39321],
  [wire4,wire128,wire255,wire4369],
  [wire4,wire128,wire4369,wire65280]]
private def pool4_4 : List (List (List T)) := [chunk3_0, chunk3_1, chunk3_6, chunk3_7, chunk3_9, chunk3_10]
private theorem checked4_4 : ∀ w ∈ chunk4_4, ¬ Need 4 w.toFinset := by
  have h : chunk4_4.all (routes 3 pool4_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_1 _ hm
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
  · exact checked3_9 _ hm
  · exact checked3_10 _ hm
private def chunk4_5 : List (List T) := [[wire4,wire143,wire240,wire4369],
  [wire4,wire3840,wire4369,wire61568],
  [wire4,wire3840,wire4497,wire61440],
  [wire4,wire3968,wire4369,wire61440]]
private def pool4_5 : List (List (List T)) := [chunk3_1, chunk3_11, chunk3_19, chunk3_20, chunk3_21, chunk3_22, chunk3_23]
private theorem checked4_5 : ∀ w ∈ chunk4_5, ¬ Need 4 w.toFinset := by
  have h : chunk4_5.all (routes 3 pool4_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_1 _ hm
  · exact checked3_11 _ hm
  · exact checked3_19 _ hm
  · exact checked3_20 _ hm
  · exact checked3_21 _ hm
  · exact checked3_22 _ hm
  · exact checked3_23 _ hm
private def chunk4_6 : List (List T) := [[wire4,wire8738,wire17487,wire35064],
  [wire5,wire240,wire4383,wire34952],
  [wire8,wire8738,wire17487,wire35064],
  [wire10,wire240,wire4369,wire34959]]
private def pool4_6 : List (List (List T)) := [chunk3_16, chunk3_33, chunk3_34]
private theorem checked4_6 : ∀ w ∈ chunk4_6, ¬ Need 4 w.toFinset := by
  have h : chunk4_6.all (routes 3 pool4_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_16 _ hm
  · exact checked3_33 _ hm
  · exact checked3_34 _ hm
private def chunk4_7 : List (List T) := [[wire11,wire128,wire240,wire4369],
  [wire11,wire240,wire4369,wire26214],
  [wire11,wire240,wire4369,wire30583],
  [wire11,wire240,wire4369,wire34952]]
private def pool4_7 : List (List (List T)) := [chunk3_1, chunk3_9, chunk3_10]
private theorem checked4_7 : ∀ w ∈ chunk4_7, ¬ Need 4 w.toFinset := by
  have h : chunk4_7.all (routes 3 pool4_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_1 _ hm
  · exact checked3_9 _ hm
  · exact checked3_10 _ hm
private def chunk4_8 : List (List T) := [[wire11,wire240,wire4369,wire34955],
  [wire11,wire240,wire4369,wire34959],
  [wire11,wire240,wire4369,wire36744],
  [wire11,wire240,wire4369,wire39321]]
private def pool4_8 : List (List (List T)) := []
private theorem checked4_8 : ∀ w ∈ chunk4_8, ¬ Need 4 w.toFinset := by
  have h : chunk4_8.all (routes 3 pool4_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_8] at hv
private def chunk4_9 : List (List T) := [[wire11,wire240,wire4369,wire63624],
  [wire11,wire240,wire26214,wire34952],
  [wire11,wire240,wire34952,wire39321],
  [wire11,wire240,wire34952,wire61166]]
private def pool4_9 : List (List (List T)) := [chunk3_2]
private theorem checked4_9 : ∀ w ∈ chunk4_9, ¬ Need 4 w.toFinset := by
  have h : chunk4_9.all (routes 3 pool4_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_2 _ hm
private def chunk4_10 : List (List T) := [[wire11,wire251,wire4369,wire34952],
  [wire11,wire4369,wire34952,wire35064],
  [wire11,wire4369,wire34952,wire65295],
  [wire11,wire8738,wire17476,wire35064]]
private def pool4_10 : List (List (List T)) := [chunk3_2, chunk3_33]
private theorem checked4_10 : ∀ w ∈ chunk4_10, ¬ Need 4 w.toFinset := by
  have h : chunk4_10.all (routes 3 pool4_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_33 _ hm
private def chunk4_11 : List (List T) := [[wire11,wire8738,wire35064,wire48059],
  [wire12,wire255,wire4369,wire34952],
  [wire12,wire3840,wire4369,wire63624],
  [wire12,wire4369,wire34952,wire65280]]
private def pool4_11 : List (List (List T)) := [chunk3_2, chunk3_16, chunk3_19, chunk3_24]
private theorem checked4_11 : ∀ w ∈ chunk4_11, ¬ Need 4 w.toFinset := by
  have h : chunk4_11.all (routes 3 pool4_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_16 _ hm
  · exact checked3_19 _ hm
  · exact checked3_24 _ hm
private def chunk4_12 : List (List T) := [[wire12,wire4369,wire36744,wire61440],
  [wire13,wire240,wire4383,wire34952],
  [wire13,wire255,wire4369,wire34952],
  [wire13,wire3840,wire4369,wire63624]]
private def pool4_12 : List (List (List T)) := [chunk3_2, chunk3_3, chunk3_16, chunk3_19, chunk3_24]
private theorem checked4_12 : ∀ w ∈ chunk4_12, ¬ Need 4 w.toFinset := by
  have h : chunk4_12.all (routes 3 pool4_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_3 _ hm
  · exact checked3_16 _ hm
  · exact checked3_19 _ hm
  · exact checked3_24 _ hm
private def chunk4_13 : List (List T) := [[wire13,wire4369,wire34952,wire65280],
  [wire13,wire4369,wire36744,wire61440],
  [wire15,wire32,wire17476,wire43770],
  [wire15,wire96,wire4369,wire17652]]
private def pool4_13 : List (List (List T)) := [chunk3_3, chunk3_5, chunk3_7, chunk3_24]
private theorem checked4_13 : ∀ w ∈ chunk4_13, ¬ Need 4 w.toFinset := by
  have h : chunk4_13.all (routes 3 pool4_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_3 _ hm
  · exact checked3_5 _ hm
  · exact checked3_7 _ hm
  · exact checked3_24 _ hm
private def chunk4_14 : List (List T) := [[wire15,wire112,wire4369,wire17476],
  [wire15,wire112,wire4369,wire17524],
  [wire15,wire112,wire4369,wire17652],
  [wire15,wire112,wire4369,wire20292]]
private def pool4_14 : List (List (List T)) := []
private theorem checked4_14 : ∀ w ∈ chunk4_14, ¬ Need 4 w.toFinset := by
  have h : chunk4_14.all (routes 3 pool4_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_14] at hv
private def chunk4_15 : List (List T) := [[wire15,wire112,wire4369,wire21845],
  [wire15,wire112,wire4369,wire43690],
  [wire15,wire112,wire4369,wire48059],
  [wire15,wire112,wire4369,wire62532]]
private def pool4_15 : List (List (List T)) := [chunk3_1]
private theorem checked4_15 : ∀ w ∈ chunk4_15, ¬ Need 4 w.toFinset := by
  have h : chunk4_15.all (routes 3 pool4_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_1 _ hm
private def chunk4_16 : List (List T) := [[wire15,wire112,wire17476,wire21845],
  [wire15,wire112,wire17476,wire43690],
  [wire15,wire112,wire17476,wire61166],
  [wire15,wire119,wire4369,wire8738]]
private def pool4_16 : List (List (List T)) := [chunk3_8, chunk3_9]
private theorem checked4_16 : ∀ w ∈ chunk4_16, ¬ Need 4 w.toFinset := by
  have h : chunk4_16.all (routes 3 pool4_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_9 _ hm
private def chunk4_17 : List (List T) := [[wire15,wire119,wire4369,wire17476],
  [wire15,wire127,wire4369,wire17476],
  [wire15,wire128,wire240,wire4373],
  [wire15,wire128,wire244,wire4369]]
private def pool4_17 : List (List (List T)) := [chunk3_0, chunk3_3, chunk3_4, chunk3_9, chunk3_11]
private theorem checked4_17 : ∀ w ∈ chunk4_17, ¬ Need 4 w.toFinset := by
  have h : chunk4_17.all (routes 3 pool4_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_3 _ hm
  · exact checked3_4 _ hm
  · exact checked3_9 _ hm
  · exact checked3_11 _ hm
private def chunk4_18 : List (List T) := [[wire15,wire132,wire240,wire4369],
  [wire15,wire144,wire4593,wire17476],
  [wire15,wire208,wire4593,wire17476],
  [wire15,wire240,wire4369,wire17508]]
private def pool4_18 : List (List (List T)) := [chunk3_3, chunk3_10, chunk3_11, chunk3_12]
private theorem checked4_18 : ∀ w ∈ chunk4_18, ¬ Need 4 w.toFinset := by
  have h : chunk4_18.all (routes 3 pool4_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_3 _ hm
  · exact checked3_10 _ hm
  · exact checked3_11 _ hm
  · exact checked3_12 _ hm
private def chunk4_19 : List (List T) := [[wire15,wire240,wire4369,wire17524],
  [wire15,wire240,wire4369,wire18020],
  [wire15,wire240,wire4369,wire20324],
  [wire15,wire240,wire4369,wire21877]]
private def pool4_19 : List (List (List T)) := []
private theorem checked4_19 : ∀ w ∈ chunk4_19, ¬ Need 4 w.toFinset := by
  have h : chunk4_19.all (routes 3 pool4_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_19] at hv
private def chunk4_20 : List (List T) := [[wire15,wire240,wire4369,wire25700],
  [wire15,wire240,wire4369,wire26212],
  [wire15,wire240,wire4369,wire30580],
  [wire15,wire240,wire4369,wire30581]]
private def pool4_20 : List (List (List T)) := []
private theorem checked4_20 : ∀ w ∈ chunk4_20, ¬ Need 4 w.toFinset := by
  have h : chunk4_20.all (routes 3 pool4_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_20] at hv
private def chunk4_21 : List (List T) := [[wire15,wire240,wire4369,wire34954],
  [wire15,wire240,wire4369,wire34955],
  [wire15,wire240,wire4369,wire35466],
  [wire15,wire240,wire4369,wire36746]]
private def pool4_21 : List (List (List T)) := []
private theorem checked4_21 : ∀ w ∈ chunk4_21, ¬ Need 4 w.toFinset := by
  have h : chunk4_21.all (routes 3 pool4_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_21] at hv
private def chunk4_22 : List (List T) := [[wire15,wire240,wire4369,wire39323],
  [wire15,wire240,wire4369,wire43146],
  [wire15,wire240,wire4369,wire43658],
  [wire15,wire240,wire4369,wire48011]]
private def pool4_22 : List (List (List T)) := []
private theorem checked4_22 : ∀ w ∈ chunk4_22, ¬ Need 4 w.toFinset := by
  have h : chunk4_22.all (routes 3 pool4_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_22] at hv
private def chunk4_23 : List (List T) := [[wire15,wire240,wire4369,wire48027],
  [wire15,wire240,wire4369,wire62564],
  [wire15,wire240,wire4369,wire63626],
  [wire15,wire240,wire4371,wire26214]]
private def pool4_23 : List (List (List T)) := []
private theorem checked4_23 : ∀ w ∈ chunk4_23, ¬ Need 4 w.toFinset := by
  have h : chunk4_23.all (routes 3 pool4_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_23] at hv
private def chunk4_24 : List (List T) := [[wire15,wire240,wire4371,wire34954],
  [wire15,wire240,wire4371,wire39321],
  [wire15,wire240,wire4373,wire26214],
  [wire15,wire240,wire4373,wire30583]]
private def pool4_24 : List (List (List T)) := [chunk3_3]
private theorem checked4_24 : ∀ w ∈ chunk4_24, ¬ Need 4 w.toFinset := by
  have h : chunk4_24.all (routes 3 pool4_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_3 _ hm
private def chunk4_25 : List (List T) := [[wire15,wire240,wire4373,wire34952],
  [wire15,wire240,wire4373,wire34956],
  [wire15,wire240,wire4373,wire34959],
  [wire15,wire240,wire4373,wire36744]]
private def pool4_25 : List (List (List T)) := []
private theorem checked4_25 : ∀ w ∈ chunk4_25, ¬ Need 4 w.toFinset := by
  have h : chunk4_25.all (routes 3 pool4_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_25] at hv
private def chunk4_26 : List (List T) := [[wire15,wire240,wire4373,wire39321],
  [wire15,wire240,wire4373,wire39325],
  [wire15,wire240,wire4373,wire63624],
  [wire15,wire240,wire4381,wire34952]]
private def pool4_26 : List (List (List T)) := [chunk3_16]
private theorem checked4_26 : ∀ w ∈ chunk4_26, ¬ Need 4 w.toFinset := by
  have h : chunk4_26.all (routes 3 pool4_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_16 _ hm
private def chunk4_27 : List (List T) := [[wire15,wire240,wire4383,wire34954],
  [wire15,wire240,wire4401,wire17508],
  [wire15,wire240,wire4401,wire21845],
  [wire15,wire240,wire4401,wire43690]]
private def pool4_27 : List (List (List T)) := [chunk3_16]
private theorem checked4_27 : ∀ w ∈ chunk4_27, ¬ Need 4 w.toFinset := by
  have h : chunk4_27.all (routes 3 pool4_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_16 _ hm
private def chunk4_28 : List (List T) := [[wire15,wire240,wire4497,wire17476],
  [wire15,wire240,wire4497,wire17604],
  [wire15,wire240,wire4497,wire17652],
  [wire15,wire240,wire4497,wire20292]]
private def pool4_28 : List (List (List T)) := []
private theorem checked4_28 : ∀ w ∈ chunk4_28, ¬ Need 4 w.toFinset := by
  have h : chunk4_28.all (routes 3 pool4_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_28] at hv
private def chunk4_29 : List (List T) := [[wire15,wire240,wire4497,wire21845],
  [wire15,wire240,wire4497,wire21973],
  [wire15,wire240,wire4497,wire43690],
  [wire15,wire240,wire4497,wire48059]]
private def pool4_29 : List (List (List T)) := [chunk3_1]
private theorem checked4_29 : ∀ w ∈ chunk4_29, ¬ Need 4 w.toFinset := by
  have h : chunk4_29.all (routes 3 pool4_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_1 _ hm
private def chunk4_30 : List (List T) := [[wire15,wire240,wire4497,wire62532],
  [wire15,wire240,wire4561,wire17476],
  [wire15,wire240,wire4593,wire17508],
  [wire15,wire240,wire13107,wire21845]]
private def pool4_30 : List (List (List T)) := [chunk3_17]
private theorem checked4_30 : ∀ w ∈ chunk4_30, ¬ Need 4 w.toFinset := by
  have h : chunk4_30.all (routes 3 pool4_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_17 _ hm
private def chunk4_31 : List (List T) := [[wire15,wire240,wire13107,wire26214],
  [wire15,wire240,wire13107,wire39321],
  [wire15,wire240,wire13107,wire43690],
  [wire15,wire240,wire13119,wire21845]]
private def pool4_31 : List (List (List T)) := [chunk3_17]
private theorem checked4_31 : ∀ w ∈ chunk4_31, ¬ Need 4 w.toFinset := by
  have h : chunk4_31.all (routes 3 pool4_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_17 _ hm
private def chunk4_32 : List (List T) := [[wire15,wire240,wire13119,wire43690],
  [wire15,wire240,wire13299,wire26214],
  [wire15,wire240,wire13299,wire39321],
  [wire15,wire240,wire17476,wire21973]]
private def pool4_32 : List (List (List T)) := [chunk3_13, chunk3_17, chunk3_18]
private theorem checked4_32 : ∀ w ∈ chunk4_32, ¬ Need 4 w.toFinset := by
  have h : chunk4_32.all (routes 3 pool4_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_13 _ hm
  · exact checked3_17 _ hm
  · exact checked3_18 _ hm
private def chunk4_33 : List (List T) := [[wire15,wire240,wire17476,wire43562],
  [wire15,wire240,wire17476,wire60974],
  [wire15,wire240,wire17476,wire61038],
  [wire15,wire240,wire17508,wire21845]]
private def pool4_33 : List (List (List T)) := [chunk3_14, chunk3_18]
private theorem checked4_33 : ∀ w ∈ chunk4_33, ¬ Need 4 w.toFinset := by
  have h : chunk4_33.all (routes 3 pool4_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_14 _ hm
  · exact checked3_18 _ hm
private def chunk4_34 : List (List T) := [[wire15,wire240,wire17508,wire21877],
  [wire15,wire240,wire17508,wire43690],
  [wire15,wire240,wire17508,wire61166],
  [wire15,wire240,wire17604,wire21845]]
private def pool4_34 : List (List (List T)) := [chunk3_5, chunk3_14, chunk3_15]
private theorem checked4_34 : ∀ w ∈ chunk4_34, ¬ Need 4 w.toFinset := by
  have h : chunk4_34.all (routes 3 pool4_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_5 _ hm
  · exact checked3_14 _ hm
  · exact checked3_15 _ hm
private def chunk4_35 : List (List T) := [[wire15,wire240,wire17604,wire43690],
  [wire15,wire240,wire21845,wire26214],
  [wire15,wire240,wire21845,wire26223],
  [wire15,wire240,wire21845,wire39321]]
private def pool4_35 : List (List (List T)) := [chunk3_15]
private theorem checked4_35 : ∀ w ∈ chunk4_35, ¬ Need 4 w.toFinset := by
  have h : chunk4_35.all (routes 3 pool4_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_15 _ hm
private def chunk4_36 : List (List T) := [[wire15,wire240,wire21845,wire39327],
  [wire15,wire240,wire21845,wire52428],
  [wire15,wire240,wire21845,wire52431],
  [wire15,wire240,wire22005,wire26214]]
private def pool4_36 : List (List (List T)) := []
private theorem checked4_36 : ∀ w ∈ chunk4_36, ¬ Need 4 w.toFinset := by
  have h : chunk4_36.all (routes 3 pool4_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_36] at hv
private def chunk4_37 : List (List T) := [[wire15,wire240,wire22005,wire39321],
  [wire15,wire240,wire26210,wire34952],
  [wire15,wire240,wire26214,wire34954],
  [wire15,wire240,wire26214,wire34956]]
private def pool4_37 : List (List (List T)) := [chunk3_5, chunk3_6, chunk3_15]
private theorem checked4_37 : ∀ w ∈ chunk4_37, ¬ Need 4 w.toFinset := by
  have h : chunk4_37.all (routes 3 pool4_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
  · exact checked3_15 _ hm
private def chunk4_38 : List (List T) := [[wire15,wire240,wire26214,wire43690],
  [wire15,wire240,wire26214,wire43770],
  [wire15,wire240,wire26214,wire52428],
  [wire15,wire240,wire26214,wire52476]]
private def pool4_38 : List (List (List T)) := []
private theorem checked4_38 : ∀ w ∈ chunk4_38, ¬ Need 4 w.toFinset := by
  have h : chunk4_38.all (routes 3 pool4_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_38] at hv
private def chunk4_39 : List (List T) := [[wire15,wire240,wire26223,wire43690],
  [wire15,wire240,wire34952,wire39325],
  [wire15,wire240,wire34952,wire61154],
  [wire15,wire240,wire34952,wire61162]]
private def pool4_39 : List (List (List T)) := [chunk3_6, chunk3_18]
private theorem checked4_39 : ∀ w ∈ chunk4_39, ¬ Need 4 w.toFinset := by
  have h : chunk4_39.all (routes 3 pool4_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_6 _ hm
  · exact checked3_18 _ hm
private def chunk4_40 : List (List T) := [[wire15,wire240,wire34954,wire39321],
  [wire15,wire240,wire34954,wire39323],
  [wire15,wire240,wire34954,wire61166],
  [wire15,wire240,wire34956,wire39321]]
private def pool4_40 : List (List (List T)) := [chunk3_6, chunk3_7]
private theorem checked4_40 : ∀ w ∈ chunk4_40, ¬ Need 4 w.toFinset := by
  have h : chunk4_40.all (routes 3 pool4_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_40,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
private def chunk4_41 : List (List T) := [[wire15,wire240,wire39321,wire43690],
  [wire15,wire240,wire39321,wire43770],
  [wire15,wire240,wire39321,wire52428],
  [wire15,wire240,wire39321,wire52476]]
private def pool4_41 : List (List (List T)) := []
private theorem checked4_41 : ∀ w ∈ chunk4_41, ¬ Need 4 w.toFinset := by
  have h : chunk4_41.all (routes 3 pool4_41.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_41] at hv
private def chunk4_42 : List (List T) := [[wire15,wire240,wire39327,wire43690],
  [wire15,wire240,wire43690,wire52428],
  [wire15,wire240,wire43690,wire52431],
  [wire15,wire242,wire4369,wire26214]]
private def pool4_42 : List (List (List T)) := []
private theorem checked4_42 : ∀ w ∈ chunk4_42, ¬ Need 4 w.toFinset := by
  have h : chunk4_42.all (routes 3 pool4_42.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_42] at hv
private def chunk4_43 : List (List T) := [[wire15,wire242,wire4369,wire30583],
  [wire15,wire242,wire4369,wire34952],
  [wire15,wire242,wire4369,wire34954],
  [wire15,wire242,wire4369,wire36744]]
private def pool4_43 : List (List (List T)) := []
private theorem checked4_43 : ∀ w ∈ chunk4_43, ¬ Need 4 w.toFinset := by
  have h : chunk4_43.all (routes 3 pool4_43.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_43] at hv
private def chunk4_44 : List (List T) := [[wire15,wire242,wire4369,wire39321],
  [wire15,wire242,wire4369,wire63624],
  [wire15,wire242,wire4371,wire34952],
  [wire15,wire242,wire4383,wire34952]]
private def pool4_44 : List (List (List T)) := []
private theorem checked4_44 : ∀ w ∈ chunk4_44, ¬ Need 4 w.toFinset := by
  have h : chunk4_44.all (routes 3 pool4_44.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_44] at hv
private def chunk4_45 : List (List T) := [[wire15,wire242,wire26214,wire34952],
  [wire15,wire242,wire34952,wire39321],
  [wire15,wire242,wire34952,wire61166],
  [wire15,wire243,wire4369,wire34952]]
private def pool4_45 : List (List (List T)) := [chunk3_5, chunk3_6, chunk3_15]
private theorem checked4_45 : ∀ w ∈ chunk4_45, ¬ Need 4 w.toFinset := by
  have h : chunk4_45.all (routes 3 pool4_45.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_45,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
  · exact checked3_15 _ hm
private def chunk4_46 : List (List T) := [[wire15,wire244,wire4369,wire26214],
  [wire15,wire244,wire4369,wire30583],
  [wire15,wire244,wire4369,wire34952],
  [wire15,wire244,wire4369,wire34956]]
private def pool4_46 : List (List (List T)) := [chunk3_3]
private theorem checked4_46 : ∀ w ∈ chunk4_46, ¬ Need 4 w.toFinset := by
  have h : chunk4_46.all (routes 3 pool4_46.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_46,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_3 _ hm
private def chunk4_47 : List (List T) := [[wire15,wire244,wire4369,wire34959],
  [wire15,wire244,wire4369,wire36744],
  [wire15,wire244,wire4369,wire39321],
  [wire15,wire244,wire4369,wire63624]]
private def pool4_47 : List (List (List T)) := []
private theorem checked4_47 : ∀ w ∈ chunk4_47, ¬ Need 4 w.toFinset := by
  have h : chunk4_47.all (routes 3 pool4_47.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_47] at hv
private def chunk4_48 : List (List T) := [[wire15,wire244,wire4373,wire34952],
  [wire15,wire244,wire26214,wire34952],
  [wire15,wire244,wire34952,wire39321],
  [wire15,wire244,wire34952,wire61166]]
private def pool4_48 : List (List (List T)) := [chunk3_6, chunk3_7]
private theorem checked4_48 : ∀ w ∈ chunk4_48, ¬ Need 4 w.toFinset := by
  have h : chunk4_48.all (routes 3 pool4_48.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_48,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
private def chunk4_49 : List (List T) := [[wire15,wire245,wire4369,wire34952],
  [wire15,wire250,wire4369,wire34952],
  [wire15,wire251,wire4369,wire34952],
  [wire15,wire252,wire4369,wire34952]]
private def pool4_49 : List (List (List T)) := [chunk3_16]
private theorem checked4_49 : ∀ w ∈ chunk4_49, ¬ Need 4 w.toFinset := by
  have h : chunk4_49.all (routes 3 pool4_49.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_49,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_16 _ hm
private def chunk4_50 : List (List T) := [[wire15,wire253,wire4369,wire34952],
  [wire15,wire255,wire4369,wire17508],
  [wire15,wire255,wire4369,wire34954],
  [wire15,wire255,wire4373,wire34952]]
private def pool4_50 : List (List (List T)) := [chunk3_16]
private theorem checked4_50 : ∀ w ∈ chunk4_50, ¬ Need 4 w.toFinset := by
  have h : chunk4_50.all (routes 3 pool4_50.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_50,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_16 _ hm
private def chunk4_51 : List (List T) := [[wire15,wire255,wire4497,wire17476],
  [wire15,wire255,wire13107,wire21845],
  [wire15,wire255,wire13107,wire26214],
  [wire15,wire255,wire13107,wire39321]]
private def pool4_51 : List (List (List T)) := [chunk3_0, chunk3_17]
private theorem checked4_51 : ∀ w ∈ chunk4_51, ¬ Need 4 w.toFinset := by
  have h : chunk4_51.all (routes 3 pool4_51.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_51,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_17 _ hm
private def chunk4_52 : List (List T) := [[wire15,wire255,wire13107,wire43690],
  [wire15,wire255,wire21845,wire26214],
  [wire15,wire255,wire21845,wire39321],
  [wire15,wire255,wire21845,wire52428]]
private def pool4_52 : List (List (List T)) := [chunk3_17]
private theorem checked4_52 : ∀ w ∈ chunk4_52, ¬ Need 4 w.toFinset := by
  have h : chunk4_52.all (routes 3 pool4_52.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_52,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_17 _ hm
private def chunk4_53 : List (List T) := [[wire15,wire255,wire26214,wire43690],
  [wire15,wire255,wire26214,wire52428],
  [wire15,wire255,wire39321,wire43690],
  [wire15,wire255,wire39321,wire52428]]
private def pool4_53 : List (List (List T)) := []
private theorem checked4_53 : ∀ w ∈ chunk4_53, ¬ Need 4 w.toFinset := by
  have h : chunk4_53.all (routes 3 pool4_53.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_53] at hv
private def chunk4_54 : List (List T) := [[wire15,wire255,wire43690,wire52428],
  [wire15,wire3840,wire4369,wire63626],
  [wire15,wire3840,wire4373,wire63624],
  [wire15,wire3842,wire4369,wire63624]]
private def pool4_54 : List (List (List T)) := [chunk3_4, chunk3_19, chunk3_21]
private theorem checked4_54 : ∀ w ∈ chunk4_54, ¬ Need 4 w.toFinset := by
  have h : chunk4_54.all (routes 3 pool4_54.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_54,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_4 _ hm
  · exact checked3_19 _ hm
  · exact checked3_21 _ hm
private def chunk4_55 : List (List T) := [[wire15,wire3844,wire4369,wire63624],
  [wire15,wire4352,wire8738,wire17476,wire35064],
  [wire15,wire4369,wire8738,wire65416],
  [wire15,wire4369,wire8802,wire17652]]
private def pool4_55 : List (List (List T)) := [chunk3_23, chunk3_24]
private theorem checked4_55 : ∀ w ∈ chunk4_55, ¬ Need 4 w.toFinset := by
  have h : chunk4_55.all (routes 3 pool4_55.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_55,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_23 _ hm
  · exact checked3_24 _ hm
private def chunk4_56 : List (List T) := [[wire15,wire4369,wire8802,wire35064],
  [wire15,wire4369,wire8946,wire17508],
  [wire15,wire4369,wire8946,wire65416],
  [wire15,wire4369,wire12066,wire65416]]
private def pool4_56 : List (List (List T)) := [chunk3_25]
private theorem checked4_56 : ∀ w ∈ chunk4_56, ¬ Need 4 w.toFinset := by
  have h : chunk4_56.all (routes 3 pool4_56.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_56,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_25 _ hm
private def chunk4_57 : List (List T) := [[wire15,wire4369,wire13107,wire65416],
  [wire15,wire4369,wire17412,wire65423],
  [wire15,wire4369,wire17476,wire65408],
  [wire15,wire4369,wire17476,wire65416]]
private def pool4_57 : List (List (List T)) := [chunk3_1]
private theorem checked4_57 : ∀ w ∈ chunk4_57, ¬ Need 4 w.toFinset := by
  have h : chunk4_57.all (routes 3 pool4_57.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_57,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_1 _ hm
private def chunk4_58 : List (List T) := [[wire15,wire4369,wire17476,wire65423],
  [wire15,wire4369,wire17508,wire35064],
  [wire15,wire4369,wire17508,wire65280],
  [wire15,wire4369,wire17508,wire65295]]
private def pool4_58 : List (List (List T)) := []
private theorem checked4_58 : ∀ w ∈ chunk4_58, ¬ Need 4 w.toFinset := by
  have h : chunk4_58.all (routes 3 pool4_58.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_58] at hv
private def chunk4_59 : List (List T) := [[wire15,wire4369,wire17652,wire65416],
  [wire15,wire4369,wire17652,wire65423],
  [wire15,wire4369,wire20292,wire65416],
  [wire15,wire4369,wire20292,wire65423]]
private def pool4_59 : List (List (List T)) := []
private theorem checked4_59 : ∀ w ∈ chunk4_59, ¬ Need 4 w.toFinset := by
  have h : chunk4_59.all (routes 3 pool4_59.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_59] at hv
private def chunk4_60 : List (List T) := [[wire15,wire4369,wire21845,wire65416],
  [wire15,wire4369,wire21845,wire65423],
  [wire15,wire4369,wire34952,wire35066],
  [wire15,wire4369,wire34952,wire35068]]
private def pool4_60 : List (List (List T)) := [chunk3_6, chunk3_7, chunk3_25]
private theorem checked4_60 : ∀ w ∈ chunk4_60, ¬ Need 4 w.toFinset := by
  have h : chunk4_60.all (routes 3 pool4_60.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_60,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_6 _ hm
  · exact checked3_7 _ hm
  · exact checked3_25 _ hm
private def chunk4_61 : List (List T) := [[wire15,wire4369,wire34952,wire65282],
  [wire15,wire4369,wire34952,wire65284],
  [wire15,wire4369,wire34952,wire65291],
  [wire15,wire4369,wire34952,wire65293]]
private def pool4_61 : List (List (List T)) := [chunk3_4, chunk3_25]
private theorem checked4_61 : ∀ w ∈ chunk4_61, ¬ Need 4 w.toFinset := by
  have h : chunk4_61.all (routes 3 pool4_61.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_61,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_4 _ hm
  · exact checked3_25 _ hm
private def chunk4_62 : List (List T) := [[wire15,wire4369,wire34954,wire35064],
  [wire15,wire4369,wire34954,wire35066],
  [wire15,wire4369,wire34954,wire65280],
  [wire15,wire4369,wire34954,wire65295]]
private def pool4_62 : List (List (List T)) := [chunk3_4, chunk3_6, chunk3_25]
private theorem checked4_62 : ∀ w ∈ chunk4_62, ¬ Need 4 w.toFinset := by
  have h : chunk4_62.all (routes 3 pool4_62.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_62,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_4 _ hm
  · exact checked3_6 _ hm
  · exact checked3_25 _ hm
private def chunk4_63 : List (List T) := [[wire15,wire4369,wire34956,wire35064],
  [wire15,wire4369,wire36744,wire61442],
  [wire15,wire4369,wire36744,wire61444],
  [wire15,wire4369,wire36746,wire61440]]
private def pool4_63 : List (List (List T)) := [chunk3_4, chunk3_6, chunk3_26]
private theorem checked4_63 : ∀ w ∈ chunk4_63, ¬ Need 4 w.toFinset := by
  have h : chunk4_63.all (routes 3 pool4_63.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_63,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_4 _ hm
  · exact checked3_6 _ hm
  · exact checked3_26 _ hm
private def chunk4_64 : List (List T) := [[wire15,wire4369,wire43658,wire65295],
  [wire15,wire4369,wire43690,wire65416],
  [wire15,wire4369,wire43690,wire65423],
  [wire15,wire4369,wire44970,wire65416]]
private def pool4_64 : List (List (List T)) := [chunk3_26]
private theorem checked4_64 : ∀ w ∈ chunk4_64, ¬ Need 4 w.toFinset := by
  have h : chunk4_64.all (routes 3 pool4_64.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_64,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_26 _ hm
private def chunk4_65 : List (List T) := [[wire15,wire4369,wire48059,wire65416],
  [wire15,wire4369,wire48059,wire65423],
  [wire15,wire4369,wire52428,wire65416],
  [wire15,wire4369,wire53196,wire65416]]
private def pool4_65 : List (List (List T)) := [chunk3_2]
private theorem checked4_65 : ∀ w ∈ chunk4_65, ¬ Need 4 w.toFinset := by
  have h : chunk4_65.all (routes 3 pool4_65.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_65,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_2 _ hm
private def chunk4_66 : List (List T) := [[wire15,wire4369,wire56797,wire65416],
  [wire15,wire4369,wire61986,wire65416],
  [wire15,wire4369,wire62532,wire65416],
  [wire15,wire4369,wire62532,wire65423]]
private def pool4_66 : List (List (List T)) := [chunk3_3, chunk3_27]
private theorem checked4_66 : ∀ w ∈ chunk4_66, ¬ Need 4 w.toFinset := by
  have h : chunk4_66.all (routes 3 pool4_66.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_66,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_3 _ hm
  · exact checked3_27 _ hm
private def chunk4_67 : List (List T) := [[wire15,wire4369,wire64170,wire65416],
  [wire15,wire4369,wire64716,wire65416],
  [wire15,wire4369,wire65314,wire65348],
  [wire15,wire4369,wire65314,wire65416]]
private def pool4_67 : List (List (List T)) := [chunk3_2, chunk3_23, chunk3_27]
private theorem checked4_67 : ∀ w ∈ chunk4_67, ¬ Need 4 w.toFinset := by
  have h : chunk4_67.all (routes 3 pool4_67.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_67,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_23 _ hm
  · exact checked3_27 _ hm
private def chunk4_68 : List (List T) := [[wire15,wire4369,wire65348,wire65416],
  [wire15,wire4369,wire65416,wire65450],
  [wire15,wire4369,wire65416,wire65484],
  [wire15,wire4373,wire34952,wire35064]]
private def pool4_68 : List (List (List T)) := [chunk3_2, chunk3_6, chunk3_28]
private theorem checked4_68 : ∀ w ∈ chunk4_68, ¬ Need 4 w.toFinset := by
  have h : chunk4_68.all (routes 3 pool4_68.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_68,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_2 _ hm
  · exact checked3_6 _ hm
  · exact checked3_28 _ hm
private def chunk4_69 : List (List T) := [[wire15,wire4373,wire34952,wire65280],
  [wire15,wire4373,wire34952,wire65295],
  [wire15,wire4373,wire36744,wire61440],
  [wire15,wire4383,wire8738,wire65416]]
private def pool4_69 : List (List (List T)) := [chunk3_0, chunk3_4, chunk3_5, chunk3_24]
private theorem checked4_69 : ∀ w ∈ chunk4_69, ¬ Need 4 w.toFinset := by
  have h : chunk4_69.all (routes 3 pool4_69.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_69,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_4 _ hm
  · exact checked3_5 _ hm
  · exact checked3_24 _ hm
private def chunk4_70 : List (List T) := [[wire15,wire4497,wire17476,wire65280],
  [wire15,wire4497,wire17476,wire65295],
  [wire15,wire4593,wire8738,wire34952,wire65348],
  [wire15,wire4593,wire8738,wire34968]]
private def pool4_70 : List (List (List T)) := [chunk3_1]
private theorem checked4_70 : ∀ w ∈ chunk4_70, ¬ Need 4 w.toFinset := by
  have h : chunk4_70.all (routes 3 pool4_70.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_70,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_1 _ hm
private def chunk4_71 : List (List T) := [[wire15,wire4593,wire8738,wire65348],
  [wire15,wire4593,wire8946,wire26214],
  [wire15,wire4593,wire8946,wire39321],
  [wire15,wire4593,wire12066,wire34952,wire62532]]
private def pool4_71 : List (List (List T)) := []
private theorem checked4_71 : ∀ w ∈ chunk4_71, ¬ Need 4 w.toFinset := by
  have h : chunk4_71.all (routes 3 pool4_71.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_71] at hv
private def chunk4_72 : List (List T) := [[wire15,wire4593,wire12066,wire62532],
  [wire15,wire4593,wire17476,wire34952,wire65314],
  [wire15,wire4593,wire17476,wire34968],
  [wire15,wire4593,wire17476,wire65314]]
private def pool4_72 : List (List (List T)) := []
private theorem checked4_72 : ∀ w ∈ chunk4_72, ¬ Need 4 w.toFinset := by
  have h : chunk4_72.all (routes 3 pool4_72.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_72] at hv
private def chunk4_73 : List (List T) := [[wire15,wire4593,wire17476,wire65327],
  [wire15,wire4593,wire17652,wire26214],
  [wire15,wire4593,wire17652,wire39321],
  [wire15,wire4593,wire20292,wire34952,wire61986]]
private def pool4_73 : List (List (List T)) := []
private theorem checked4_73 : ∀ w ∈ chunk4_73, ¬ Need 4 w.toFinset := by
  have h : chunk4_73.all (routes 3 pool4_73.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_73] at hv
private def chunk4_74 : List (List T) := [[wire15,wire4593,wire20292,wire61986],
  [wire15,wire8738,wire13107,wire65416],
  [wire15,wire8738,wire17472,wire35064],
  [wire15,wire8738,wire17476,wire30471]]
private def pool4_74 : List (List (List T)) := [chunk3_5, chunk3_32, chunk3_33]
private theorem checked4_74 : ∀ w ∈ chunk4_74, ¬ Need 4 w.toFinset := by
  have h : chunk4_74.all (routes 3 pool4_74.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_74,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_5 _ hm
  · exact checked3_32 _ hm
  · exact checked3_33 _ hm
private def chunk4_75 : List (List T) := [[wire15,wire8738,wire17476,wire35064],
  [wire15,wire8738,wire17476,wire35066],
  [wire15,wire8738,wire17476,wire35068],
  [wire15,wire8738,wire17477,wire35064]]
private def pool4_75 : List (List (List T)) := [chunk3_5, chunk3_6, chunk3_33, chunk3_35]
private theorem checked4_75 : ∀ w ∈ chunk4_75, ¬ Need 4 w.toFinset := by
  have h : chunk4_75.all (routes 3 pool4_75.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_75,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_5 _ hm
  · exact checked3_6 _ hm
  · exact checked3_33 _ hm
  · exact checked3_35 _ hm
private def chunk4_76 : List (List T) := [[wire15,wire8738,wire17478,wire35064],
  [wire15,wire8738,wire17484,wire35064],
  [wire15,wire8738,wire17487,wire30471],
  [wire15,wire8738,wire17487,wire35064]]
private def pool4_76 : List (List (List T)) := [chunk3_32, chunk3_33]
private theorem checked4_76 : ∀ w ∈ chunk4_76, ¬ Need 4 w.toFinset := by
  have h : chunk4_76.all (routes 3 pool4_76.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_76,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_32 _ hm
  · exact checked3_33 _ hm
private def chunk4_77 : List (List T) := [[wire15,wire8738,wire17508,wire35064],
  [wire15,wire8738,wire17988,wire35064],
  [wire15,wire8738,wire25668,wire35064],
  [wire15,wire8738,wire26214,wire30471]]
private def pool4_77 : List (List (List T)) := [chunk3_5, chunk3_33]
private theorem checked4_77 : ∀ w ∈ chunk4_77, ¬ Need 4 w.toFinset := by
  have h : chunk4_77.all (routes 3 pool4_77.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_77,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_5 _ hm
  · exact checked3_33 _ hm
private def chunk4_78 : List (List T) := [[wire15,wire8738,wire26214,wire35064],
  [wire15,wire8738,wire26223,wire35064],
  [wire15,wire8738,wire30471,wire39321],
  [wire15,wire8738,wire30471,wire48059]]
private def pool4_78 : List (List (List T)) := [chunk3_0]
private theorem checked4_78 : ∀ w ∈ chunk4_78, ¬ Need 4 w.toFinset := by
  have h : chunk4_78.all (routes 3 pool4_78.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_78,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_0 _ hm
private def chunk4_79 : List (List T) := [[wire15,wire8738,wire35064,wire39321],
  [wire15,wire8738,wire35064,wire39327],
  [wire15,wire8738,wire35064,wire48048],
  [wire15,wire8738,wire35064,wire48059]]
private def pool4_79 : List (List (List T)) := []
private theorem checked4_79 : ∀ w ∈ chunk4_79, ¬ Need 4 w.toFinset := by
  have h : chunk4_79.all (routes 3 pool4_79.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_79] at hv
private def chunk4_80 : List (List T) := [[wire15,wire8738,wire35064,wire48063],
  [wire15,wire8738,wire52428,wire65416],
  [wire15,wire8738,wire61166,wire65416],
  [wire15,wire8742,wire17476,wire35064]]
private def pool4_80 : List (List (List T)) := []
private theorem checked4_80 : ∀ w ∈ chunk4_80, ¬ Need 4 w.toFinset := by
  have h : chunk4_80.all (routes 3 pool4_80.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_80] at hv
private def chunk4_81 : List (List T) := [[wire15,wire8746,wire17476,wire35064],
  [wire15,wire8802,wire17476,wire35064],
  [wire15,wire8802,wire17652,wire34952],
  [wire15,wire8946,wire17508,wire34952]]
private def pool4_81 : List (List (List T)) := [chunk3_5, chunk3_34, chunk3_35]
private theorem checked4_81 : ∀ w ∈ chunk4_81, ¬ Need 4 w.toFinset := by
  have h : chunk4_81.all (routes 3 pool4_81.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_81,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_5 _ hm
  · exact checked3_34 _ hm
  · exact checked3_35 _ hm
private def chunk4_82 : List (List T) := [[wire15,wire8946,wire26214,wire35064],
  [wire15,wire8946,wire35064,wire39321],
  [wire15,wire9762,wire17476,wire35064],
  [wire15,wire12066,wire26214,wire35064]]
private def pool4_82 : List (List (List T)) := []
private theorem checked4_82 : ∀ w ∈ chunk4_82, ¬ Need 4 w.toFinset := by
  have h : chunk4_82.all (routes 3 pool4_82.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_82] at hv
private def chunk4_83 : List (List T) := [[wire15,wire12066,wire35064,wire39321],
  [wire15,wire13107,wire21845,wire35064],
  [wire15,wire13107,wire21845,wire65280],
  [wire15,wire13107,wire21845,wire65295]]
private def pool4_83 : List (List (List T)) := [chunk3_36]
private theorem checked4_83 : ∀ w ∈ chunk4_83, ¬ Need 4 w.toFinset := by
  have h : chunk4_83.all (routes 3 pool4_83.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_83,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_36 _ hm
private def chunk4_84 : List (List T) := [[wire15,wire13107,wire26214,wire35064],
  [wire15,wire13107,wire26214,wire65280],
  [wire15,wire13107,wire26214,wire65295],
  [wire15,wire13107,wire35064,wire39321]]
private def pool4_84 : List (List (List T)) := []
private theorem checked4_84 : ∀ w ∈ chunk4_84, ¬ Need 4 w.toFinset := by
  have h : chunk4_84.all (routes 3 pool4_84.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_84] at hv
private def chunk4_85 : List (List T) := [[wire15,wire13107,wire35064,wire43690],
  [wire15,wire13107,wire39321,wire65280],
  [wire15,wire13107,wire39321,wire65295],
  [wire15,wire13107,wire43690,wire65280]]
private def pool4_85 : List (List (List T)) := [chunk3_36]
private theorem checked4_85 : ∀ w ∈ chunk4_85, ¬ Need 4 w.toFinset := by
  have h : chunk4_85.all (routes 3 pool4_85.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_85,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_36 _ hm
private def chunk4_86 : List (List T) := [[wire15,wire13107,wire43690,wire65295],
  [wire15,wire17476,wire21845,wire65416],
  [wire15,wire17476,wire21845,wire65423],
  [wire15,wire17476,wire25122,wire35064]]
private def pool4_86 : List (List (List T)) := [chunk3_37]
private theorem checked4_86 : ∀ w ∈ chunk4_86, ¬ Need 4 w.toFinset := by
  have h : chunk4_86.all (routes 3 pool4_86.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_86,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_37 _ hm
private def chunk4_87 : List (List T) := [[wire15,wire17476,wire26214,wire30471],
  [wire15,wire17476,wire26214,wire35064],
  [wire15,wire17476,wire30471,wire39321],
  [wire15,wire17476,wire30471,wire56797]]
private def pool4_87 : List (List (List T)) := [chunk3_37]
private theorem checked4_87 : ∀ w ∈ chunk4_87, ¬ Need 4 w.toFinset := by
  have h : chunk4_87.all (routes 3 pool4_87.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_87,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_37 _ hm
private def chunk4_88 : List (List T) := [[wire15,wire17476,wire35064,wire39321],
  [wire15,wire17476,wire35064,wire56797],
  [wire15,wire17476,wire43562,wire65295],
  [wire15,wire17476,wire43690,wire65416]]
private def pool4_88 : List (List (List T)) := [chunk3_37, chunk3_38]
private theorem checked4_88 : ∀ w ∈ chunk4_88, ¬ Need 4 w.toFinset := by
  have h : chunk4_88.all (routes 3 pool4_88.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_88,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_37 _ hm
  · exact checked3_38 _ hm
private def chunk4_89 : List (List T) := [[wire15,wire17476,wire43690,wire65423],
  [wire15,wire17476,wire61166,wire65416],
  [wire15,wire17476,wire61166,wire65423],
  [wire15,wire17487,wire35064,wire56797]]
private def pool4_89 : List (List (List T)) := [chunk3_37, chunk3_38]
private theorem checked4_89 : ∀ w ∈ chunk4_89, ¬ Need 4 w.toFinset := by
  have h : chunk4_89.all (routes 3 pool4_89.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_89,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_37 _ hm
  · exact checked3_38 _ hm
private def chunk4_90 : List (List T) := [[wire15,wire17652,wire26214,wire35064],
  [wire15,wire17652,wire35064,wire39321],
  [wire15,wire20292,wire26214,wire35064],
  [wire15,wire20292,wire35064,wire39321]]
private def pool4_90 : List (List (List T)) := []
private theorem checked4_90 : ∀ w ∈ chunk4_90, ¬ Need 4 w.toFinset := by
  have h : chunk4_90.all (routes 3 pool4_90.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_90] at hv
private def chunk4_91 : List (List T) := [[wire15,wire21845,wire26214,wire35064],
  [wire15,wire21845,wire26214,wire65280],
  [wire15,wire21845,wire26214,wire65295],
  [wire15,wire21845,wire35064,wire39321]]
private def pool4_91 : List (List (List T)) := []
private theorem checked4_91 : ∀ w ∈ chunk4_91, ¬ Need 4 w.toFinset := by
  have h : chunk4_91.all (routes 3 pool4_91.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_91] at hv
private def chunk4_92 : List (List T) := [[wire15,wire21845,wire35064,wire52428],
  [wire15,wire21845,wire39321,wire65280],
  [wire15,wire21845,wire39321,wire65295],
  [wire15,wire21845,wire52428,wire65280]]
private def pool4_92 : List (List (List T)) := []
private theorem checked4_92 : ∀ w ∈ chunk4_92, ¬ Need 4 w.toFinset := by
  have h : chunk4_92.all (routes 3 pool4_92.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_92] at hv
private def chunk4_93 : List (List T) := [[wire15,wire21845,wire52428,wire65295],
  [wire15,wire26214,wire35064,wire43690],
  [wire15,wire26214,wire35064,wire43770],
  [wire15,wire26214,wire35064,wire48059]]
private def pool4_93 : List (List (List T)) := [chunk3_2]
private theorem checked4_93 : ∀ w ∈ chunk4_93, ¬ Need 4 w.toFinset := by
  have h : chunk4_93.all (routes 3 pool4_93.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_93,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_2 _ hm
private def chunk4_94 : List (List T) := [[wire15,wire26214,wire35064,wire52428],
  [wire15,wire26214,wire35064,wire52476],
  [wire15,wire26214,wire35064,wire56797],
  [wire15,wire26214,wire35064,wire61986]]
private def pool4_94 : List (List (List T)) := []
private theorem checked4_94 : ∀ w ∈ chunk4_94, ¬ Need 4 w.toFinset := by
  have h : chunk4_94.all (routes 3 pool4_94.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_94] at hv
private def chunk4_95 : List (List T) := [[wire15,wire26214,wire35064,wire62532],
  [wire15,wire26214,wire43690,wire65280],
  [wire15,wire26214,wire43690,wire65295],
  [wire15,wire26214,wire52428,wire65280]]
private def pool4_95 : List (List (List T)) := []
private theorem checked4_95 : ∀ w ∈ chunk4_95, ¬ Need 4 w.toFinset := by
  have h : chunk4_95.all (routes 3 pool4_95.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_95] at hv
private def chunk4_96 : List (List T) := [[wire15,wire26214,wire52428,wire65295],
  [wire15,wire35064,wire39321,wire43690],
  [wire15,wire35064,wire39321,wire43770],
  [wire15,wire35064,wire39321,wire48059]]
private def pool4_96 : List (List (List T)) := [chunk3_2]
private theorem checked4_96 : ∀ w ∈ chunk4_96, ¬ Need 4 w.toFinset := by
  have h : chunk4_96.all (routes 3 pool4_96.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_96,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_2 _ hm
private def chunk4_97 : List (List T) := [[wire15,wire35064,wire39321,wire52428],
  [wire15,wire35064,wire39321,wire52476],
  [wire15,wire35064,wire39321,wire56797],
  [wire15,wire35064,wire39321,wire61986]]
private def pool4_97 : List (List (List T)) := []
private theorem checked4_97 : ∀ w ∈ chunk4_97, ¬ Need 4 w.toFinset := by
  have h : chunk4_97.all (routes 3 pool4_97.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_97] at hv
private def chunk4_98 : List (List T) := [[wire15,wire35064,wire39321,wire62532],
  [wire15,wire35064,wire43690,wire52428],
  [wire15,wire35064,wire48059,wire56797],
  [wire15,wire39321,wire43690,wire65280]]
private def pool4_98 : List (List (List T)) := []
private theorem checked4_98 : ∀ w ∈ chunk4_98, ¬ Need 4 w.toFinset := by
  have h : chunk4_98.all (routes 3 pool4_98.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_98] at hv
private def chunk4_99 : List (List T) := [[wire15,wire39321,wire43690,wire65295],
  [wire15,wire39321,wire52428,wire65280],
  [wire15,wire39321,wire52428,wire65295],
  [wire15,wire43690,wire52428,wire65280]]
private def pool4_99 : List (List (List T)) := []
private theorem checked4_99 : ∀ w ∈ chunk4_99, ¬ Need 4 w.toFinset := by
  have h : chunk4_99.all (routes 3 pool4_99.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_99] at hv
private def chunk4_100 : List (List T) := [[wire15,wire43690,wire52428,wire65295],
  [wire16,wire8738,wire17487,wire35064],
  [wire31,wire4593,wire8738,wire34952],
  [wire31,wire4593,wire17476,wire34952]]
private def pool4_100 : List (List (List T)) := [chunk3_33]
private theorem checked4_100 : ∀ w ∈ chunk4_100, ¬ Need 4 w.toFinset := by
  have h : chunk4_100.all (routes 3 pool4_100.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_100,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_101 : List (List T) := [[wire32,wire240,wire4369,wire65348],
  [wire32,wire240,wire17487,wire21845],
  [wire32,wire240,wire17487,wire43690],
  [wire32,wire255,wire4593,wire17476]]
private def pool4_101 : List (List (List T)) := [chunk3_7, chunk3_12, chunk3_14, chunk3_17]
private theorem checked4_101 : ∀ w ∈ chunk4_101, ¬ Need 4 w.toFinset := by
  have h : chunk4_101.all (routes 3 pool4_101.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_101,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_12 _ hm
  · exact checked3_14 _ hm
  · exact checked3_17 _ hm
private def chunk4_102 : List (List T) := [[wire32,wire3840,wire4593,wire62532],
  [wire32,wire4593,wire17476,wire65280],
  [wire32,wire4593,wire20292,wire61440],
  [wire32,wire8738,wire17487,wire35064]]
private def pool4_102 : List (List (List T)) := [chunk3_7, chunk3_20, chunk3_22, chunk3_29, chunk3_30, chunk3_33]
private theorem checked4_102 : ∀ w ∈ chunk4_102, ¬ Need 4 w.toFinset := by
  have h : chunk4_102.all (routes 3 pool4_102.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_102,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_20 _ hm
  · exact checked3_22 _ hm
  · exact checked3_29 _ hm
  · exact checked3_30 _ hm
  · exact checked3_33 _ hm
private def chunk4_103 : List (List T) := [[wire32,wire8946,wire17487,wire34952],
  [wire34,wire255,wire4383,wire34952],
  [wire34,wire255,wire4593,wire17476],
  [wire47,wire240,wire4369,wire17476]]
private def pool4_103 : List (List (List T)) := [chunk3_7, chunk3_35]
private theorem checked4_103 : ∀ w ∈ chunk4_103, ¬ Need 4 w.toFinset := by
  have h : chunk4_103.all (routes 3 pool4_103.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_103,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_35 _ hm
private def chunk4_104 : List (List T) := [[wire47,wire240,wire4369,wire17508],
  [wire47,wire240,wire4369,wire20292],
  [wire47,wire240,wire4369,wire21845],
  [wire47,wire240,wire4369,wire43690]]
private def pool4_104 : List (List (List T)) := []
private theorem checked4_104 : ∀ w ∈ chunk4_104, ¬ Need 4 w.toFinset := by
  have h : chunk4_104.all (routes 3 pool4_104.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_104] at hv
private def chunk4_105 : List (List T) := [[wire47,wire240,wire4369,wire48059],
  [wire47,wire240,wire4369,wire62532],
  [wire47,wire240,wire4401,wire17476],
  [wire47,wire240,wire4593,wire17476]]
private def pool4_105 : List (List (List T)) := []
private theorem checked4_105 : ∀ w ∈ chunk4_105, ¬ Need 4 w.toFinset := by
  have h : chunk4_105.all (routes 3 pool4_105.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_105] at hv
private def chunk4_106 : List (List T) := [[wire47,wire240,wire17476,wire21845],
  [wire47,wire240,wire17476,wire43690],
  [wire47,wire240,wire17476,wire61166],
  [wire47,wire255,wire4369,wire17476]]
private def pool4_106 : List (List (List T)) := [chunk3_7, chunk3_14]
private theorem checked4_106 : ∀ w ∈ chunk4_106, ¬ Need 4 w.toFinset := by
  have h : chunk4_106.all (routes 3 pool4_106.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_106,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_14 _ hm
private def chunk4_107 : List (List T) := [[wire47,wire4369,wire8946,wire17476],
  [wire47,wire4369,wire17476,wire35064],
  [wire47,wire4369,wire17476,wire65280],
  [wire47,wire4369,wire17476,wire65295]]
private def pool4_107 : List (List (List T)) := []
private theorem checked4_107 : ∀ w ∈ chunk4_107, ¬ Need 4 w.toFinset := by
  have h : chunk4_107.all (routes 3 pool4_107.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_107] at hv
private def chunk4_108 : List (List T) := [[wire47,wire8738,wire17476,wire35064],
  [wire47,wire8946,wire17476,wire34952],
  [wire63,wire240,wire4369,wire17476],
  [wire64,wire8738,wire17487,wire35064]]
private def pool4_108 : List (List (List T)) := [chunk3_7, chunk3_33, chunk3_35]
private theorem checked4_108 : ∀ w ∈ chunk4_108, ¬ Need 4 w.toFinset := by
  have h : chunk4_108.all (routes 3 pool4_108.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_108,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_33 _ hm
  · exact checked3_35 _ hm
private def chunk4_109 : List (List T) := [[wire68,wire255,wire4369,wire8751],
  [wire68,wire255,wire4593,wire8738],
  [wire72,wire8738,wire17487,wire35064],
  [wire79,wire4369,wire8738,wire35064]]
private def pool4_109 : List (List (List T)) := [chunk3_8, chunk3_33, chunk3_35]
private theorem checked4_109 : ∀ w ∈ chunk4_109, ¬ Need 4 w.toFinset := by
  have h : chunk4_109.all (routes 3 pool4_109.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_109,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_33 _ hm
  · exact checked3_35 _ hm
private def chunk4_110 : List (List T) := [[wire79,wire8738,wire17476,wire35064],
  [wire111,wire240,wire4369,wire17476],
  [wire112,wire127,wire4369,wire17476],
  [wire112,wire4369,wire17476,wire17487]]
private def pool4_110 : List (List (List T)) := [chunk3_8, chunk3_33]
private theorem checked4_110 : ∀ w ∈ chunk4_110, ¬ Need 4 w.toFinset := by
  have h : chunk4_110.all (routes 3 pool4_110.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_110,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_33 _ hm
private def chunk4_111 : List (List T) := [[wire112,wire4369,wire17476,wire65520],
  [wire112,wire8738,wire17487,wire30583],
  [wire112,wire8738,wire17487,wire34952],
  [wire127,wire240,wire4369,wire17476]]
private def pool4_111 : List (List (List T)) := [chunk3_8, chunk3_33]
private theorem checked4_111 : ∀ w ∈ chunk4_111, ¬ Need 4 w.toFinset := by
  have h : chunk4_111.all (routes 3 pool4_111.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_111,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_33 _ hm
private def chunk4_112 : List (List T) := [[wire128,wire240,wire4369,wire65348],
  [wire128,wire240,wire4369,wire65524],
  [wire128,wire240,wire17487,wire21845],
  [wire128,wire240,wire17487,wire43690]]
private def pool4_112 : List (List (List T)) := [chunk3_13, chunk3_15]
private theorem checked4_112 : ∀ w ∈ chunk4_112, ¬ Need 4 w.toFinset := by
  have h : chunk4_112.all (routes 3 pool4_112.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_112,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_13 _ hm
  · exact checked3_15 _ hm
private def chunk4_113 : List (List T) := [[wire128,wire3840,wire4369,wire61444],
  [wire128,wire3840,wire4373,wire61440],
  [wire128,wire3844,wire4369,wire61440],
  [wire128,wire8738,wire17487,wire35064]]
private def pool4_113 : List (List (List T)) := [chunk3_9, chunk3_10, chunk3_19, chunk3_20, chunk3_21, chunk3_22, chunk3_23, chunk3_33]
private theorem checked4_113 : ∀ w ∈ chunk4_113, ¬ Need 4 w.toFinset := by
  have h : chunk4_113.all (routes 3 pool4_113.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_113,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_9 _ hm
  · exact checked3_10 _ hm
  · exact checked3_19 _ hm
  · exact checked3_20 _ hm
  · exact checked3_21 _ hm
  · exact checked3_22 _ hm
  · exact checked3_23 _ hm
  · exact checked3_33 _ hm
private def chunk4_114 : List (List T) := [[wire132,wire3840,wire4369,wire61440],
  [wire136,wire255,wire4369,wire8946],
  [wire136,wire255,wire4383,wire8738],
  [wire143,wire240,wire4369,wire17476]]
private def pool4_114 : List (List (List T)) := [chunk3_10, chunk3_19, chunk3_20, chunk3_23]
private theorem checked4_114 : ∀ w ∈ chunk4_114, ¬ Need 4 w.toFinset := by
  have h : chunk4_114.all (routes 3 pool4_114.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_114,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_10 _ hm
  · exact checked3_19 _ hm
  · exact checked3_20 _ hm
  · exact checked3_23 _ hm
private def chunk4_115 : List (List T) := [[wire143,wire240,wire4369,wire17604],
  [wire143,wire240,wire4369,wire17652],
  [wire143,wire240,wire4369,wire20292],
  [wire143,wire240,wire4369,wire21845]]
private def pool4_115 : List (List (List T)) := []
private theorem checked4_115 : ∀ w ∈ chunk4_115, ¬ Need 4 w.toFinset := by
  have h : chunk4_115.all (routes 3 pool4_115.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_115] at hv
private def chunk4_116 : List (List T) := [[wire143,wire240,wire4369,wire43690],
  [wire143,wire240,wire4369,wire48059],
  [wire143,wire240,wire4369,wire62532],
  [wire143,wire240,wire4497,wire17476]]
private def pool4_116 : List (List (List T)) := [chunk3_10]
private theorem checked4_116 : ∀ w ∈ chunk4_116, ¬ Need 4 w.toFinset := by
  have h : chunk4_116.all (routes 3 pool4_116.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_116,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_10 _ hm
private def chunk4_117 : List (List T) := [[wire143,wire240,wire17476,wire21845],
  [wire143,wire240,wire17476,wire43690],
  [wire143,wire240,wire17476,wire61166],
  [wire143,wire4369,wire17476,wire65295]]
private def pool4_117 : List (List (List T)) := [chunk3_15]
private theorem checked4_117 : ∀ w ∈ chunk4_117, ¬ Need 4 w.toFinset := by
  have h : chunk4_117.all (routes 3 pool4_117.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_117,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_15 _ hm
private def chunk4_118 : List (List T) := [[wire159,wire240,wire4369,wire17476],
  [wire187,wire240,wire4369,wire8738],
  [wire187,wire240,wire4369,wire34952],
  [wire192,wire255,wire4369,wire17476]]
private def pool4_118 : List (List (List T)) := [chunk3_11, chunk3_17]
private theorem checked4_118 : ∀ w ∈ chunk4_118, ¬ Need 4 w.toFinset := by
  have h : chunk4_118.all (routes 3 pool4_118.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_118,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_11 _ hm
  · exact checked3_17 _ hm
private def chunk4_119 : List (List T) := [[wire192,wire3840,wire4369,wire62532],
  [wire192,wire4369,wire17476,wire65280],
  [wire192,wire4369,wire20292,wire61440],
  [wire207,wire240,wire4369,wire17476]]
private def pool4_119 : List (List (List T)) := [chunk3_12, chunk3_20, chunk3_28]
private theorem checked4_119 : ∀ w ∈ chunk4_119, ¬ Need 4 w.toFinset := by
  have h : chunk4_119.all (routes 3 pool4_119.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_119,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_20 _ hm
  · exact checked3_28 _ hm
private def chunk4_120 : List (List T) := [[wire208,wire255,wire4369,wire17476],
  [wire208,wire3840,wire4369,wire62532],
  [wire208,wire4369,wire17476,wire65280],
  [wire208,wire4369,wire20292,wire61440]]
private def pool4_120 : List (List (List T)) := [chunk3_12, chunk3_17, chunk3_20, chunk3_28]
private theorem checked4_120 : ∀ w ∈ chunk4_120, ¬ Need 4 w.toFinset := by
  have h : chunk4_120.all (routes 3 pool4_120.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_120,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_17 _ hm
  · exact checked3_20 _ hm
  · exact checked3_28 _ hm
private def chunk4_121 : List (List T) := [[wire223,wire240,wire4369,wire17476],
  [wire240,wire251,wire4369,wire34952],
  [wire240,wire255,wire4369,wire17508],
  [wire240,wire255,wire4369,wire34954]]
private def pool4_121 : List (List (List T)) := [chunk3_9, chunk3_12, chunk3_17]
private theorem checked4_121 : ∀ w ∈ chunk4_121, ¬ Need 4 w.toFinset := by
  have h : chunk4_121.all (routes 3 pool4_121.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_121,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_9 _ hm
  · exact checked3_12 _ hm
  · exact checked3_17 _ hm
private def chunk4_122 : List (List T) := [[wire240,wire255,wire4373,wire34952],
  [wire240,wire255,wire4497,wire17476],
  [wire240,wire255,wire13107,wire21845],
  [wire240,wire255,wire13107,wire26214]]
private def pool4_122 : List (List (List T)) := [chunk3_9, chunk3_18]
private theorem checked4_122 : ∀ w ∈ chunk4_122, ¬ Need 4 w.toFinset := by
  have h : chunk4_122.all (routes 3 pool4_122.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_122,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_9 _ hm
  · exact checked3_18 _ hm
private def chunk4_123 : List (List T) := [[wire240,wire255,wire13107,wire39321],
  [wire240,wire255,wire13107,wire43690],
  [wire240,wire255,wire21845,wire26214],
  [wire240,wire255,wire21845,wire39321]]
private def pool4_123 : List (List (List T)) := [chunk3_18]
private theorem checked4_123 : ∀ w ∈ chunk4_123, ¬ Need 4 w.toFinset := by
  have h : chunk4_123.all (routes 3 pool4_123.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_123,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_18 _ hm
private def chunk4_124 : List (List T) := [[wire240,wire255,wire21845,wire52428],
  [wire240,wire255,wire26214,wire43690],
  [wire240,wire255,wire26214,wire52428],
  [wire240,wire255,wire39321,wire43690]]
private def pool4_124 : List (List (List T)) := []
private theorem checked4_124 : ∀ w ∈ chunk4_124, ¬ Need 4 w.toFinset := by
  have h : chunk4_124.all (routes 3 pool4_124.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_124] at hv
private def chunk4_125 : List (List T) := [[wire240,wire255,wire39321,wire52428],
  [wire240,wire255,wire43690,wire52428],
  [wire240,wire3840,wire4369,wire62564],
  [wire240,wire3840,wire4497,wire62532]]
private def pool4_125 : List (List (List T)) := [chunk3_12, chunk3_13, chunk3_20]
private theorem checked4_125 : ∀ w ∈ chunk4_125, ¬ Need 4 w.toFinset := by
  have h : chunk4_125.all (routes 3 pool4_125.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_125,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_13 _ hm
  · exact checked3_20 _ hm
private def chunk4_126 : List (List T) := [[wire240,wire3872,wire4369,wire62532],
  [wire240,wire3968,wire4369,wire62532],
  [wire240,wire4352,wire8738,wire17487,wire34952],
  [wire240,wire4369,wire8738,wire65348]]
private def pool4_126 : List (List (List T)) := [chunk3_12, chunk3_22, chunk3_23, chunk3_28]
private theorem checked4_126 : ∀ w ∈ chunk4_126, ¬ Need 4 w.toFinset := by
  have h : chunk4_126.all (routes 3 pool4_126.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_126,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_22 _ hm
  · exact checked3_23 _ hm
  · exact checked3_28 _ hm
private def chunk4_127 : List (List T) := [[wire240,wire4369,wire8746,wire17487],
  [wire240,wire4369,wire8746,wire34959],
  [wire240,wire4369,wire8751,wire34954],
  [wire240,wire4369,wire8751,wire65348]]
private def pool4_127 : List (List (List T)) := []
private theorem checked4_127 : ∀ w ∈ chunk4_127, ¬ Need 4 w.toFinset := by
  have h : chunk4_127.all (routes 3 pool4_127.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_127] at hv
private def chunk4_128 : List (List T) := [[wire240,wire4369,wire12066,wire65348],
  [wire240,wire4369,wire13107,wire65348],
  [wire240,wire4369,wire17476,wire17519],
  [wire240,wire4369,wire17476,wire17615]]
private def pool4_128 : List (List (List T)) := [chunk3_14, chunk3_15, chunk3_29]
private theorem checked4_128 : ∀ w ∈ chunk4_128, ¬ Need 4 w.toFinset := by
  have h : chunk4_128.all (routes 3 pool4_128.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_128,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_14 _ hm
  · exact checked3_15 _ hm
  · exact checked3_29 _ hm
private def chunk4_129 : List (List T) := [[wire240,wire4369,wire17476,wire65312],
  [wire240,wire4369,wire17476,wire65392],
  [wire240,wire4369,wire17476,wire65408],
  [wire240,wire4369,wire17476,wire65488]]
private def pool4_129 : List (List (List T)) := [chunk3_12, chunk3_13, chunk3_29]
private theorem checked4_129 : ∀ w ∈ chunk4_129, ¬ Need 4 w.toFinset := by
  have h : chunk4_129.all (routes 3 pool4_129.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_129,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_13 _ hm
  · exact checked3_29 _ hm
private def chunk4_130 : List (List T) := [[wire240,wire4369,wire17487,wire17508],
  [wire240,wire4369,wire17487,wire17604],
  [wire240,wire4369,wire17487,wire34954],
  [wire240,wire4369,wire17508,wire17519]]
private def pool4_130 : List (List (List T)) := [chunk3_13, chunk3_14]
private theorem checked4_130 : ∀ w ∈ chunk4_130, ¬ Need 4 w.toFinset := by
  have h : chunk4_130.all (routes 3 pool4_130.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_130,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_13 _ hm
  · exact checked3_14 _ hm
private def chunk4_131 : List (List T) := [[wire240,wire4369,wire17508,wire65280],
  [wire240,wire4369,wire17508,wire65520],
  [wire240,wire4369,wire20292,wire61472],
  [wire240,wire4369,wire20292,wire61568]]
private def pool4_131 : List (List (List T)) := [chunk3_12, chunk3_29]
private theorem checked4_131 : ∀ w ∈ chunk4_131, ¬ Need 4 w.toFinset := by
  have h : chunk4_131.all (routes 3 pool4_131.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_131,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_29 _ hm
private def chunk4_132 : List (List T) := [[wire240,wire4369,wire20324,wire61440],
  [wire240,wire4369,wire26212,wire65520],
  [wire240,wire4369,wire26214,wire65348],
  [wire240,wire4369,wire26214,wire65524]]
private def pool4_132 : List (List (List T)) := [chunk3_12, chunk3_30]
private theorem checked4_132 : ∀ w ∈ chunk4_132, ¬ Need 4 w.toFinset := by
  have h : chunk4_132.all (routes 3 pool4_132.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_132,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_30 _ hm
private def chunk4_133 : List (List T) := [[wire240,wire4369,wire28518,wire65348],
  [wire240,wire4369,wire30583,wire65348],
  [wire240,wire4369,wire30583,wire65524],
  [wire240,wire4369,wire34944,wire65524]]
private def pool4_133 : List (List (List T)) := [chunk3_8, chunk3_30]
private theorem checked4_133 : ∀ w ∈ chunk4_133, ¬ Need 4 w.toFinset := by
  have h : chunk4_133.all (routes 3 pool4_133.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_133,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_30 _ hm
private def chunk4_134 : List (List T) := [[wire240,wire4369,wire34952,wire65284],
  [wire240,wire4369,wire34952,wire65348],
  [wire240,wire4369,wire34952,wire65524],
  [wire240,wire4369,wire34954,wire65280]]
private def pool4_134 : List (List (List T)) := [chunk3_9]
private theorem checked4_134 : ∀ w ∈ chunk4_134, ¬ Need 4 w.toFinset := by
  have h : chunk4_134.all (routes 3 pool4_134.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_134,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_9 _ hm
private def chunk4_135 : List (List T) := [[wire240,wire4369,wire34954,wire65520],
  [wire240,wire4369,wire34959,wire65348],
  [wire240,wire4369,wire34959,wire65524],
  [wire240,wire4369,wire36744,wire65348]]
private def pool4_135 : List (List (List T)) := []
private theorem checked4_135 : ∀ w ∈ chunk4_135, ¬ Need 4 w.toFinset := by
  have h : chunk4_135.all (routes 3 pool4_135.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_135] at hv
private def chunk4_136 : List (List T) := [[wire240,wire4369,wire36744,wire65524],
  [wire240,wire4369,wire39321,wire65348],
  [wire240,wire4369,wire39321,wire65524],
  [wire240,wire4369,wire52428,wire65348]]
private def pool4_136 : List (List (List T)) := [chunk3_12, chunk3_30]
private theorem checked4_136 : ∀ w ∈ chunk4_136, ¬ Need 4 w.toFinset := by
  have h : chunk4_136.all (routes 3 pool4_136.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_136,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_30 _ hm
private def chunk4_137 : List (List T) := [[wire240,wire4369,wire53196,wire65348],
  [wire240,wire4369,wire56797,wire65348],
  [wire240,wire4369,wire61986,wire65348],
  [wire240,wire4369,wire63078,wire65348]]
private def pool4_137 : List (List (List T)) := [chunk3_12, chunk3_31]
private theorem checked4_137 : ∀ w ∈ chunk4_137, ¬ Need 4 w.toFinset := by
  have h : chunk4_137.all (routes 3 pool4_137.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_137,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_31 _ hm
private def chunk4_138 : List (List T) := [[wire240,wire4369,wire63624,wire65348],
  [wire240,wire4369,wire63624,wire65524],
  [wire240,wire4369,wire64716,wire65348],
  [wire240,wire4369,wire65314,wire65348]]
private def pool4_138 : List (List (List T)) := [chunk3_12, chunk3_31]
private theorem checked4_138 : ∀ w ∈ chunk4_138, ¬ Need 4 w.toFinset := by
  have h : chunk4_138.all (routes 3 pool4_138.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_138,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_31 _ hm
private def chunk4_139 : List (List T) := [[wire240,wire4369,wire65314,wire65416],
  [wire240,wire4369,wire65348,wire65382],
  [wire240,wire4369,wire65348,wire65416],
  [wire240,wire4369,wire65348,wire65484]]
private def pool4_139 : List (List (List T)) := [chunk3_12, chunk3_23, chunk3_32]
private theorem checked4_139 : ∀ w ∈ chunk4_139, ¬ Need 4 w.toFinset := by
  have h : chunk4_139.all (routes 3 pool4_139.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_139,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_12 _ hm
  · exact checked3_23 _ hm
  · exact checked3_32 _ hm
private def chunk4_140 : List (List T) := [[wire240,wire4373,wire34952,wire65280],
  [wire240,wire4373,wire34952,wire65520],
  [wire240,wire4383,wire8738,wire17476,wire65416],
  [wire240,wire4383,wire8738,wire17477]]
private def pool4_140 : List (List (List T)) := [chunk3_10]
private theorem checked4_140 : ∀ w ∈ chunk4_140, ¬ Need 4 w.toFinset := by
  have h : chunk4_140.all (routes 3 pool4_140.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_140,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_10 _ hm
private def chunk4_141 : List (List T) := [[wire240,wire4383,wire8738,wire65416],
  [wire240,wire4383,wire8751,wire21845],
  [wire240,wire4383,wire8751,wire43690],
  [wire240,wire4383,wire12066,wire17476,wire63624]]
private def pool4_141 : List (List (List T)) := []
private theorem checked4_141 : ∀ w ∈ chunk4_141, ¬ Need 4 w.toFinset := by
  have h : chunk4_141.all (routes 3 pool4_141.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_141] at hv
private def chunk4_142 : List (List T) := [[wire240,wire4383,wire12066,wire63624],
  [wire240,wire4383,wire17476,wire34952,wire65314],
  [wire240,wire4383,wire17476,wire36744,wire61986],
  [wire240,wire4383,wire17477,wire34952]]
private def pool4_142 : List (List (List T)) := []
private theorem checked4_142 : ∀ w ∈ chunk4_142, ¬ Need 4 w.toFinset := by
  have h : chunk4_142.all (routes 3 pool4_142.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_142] at hv
private def chunk4_143 : List (List T) := [[wire240,wire4383,wire21845,wire34959],
  [wire240,wire4383,wire34952,wire65314],
  [wire240,wire4383,wire34952,wire65522],
  [wire240,wire4383,wire34959,wire43690]]
private def pool4_143 : List (List (List T)) := []
private theorem checked4_143 : ∀ w ∈ chunk4_143, ¬ Need 4 w.toFinset := by
  have h : chunk4_143.all (routes 3 pool4_143.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_143] at hv
private def chunk4_144 : List (List T) := [[wire240,wire4383,wire36744,wire61986],
  [wire240,wire4497,wire17476,wire17487],
  [wire240,wire4497,wire17476,wire65280],
  [wire240,wire4497,wire17476,wire65520]]
private def pool4_144 : List (List (List T)) := [chunk3_13]
private theorem checked4_144 : ∀ w ∈ chunk4_144, ¬ Need 4 w.toFinset := by
  have h : chunk4_144.all (routes 3 pool4_144.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_144,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_13 _ hm
private def chunk4_145 : List (List T) := [[wire240,wire4497,wire20292,wire61440],
  [wire240,wire4593,wire8738,wire65348],
  [wire240,wire8738,wire13107,wire65348],
  [wire240,wire8738,wire17487,wire21845]]
private def pool4_145 : List (List (List T)) := [chunk3_7, chunk3_13, chunk3_28, chunk3_32]
private theorem checked4_145 : ∀ w ∈ chunk4_145, ¬ Need 4 w.toFinset := by
  have h : chunk4_145.all (routes 3 pool4_145.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_145,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_13 _ hm
  · exact checked3_28 _ hm
  · exact checked3_32 _ hm
private def chunk4_146 : List (List T) := [[wire240,wire8738,wire17487,wire22005],
  [wire240,wire8738,wire17487,wire30471],
  [wire240,wire8738,wire17487,wire30583],
  [wire240,wire8738,wire17487,wire30711]]
private def pool4_146 : List (List (List T)) := []
private theorem checked4_146 : ∀ w ∈ chunk4_146, ¬ Need 4 w.toFinset := by
  have h : chunk4_146.all (routes 3 pool4_146.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_146] at hv
private def chunk4_147 : List (List T) := [[wire240,wire8738,wire17487,wire34824],
  [wire240,wire8738,wire17487,wire34952],
  [wire240,wire8738,wire17487,wire34954],
  [wire240,wire8738,wire17487,wire34968]]
private def pool4_147 : List (List (List T)) := [chunk3_14, chunk3_15, chunk3_33]
private theorem checked4_147 : ∀ w ∈ chunk4_147, ¬ Need 4 w.toFinset := by
  have h : chunk4_147.all (routes 3 pool4_147.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_147,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_14 _ hm
  · exact checked3_15 _ hm
  · exact checked3_33 _ hm
private def chunk4_148 : List (List T) := [[wire240,wire8738,wire17487,wire34984],
  [wire240,wire8738,wire17487,wire35016],
  [wire240,wire8738,wire17487,wire35064],
  [wire240,wire8738,wire17487,wire35464]]
private def pool4_148 : List (List (List T)) := [chunk3_33]
private theorem checked4_148 : ∀ w ∈ chunk4_148, ¬ Need 4 w.toFinset := by
  have h : chunk4_148.all (routes 3 pool4_148.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_148,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_149 : List (List T) := [[wire240,wire8738,wire17487,wire43144],
  [wire240,wire8738,wire17487,wire43690],
  [wire240,wire8738,wire17487,wire43770],
  [wire240,wire8738,wire17519,wire34952]]
private def pool4_149 : List (List (List T)) := [chunk3_7, chunk3_14, chunk3_33, chunk3_35]
private theorem checked4_149 : ∀ w ∈ chunk4_149, ¬ Need 4 w.toFinset := by
  have h : chunk4_149.all (routes 3 pool4_149.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_149,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_14 _ hm
  · exact checked3_33 _ hm
  · exact checked3_35 _ hm
private def chunk4_150 : List (List T) := [[wire240,wire8738,wire17615,wire34952],
  [wire240,wire8738,wire21845,wire48048],
  [wire240,wire8738,wire30583,wire48048],
  [wire240,wire8738,wire34952,wire48048]]
private def pool4_150 : List (List (List T)) := [chunk3_15, chunk3_34]
private theorem checked4_150 : ∀ w ∈ chunk4_150, ¬ Need 4 w.toFinset := by
  have h : chunk4_150.all (routes 3 pool4_150.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_150,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_15 _ hm
  · exact checked3_34 _ hm
private def chunk4_151 : List (List T) := [[wire240,wire8738,wire35064,wire48048],
  [wire240,wire8738,wire43690,wire48048],
  [wire240,wire8738,wire52428,wire65348],
  [wire240,wire8738,wire61166,wire65348]]
private def pool4_151 : List (List (List T)) := [chunk3_34]
private theorem checked4_151 : ∀ w ∈ chunk4_151, ¬ Need 4 w.toFinset := by
  have h : chunk4_151.all (routes 3 pool4_151.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_151,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_34 _ hm
private def chunk4_152 : List (List T) := [[wire240,wire8746,wire17476,wire34959],
  [wire240,wire8746,wire17487,wire34952],
  [wire240,wire8751,wire17476,wire34954],
  [wire240,wire8751,wire17487,wire21845]]
private def pool4_152 : List (List (List T)) := [chunk3_15, chunk3_34, chunk3_35]
private theorem checked4_152 : ∀ w ∈ chunk4_152, ¬ Need 4 w.toFinset := by
  have h : chunk4_152.all (routes 3 pool4_152.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_152,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_15 _ hm
  · exact checked3_34 _ hm
  · exact checked3_35 _ hm
private def chunk4_153 : List (List T) := [[wire240,wire8751,wire17487,wire43690],
  [wire240,wire8802,wire17487,wire34952],
  [wire240,wire8866,wire17487,wire34952],
  [wire240,wire10786,wire17487,wire34952]]
private def pool4_153 : List (List (List T)) := [chunk3_35]
private theorem checked4_153 : ∀ w ∈ chunk4_153, ¬ Need 4 w.toFinset := by
  have h : chunk4_153.all (routes 3 pool4_153.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_153,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_35 _ hm
private def chunk4_154 : List (List T) := [[wire240,wire12066,wire17487,wire21845],
  [wire240,wire12066,wire17487,wire43690],
  [wire240,wire13107,wire17487,wire21845],
  [wire240,wire13107,wire17487,wire26214]]
private def pool4_154 : List (List (List T)) := []
private theorem checked4_154 : ∀ w ∈ chunk4_154, ¬ Need 4 w.toFinset := by
  have h : chunk4_154.all (routes 3 pool4_154.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_154] at hv
private def chunk4_155 : List (List T) := [[wire240,wire13107,wire17487,wire39321],
  [wire240,wire13107,wire17487,wire43690],
  [wire240,wire13107,wire21845,wire65280],
  [wire240,wire13107,wire21845,wire65520]]
private def pool4_155 : List (List (List T)) := []
private theorem checked4_155 : ∀ w ∈ chunk4_155, ¬ Need 4 w.toFinset := by
  have h : chunk4_155.all (routes 3 pool4_155.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_155] at hv
private def chunk4_156 : List (List T) := [[wire240,wire13107,wire26214,wire65280],
  [wire240,wire13107,wire26214,wire65520],
  [wire240,wire13107,wire39321,wire65280],
  [wire240,wire13107,wire39321,wire65520]]
private def pool4_156 : List (List (List T)) := [chunk3_36]
private theorem checked4_156 : ∀ w ∈ chunk4_156, ¬ Need 4 w.toFinset := by
  have h : chunk4_156.all (routes 3 pool4_156.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_156,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_36 _ hm
private def chunk4_157 : List (List T) := [[wire240,wire13107,wire43690,wire65280],
  [wire240,wire13107,wire43690,wire65520],
  [wire240,wire17487,wire21845,wire26214],
  [wire240,wire17487,wire21845,wire26223]]
private def pool4_157 : List (List (List T)) := []
private theorem checked4_157 : ∀ w ∈ chunk4_157, ¬ Need 4 w.toFinset := by
  have h : chunk4_157.all (routes 3 pool4_157.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_157] at hv
private def chunk4_158 : List (List T) := [[wire240,wire17487,wire21845,wire30583],
  [wire240,wire17487,wire21845,wire34952],
  [wire240,wire17487,wire21845,wire34959],
  [wire240,wire17487,wire21845,wire36744]]
private def pool4_158 : List (List (List T)) := [chunk3_8]
private theorem checked4_158 : ∀ w ∈ chunk4_158, ¬ Need 4 w.toFinset := by
  have h : chunk4_158.all (routes 3 pool4_158.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_158,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_8 _ hm
private def chunk4_159 : List (List T) := [[wire240,wire17487,wire21845,wire39321],
  [wire240,wire17487,wire21845,wire52428],
  [wire240,wire17487,wire21845,wire52431],
  [wire240,wire17487,wire21845,wire56797]]
private def pool4_159 : List (List (List T)) := []
private theorem checked4_159 : ∀ w ∈ chunk4_159, ¬ Need 4 w.toFinset := by
  have h : chunk4_159.all (routes 3 pool4_159.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_159] at hv
private def chunk4_160 : List (List T) := [[wire240,wire17487,wire21845,wire61986],
  [wire240,wire17487,wire21845,wire63624],
  [wire240,wire17487,wire26214,wire43690],
  [wire240,wire17487,wire26214,wire52428]]
private def pool4_160 : List (List (List T)) := []
private theorem checked4_160 : ∀ w ∈ chunk4_160, ¬ Need 4 w.toFinset := by
  have h : chunk4_160.all (routes 3 pool4_160.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_160] at hv
private def chunk4_161 : List (List T) := [[wire240,wire17487,wire26223,wire43690],
  [wire240,wire17487,wire30583,wire43690],
  [wire240,wire17487,wire30583,wire56797],
  [wire240,wire17487,wire34952,wire41506]]
private def pool4_161 : List (List (List T)) := [chunk3_8]
private theorem checked4_161 : ∀ w ∈ chunk4_161, ¬ Need 4 w.toFinset := by
  have h : chunk4_161.all (routes 3 pool4_161.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_161,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_8 _ hm
private def chunk4_162 : List (List T) := [[wire240,wire17487,wire34952,wire43690],
  [wire240,wire17487,wire34952,wire56797],
  [wire240,wire17487,wire34959,wire43690],
  [wire240,wire17487,wire35064,wire56797]]
private def pool4_162 : List (List (List T)) := [chunk3_37]
private theorem checked4_162 : ∀ w ∈ chunk4_162, ¬ Need 4 w.toFinset := by
  have h : chunk4_162.all (routes 3 pool4_162.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_162,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_37 _ hm
private def chunk4_163 : List (List T) := [[wire240,wire17487,wire36744,wire43690],
  [wire240,wire17487,wire39321,wire43690],
  [wire240,wire17487,wire39321,wire52428],
  [wire240,wire17487,wire43690,wire52428]]
private def pool4_163 : List (List (List T)) := []
private theorem checked4_163 : ∀ w ∈ chunk4_163, ¬ Need 4 w.toFinset := by
  have h : chunk4_163.all (routes 3 pool4_163.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_163] at hv
private def chunk4_164 : List (List T) := [[wire240,wire17487,wire43690,wire52431],
  [wire240,wire17487,wire43690,wire56797],
  [wire240,wire17487,wire43690,wire61986],
  [wire240,wire17487,wire43690,wire63624]]
private def pool4_164 : List (List (List T)) := []
private theorem checked4_164 : ∀ w ∈ chunk4_164, ¬ Need 4 w.toFinset := by
  have h : chunk4_164.all (routes 3 pool4_164.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_164] at hv
private def chunk4_165 : List (List T) := [[wire240,wire21845,wire26214,wire65280],
  [wire240,wire21845,wire26214,wire65520],
  [wire240,wire21845,wire34952,wire48048],
  [wire240,wire21845,wire39321,wire65280]]
private def pool4_165 : List (List (List T)) := []
private theorem checked4_165 : ∀ w ∈ chunk4_165, ¬ Need 4 w.toFinset := by
  have h : chunk4_165.all (routes 3 pool4_165.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_165] at hv
private def chunk4_166 : List (List T) := [[wire240,wire21845,wire39321,wire65520],
  [wire240,wire21845,wire52428,wire65280],
  [wire240,wire21845,wire52428,wire65520],
  [wire240,wire26210,wire34952,wire65520]]
private def pool4_166 : List (List (List T)) := [chunk3_38]
private theorem checked4_166 : ∀ w ∈ chunk4_166, ¬ Need 4 w.toFinset := by
  have h : chunk4_166.all (routes 3 pool4_166.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_166,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_38 _ hm
private def chunk4_167 : List (List T) := [[wire240,wire26214,wire34952,wire65348],
  [wire240,wire26214,wire34952,wire65524],
  [wire240,wire26214,wire43690,wire65280],
  [wire240,wire26214,wire43690,wire65520]]
private def pool4_167 : List (List (List T)) := [chunk3_39]
private theorem checked4_167 : ∀ w ∈ chunk4_167, ¬ Need 4 w.toFinset := by
  have h : chunk4_167.all (routes 3 pool4_167.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_167,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_39 _ hm
private def chunk4_168 : List (List T) := [[wire240,wire26214,wire52428,wire65280],
  [wire240,wire26214,wire52428,wire65520],
  [wire240,wire34952,wire39321,wire65348],
  [wire240,wire34952,wire39321,wire65524]]
private def pool4_168 : List (List (List T)) := [chunk3_39]
private theorem checked4_168 : ∀ w ∈ chunk4_168, ¬ Need 4 w.toFinset := by
  have h : chunk4_168.all (routes 3 pool4_168.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_168,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_39 _ hm
private def chunk4_169 : List (List T) := [[wire240,wire34952,wire43690,wire48048],
  [wire240,wire34952,wire48048,wire56797],
  [wire240,wire34952,wire61166,wire65348],
  [wire240,wire34952,wire61166,wire65524]]
private def pool4_169 : List (List (List T)) := [chunk3_39]
private theorem checked4_169 : ∀ w ∈ chunk4_169, ¬ Need 4 w.toFinset := by
  have h : chunk4_169.all (routes 3 pool4_169.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_169,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_39 _ hm
private def chunk4_170 : List (List T) := [[wire240,wire39321,wire43690,wire65280],
  [wire240,wire39321,wire43690,wire65520],
  [wire240,wire39321,wire52428,wire65280],
  [wire240,wire39321,wire52428,wire65520]]
private def pool4_170 : List (List (List T)) := []
private theorem checked4_170 : ∀ w ∈ chunk4_170, ¬ Need 4 w.toFinset := by
  have h : chunk4_170.all (routes 3 pool4_170.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_170] at hv
private def chunk4_171 : List (List T) := [[wire240,wire43690,wire52428,wire65280],
  [wire240,wire43690,wire52428,wire65520],
  [wire241,wire4383,wire8738,wire17476],
  [wire241,wire4383,wire17476,wire34952]]
private def pool4_171 : List (List (List T)) := []
private theorem checked4_171 : ∀ w ∈ chunk4_171, ¬ Need 4 w.toFinset := by
  have h : chunk4_171.all (routes 3 pool4_171.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_171] at hv
private def chunk4_172 : List (List T) := [[wire242,wire255,wire4369,wire34952],
  [wire242,wire4369,wire8751,wire34952],
  [wire242,wire4369,wire17487,wire34952],
  [wire242,wire4369,wire34952,wire65280]]
private def pool4_172 : List (List (List T)) := []
private theorem checked4_172 : ∀ w ∈ chunk4_172, ¬ Need 4 w.toFinset := by
  have h : chunk4_172.all (routes 3 pool4_172.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_172] at hv
private def chunk4_173 : List (List T) := [[wire242,wire4369,wire34952,wire65520],
  [wire242,wire8738,wire17487,wire34952],
  [wire242,wire8751,wire17476,wire34952],
  [wire244,wire4369,wire34952,wire65520]]
private def pool4_173 : List (List (List T)) := [chunk3_15, chunk3_33, chunk3_35]
private theorem checked4_173 : ∀ w ∈ chunk4_173, ¬ Need 4 w.toFinset := by
  have h : chunk4_173.all (routes 3 pool4_173.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_173,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_15 _ hm
  · exact checked3_33 _ hm
  · exact checked3_35 _ hm
private def chunk4_174 : List (List T) := [[wire248,wire4369,wire8738,wire17487],
  [wire248,wire8738,wire17487,wire34952],
  [wire255,wire4369,wire8751,wire17476],
  [wire255,wire4369,wire8751,wire20292]]
private def pool4_174 : List (List (List T)) := [chunk3_33]
private theorem checked4_174 : ∀ w ∈ chunk4_174, ¬ Need 4 w.toFinset := by
  have h : chunk4_174.all (routes 3 pool4_174.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_174,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_175 : List (List T) := [[wire255,wire4369,wire8751,wire21845],
  [wire255,wire4369,wire8751,wire43690],
  [wire255,wire4369,wire8751,wire48059],
  [wire255,wire4369,wire8751,wire62532]]
private def pool4_175 : List (List (List T)) := [chunk3_17]
private theorem checked4_175 : ∀ w ∈ chunk4_175, ¬ Need 4 w.toFinset := by
  have h : chunk4_175.all (routes 3 pool4_175.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_175,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_17 _ hm
private def chunk4_176 : List (List T) := [[wire255,wire4369,wire8946,wire26214],
  [wire255,wire4369,wire8946,wire30583],
  [wire255,wire4369,wire8946,wire34952],
  [wire255,wire4369,wire8946,wire36744]]
private def pool4_176 : List (List (List T)) := [chunk3_18]
private theorem checked4_176 : ∀ w ∈ chunk4_176, ¬ Need 4 w.toFinset := by
  have h : chunk4_176.all (routes 3 pool4_176.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_176,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_18 _ hm
private def chunk4_177 : List (List T) := [[wire255,wire4369,wire8946,wire39321],
  [wire255,wire4369,wire8946,wire63624],
  [wire255,wire4369,wire12079,wire17476],
  [wire255,wire4369,wire12274,wire34952]]
private def pool4_177 : List (List (List T)) := [chunk3_18]
private theorem checked4_177 : ∀ w ∈ chunk4_177, ¬ Need 4 w.toFinset := by
  have h : chunk4_177.all (routes 3 pool4_177.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_177,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_18 _ hm
private def chunk4_178 : List (List T) := [[wire255,wire4369,wire13119,wire17476],
  [wire255,wire4369,wire13299,wire34952],
  [wire255,wire4369,wire17476,wire56784],
  [wire255,wire4369,wire17476,wire61999]]
private def pool4_178 : List (List (List T)) := [chunk3_17, chunk3_18]
private theorem checked4_178 : ∀ w ∈ chunk4_178, ¬ Need 4 w.toFinset := by
  have h : chunk4_178.all (routes 3 pool4_178.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_178,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_17 _ hm
  · exact checked3_18 _ hm
private def chunk4_179 : List (List T) := [[wire255,wire4369,wire17476,wire65327],
  [wire255,wire4369,wire17652,wire34959],
  [wire255,wire4369,wire34952,wire56589],
  [wire255,wire4369,wire34952,wire62194]]
private def pool4_179 : List (List (List T)) := [chunk3_10]
private theorem checked4_179 : ∀ w ∈ chunk4_179, ¬ Need 4 w.toFinset := by
  have h : chunk4_179.all (routes 3 pool4_179.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_179,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_10 _ hm
private def chunk4_180 : List (List T) := [[wire255,wire4369,wire34952,wire65522],
  [wire255,wire4383,wire8738,wire21845],
  [wire255,wire4383,wire8738,wire30583],
  [wire255,wire4383,wire8738,wire34952]]
private def pool4_180 : List (List (List T)) := [chunk3_9, chunk3_17]
private theorem checked4_180 : ∀ w ∈ chunk4_180, ¬ Need 4 w.toFinset := by
  have h : chunk4_180.all (routes 3 pool4_180.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_180,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_9 _ hm
  · exact checked3_17 _ hm
private def chunk4_181 : List (List T) := [[wire255,wire4383,wire8738,wire36744],
  [wire255,wire4383,wire8738,wire43690],
  [wire255,wire4383,wire8738,wire63624],
  [wire255,wire4383,wire12066,wire34952]]
private def pool4_181 : List (List (List T)) := [chunk3_17]
private theorem checked4_181 : ∀ w ∈ chunk4_181, ¬ Need 4 w.toFinset := by
  have h : chunk4_181.all (routes 3 pool4_181.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_181,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_17 _ hm
private def chunk4_182 : List (List T) := [[wire255,wire4383,wire21845,wire34952],
  [wire255,wire4383,wire34952,wire43690],
  [wire255,wire4383,wire34952,wire56797],
  [wire255,wire4383,wire34952,wire61986]]
private def pool4_182 : List (List (List T)) := [chunk3_16]
private theorem checked4_182 : ∀ w ∈ chunk4_182, ¬ Need 4 w.toFinset := by
  have h : chunk4_182.all (routes 3 pool4_182.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_182,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_16 _ hm
private def chunk4_183 : List (List T) := [[wire255,wire4593,wire8738,wire17476],
  [wire255,wire4593,wire8738,wire20292],
  [wire255,wire4593,wire8738,wire26214],
  [wire255,wire4593,wire8738,wire39321]]
private def pool4_183 : List (List (List T)) := [chunk3_18]
private theorem checked4_183 : ∀ w ∈ chunk4_183, ¬ Need 4 w.toFinset := by
  have h : chunk4_183.all (routes 3 pool4_183.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_183,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_18 _ hm
private def chunk4_184 : List (List T) := [[wire255,wire4593,wire8738,wire48059],
  [wire255,wire4593,wire8738,wire62532],
  [wire255,wire4593,wire12066,wire17476],
  [wire255,wire4593,wire17476,wire26214]]
private def pool4_184 : List (List (List T)) := [chunk3_11]
private theorem checked4_184 : ∀ w ∈ chunk4_184, ¬ Need 4 w.toFinset := by
  have h : chunk4_184.all (routes 3 pool4_184.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_184,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_11 _ hm
private def chunk4_185 : List (List T) := [[wire255,wire4593,wire17476,wire39321],
  [wire255,wire4593,wire17476,wire56797],
  [wire255,wire4593,wire17476,wire61986],
  [wire255,wire8738,wire13119,wire34952]]
private def pool4_185 : List (List (List T)) := [chunk3_17]
private theorem checked4_185 : ∀ w ∈ chunk4_185, ¬ Need 4 w.toFinset := by
  have h : chunk4_185.all (routes 3 pool4_185.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_185,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_17 _ hm
private def chunk4_186 : List (List T) := [[wire255,wire8738,wire13299,wire17476],
  [wire255,wire8738,wire17476,wire60942],
  [wire255,wire8738,wire17487,wire35064],
  [wire255,wire8738,wire34952,wire61152]]
private def pool4_186 : List (List (List T)) := [chunk3_18]
private theorem checked4_186 : ∀ w ∈ chunk4_186, ¬ Need 4 w.toFinset := by
  have h : chunk4_186.all (routes 3 pool4_186.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_186,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_18 _ hm
private def chunk4_187 : List (List T) := [[wire255,wire8751,wire17476,wire21845],
  [wire255,wire8751,wire17476,wire43690],
  [wire255,wire8751,wire17476,wire61166],
  [wire255,wire8946,wire26214,wire34952]]
private def pool4_187 : List (List (List T)) := []
private theorem checked4_187 : ∀ w ∈ chunk4_187, ¬ Need 4 w.toFinset := by
  have h : chunk4_187.all (routes 3 pool4_187.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_187] at hv
private def chunk4_188 : List (List T) := [[wire255,wire8946,wire34952,wire39321],
  [wire255,wire8946,wire34952,wire61166],
  [wire256,wire8738,wire17487,wire35064],
  [wire512,wire8738,wire17487,wire35064]]
private def pool4_188 : List (List (List T)) := [chunk3_33]
private theorem checked4_188 : ∀ w ∈ chunk4_188, ¬ Need 4 w.toFinset := by
  have h : chunk4_188.all (routes 3 pool4_188.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_188,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_189 : List (List T) := [[wire1024,wire8738,wire17487,wire35064],
  [wire1039,wire8738,wire17476,wire35064],
  [wire1911,wire3840,wire4383,wire8738],
  [wire2048,wire8738,wire17487,wire35064]]
private def pool4_189 : List (List (List T)) := [chunk3_33]
private theorem checked4_189 : ∀ w ∈ chunk4_189, ¬ Need 4 w.toFinset := by
  have h : chunk4_189.all (routes 3 pool4_189.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_189,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_190 : List (List T) := [[wire2288,wire8738,wire17487,wire34952],
  [wire3003,wire3840,wire4593,wire8738],
  [wire3840,wire4369,wire61999,wire62532],
  [wire3840,wire4369,wire62194,wire63624]]
private def pool4_190 : List (List (List T)) := [chunk3_33]
private theorem checked4_190 : ∀ w ∈ chunk4_190, ¬ Need 4 w.toFinset := by
  have h : chunk4_190.all (routes 3 pool4_190.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_190,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_191 : List (List T) := [[wire3840,wire4369,wire62532,wire65327],
  [wire3840,wire4369,wire63624,wire65522],
  [wire3840,wire4381,wire34952,wire61440],
  [wire3840,wire4383,wire8738,wire63624]]
private def pool4_191 : List (List (List T)) := [chunk3_19, chunk3_23, chunk3_24]
private theorem checked4_191 : ∀ w ∈ chunk4_191, ¬ Need 4 w.toFinset := by
  have h : chunk4_191.all (routes 3 pool4_191.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_191,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_19 _ hm
  · exact checked3_23 _ hm
  · exact checked3_24 _ hm
private def chunk4_192 : List (List T) := [[wire3840,wire4383,wire8738,wire65416],
  [wire3840,wire4383,wire12066,wire63624],
  [wire3840,wire4383,wire21845,wire63624],
  [wire3840,wire4383,wire34952,wire61442]]
private def pool4_192 : List (List (List T)) := [chunk3_19, chunk3_24, chunk3_25, chunk3_26]
private theorem checked4_192 : ∀ w ∈ chunk4_192, ¬ Need 4 w.toFinset := by
  have h : chunk4_192.all (routes 3 pool4_192.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_192,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_19 _ hm
  · exact checked3_24 _ hm
  · exact checked3_25 _ hm
  · exact checked3_26 _ hm
private def chunk4_193 : List (List T) := [[wire3840,wire4383,wire34954,wire61440],
  [wire3840,wire4383,wire43690,wire63624],
  [wire3840,wire4383,wire56797,wire63624],
  [wire3840,wire4383,wire61986,wire63624]]
private def pool4_193 : List (List (List T)) := [chunk3_19, chunk3_25, chunk3_26, chunk3_27]
private theorem checked4_193 : ∀ w ∈ chunk4_193, ¬ Need 4 w.toFinset := by
  have h : chunk4_193.all (routes 3 pool4_193.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_193,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_19 _ hm
  · exact checked3_25 _ hm
  · exact checked3_26 _ hm
  · exact checked3_27 _ hm
private def chunk4_194 : List (List T) := [[wire3840,wire4383,wire63624,wire64170],
  [wire3840,wire4561,wire17476,wire61440],
  [wire3840,wire4593,wire8738,wire62532],
  [wire3840,wire4593,wire8738,wire65348]]
private def pool4_194 : List (List (List T)) := [chunk3_20, chunk3_27, chunk3_28, chunk3_29]
private theorem checked4_194 : ∀ w ∈ chunk4_194, ¬ Need 4 w.toFinset := by
  have h : chunk4_194.all (routes 3 pool4_194.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_194,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_20 _ hm
  · exact checked3_27 _ hm
  · exact checked3_28 _ hm
  · exact checked3_29 _ hm
private def chunk4_195 : List (List T) := [[wire3840,wire4593,wire12066,wire62532],
  [wire3840,wire4593,wire17476,wire61472],
  [wire3840,wire4593,wire17508,wire61440],
  [wire3840,wire4593,wire26214,wire62532]]
private def pool4_195 : List (List (List T)) := [chunk3_20, chunk3_29, chunk3_30]
private theorem checked4_195 : ∀ w ∈ chunk4_195, ¬ Need 4 w.toFinset := by
  have h : chunk4_195.all (routes 3 pool4_195.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_195,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_20 _ hm
  · exact checked3_29 _ hm
  · exact checked3_30 _ hm
private def chunk4_196 : List (List T) := [[wire3840,wire4593,wire39321,wire62532],
  [wire3840,wire4593,wire56797,wire62532],
  [wire3840,wire4593,wire61986,wire62532],
  [wire3840,wire4593,wire62532,wire63078]]
private def pool4_196 : List (List (List T)) := [chunk3_20, chunk3_30, chunk3_31]
private theorem checked4_196 : ∀ w ∈ chunk4_196, ¬ Need 4 w.toFinset := by
  have h : chunk4_196.all (routes 3 pool4_196.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_196,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_20 _ hm
  · exact checked3_30 _ hm
  · exact checked3_31 _ hm
private def chunk4_197 : List (List T) := [[wire3840,wire8738,wire13119,wire63624],
  [wire3840,wire8738,wire13299,wire62532],
  [wire3840,wire8738,wire17487,wire30471],
  [wire3840,wire8738,wire17487,wire35064]]
private def pool4_197 : List (List (List T)) := [chunk3_32]
private theorem checked4_197 : ∀ w ∈ chunk4_197, ¬ Need 4 w.toFinset := by
  have h : chunk4_197.all (routes 3 pool4_197.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_197,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_32 _ hm
private def chunk4_198 : List (List T) := [[wire3840,wire8738,wire35064,wire48048],
  [wire3840,wire8738,wire60942,wire62532],
  [wire3840,wire8738,wire61152,wire63624],
  [wire3840,wire13119,wire21845,wire61440]]
private def pool4_198 : List (List (List T)) := [chunk3_21, chunk3_34, chunk3_36]
private theorem checked4_198 : ∀ w ∈ chunk4_198, ¬ Need 4 w.toFinset := by
  have h : chunk4_198.all (routes 3 pool4_198.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_198,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_21 _ hm
  · exact checked3_34 _ hm
  · exact checked3_36 _ hm
private def chunk4_199 : List (List T) := [[wire3840,wire13119,wire43690,wire61440],
  [wire3840,wire13299,wire26214,wire61440],
  [wire3840,wire13299,wire39321,wire61440],
  [wire3840,wire17476,wire60974,wire61440]]
private def pool4_199 : List (List (List T)) := [chunk3_21, chunk3_36, chunk3_37, chunk3_38]
private theorem checked4_199 : ∀ w ∈ chunk4_199, ¬ Need 4 w.toFinset := by
  have h : chunk4_199.all (routes 3 pool4_199.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_199,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_21 _ hm
  · exact checked3_36 _ hm
  · exact checked3_37 _ hm
  · exact checked3_38 _ hm
private def chunk4_200 : List (List T) := [[wire3840,wire17487,wire35064,wire56797],
  [wire3840,wire34952,wire61154,wire61440],
  [wire3842,wire4383,wire34952,wire61440],
  [wire3855,wire4369,wire20292,wire63624]]
private def pool4_200 : List (List (List T)) := [chunk3_21, chunk3_25, chunk3_26, chunk3_39, chunk3_40]
private theorem checked4_200 : ∀ w ∈ chunk4_200, ¬ Need 4 w.toFinset := by
  have h : chunk4_200.all (routes 3 pool4_200.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_200,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked3_21 _ hm
  · exact checked3_25 _ hm
  · exact checked3_26 _ hm
  · exact checked3_39 _ hm
  · exact checked3_40 _ hm
private def chunk4_201 : List (List T) := [[wire3855,wire8738,wire17487,wire35064],
  [wire3872,wire4593,wire17476,wire61440],
  [wire4080,wire4369,wire36744,wire62532],
  [wire4080,wire8738,wire17487,wire35064]]
private def pool4_201 : List (List (List T)) := [chunk3_22, chunk3_29, chunk3_30]
private theorem checked4_201 : ∀ w ∈ chunk4_201, ¬ Need 4 w.toFinset := by
  have h : chunk4_201.all (routes 3 pool4_201.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_201,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_22 _ hm
  · exact checked3_29 _ hm
  · exact checked3_30 _ hm
private def chunk4_202 : List (List T) := [[wire4095,wire4383,wire8738,wire36744],
  [wire4095,wire4593,wire8738,wire20292],
  [wire4095,wire8738,wire17487,wire35064],
  [wire4096,wire8738,wire17487,wire35064]]
private def pool4_202 : List (List (List T)) := []
private theorem checked4_202 : ∀ w ∈ chunk4_202, ¬ Need 4 w.toFinset := by
  have h : chunk4_202.all (routes 3 pool4_202.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_202] at hv
private def chunk4_203 : List (List T) := [[wire4369,wire4383,wire8738,wire65416],
  [wire4369,wire4383,wire17476,wire65416],
  [wire4369,wire4593,wire8738,wire65348],
  [wire4369,wire4593,wire34952,wire65348]]
private def pool4_203 : List (List (List T)) := [chunk3_24, chunk3_25, chunk3_28, chunk3_30]
private theorem checked4_203 : ∀ w ∈ chunk4_203, ¬ Need 4 w.toFinset := by
  have h : chunk4_203.all (routes 3 pool4_203.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_203,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_24 _ hm
  · exact checked3_25 _ hm
  · exact checked3_28 _ hm
  · exact checked3_30 _ hm
private def chunk4_204 : List (List T) := [[wire4369,wire8738,wire8751,wire65416],
  [wire4369,wire8738,wire8946,wire65348],
  [wire4369,wire8738,wire17487,wire30471],
  [wire4369,wire8738,wire17487,wire35064]]
private def pool4_204 : List (List (List T)) := [chunk3_32]
private theorem checked4_204 : ∀ w ∈ chunk4_204, ¬ Need 4 w.toFinset := by
  have h : chunk4_204.all (routes 3 pool4_204.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_204,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_32 _ hm
private def chunk4_205 : List (List T) := [[wire4369,wire8738,wire17487,wire35064,wire65280],
  [wire4369,wire8738,wire35064,wire48048],
  [wire4369,wire8738,wire65295,wire65348],
  [wire4369,wire8738,wire65416,wire65520]]
private def pool4_205 : List (List (List T)) := [chunk3_23]
private theorem checked4_205 : ∀ w ∈ chunk4_205, ¬ Need 4 w.toFinset := by
  have h : chunk4_205.all (routes 3 pool4_205.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_205,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_23 _ hm
private def chunk4_206 : List (List T) := [[wire4369,wire8751,wire17476,wire35071],
  [wire4369,wire8751,wire17476,wire65280],
  [wire4369,wire8751,wire20292,wire65280],
  [wire4369,wire8751,wire21845,wire65280]]
private def pool4_206 : List (List (List T)) := [chunk3_36]
private theorem checked4_206 : ∀ w ∈ chunk4_206, ¬ Need 4 w.toFinset := by
  have h : chunk4_206.all (routes 3 pool4_206.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_206,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_36 _ hm
private def chunk4_207 : List (List T) := [[wire4369,wire8751,wire43690,wire65280],
  [wire4369,wire8751,wire48059,wire65280],
  [wire4369,wire8751,wire62532,wire65280],
  [wire4369,wire8751,wire65280,wire65348]]
private def pool4_207 : List (List (List T)) := [chunk3_23, chunk3_36]
private theorem checked4_207 : ∀ w ∈ chunk4_207, ¬ Need 4 w.toFinset := by
  have h : chunk4_207.all (routes 3 pool4_207.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_207,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_23 _ hm
  · exact checked3_36 _ hm
private def chunk4_208 : List (List T) := [[wire4369,wire8946,wire17663,wire34952],
  [wire4369,wire8946,wire26214,wire65280],
  [wire4369,wire8946,wire30583,wire65280],
  [wire4369,wire8946,wire34952,wire65280]]
private def pool4_208 : List (List (List T)) := [chunk3_36]
private theorem checked4_208 : ∀ w ∈ chunk4_208, ¬ Need 4 w.toFinset := by
  have h : chunk4_208.all (routes 3 pool4_208.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_208,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_36 _ hm
private def chunk4_209 : List (List T) := [[wire4369,wire8946,wire36744,wire65280],
  [wire4369,wire8946,wire39321,wire65280],
  [wire4369,wire8946,wire63624,wire65280],
  [wire4369,wire8946,wire65280,wire65416]]
private def pool4_209 : List (List (List T)) := [chunk3_23, chunk3_36]
private theorem checked4_209 : ∀ w ∈ chunk4_209, ¬ Need 4 w.toFinset := by
  have h : chunk4_209.all (routes 3 pool4_209.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_209,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_23 _ hm
  · exact checked3_36 _ hm
private def chunk4_210 : List (List T) := [[wire4369,wire12079,wire17476,wire65280],
  [wire4369,wire12079,wire20292,wire61440],
  [wire4369,wire12274,wire34952,wire65280],
  [wire4369,wire12274,wire36744,wire61440]]
private def pool4_210 : List (List (List T)) := []
private theorem checked4_210 : ∀ w ∈ chunk4_210, ¬ Need 4 w.toFinset := by
  have h : chunk4_210.all (routes 3 pool4_210.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_210] at hv
private def chunk4_211 : List (List T) := [[wire4369,wire13107,wire17487,wire35064],
  [wire4369,wire13119,wire17476,wire65280],
  [wire4369,wire13299,wire34952,wire65280],
  [wire4369,wire17476,wire17487,wire65423]]
private def pool4_211 : List (List (List T)) := [chunk3_36, chunk3_37]
private theorem checked4_211 : ∀ w ∈ chunk4_211, ¬ Need 4 w.toFinset := by
  have h : chunk4_211.all (routes 3 pool4_211.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_211,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_36 _ hm
  · exact checked3_37 _ hm
private def chunk4_212 : List (List T) := [[wire4369,wire17476,wire56784,wire65280],
  [wire4369,wire17476,wire61999,wire65280],
  [wire4369,wire17476,wire65280,wire65327],
  [wire4369,wire17476,wire65416,wire65520]]
private def pool4_212 : List (List (List T)) := [chunk3_23]
private theorem checked4_212 : ∀ w ∈ chunk4_212, ¬ Need 4 w.toFinset := by
  have h : chunk4_212.all (routes 3 pool4_212.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_212,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_23 _ hm
private def chunk4_213 : List (List T) := [[wire4369,wire17476,wire65423,wire65520],
  [wire4369,wire17487,wire35064,wire52428],
  [wire4369,wire17487,wire35064,wire56797],
  [wire4369,wire17652,wire34959,wire65280]]
private def pool4_213 : List (List (List T)) := [chunk3_10, chunk3_24, chunk3_37]
private theorem checked4_213 : ∀ w ∈ chunk4_213, ¬ Need 4 w.toFinset := by
  have h : chunk4_213.all (routes 3 pool4_213.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_213,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_10 _ hm
  · exact checked3_24 _ hm
  · exact checked3_37 _ hm
private def chunk4_214 : List (List T) := [[wire4369,wire20292,wire61440,wire65327],
  [wire4369,wire20292,wire61680,wire63624],
  [wire4369,wire34952,wire35064,wire65524],
  [wire4369,wire34952,wire56589,wire65280]]
private def pool4_214 : List (List (List T)) := [chunk3_23, chunk3_39]
private theorem checked4_214 : ∀ w ∈ chunk4_214, ¬ Need 4 w.toFinset := by
  have h : chunk4_214.all (routes 3 pool4_214.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_214,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_23 _ hm
  · exact checked3_39 _ hm
private def chunk4_215 : List (List T) := [[wire4369,wire34952,wire62194,wire65280],
  [wire4369,wire34952,wire65280,wire65522],
  [wire4369,wire34952,wire65295,wire65348],
  [wire4369,wire34952,wire65295,wire65524]]
private def pool4_215 : List (List (List T)) := [chunk3_23, chunk3_24]
private theorem checked4_215 : ∀ w ∈ chunk4_215, ¬ Need 4 w.toFinset := by
  have h : chunk4_215.all (routes 3 pool4_215.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_215,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_23 _ hm
  · exact checked3_24 _ hm
private def chunk4_216 : List (List T) := [[wire4369,wire36744,wire61440,wire65522],
  [wire4369,wire36744,wire61455,wire62532],
  [wire4383,wire8738,wire17476,wire65416],
  [wire4383,wire8738,wire17487,wire35064]]
private def pool4_216 : List (List (List T)) := [chunk3_23]
private theorem checked4_216 : ∀ w ∈ chunk4_216, ¬ Need 4 w.toFinset := by
  have h : chunk4_216.all (routes 3 pool4_216.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_216,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_23 _ hm
private def chunk4_217 : List (List T) := [[wire4383,wire8738,wire21845,wire65280],
  [wire4383,wire8738,wire28791,wire61440],
  [wire4383,wire8738,wire30583,wire65280],
  [wire4383,wire8738,wire34952,wire35071]]
private def pool4_217 : List (List (List T)) := [chunk3_36]
private theorem checked4_217 : ∀ w ∈ chunk4_217, ¬ Need 4 w.toFinset := by
  have h : chunk4_217.all (routes 3 pool4_217.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_217,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_36 _ hm
private def chunk4_218 : List (List T) := [[wire4383,wire8738,wire34952,wire65280],
  [wire4383,wire8738,wire34952,wire65416],
  [wire4383,wire8738,wire34959,wire35064],
  [wire4383,wire8738,wire36744,wire61440]]
private def pool4_218 : List (List (List T)) := [chunk3_24, chunk3_26]
private theorem checked4_218 : ∀ w ∈ chunk4_218, ¬ Need 4 w.toFinset := by
  have h : chunk4_218.all (routes 3 pool4_218.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_218,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_24 _ hm
  · exact checked3_26 _ hm
private def chunk4_219 : List (List T) := [[wire4383,wire8738,wire36744,wire63624],
  [wire4383,wire8738,wire36744,wire65280],
  [wire4383,wire8738,wire36744,wire65416],
  [wire4383,wire8738,wire43690,wire65280]]
private def pool4_219 : List (List (List T)) := [chunk3_24, chunk3_26, chunk3_36]
private theorem checked4_219 : ∀ w ∈ chunk4_219, ¬ Need 4 w.toFinset := by
  have h : chunk4_219.all (routes 3 pool4_219.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_219,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_24 _ hm
  · exact checked3_26 _ hm
  · exact checked3_36 _ hm
private def chunk4_220 : List (List T) := [[wire4383,wire8738,wire61440,wire65416],
  [wire4383,wire8738,wire61695,wire63624],
  [wire4383,wire8738,wire63624,wire65280],
  [wire4383,wire8738,wire63624,wire65416]]
private def pool4_220 : List (List (List T)) := [chunk3_24, chunk3_27]
private theorem checked4_220 : ∀ w ∈ chunk4_220, ¬ Need 4 w.toFinset := by
  have h : chunk4_220.all (routes 3 pool4_220.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_220,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_24 _ hm
  · exact checked3_27 _ hm
private def chunk4_221 : List (List T) := [[wire4383,wire8738,wire65280,wire65416],
  [wire4383,wire8738,wire65416],
  [wire4383,wire12066,wire34952,wire65280],
  [wire4383,wire12066,wire36744,wire61440]]
private def pool4_221 : List (List (List T)) := [chunk3_0, chunk3_9, chunk3_24, chunk3_25, chunk3_27, chunk3_28, chunk3_32, chunk3_34]
private theorem checked4_221 : ∀ w ∈ chunk4_221, ¬ Need 4 w.toFinset := by
  have h : chunk4_221.all (routes 3 pool4_221.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_221,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_9 _ hm
  · exact checked3_24 _ hm
  · exact checked3_25 _ hm
  · exact checked3_27 _ hm
  · exact checked3_28 _ hm
  · exact checked3_32 _ hm
  · exact checked3_34 _ hm
private def chunk4_222 : List (List T) := [[wire4383,wire21845,wire34952,wire65280],
  [wire4383,wire21845,wire36744,wire61440],
  [wire4383,wire34952,wire43690,wire65280],
  [wire4383,wire34952,wire56797,wire65280]]
private def pool4_222 : List (List (List T)) := [chunk3_24, chunk3_25, chunk3_26, chunk3_27]
private theorem checked4_222 : ∀ w ∈ chunk4_222, ¬ Need 4 w.toFinset := by
  have h : chunk4_222.all (routes 3 pool4_222.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_222,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_24 _ hm
  · exact checked3_25 _ hm
  · exact checked3_26 _ hm
  · exact checked3_27 _ hm
private def chunk4_223 : List (List T) := [[wire4383,wire34952,wire61986,wire65280],
  [wire4383,wire34952,wire65280,wire65314],
  [wire4383,wire36744,wire43690,wire61440],
  [wire4383,wire36744,wire44970,wire61440]]
private def pool4_223 : List (List (List T)) := [chunk3_26, chunk3_27]
private theorem checked4_223 : ∀ w ∈ chunk4_223, ¬ Need 4 w.toFinset := by
  have h : chunk4_223.all (routes 3 pool4_223.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_223,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_26 _ hm
  · exact checked3_27 _ hm
private def chunk4_224 : List (List T) := [[wire4383,wire36744,wire56797,wire61440],
  [wire4383,wire36744,wire61440,wire61986],
  [wire4593,wire8738,wire17476,wire17663],
  [wire4593,wire8738,wire17476,wire65280]]
private def pool4_224 : List (List (List T)) := [chunk3_24, chunk3_27, chunk3_28]
private theorem checked4_224 : ∀ w ∈ chunk4_224, ¬ Need 4 w.toFinset := by
  have h : chunk4_224.all (routes 3 pool4_224.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_224,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_24 _ hm
  · exact checked3_27 _ hm
  · exact checked3_28 _ hm
private def chunk4_225 : List (List T) := [[wire4593,wire8738,wire17476,wire65348],
  [wire4593,wire8738,wire17487,wire17652],
  [wire4593,wire8738,wire17487,wire35064],
  [wire4593,wire8738,wire20292,wire61440]]
private def pool4_225 : List (List (List T)) := [chunk3_28, chunk3_30]
private theorem checked4_225 : ∀ w ∈ chunk4_225, ¬ Need 4 w.toFinset := by
  have h : chunk4_225.all (routes 3 pool4_225.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_225,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_28 _ hm
  · exact checked3_30 _ hm
private def chunk4_226 : List (List T) := [[wire4593,wire8738,wire20292,wire62532],
  [wire4593,wire8738,wire20292,wire65280],
  [wire4593,wire8738,wire20292,wire65348],
  [wire4593,wire8738,wire26214,wire65280]]
private def pool4_226 : List (List (List T)) := [chunk3_28, chunk3_30, chunk3_36]
private theorem checked4_226 : ∀ w ∈ chunk4_226, ¬ Need 4 w.toFinset := by
  have h : chunk4_226.all (routes 3 pool4_226.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_226,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_28 _ hm
  · exact checked3_30 _ hm
  · exact checked3_36 _ hm
private def chunk4_227 : List (List T) := [[wire4593,wire8738,wire34952,wire65348],
  [wire4593,wire8738,wire39321,wire65280],
  [wire4593,wire8738,wire45243,wire61440],
  [wire4593,wire8738,wire48059,wire65280]]
private def pool4_227 : List (List (List T)) := [chunk3_36]
private theorem checked4_227 : ∀ w ∈ chunk4_227, ¬ Need 4 w.toFinset := by
  have h : chunk4_227.all (routes 3 pool4_227.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_227,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_36 _ hm
private def chunk4_228 : List (List T) := [[wire4593,wire8738,wire61440,wire65348],
  [wire4593,wire8738,wire61695,wire62532],
  [wire4593,wire8738,wire62532,wire65280],
  [wire4593,wire8738,wire62532,wire65348]]
private def pool4_228 : List (List (List T)) := [chunk3_28, chunk3_31]
private theorem checked4_228 : ∀ w ∈ chunk4_228, ¬ Need 4 w.toFinset := by
  have h : chunk4_228.all (routes 3 pool4_228.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_228,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_28 _ hm
  · exact checked3_31 _ hm
private def chunk4_229 : List (List T) := [[wire4593,wire8738,wire65280,wire65348],
  [wire4593,wire8738,wire65348],
  [wire4593,wire12066,wire17476,wire65280],
  [wire4593,wire12066,wire20292,wire61440]]
private def pool4_229 : List (List (List T)) := [chunk3_7, chunk3_11, chunk3_28, chunk3_29, chunk3_31, chunk3_32, chunk3_34]
private theorem checked4_229 : ∀ w ∈ chunk4_229, ¬ Need 4 w.toFinset := by
  have h : chunk4_229.all (routes 3 pool4_229.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_229,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_11 _ hm
  · exact checked3_28 _ hm
  · exact checked3_29 _ hm
  · exact checked3_31 _ hm
  · exact checked3_32 _ hm
  · exact checked3_34 _ hm
private def chunk4_230 : List (List T) := [[wire4593,wire17476,wire26214,wire65280],
  [wire4593,wire17476,wire39321,wire65280],
  [wire4593,wire17476,wire56797,wire65280],
  [wire4593,wire17476,wire61986,wire65280]]
private def pool4_230 : List (List (List T)) := [chunk3_28, chunk3_30, chunk3_31]
private theorem checked4_230 : ∀ w ∈ chunk4_230, ¬ Need 4 w.toFinset := by
  have h : chunk4_230.all (routes 3 pool4_230.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_230,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_28 _ hm
  · exact checked3_30 _ hm
  · exact checked3_31 _ hm
private def chunk4_231 : List (List T) := [[wire4593,wire17476,wire65280,wire65314],
  [wire4593,wire20292,wire26214,wire61440],
  [wire4593,wire20292,wire28518,wire61440],
  [wire4593,wire20292,wire39321,wire61440]]
private def pool4_231 : List (List (List T)) := [chunk3_30, chunk3_31]
private theorem checked4_231 : ∀ w ∈ chunk4_231, ¬ Need 4 w.toFinset := by
  have h : chunk4_231.all (routes 3 pool4_231.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_231,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_30 _ hm
  · exact checked3_31 _ hm
private def chunk4_232 : List (List T) := [[wire4593,wire20292,wire56797,wire61440],
  [wire4593,wire20292,wire61440,wire61986],
  [wire7953,wire8738,wire17487,wire35064],
  [wire8192,wire8738,wire17487,wire35064]]
private def pool4_232 : List (List (List T)) := [chunk3_28, chunk3_31, chunk3_33]
private theorem checked4_232 : ∀ w ∈ chunk4_232, ¬ Need 4 w.toFinset := by
  have h : chunk4_232.all (routes 3 pool4_232.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_232,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_28 _ hm
  · exact checked3_31 _ hm
  · exact checked3_33 _ hm
private def chunk4_233 : List (List T) := [[wire8738,wire8751,wire17487,wire35064],
  [wire8738,wire8946,wire17487,wire35064],
  [wire8738,wire12066,wire17487,wire35064],
  [wire8738,wire13107,wire17487,wire35064]]
private def pool4_233 : List (List (List T)) := [chunk3_33]
private theorem checked4_233 : ∀ w ∈ chunk4_233, ¬ Need 4 w.toFinset := by
  have h : chunk4_233.all (routes 3 pool4_233.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_233,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_234 : List (List T) := [[wire8738,wire13119,wire34952,wire65280],
  [wire8738,wire13119,wire36744,wire61440],
  [wire8738,wire13299,wire17476,wire65280],
  [wire8738,wire13299,wire20292,wire61440]]
private def pool4_234 : List (List (List T)) := [chunk3_32, chunk3_36]
private theorem checked4_234 : ∀ w ∈ chunk4_234, ¬ Need 4 w.toFinset := by
  have h : chunk4_234.all (routes 3 pool4_234.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_234,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_32 _ hm
  · exact checked3_36 _ hm
private def chunk4_235 : List (List T) := [[wire8738,wire16384,wire17487,wire35064],
  [wire8738,wire16399,wire17476,wire35064],
  [wire8738,wire17472,wire35064,wire65520],
  [wire8738,wire17476,wire17487,wire30471]]
private def pool4_235 : List (List (List T)) := [chunk3_32, chunk3_33, chunk3_38]
private theorem checked4_235 : ∀ w ∈ chunk4_235, ¬ Need 4 w.toFinset := by
  have h : chunk4_235.all (routes 3 pool4_235.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_235,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_32 _ hm
  · exact checked3_33 _ hm
  · exact checked3_38 _ hm
private def chunk4_236 : List (List T) := [[wire8738,wire17476,wire17487,wire35064],
  [wire8738,wire17476,wire30471,wire65520],
  [wire8738,wire17476,wire35064,wire48048],
  [wire8738,wire17476,wire35064,wire65520]]
private def pool4_236 : List (List (List T)) := [chunk3_33]
private theorem checked4_236 : ∀ w ∈ chunk4_236, ¬ Need 4 w.toFinset := by
  have h : chunk4_236.all (routes 3 pool4_236.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_236,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_237 : List (List T) := [[wire8738,wire17476,wire35064,wire65524],
  [wire8738,wire17476,wire60942,wire65280],
  [wire8738,wire17487,wire17652,wire35064],
  [wire8738,wire17487,wire17663,wire35064]]
private def pool4_237 : List (List (List T)) := [chunk3_33, chunk3_34, chunk3_37, chunk3_39]
private theorem checked4_237 : ∀ w ∈ chunk4_237, ¬ Need 4 w.toFinset := by
  have h : chunk4_237.all (routes 3 pool4_237.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_237,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_33 _ hm
  · exact checked3_34 _ hm
  · exact checked3_37 _ hm
  · exact checked3_39 _ hm
private def chunk4_238 : List (List T) := [[wire8738,wire17487,wire20292,wire35064],
  [wire8738,wire17487,wire20303,wire35064],
  [wire8738,wire17487,wire21845,wire35064],
  [wire8738,wire17487,wire21845,wire65295]]
private def pool4_238 : List (List (List T)) := [chunk3_33]
private theorem checked4_238 : ∀ w ∈ chunk4_238, ¬ Need 4 w.toFinset := by
  have h : chunk4_238.all (routes 3 pool4_238.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_238,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_239 : List (List T) := [[wire8738,wire17487,wire21855,wire35064],
  [wire8738,wire17487,wire26214,wire35064],
  [wire8738,wire17487,wire26223,wire35064],
  [wire8738,wire17487,wire30471]]
private def pool4_239 : List (List (List T)) := [chunk3_0, chunk3_32, chunk3_33, chunk3_37]
private theorem checked4_239 : ∀ w ∈ chunk4_239, ¬ Need 4 w.toFinset := by
  have h : chunk4_239.all (routes 3 pool4_239.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_239,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_0 _ hm
  · exact checked3_32 _ hm
  · exact checked3_33 _ hm
  · exact checked3_37 _ hm
private def chunk4_240 : List (List T) := [[wire8738,wire17487,wire30471,wire34952],
  [wire8738,wire17487,wire30471,wire35064],
  [wire8738,wire17487,wire30471,wire61440],
  [wire8738,wire17487,wire30583,wire35064]]
private def pool4_240 : List (List (List T)) := [chunk3_32, chunk3_33]
private theorem checked4_240 : ∀ w ∈ chunk4_240, ¬ Need 4 w.toFinset := by
  have h : chunk4_240.all (routes 3 pool4_240.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_240,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_32 _ hm
  · exact checked3_33 _ hm
private def chunk4_241 : List (List T) := [[wire8738,wire17487,wire30583,wire65295],
  [wire8738,wire17487,wire32768,wire35064],
  [wire8738,wire17487,wire33008,wire34952],
  [wire8738,wire17487,wire34824,wire65295]]
private def pool4_241 : List (List (List T)) := [chunk3_32, chunk3_33, chunk3_38]
private theorem checked4_241 : ∀ w ∈ chunk4_241, ¬ Need 4 w.toFinset := by
  have h : chunk4_241.all (routes 3 pool4_241.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_241,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_32 _ hm
  · exact checked3_33 _ hm
  · exact checked3_38 _ hm
private def chunk4_242 : List (List T) := [[wire8738,wire17487,wire34952,wire35064],
  [wire8738,wire17487,wire34952,wire65295],
  [wire8738,wire17487,wire34952,wire65423],
  [wire8738,wire17487,wire34959,wire35064]]
private def pool4_242 : List (List (List T)) := [chunk3_33, chunk3_38]
private theorem checked4_242 : ∀ w ∈ chunk4_242, ¬ Need 4 w.toFinset := by
  have h : chunk4_242.all (routes 3 pool4_242.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_242,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_33 _ hm
  · exact checked3_38 _ hm
private def chunk4_243 : List (List T) := [[wire8738,wire17487,wire35064],
  [wire8738,wire17487,wire35064,wire35071],
  [wire8738,wire17487,wire35064,wire36744],
  [wire8738,wire17487,wire35064,wire36856]]
private def pool4_243 : List (List (List T)) := [chunk3_32, chunk3_33, chunk3_34, chunk3_37]
private theorem checked4_243 : ∀ w ∈ chunk4_243, ¬ Need 4 w.toFinset := by
  have h : chunk4_243.all (routes 3 pool4_243.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_243,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_32 _ hm
  · exact checked3_33 _ hm
  · exact checked3_34 _ hm
  · exact checked3_37 _ hm
private def chunk4_244 : List (List T) := [[wire8738,wire17487,wire35064,wire39321],
  [wire8738,wire17487,wire35064,wire39417],
  [wire8738,wire17487,wire35064,wire43690],
  [wire8738,wire17487,wire35064,wire43770]]
private def pool4_244 : List (List (List T)) := [chunk3_7, chunk3_33]
private theorem checked4_244 : ∀ w ∈ chunk4_244, ¬ Need 4 w.toFinset := by
  have h : chunk4_244.all (routes 3 pool4_244.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_244,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_7 _ hm
  · exact checked3_33 _ hm
private def chunk4_245 : List (List T) := [[wire8738,wire17487,wire35064,wire48048],
  [wire8738,wire17487,wire35064,wire48059],
  [wire8738,wire17487,wire35064,wire52428],
  [wire8738,wire17487,wire35064,wire52431]]
private def pool4_245 : List (List (List T)) := [chunk3_33, chunk3_34]
private theorem checked4_245 : ∀ w ∈ chunk4_245, ¬ Need 4 w.toFinset := by
  have h : chunk4_245.all (routes 3 pool4_245.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_245,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_33 _ hm
  · exact checked3_34 _ hm
private def chunk4_246 : List (List T) := [[wire8738,wire17487,wire35064,wire52476],
  [wire8738,wire17487,wire35064,wire52479],
  [wire8738,wire17487,wire35064,wire56797],
  [wire8738,wire17487,wire35064,wire61166]]
private def pool4_246 : List (List (List T)) := [chunk3_8, chunk3_33, chunk3_37]
private theorem checked4_246 : ∀ w ∈ chunk4_246, ¬ Need 4 w.toFinset := by
  have h : chunk4_246.all (routes 3 pool4_246.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_246,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_8 _ hm
  · exact checked3_33 _ hm
  · exact checked3_37 _ hm
private def chunk4_247 : List (List T) := [[wire8738,wire17487,wire35064,wire61440],
  [wire8738,wire17487,wire35064,wire61455],
  [wire8738,wire17487,wire35064,wire61680],
  [wire8738,wire17487,wire35064,wire61695]]
private def pool4_247 : List (List (List T)) := []
private theorem checked4_247 : ∀ w ∈ chunk4_247, ¬ Need 4 w.toFinset := by
  have h : chunk4_247.all (routes 3 pool4_247.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_247] at hv
private def chunk4_248 : List (List T) := [[wire8738,wire17487,wire35064,wire61713],
  [wire8738,wire17487,wire35064,wire61986],
  [wire8738,wire17487,wire35064,wire62532],
  [wire8738,wire17487,wire35064,wire62543]]
private def pool4_248 : List (List (List T)) := [chunk3_33]
private theorem checked4_248 : ∀ w ∈ chunk4_248, ¬ Need 4 w.toFinset := by
  have h : chunk4_248.all (routes 3 pool4_248.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_248,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_249 : List (List T) := [[wire8738,wire17487,wire35064,wire63624],
  [wire8738,wire17487,wire35064,wire63736],
  [wire8738,wire17487,wire35064,wire65280],
  [wire8738,wire17487,wire35064,wire65295]]
private def pool4_249 : List (List (List T)) := [chunk3_33]
private theorem checked4_249 : ∀ w ∈ chunk4_249, ¬ Need 4 w.toFinset := by
  have h : chunk4_249.all (routes 3 pool4_249.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_249,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_33 _ hm
private def chunk4_250 : List (List T) := [[wire8738,wire17487,wire35064,wire65520],
  [wire8738,wire17487,wire35064,wire65535],
  [wire8738,wire17487,wire43690,wire65295],
  [wire8738,wire20292,wire60942,wire61440]]
private def pool4_250 : List (List (List T)) := [chunk3_33, chunk3_34, chunk3_38]
private theorem checked4_250 : ∀ w ∈ chunk4_250, ¬ Need 4 w.toFinset := by
  have h : chunk4_250.all (routes 3 pool4_250.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_250,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_33 _ hm
  · exact checked3_34 _ hm
  · exact checked3_38 _ hm
private def chunk4_251 : List (List T) := [[wire8738,wire26214,wire35064,wire65520],
  [wire8738,wire34952,wire35064,wire48048],
  [wire8738,wire34952,wire48048,wire65295],
  [wire8738,wire34952,wire61152,wire65280]]
private def pool4_251 : List (List (List T)) := [chunk3_34, chunk3_39]
private theorem checked4_251 : ∀ w ∈ chunk4_251, ¬ Need 4 w.toFinset := by
  have h : chunk4_251.all (routes 3 pool4_251.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_251,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_34 _ hm
  · exact checked3_39 _ hm
private def chunk4_252 : List (List T) := [[wire8738,wire35064,wire39321,wire65520],
  [wire8738,wire35064,wire48048],
  [wire8738,wire35064,wire48048,wire61440],
  [wire8738,wire35064,wire48059,wire65520]]
private def pool4_252 : List (List (List T)) := [chunk3_33, chunk3_34, chunk3_39]
private theorem checked4_252 : ∀ w ∈ chunk4_252, ¬ Need 4 w.toFinset := by
  have h : chunk4_252.all (routes 3 pool4_252.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_252,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked3_33 _ hm
  · exact checked3_34 _ hm
  · exact checked3_39 _ hm
private def chunk4_253 : List (List T) := [[wire8738,wire36744,wire61152,wire61440],
  [wire8751,wire17476,wire21845,wire65280],
  [wire8751,wire17476,wire43690,wire65280],
  [wire8751,wire17476,wire61166,wire65280]]
private def pool4_253 : List (List (List T)) := [chunk3_34, chunk3_40]
private theorem checked4_253 : ∀ w ∈ chunk4_253, ¬ Need 4 w.toFinset := by
  have h : chunk4_253.all (routes 3 pool4_253.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_253,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_34 _ hm
  · exact checked3_40 _ hm
private def chunk4_254 : List (List T) := [[wire8946,wire26214,wire34952,wire65280],
  [wire8946,wire34952,wire39321,wire65280],
  [wire8946,wire34952,wire61166,wire65280],
  [wire17476,wire17487,wire26214,wire35064]]
private def pool4_254 : List (List (List T)) := []
private theorem checked4_254 : ∀ w ∈ chunk4_254, ¬ Need 4 w.toFinset := by
  have h : chunk4_254.all (routes 3 pool4_254.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_254] at hv
private def chunk4_255 : List (List T) := [[wire17476,wire17487,wire35064,wire39321],
  [wire17476,wire17487,wire35064,wire56797],
  [wire17476,wire26214,wire35064,wire65520],
  [wire17476,wire35064,wire39321,wire65520]]
private def pool4_255 : List (List (List T)) := [chunk3_37, chunk3_39]
private theorem checked4_255 : ∀ w ∈ chunk4_255, ¬ Need 4 w.toFinset := by
  have h : chunk4_255.all (routes 3 pool4_255.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_255,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked3_37 _ hm
  · exact checked3_39 _ hm
private def chunk4_256 : List (List T) := [[wire17476,wire35064,wire56797,wire65520],
  [wire17487,wire21845,wire34952,wire35064],
  [wire17487,wire21845,wire34952,wire65295],
  [wire17487,wire34952,wire35064,wire43690]]
private def pool4_256 : List (List (List T)) := [chunk3_37]
private theorem checked4_256 : ∀ w ∈ chunk4_256, ¬ Need 4 w.toFinset := by
  have h : chunk4_256.all (routes 3 pool4_256.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_256,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked3_37 _ hm
private def chunk4_257 : List (List T) := [[wire17487,wire34952,wire35064,wire56797],
  [wire17487,wire34952,wire43690,wire65295],
  [wire17487,wire34952,wire56797,wire65295],
  [wire17487,wire35064,wire56797]]
private def pool4_257 : List (List (List T)) := [chunk3_33, chunk3_37, chunk3_38, chunk3_39]
private theorem checked4_257 : ∀ w ∈ chunk4_257, ¬ Need 4 w.toFinset := by
  have h : chunk4_257.all (routes 3 pool4_257.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool4_257,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked3_33 _ hm
  · exact checked3_37 _ hm
  · exact checked3_38 _ hm
  · exact checked3_39 _ hm
private def chunk4_258 : List (List T) := [[wire17487,wire35064,wire56797,wire61440]]
private def pool4_258 : List (List (List T)) := []
private theorem checked4_258 : ∀ w ∈ chunk4_258, ¬ Need 4 w.toFinset := by
  have h : chunk4_258.all (routes 3 pool4_258.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_258] at hv
#print axioms checked4_258
private def chunk5_0 : List (List T) := [[wire0,wire15,wire8738,wire17476,wire35064],
  [wire0,wire240,wire8738,wire17487,wire34952],
  [wire1,wire15,wire8738,wire17476,wire35064],
  [wire1,wire240,wire4383,wire8738,wire17476]]
private def pool5_0 : List (List (List T)) := [chunk4_0, chunk4_75, chunk4_140, chunk4_147, chunk4_171]
private theorem checked5_0 : ∀ w ∈ chunk5_0, ¬ Need 5 w.toFinset := by
  have h : chunk5_0.all (routes 4 pool5_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_75 _ hm
  · exact checked4_140 _ hm
  · exact checked4_147 _ hm
  · exact checked4_171 _ hm
private def chunk5_1 : List (List T) := [[wire1,wire240,wire4383,wire17476,wire34952],
  [wire1,wire240,wire8738,wire17487,wire34952],
  [wire2,wire15,wire240,wire4369,wire26214],
  [wire2,wire15,wire240,wire4369,wire30583]]
private def pool5_1 : List (List (List T)) := [chunk4_0, chunk4_23, chunk4_42, chunk4_43, chunk4_142, chunk4_147, chunk4_171]
private theorem checked5_1 : ∀ w ∈ chunk5_1, ¬ Need 5 w.toFinset := by
  have h : chunk5_1.all (routes 4 pool5_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_23 _ hm
  · exact checked4_42 _ hm
  · exact checked4_43 _ hm
  · exact checked4_142 _ hm
  · exact checked4_147 _ hm
  · exact checked4_171 _ hm
private def chunk5_2 : List (List T) := [[wire2,wire15,wire240,wire4369,wire34952],
  [wire2,wire15,wire240,wire4369,wire34954],
  [wire2,wire15,wire240,wire4369,wire36744],
  [wire2,wire15,wire240,wire4369,wire39321]]
private def pool5_2 : List (List (List T)) := [chunk4_21, chunk4_22, chunk4_24, chunk4_43, chunk4_44]
private theorem checked5_2 : ∀ w ∈ chunk5_2, ¬ Need 5 w.toFinset := by
  have h : chunk5_2.all (routes 4 pool5_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_21 _ hm
  · exact checked4_22 _ hm
  · exact checked4_24 _ hm
  · exact checked4_43 _ hm
  · exact checked4_44 _ hm
private def chunk5_3 : List (List T) := [[wire2,wire15,wire240,wire4369,wire63624],
  [wire2,wire15,wire240,wire4371,wire34952],
  [wire2,wire15,wire240,wire4383,wire34952],
  [wire2,wire15,wire240,wire26214,wire34952]]
private def pool5_3 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_23, chunk4_24, chunk4_27, chunk4_37, chunk4_44, chunk4_45]
private theorem checked5_3 : ∀ w ∈ chunk5_3, ¬ Need 5 w.toFinset := by
  have h : chunk5_3.all (routes 4 pool5_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_23 _ hm
  · exact checked4_24 _ hm
  · exact checked4_27 _ hm
  · exact checked4_37 _ hm
  · exact checked4_44 _ hm
  · exact checked4_45 _ hm
private def chunk5_4 : List (List T) := [[wire2,wire15,wire240,wire34952,wire39321],
  [wire2,wire15,wire240,wire34952,wire61166],
  [wire2,wire15,wire242,wire4369,wire34952],
  [wire2,wire15,wire255,wire4369,wire34952]]
private def pool5_4 : List (List (List T)) := [chunk4_1, chunk4_40, chunk4_43, chunk4_44, chunk4_45, chunk4_50]
private theorem checked5_4 : ∀ w ∈ chunk5_4, ¬ Need 5 w.toFinset := by
  have h : chunk5_4.all (routes 4 pool5_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_40 _ hm
  · exact checked4_43 _ hm
  · exact checked4_44 _ hm
  · exact checked4_45 _ hm
  · exact checked4_50 _ hm
private def chunk5_5 : List (List T) := [[wire2,wire15,wire3840,wire4369,wire63624],
  [wire2,wire15,wire4369,wire34952,wire35064],
  [wire2,wire15,wire4369,wire34952,wire65280],
  [wire2,wire15,wire4369,wire34952,wire65295]]
private def pool5_5 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_2, chunk4_54, chunk4_60, chunk4_61, chunk4_62]
private theorem checked5_5 : ∀ w ∈ chunk5_5, ¬ Need 5 w.toFinset := by
  have h : chunk5_5.all (routes 4 pool5_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_54 _ hm
  · exact checked4_60 _ hm
  · exact checked4_61 _ hm
  · exact checked4_62 _ hm
private def chunk5_6 : List (List T) := [[wire2,wire15,wire4369,wire36744,wire61440],
  [wire2,wire15,wire8738,wire17476,wire35064],
  [wire2,wire240,wire255,wire4369,wire34952],
  [wire2,wire240,wire4369,wire8751,wire34952]]
private def pool5_6 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_63, chunk4_75, chunk4_76, chunk4_121, chunk4_127, chunk4_172]
private theorem checked5_6 : ∀ w ∈ chunk5_6, ¬ Need 5 w.toFinset := by
  have h : chunk5_6.all (routes 4 pool5_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_63 _ hm
  · exact checked4_75 _ hm
  · exact checked4_76 _ hm
  · exact checked4_121 _ hm
  · exact checked4_127 _ hm
  · exact checked4_172 _ hm
private def chunk5_7 : List (List T) := [[wire2,wire240,wire4369,wire17487,wire34952],
  [wire2,wire240,wire4369,wire34952,wire65280],
  [wire2,wire240,wire4369,wire34952,wire65520],
  [wire2,wire240,wire8738,wire17487,wire34952]]
private def pool5_7 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_130, chunk4_134, chunk4_135, chunk4_147, chunk4_172, chunk4_173]
private theorem checked5_7 : ∀ w ∈ chunk5_7, ¬ Need 5 w.toFinset := by
  have h : chunk5_7.all (routes 4 pool5_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_130 _ hm
  · exact checked4_134 _ hm
  · exact checked4_135 _ hm
  · exact checked4_147 _ hm
  · exact checked4_172 _ hm
  · exact checked4_173 _ hm
private def chunk5_8 : List (List T) := [[wire2,wire240,wire8751,wire17476,wire34952],
  [wire2,wire3840,wire4383,wire34952,wire61440],
  [wire3,wire15,wire240,wire4369,wire34952],
  [wire4,wire15,wire128,wire240,wire4369]]
private def pool5_8 : List (List (List T)) := [chunk4_1, chunk4_2, chunk4_3, chunk4_4, chunk4_5, chunk4_17, chunk4_18, chunk4_21, chunk4_45, chunk4_152, chunk4_173, chunk4_192, chunk4_193, chunk4_200]
private theorem checked5_8 : ∀ w ∈ chunk5_8, ¬ Need 5 w.toFinset := by
  have h : chunk5_8.all (routes 4 pool5_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_2 _ hm
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_17 _ hm
  · exact checked4_18 _ hm
  · exact checked4_21 _ hm
  · exact checked4_45 _ hm
  · exact checked4_152 _ hm
  · exact checked4_173 _ hm
  · exact checked4_192 _ hm
  · exact checked4_193 _ hm
  · exact checked4_200 _ hm
private def chunk5_9 : List (List T) := [[wire4,wire15,wire240,wire4369,wire26214],
  [wire4,wire15,wire240,wire4369,wire30583],
  [wire4,wire15,wire240,wire4369,wire34952],
  [wire4,wire15,wire240,wire4369,wire34956]]
private def pool5_9 : List (List (List T)) := [chunk4_3, chunk4_24, chunk4_25, chunk4_46]
private theorem checked5_9 : ∀ w ∈ chunk5_9, ¬ Need 5 w.toFinset := by
  have h : chunk5_9.all (routes 4 pool5_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_24 _ hm
  · exact checked4_25 _ hm
  · exact checked4_46 _ hm
private def chunk5_10 : List (List T) := [[wire4,wire15,wire240,wire4369,wire34959],
  [wire4,wire15,wire240,wire4369,wire36744],
  [wire4,wire15,wire240,wire4369,wire39321],
  [wire4,wire15,wire240,wire4369,wire63624]]
private def pool5_10 : List (List (List T)) := [chunk4_25, chunk4_26, chunk4_47]
private theorem checked5_10 : ∀ w ∈ chunk5_10, ¬ Need 5 w.toFinset := by
  have h : chunk5_10.all (routes 4 pool5_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_25 _ hm
  · exact checked4_26 _ hm
  · exact checked4_47 _ hm
private def chunk5_11 : List (List T) := [[wire4,wire15,wire240,wire4373,wire34952],
  [wire4,wire15,wire240,wire26214,wire34952],
  [wire4,wire15,wire240,wire34952,wire39321],
  [wire4,wire15,wire240,wire34952,wire61166]]
private def pool5_11 : List (List (List T)) := [chunk4_4, chunk4_25, chunk4_37, chunk4_39, chunk4_40, chunk4_48]
private theorem checked5_11 : ∀ w ∈ chunk5_11, ¬ Need 5 w.toFinset := by
  have h : chunk5_11.all (routes 4 pool5_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_25 _ hm
  · exact checked4_37 _ hm
  · exact checked4_39 _ hm
  · exact checked4_40 _ hm
  · exact checked4_48 _ hm
private def chunk5_12 : List (List T) := [[wire4,wire15,wire244,wire4369,wire34952],
  [wire4,wire15,wire255,wire4369,wire34952],
  [wire4,wire15,wire3840,wire4369,wire63624],
  [wire4,wire15,wire4369,wire34952,wire35064]]
private def pool5_12 : List (List (List T)) := [chunk4_3, chunk4_4, chunk4_46, chunk4_48, chunk4_50, chunk4_54, chunk4_55, chunk4_60, chunk4_63, chunk4_68]
private theorem checked5_12 : ∀ w ∈ chunk5_12, ¬ Need 5 w.toFinset := by
  have h : chunk5_12.all (routes 4 pool5_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_46 _ hm
  · exact checked4_48 _ hm
  · exact checked4_50 _ hm
  · exact checked4_54 _ hm
  · exact checked4_55 _ hm
  · exact checked4_60 _ hm
  · exact checked4_63 _ hm
  · exact checked4_68 _ hm
private def chunk5_13 : List (List T) := [[wire4,wire15,wire4369,wire34952,wire65280],
  [wire4,wire15,wire4369,wire34952,wire65295],
  [wire4,wire15,wire4369,wire36744,wire61440],
  [wire4,wire15,wire8738,wire17476,wire35064]]
private def pool5_13 : List (List (List T)) := [chunk4_3, chunk4_4, chunk4_6, chunk4_61, chunk4_63, chunk4_69, chunk4_75, chunk4_80]
private theorem checked5_13 : ∀ w ∈ chunk5_13, ¬ Need 5 w.toFinset := by
  have h : chunk5_13.all (routes 4 pool5_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_4 _ hm
  · exact checked4_6 _ hm
  · exact checked4_61 _ hm
  · exact checked4_63 _ hm
  · exact checked4_69 _ hm
  · exact checked4_75 _ hm
  · exact checked4_80 _ hm
private def chunk5_14 : List (List T) := [[wire4,wire128,wire3840,wire4369,wire61440],
  [wire4,wire240,wire255,wire4369,wire34952],
  [wire4,wire240,wire4369,wire34952,wire65280],
  [wire4,wire240,wire4369,wire34952,wire65520]]
private def pool5_14 : List (List (List T)) := [chunk4_4, chunk4_5, chunk4_113, chunk4_114, chunk4_122, chunk4_134, chunk4_140, chunk4_173]
private theorem checked5_14 : ∀ w ∈ chunk5_14, ¬ Need 5 w.toFinset := by
  have h : chunk5_14.all (routes 4 pool5_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_5 _ hm
  · exact checked4_113 _ hm
  · exact checked4_114 _ hm
  · exact checked4_122 _ hm
  · exact checked4_134 _ hm
  · exact checked4_140 _ hm
  · exact checked4_173 _ hm
private def chunk5_15 : List (List T) := [[wire4,wire240,wire8738,wire17487,wire34952],
  [wire5,wire15,wire240,wire4369,wire34952],
  [wire8,wire15,wire8738,wire17476,wire35064],
  [wire8,wire240,wire4369,wire8738,wire17487]]
private def pool5_15 : List (List (List T)) := [chunk4_6, chunk4_25, chunk4_49, chunk4_75, chunk4_76, chunk4_81, chunk4_127, chunk4_147, chunk4_174]
private theorem checked5_15 : ∀ w ∈ chunk5_15, ¬ Need 5 w.toFinset := by
  have h : chunk5_15.all (routes 4 pool5_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_25 _ hm
  · exact checked4_49 _ hm
  · exact checked4_75 _ hm
  · exact checked4_76 _ hm
  · exact checked4_81 _ hm
  · exact checked4_127 _ hm
  · exact checked4_147 _ hm
  · exact checked4_174 _ hm
private def chunk5_16 : List (List T) := [[wire8,wire240,wire4369,wire8738,wire34959],
  [wire8,wire240,wire8738,wire17476,wire34959],
  [wire8,wire240,wire8738,wire17487,wire34952],
  [wire10,wire15,wire240,wire4369,wire34952]]
private def pool5_16 : List (List (List T)) := [chunk4_6, chunk4_21, chunk4_49, chunk4_127, chunk4_147, chunk4_152, chunk4_174]
private theorem checked5_16 : ∀ w ∈ chunk5_16, ¬ Need 5 w.toFinset := by
  have h : chunk5_16.all (routes 4 pool5_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_21 _ hm
  · exact checked4_49 _ hm
  · exact checked4_127 _ hm
  · exact checked4_147 _ hm
  · exact checked4_152 _ hm
  · exact checked4_174 _ hm
private def chunk5_17 : List (List T) := [[wire11,wire15,wire240,wire4369,wire34952],
  [wire11,wire240,wire3840,wire4369,wire34952],
  [wire11,wire240,wire4369,wire8738,wire17476],
  [wire11,wire240,wire4369,wire8738,wire34952]]
private def pool5_17 : List (List (List T)) := [chunk4_7, chunk4_8, chunk4_21, chunk4_49]
private theorem checked5_17 : ∀ w ∈ chunk5_17, ¬ Need 5 w.toFinset := by
  have h : chunk5_17.all (routes 4 pool5_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_8 _ hm
  · exact checked4_21 _ hm
  · exact checked4_49 _ hm
private def chunk5_18 : List (List T) := [[wire11,wire240,wire4369,wire8738,wire48059],
  [wire11,wire240,wire4369,wire17476,wire34952],
  [wire11,wire240,wire4369,wire34952],
  [wire11,wire240,wire4369,wire34952,wire48059]]
private def pool5_18 : List (List (List T)) := [chunk4_7, chunk4_8, chunk4_9, chunk4_10, chunk4_121, chunk4_134]
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
  · exact checked4_10 _ hm
  · exact checked4_121 _ hm
  · exact checked4_134 _ hm
private def chunk5_19 : List (List T) := [[wire11,wire240,wire4369,wire34952,wire61440],
  [wire11,wire240,wire8738,wire17476,wire34952],
  [wire11,wire240,wire8738,wire34952,wire48059],
  [wire12,wire15,wire240,wire4369,wire34952]]
private def pool5_19 : List (List (List T)) := [chunk4_9, chunk4_10, chunk4_11, chunk4_26, chunk4_49, chunk4_147]
private theorem checked5_19 : ∀ w ∈ chunk5_19, ¬ Need 5 w.toFinset := by
  have h : chunk5_19.all (routes 4 pool5_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_10 _ hm
  · exact checked4_11 _ hm
  · exact checked4_26 _ hm
  · exact checked4_49 _ hm
  · exact checked4_147 _ hm
private def chunk5_20 : List (List T) := [[wire12,wire3840,wire4369,wire34952,wire61440],
  [wire13,wire15,wire240,wire4369,wire34952],
  [wire13,wire3840,wire4369,wire34952,wire61440],
  [wire15,wire16,wire4593,wire8738,wire34952]]
private def pool5_20 : List (List (List T)) := [chunk4_11, chunk4_12, chunk4_13, chunk4_26, chunk4_50, chunk4_70, chunk4_100, chunk4_191]
private theorem checked5_20 : ∀ w ∈ chunk5_20, ¬ Need 5 w.toFinset := by
  have h : chunk5_20.all (routes 4 pool5_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_26 _ hm
  · exact checked4_50 _ hm
  · exact checked4_70 _ hm
  · exact checked4_100 _ hm
  · exact checked4_191 _ hm
private def chunk5_21 : List (List T) := [[wire15,wire16,wire4593,wire17476,wire34952],
  [wire15,wire16,wire8738,wire17476,wire35064],
  [wire15,wire32,wire240,wire4369,wire17476],
  [wire15,wire32,wire240,wire4369,wire17508]]
private def pool5_21 : List (List (List T)) := [chunk4_18, chunk4_27, chunk4_72, chunk4_75, chunk4_100, chunk4_103, chunk4_104]
private theorem checked5_21 : ∀ w ∈ chunk5_21, ¬ Need 5 w.toFinset := by
  have h : chunk5_21.all (routes 4 pool5_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_18 _ hm
  · exact checked4_27 _ hm
  · exact checked4_72 _ hm
  · exact checked4_75 _ hm
  · exact checked4_100 _ hm
  · exact checked4_103 _ hm
  · exact checked4_104 _ hm
private def chunk5_22 : List (List T) := [[wire15,wire32,wire240,wire4369,wire20292],
  [wire15,wire32,wire240,wire4369,wire21845],
  [wire15,wire32,wire240,wire4369,wire43690],
  [wire15,wire32,wire240,wire4369,wire48059]]
private def pool5_22 : List (List (List T)) := [chunk4_19, chunk4_27, chunk4_104, chunk4_105]
private theorem checked5_22 : ∀ w ∈ chunk5_22, ¬ Need 5 w.toFinset := by
  have h : chunk5_22.all (routes 4 pool5_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_19 _ hm
  · exact checked4_27 _ hm
  · exact checked4_104 _ hm
  · exact checked4_105 _ hm
private def chunk5_23 : List (List T) := [[wire15,wire32,wire240,wire4369,wire62532],
  [wire15,wire32,wire240,wire4401,wire17476],
  [wire15,wire32,wire240,wire4593,wire17476],
  [wire15,wire32,wire240,wire17476,wire21845]]
private def pool5_23 : List (List (List T)) := [chunk4_23, chunk4_27, chunk4_30, chunk4_33, chunk4_101, chunk4_105, chunk4_106]
private theorem checked5_23 : ∀ w ∈ chunk5_23, ¬ Need 5 w.toFinset := by
  have h : chunk5_23.all (routes 4 pool5_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_23 _ hm
  · exact checked4_27 _ hm
  · exact checked4_30 _ hm
  · exact checked4_33 _ hm
  · exact checked4_101 _ hm
  · exact checked4_105 _ hm
  · exact checked4_106 _ hm
private def chunk5_24 : List (List T) := [[wire15,wire32,wire240,wire17476,wire43690],
  [wire15,wire32,wire240,wire17476,wire61166],
  [wire15,wire32,wire255,wire4369,wire17476],
  [wire15,wire32,wire4369,wire8946,wire17476]]
private def pool5_24 : List (List (List T)) := [chunk4_13, chunk4_34, chunk4_50, chunk4_56, chunk4_101, chunk4_106, chunk4_107]
private theorem checked5_24 : ∀ w ∈ chunk5_24, ¬ Need 5 w.toFinset := by
  have h : chunk5_24.all (routes 4 pool5_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_34 _ hm
  · exact checked4_50 _ hm
  · exact checked4_56 _ hm
  · exact checked4_101 _ hm
  · exact checked4_106 _ hm
  · exact checked4_107 _ hm
private def chunk5_25 : List (List T) := [[wire15,wire32,wire4369,wire17476,wire35064],
  [wire15,wire32,wire4369,wire17476,wire65280],
  [wire15,wire32,wire4369,wire17476,wire65295],
  [wire15,wire32,wire8738,wire17476,wire35064]]
private def pool5_25 : List (List (List T)) := [chunk4_13, chunk4_58, chunk4_75, chunk4_77, chunk4_102, chunk4_107, chunk4_108]
private theorem checked5_25 : ∀ w ∈ chunk5_25, ¬ Need 5 w.toFinset := by
  have h : chunk5_25.all (routes 4 pool5_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_58 _ hm
  · exact checked4_75 _ hm
  · exact checked4_77 _ hm
  · exact checked4_102 _ hm
  · exact checked4_107 _ hm
  · exact checked4_108 _ hm
private def chunk5_26 : List (List T) := [[wire15,wire32,wire8946,wire17476,wire34952],
  [wire15,wire34,wire240,wire4369,wire17476],
  [wire15,wire34,wire240,wire4369,wire34952],
  [wire15,wire34,wire255,wire4369,wire17476]]
private def pool5_26 : List (List (List T)) := [chunk4_13, chunk4_43, chunk4_81, chunk4_103, chunk4_106, chunk4_108]
private theorem checked5_26 : ∀ w ∈ chunk5_26, ¬ Need 5 w.toFinset := by
  have h : chunk5_26.all (routes 4 pool5_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_43 _ hm
  · exact checked4_81 _ hm
  · exact checked4_103 _ hm
  · exact checked4_106 _ hm
  · exact checked4_108 _ hm
private def chunk5_27 : List (List T) := [[wire15,wire34,wire255,wire4369,wire34952],
  [wire15,wire47,wire240,wire4369,wire17476],
  [wire15,wire48,wire240,wire4369,wire17476],
  [wire15,wire64,wire4369,wire8738,wire17652]]
private def pool5_27 : List (List (List T)) := [chunk4_19, chunk4_55, chunk4_103, chunk4_106, chunk4_108]
private theorem checked5_27 : ∀ w ∈ chunk5_27, ¬ Need 5 w.toFinset := by
  have h : chunk5_27.all (routes 4 pool5_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_19 _ hm
  · exact checked4_55 _ hm
  · exact checked4_103 _ hm
  · exact checked4_106 _ hm
  · exact checked4_108 _ hm
private def chunk5_28 : List (List T) := [[wire15,wire64,wire4369,wire8738,wire35064],
  [wire15,wire64,wire8738,wire17476,wire35064],
  [wire15,wire64,wire8738,wire17652,wire34952],
  [wire15,wire68,wire240,wire4369,wire8738]]
private def pool5_28 : List (List (List T)) := [chunk4_56, chunk4_75, chunk4_81, chunk4_108, chunk4_109, chunk4_110]
private theorem checked5_28 : ∀ w ∈ chunk5_28, ¬ Need 5 w.toFinset := by
  have h : chunk5_28.all (routes 4 pool5_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_56 _ hm
  · exact checked4_75 _ hm
  · exact checked4_81 _ hm
  · exact checked4_108 _ hm
  · exact checked4_109 _ hm
  · exact checked4_110 _ hm
private def chunk5_29 : List (List T) := [[wire15,wire68,wire240,wire4369,wire34952],
  [wire15,wire68,wire255,wire4369,wire8738],
  [wire15,wire68,wire255,wire4369,wire34952],
  [wire15,wire96,wire240,wire4369,wire17476]]
private def pool5_29 : List (List (List T)) := [chunk4_13, chunk4_18, chunk4_46, chunk4_109, chunk4_110]
private theorem checked5_29 : ∀ w ∈ chunk5_29, ¬ Need 5 w.toFinset := by
  have h : chunk5_29.all (routes 4 pool5_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_18 _ hm
  · exact checked4_46 _ hm
  · exact checked4_109 _ hm
  · exact checked4_110 _ hm
private def chunk5_30 : List (List T) := [[wire15,wire112,wire240,wire4369,wire17476],
  [wire15,wire112,wire3840,wire4369,wire17476],
  [wire15,wire112,wire4369,wire8738,wire17476],
  [wire15,wire112,wire4369,wire8738,wire30583]]
private def pool5_30 : List (List (List T)) := [chunk4_14, chunk4_19, chunk4_111]
private theorem checked5_30 : ∀ w ∈ chunk5_30, ¬ Need 5 w.toFinset := by
  have h : chunk5_30.all (routes 4 pool5_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_14 _ hm
  · exact checked4_19 _ hm
  · exact checked4_111 _ hm
private def chunk5_31 : List (List T) := [[wire15,wire112,wire4369,wire8738,wire34952],
  [wire15,wire112,wire4369,wire17476],
  [wire15,wire112,wire4369,wire17476,wire30583],
  [wire15,wire112,wire4369,wire17476,wire34952]]
private def pool5_31 : List (List (List T)) := [chunk4_3, chunk4_14, chunk4_15, chunk4_16, chunk4_17, chunk4_58, chunk4_110, chunk4_111]
private theorem checked5_31 : ∀ w ∈ chunk5_31, ¬ Need 5 w.toFinset := by
  have h : chunk5_31.all (routes 4 pool5_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_14 _ hm
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
  · exact checked4_17 _ hm
  · exact checked4_58 _ hm
  · exact checked4_110 _ hm
  · exact checked4_111 _ hm
private def chunk5_32 : List (List T) := [[wire15,wire112,wire4369,wire17476,wire61440],
  [wire15,wire112,wire8738,wire17476,wire30583],
  [wire15,wire112,wire8738,wire17476,wire34952],
  [wire15,wire128,wire240,wire4369,wire17476]]
private def pool5_32 : List (List (List T)) := [chunk4_15, chunk4_16, chunk4_28, chunk4_75, chunk4_111, chunk4_114]
private theorem checked5_32 : ∀ w ∈ chunk5_32, ¬ Need 5 w.toFinset := by
  have h : chunk5_32.all (routes 4 pool5_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_15 _ hm
  · exact checked4_16 _ hm
  · exact checked4_28 _ hm
  · exact checked4_75 _ hm
  · exact checked4_111 _ hm
  · exact checked4_114 _ hm
private def chunk5_33 : List (List T) := [[wire15,wire128,wire240,wire4369,wire17604],
  [wire15,wire128,wire240,wire4369,wire17652],
  [wire15,wire128,wire240,wire4369,wire20292],
  [wire15,wire128,wire240,wire4369,wire21845]]
private def pool5_33 : List (List (List T)) := [chunk4_28, chunk4_29, chunk4_115]
private theorem checked5_33 : ∀ w ∈ chunk5_33, ¬ Need 5 w.toFinset := by
  have h : chunk5_33.all (routes 4 pool5_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_28 _ hm
  · exact checked4_29 _ hm
  · exact checked4_115 _ hm
private def chunk5_34 : List (List T) := [[wire15,wire128,wire240,wire4369,wire43690],
  [wire15,wire128,wire240,wire4369,wire48059],
  [wire15,wire128,wire240,wire4369,wire62532],
  [wire15,wire128,wire240,wire4497,wire17476]]
private def pool5_34 : List (List (List T)) := [chunk4_7, chunk4_28, chunk4_29, chunk4_30, chunk4_116]
private theorem checked5_34 : ∀ w ∈ chunk5_34, ¬ Need 5 w.toFinset := by
  have h : chunk5_34.all (routes 4 pool5_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_28 _ hm
  · exact checked4_29 _ hm
  · exact checked4_30 _ hm
  · exact checked4_116 _ hm
private def chunk5_35 : List (List T) := [[wire15,wire128,wire240,wire17476,wire21845],
  [wire15,wire128,wire240,wire17476,wire43690],
  [wire15,wire128,wire240,wire17476,wire61166],
  [wire15,wire128,wire255,wire4369,wire17476]]
private def pool5_35 : List (List (List T)) := [chunk4_4, chunk4_32, chunk4_34, chunk4_35, chunk4_51, chunk4_112, chunk4_117]
private theorem checked5_35 : ∀ w ∈ chunk5_35, ¬ Need 5 w.toFinset := by
  have h : chunk5_35.all (routes 4 pool5_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_32 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
  · exact checked4_51 _ hm
  · exact checked4_112 _ hm
  · exact checked4_117 _ hm
private def chunk5_36 : List (List T) := [[wire15,wire128,wire4369,wire17476,wire65280],
  [wire15,wire128,wire4369,wire17476,wire65295],
  [wire15,wire128,wire8738,wire17476,wire35064],
  [wire15,wire136,wire240,wire4369,wire8738]]
private def pool5_36 : List (List (List T)) := [chunk4_4, chunk4_57, chunk4_58, chunk4_70, chunk4_75, chunk4_113, chunk4_117]
private theorem checked5_36 : ∀ w ∈ chunk5_36, ¬ Need 5 w.toFinset := by
  have h : chunk5_36.all (routes 4 pool5_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_36,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_57 _ hm
  · exact checked4_58 _ hm
  · exact checked4_70 _ hm
  · exact checked4_75 _ hm
  · exact checked4_113 _ hm
  · exact checked4_117 _ hm
private def chunk5_37 : List (List T) := [[wire15,wire136,wire240,wire4369,wire17476],
  [wire15,wire136,wire255,wire4369,wire8738],
  [wire15,wire136,wire255,wire4369,wire17476],
  [wire15,wire143,wire240,wire4369,wire17476]]
private def pool5_37 : List (List (List T)) := [chunk4_5, chunk4_114]
private theorem checked5_37 : ∀ w ∈ chunk5_37, ¬ Need 5 w.toFinset := by
  have h : chunk5_37.all (routes 4 pool5_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_114 _ hm
private def chunk5_38 : List (List T) := [[wire15,wire144,wire240,wire4369,wire17476],
  [wire15,wire192,wire240,wire4369,wire17476],
  [wire15,wire208,wire240,wire4369,wire17476],
  [wire15,wire240,wire242,wire4369,wire34952]]
private def pool5_38 : List (List (List T)) := [chunk4_18, chunk4_28, chunk4_30, chunk4_43, chunk4_118, chunk4_119, chunk4_120, chunk4_121, chunk4_172]
private theorem checked5_38 : ∀ w ∈ chunk5_38, ¬ Need 5 w.toFinset := by
  have h : chunk5_38.all (routes 4 pool5_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_38,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_18 _ hm
  · exact checked4_28 _ hm
  · exact checked4_30 _ hm
  · exact checked4_43 _ hm
  · exact checked4_118 _ hm
  · exact checked4_119 _ hm
  · exact checked4_120 _ hm
  · exact checked4_121 _ hm
  · exact checked4_172 _ hm
private def chunk5_39 : List (List T) := [[wire15,wire240,wire244,wire4369,wire34952],
  [wire15,wire240,wire514,wire4369,wire34952],
  [wire15,wire240,wire544,wire4369,wire17476],
  [wire15,wire240,wire546,wire4369,wire17476]]
private def pool5_39 : List (List (List T)) := [chunk4_17, chunk4_19, chunk4_21, chunk4_46]
private theorem checked5_39 : ∀ w ∈ chunk5_39, ¬ Need 5 w.toFinset := by
  have h : chunk5_39.all (routes 4 pool5_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_17 _ hm
  · exact checked4_19 _ hm
  · exact checked4_21 _ hm
  · exact checked4_46 _ hm
private def chunk5_40 : List (List T) := [[wire15,wire240,wire546,wire4369,wire34952],
  [wire15,wire240,wire1028,wire4369,wire34952],
  [wire15,wire240,wire1092,wire4369,wire8738],
  [wire15,wire240,wire1092,wire4369,wire34952]]
private def pool5_40 : List (List (List T)) := []
private theorem checked5_40 : ∀ w ∈ chunk5_40, ¬ Need 5 w.toFinset := by
  have h : chunk5_40.all (routes 4 pool5_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_40] at hv
private def chunk5_41 : List (List T) := [[wire15,wire240,wire1911,wire4369,wire8738],
  [wire15,wire240,wire1911,wire4369,wire17476],
  [wire15,wire240,wire2176,wire4369,wire17476],
  [wire15,wire240,wire2184,wire4369,wire8738]]
private def pool5_41 : List (List (List T)) := [chunk4_14]
private theorem checked5_41 : ∀ w ∈ chunk5_41, ¬ Need 5 w.toFinset := by
  have h : chunk5_41.all (routes 4 pool5_41.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_41,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_14 _ hm
private def chunk5_42 : List (List T) := [[wire15,wire240,wire2184,wire4369,wire17476],
  [wire15,wire240,wire3003,wire4369,wire8738],
  [wire15,wire240,wire3003,wire4369,wire34952],
  [wire15,wire240,wire3549,wire4369,wire17476]]
private def pool5_42 : List (List (List T)) := [chunk4_7]
private theorem checked5_42 : ∀ w ∈ chunk5_42, ¬ Need 5 w.toFinset := by
  have h : chunk5_42.all (routes 4 pool5_42.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_42,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_7 _ hm
private def chunk5_43 : List (List T) := [[wire15,wire240,wire3549,wire4369,wire34952],
  [wire15,wire240,wire3840,wire4369,wire17508],
  [wire15,wire240,wire3840,wire4369,wire34954],
  [wire15,wire240,wire3840,wire4373,wire34952]]
private def pool5_43 : List (List (List T)) := [chunk4_19, chunk4_21, chunk4_25]
private theorem checked5_43 : ∀ w ∈ chunk5_43, ¬ Need 5 w.toFinset := by
  have h : chunk5_43.all (routes 4 pool5_43.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_43,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_19 _ hm
  · exact checked4_21 _ hm
  · exact checked4_25 _ hm
private def chunk5_44 : List (List T) := [[wire15,wire240,wire3840,wire4497,wire17476],
  [wire15,wire240,wire3840,wire13107,wire21845],
  [wire15,wire240,wire3840,wire13107,wire26214],
  [wire15,wire240,wire3840,wire13107,wire39321]]
private def pool5_44 : List (List (List T)) := [chunk4_28]
private theorem checked5_44 : ∀ w ∈ chunk5_44, ¬ Need 5 w.toFinset := by
  have h : chunk5_44.all (routes 4 pool5_44.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_44,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_28 _ hm
private def chunk5_45 : List (List T) := [[wire15,wire240,wire3840,wire13107,wire43690],
  [wire15,wire240,wire3840,wire21845,wire26214],
  [wire15,wire240,wire3840,wire21845,wire39321],
  [wire15,wire240,wire3840,wire21845,wire52428]]
private def pool5_45 : List (List (List T)) := []
private theorem checked5_45 : ∀ w ∈ chunk5_45, ¬ Need 5 w.toFinset := by
  have h : chunk5_45.all (routes 4 pool5_45.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_45] at hv
private def chunk5_46 : List (List T) := [[wire15,wire240,wire3840,wire26214,wire43690],
  [wire15,wire240,wire3840,wire26214,wire52428],
  [wire15,wire240,wire3840,wire39321,wire43690],
  [wire15,wire240,wire3840,wire39321,wire52428]]
private def pool5_46 : List (List (List T)) := []
private theorem checked5_46 : ∀ w ∈ chunk5_46, ¬ Need 5 w.toFinset := by
  have h : chunk5_46.all (routes 4 pool5_46.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_46] at hv
private def chunk5_47 : List (List T) := [[wire15,wire240,wire3840,wire43690,wire52428],
  [wire15,wire240,wire3842,wire4369,wire34952],
  [wire15,wire240,wire3844,wire4369,wire34952],
  [wire15,wire240,wire3872,wire4369,wire17476]]
private def pool5_47 : List (List (List T)) := [chunk4_19, chunk4_21]
private theorem checked5_47 : ∀ w ∈ chunk5_47, ¬ Need 5 w.toFinset := by
  have h : chunk5_47.all (routes 4 pool5_47.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_47,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_19 _ hm
  · exact checked4_21 _ hm
private def chunk5_48 : List (List T) := [[wire15,wire240,wire3968,wire4369,wire17476],
  [wire15,wire240,wire4352,wire8738,wire17476,wire34952],
  [wire15,wire240,wire4353,wire8738,wire17476],
  [wire15,wire240,wire4368,wire8738,wire34952]]
private def pool5_48 : List (List (List T)) := [chunk4_55, chunk4_126]
private theorem checked5_48 : ∀ w ∈ chunk5_48, ¬ Need 5 w.toFinset := by
  have h : chunk5_48.all (routes 4 pool5_48.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_48,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_126 _ hm
private def chunk5_49 : List (List T) := [[wire15,wire240,wire4369,wire4371,wire34952],
  [wire15,wire240,wire4369,wire4373,wire34952],
  [wire15,wire240,wire4369,wire4401,wire17476],
  [wire15,wire240,wire4369,wire4497,wire17476]]
private def pool5_49 : List (List (List T)) := [chunk4_19, chunk4_22, chunk4_24, chunk4_25, chunk4_26, chunk4_27, chunk4_28, chunk4_29]
private theorem checked5_49 : ∀ w ∈ chunk5_49, ¬ Need 5 w.toFinset := by
  have h : chunk5_49.all (routes 4 pool5_49.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_49,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_19 _ hm
  · exact checked4_22 _ hm
  · exact checked4_24 _ hm
  · exact checked4_25 _ hm
  · exact checked4_26 _ hm
  · exact checked4_27 _ hm
  · exact checked4_28 _ hm
  · exact checked4_29 _ hm
private def chunk5_50 : List (List T) := [[wire15,wire240,wire4369,wire8194,wire34952],
  [wire15,wire240,wire4369,wire8224,wire17476],
  [wire15,wire240,wire4369,wire8226,wire17476],
  [wire15,wire240,wire4369,wire8226,wire34952]]
private def pool5_50 : List (List (List T)) := [chunk4_20, chunk4_22]
private theorem checked5_50 : ∀ w ∈ chunk5_50, ¬ Need 5 w.toFinset := by
  have h : chunk5_50.all (routes 4 pool5_50.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_50,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_20 _ hm
  · exact checked4_22 _ hm
private def chunk5_51 : List (List T) := [[wire15,wire240,wire4369,wire8706,wire34952],
  [wire15,wire240,wire4369,wire8736,wire17476],
  [wire15,wire240,wire4369,wire8738,wire16452],
  [wire15,wire240,wire4369,wire8738,wire17476]]
private def pool5_51 : List (List (List T)) := [chunk4_20, chunk4_22]
private theorem checked5_51 : ∀ w ∈ chunk5_51, ¬ Need 5 w.toFinset := by
  have h : chunk5_51.all (routes 4 pool5_51.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_51,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_20 _ hm
  · exact checked4_22 _ hm
private def chunk5_52 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire65416],
  [wire15,wire240,wire4369,wire8738,wire17477],
  [wire15,wire240,wire4369,wire8738,wire17478],
  [wire15,wire240,wire4369,wire8738,wire17492]]
private def pool5_52 : List (List (List T)) := [chunk4_140]
private theorem checked5_52 : ∀ w ∈ chunk5_52, ¬ Need 5 w.toFinset := by
  have h : chunk5_52.all (routes 4 pool5_52.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_52,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_140 _ hm
private def chunk5_53 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17508],
  [wire15,wire240,wire4369,wire8738,wire17732],
  [wire15,wire240,wire4369,wire8738,wire17988],
  [wire15,wire240,wire4369,wire8738,wire19524]]
private def pool5_53 : List (List (List T)) := [chunk4_56]
private theorem checked5_53 : ∀ w ∈ chunk5_53, ¬ Need 5 w.toFinset := by
  have h : chunk5_53.all (routes 4 pool5_53.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_53,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_56 _ hm
private def chunk5_54 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire20292],
  [wire15,wire240,wire4369,wire8738,wire20292,wire63624],
  [wire15,wire240,wire4369,wire8738,wire21572],
  [wire15,wire240,wire4369,wire8738,wire21845]]
private def pool5_54 : List (List (List T)) := [chunk4_30]
private theorem checked5_54 : ∀ w ∈ chunk5_54, ¬ Need 5 w.toFinset := by
  have h : chunk5_54.all (routes 4 pool5_54.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_54,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_30 _ hm
private def chunk5_55 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire24405],
  [wire15,wire240,wire4369,wire8738,wire25668],
  [wire15,wire240,wire4369,wire8738,wire26214],
  [wire15,wire240,wire4369,wire8738,wire28518]]
private def pool5_55 : List (List (List T)) := [chunk4_31]
private theorem checked5_55 : ∀ w ∈ chunk5_55, ¬ Need 5 w.toFinset := by
  have h : chunk5_55.all (routes 4 pool5_55.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_55,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_31 _ hm
private def chunk5_56 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire28791],
  [wire15,wire240,wire4369,wire8738,wire30583],
  [wire15,wire240,wire4369,wire8738,wire32631],
  [wire15,wire240,wire4369,wire8738,wire32904]]
private def pool5_56 : List (List (List T)) := []
private theorem checked5_56 : ∀ w ∈ chunk5_56, ¬ Need 5 w.toFinset := by
  have h : chunk5_56.all (routes 4 pool5_56.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_56] at hv
private def chunk5_57 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire34952],
  [wire15,wire240,wire4369,wire8738,wire34952,wire65348],
  [wire15,wire240,wire4369,wire8738,wire34953],
  [wire15,wire240,wire4369,wire8738,wire34954]]
private def pool5_57 : List (List (List T)) := [chunk4_70, chunk4_127]
private theorem checked5_57 : ∀ w ∈ chunk5_57, ¬ Need 5 w.toFinset := by
  have h : chunk5_57.all (routes 4 pool5_57.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_57,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_70 _ hm
  · exact checked4_127 _ hm
private def chunk5_58 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire34968],
  [wire15,wire240,wire4369,wire8738,wire34984],
  [wire15,wire240,wire4369,wire8738,wire35208],
  [wire15,wire240,wire4369,wire8738,wire35464]]
private def pool5_58 : List (List (List T)) := [chunk4_70]
private theorem checked5_58 : ∀ w ∈ chunk5_58, ¬ Need 5 w.toFinset := by
  have h : chunk5_58.all (routes 4 pool5_58.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_58,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_70 _ hm
private def chunk5_59 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire35976],
  [wire15,wire240,wire4369,wire8738,wire36744],
  [wire15,wire240,wire4369,wire8738,wire36744,wire62532],
  [wire15,wire240,wire4369,wire8738,wire39048]]
private def pool5_59 : List (List (List T)) := []
private theorem checked5_59 : ∀ w ∈ chunk5_59, ¬ Need 5 w.toFinset := by
  have h : chunk5_59.all (routes 4 pool5_59.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_59] at hv
private def chunk5_60 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire39321],
  [wire15,wire240,wire4369,wire8738,wire40857],
  [wire15,wire240,wire4369,wire8738,wire43144],
  [wire15,wire240,wire4369,wire8738,wire43690]]
private def pool5_60 : List (List (List T)) := [chunk4_31]
private theorem checked5_60 : ∀ w ∈ chunk5_60, ¬ Need 5 w.toFinset := by
  have h : chunk5_60.all (routes 4 pool5_60.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_60,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_31 _ hm
private def chunk5_61 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire44970],
  [wire15,wire240,wire4369,wire8738,wire45243],
  [wire15,wire240,wire4369,wire8738,wire48059],
  [wire15,wire240,wire4369,wire8738,wire49083]]
private def pool5_61 : List (List (List T)) := []
private theorem checked5_61 : ∀ w ∈ chunk5_61, ¬ Need 5 w.toFinset := by
  have h : chunk5_61.all (routes 4 pool5_61.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_61] at hv
private def chunk5_62 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire50244],
  [wire15,wire240,wire4369,wire8738,wire51336],
  [wire15,wire240,wire4369,wire8738,wire62532],
  [wire15,wire240,wire4369,wire8738,wire62805]]
private def pool5_62 : List (List (List T)) := []
private theorem checked5_62 : ∀ w ∈ chunk5_62, ¬ Need 5 w.toFinset := by
  have h : chunk5_62.all (routes 4 pool5_62.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_62] at hv
private def chunk5_63 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire63078],
  [wire15,wire240,wire4369,wire8738,wire63351],
  [wire15,wire240,wire4369,wire8738,wire63624],
  [wire15,wire240,wire4369,wire8738,wire63897]]
private def pool5_63 : List (List (List T)) := []
private theorem checked5_63 : ∀ w ∈ chunk5_63, ¬ Need 5 w.toFinset := by
  have h : chunk5_63.all (routes 4 pool5_63.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_63] at hv
private def chunk5_64 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire64170],
  [wire15,wire240,wire4369,wire8738,wire64443],
  [wire15,wire240,wire4369,wire8738,wire65348],
  [wire15,wire240,wire4369,wire8738,wire65416]]
private def pool5_64 : List (List (List T)) := [chunk4_56, chunk4_71, chunk4_127, chunk4_141]
private theorem checked5_64 : ∀ w ∈ chunk5_64, ¬ Need 5 w.toFinset := by
  have h : chunk5_64.all (routes 4 pool5_64.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_64,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_56 _ hm
  · exact checked4_71 _ hm
  · exact checked4_127 _ hm
  · exact checked4_141 _ hm
private def chunk5_65 : List (List T) := [[wire15,wire240,wire4369,wire8739,wire17476],
  [wire15,wire240,wire4369,wire8739,wire34952],
  [wire15,wire240,wire4369,wire8742,wire17476],
  [wire15,wire240,wire4369,wire8746,wire17476]]
private def pool5_65 : List (List (List T)) := [chunk4_127]
private theorem checked5_65 : ∀ w ∈ chunk5_65, ¬ Need 5 w.toFinset := by
  have h : chunk5_65.all (routes 4 pool5_65.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_65,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_127 _ hm
private def chunk5_66 : List (List T) := [[wire15,wire240,wire4369,wire8746,wire34952],
  [wire15,wire240,wire4369,wire8751,wire17476],
  [wire15,wire240,wire4369,wire8751,wire20292],
  [wire15,wire240,wire4369,wire8751,wire21845]]
private def pool5_66 : List (List (List T)) := [chunk4_31, chunk4_127, chunk4_141, chunk4_174, chunk4_175]
private theorem checked5_66 : ∀ w ∈ chunk5_66, ¬ Need 5 w.toFinset := by
  have h : chunk5_66.all (routes 4 pool5_66.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_66,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_31 _ hm
  · exact checked4_127 _ hm
  · exact checked4_141 _ hm
  · exact checked4_174 _ hm
  · exact checked4_175 _ hm
private def chunk5_67 : List (List T) := [[wire15,wire240,wire4369,wire8751,wire43690],
  [wire15,wire240,wire4369,wire8751,wire48059],
  [wire15,wire240,wire4369,wire8751,wire62532],
  [wire15,wire240,wire4369,wire8754,wire17476]]
private def pool5_67 : List (List (List T)) := [chunk4_32, chunk4_141, chunk4_175]
private theorem checked5_67 : ∀ w ∈ chunk5_67, ¬ Need 5 w.toFinset := by
  have h : chunk5_67.all (routes 4 pool5_67.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_67,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_32 _ hm
  · exact checked4_141 _ hm
  · exact checked4_175 _ hm
private def chunk5_68 : List (List T) := [[wire15,wire240,wire4369,wire8754,wire34952],
  [wire15,wire240,wire4369,wire8802,wire17476],
  [wire15,wire240,wire4369,wire8802,wire34952],
  [wire15,wire240,wire4369,wire8866,wire34952]]
private def pool5_68 : List (List (List T)) := [chunk4_55, chunk4_56]
private theorem checked5_68 : ∀ w ∈ chunk5_68, ¬ Need 5 w.toFinset := by
  have h : chunk5_68.all (routes 4 pool5_68.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_68,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_56 _ hm
private def chunk5_69 : List (List T) := [[wire15,wire240,wire4369,wire8946,wire26214],
  [wire15,wire240,wire4369,wire8946,wire30583],
  [wire15,wire240,wire4369,wire8946,wire34952],
  [wire15,wire240,wire4369,wire8946,wire36744]]
private def pool5_69 : List (List (List T)) := [chunk4_32, chunk4_71, chunk4_176]
private theorem checked5_69 : ∀ w ∈ chunk5_69, ¬ Need 5 w.toFinset := by
  have h : chunk5_69.all (routes 4 pool5_69.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_69,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_32 _ hm
  · exact checked4_71 _ hm
  · exact checked4_176 _ hm
private def chunk5_70 : List (List T) := [[wire15,wire240,wire4369,wire8946,wire39321],
  [wire15,wire240,wire4369,wire8946,wire63624],
  [wire15,wire240,wire4369,wire8994,wire17476],
  [wire15,wire240,wire4369,wire8994,wire34952]]
private def pool5_70 : List (List (List T)) := [chunk4_32, chunk4_71, chunk4_177]
private theorem checked5_70 : ∀ w ∈ chunk5_70, ¬ Need 5 w.toFinset := by
  have h : chunk5_70.all (routes 4 pool5_70.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_70,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_32 _ hm
  · exact checked4_71 _ hm
  · exact checked4_177 _ hm
private def chunk5_71 : List (List T) := [[wire15,wire240,wire4369,wire9762,wire17476],
  [wire15,wire240,wire4369,wire9762,wire34952],
  [wire15,wire240,wire4369,wire10786,wire17476],
  [wire15,wire240,wire4369,wire10786,wire34952]]
private def pool5_71 : List (List (List T)) := []
private theorem checked5_71 : ∀ w ∈ chunk5_71, ¬ Need 5 w.toFinset := by
  have h : chunk5_71.all (routes 4 pool5_71.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_71] at hv
private def chunk5_72 : List (List T) := [[wire15,wire240,wire4369,wire12066,wire17476],
  [wire15,wire240,wire4369,wire12066,wire17476,wire63624],
  [wire15,wire240,wire4369,wire12066,wire20292],
  [wire15,wire240,wire4369,wire12066,wire21845]]
private def pool5_72 : List (List (List T)) := [chunk4_141]
private theorem checked5_72 : ∀ w ∈ chunk5_72, ¬ Need 5 w.toFinset := by
  have h : chunk5_72.all (routes 4 pool5_72.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_72,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_141 _ hm
private def chunk5_73 : List (List T) := [[wire15,wire240,wire4369,wire12066,wire26214],
  [wire15,wire240,wire4369,wire12066,wire28518],
  [wire15,wire240,wire4369,wire12066,wire30583],
  [wire15,wire240,wire4369,wire12066,wire34952]]
private def pool5_73 : List (List (List T)) := []
private theorem checked5_73 : ∀ w ∈ chunk5_73, ¬ Need 5 w.toFinset := by
  have h : chunk5_73.all (routes 4 pool5_73.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_73] at hv
private def chunk5_74 : List (List T) := [[wire15,wire240,wire4369,wire12066,wire34952,wire62532],
  [wire15,wire240,wire4369,wire12066,wire36744],
  [wire15,wire240,wire4369,wire12066,wire39321],
  [wire15,wire240,wire4369,wire12066,wire43690]]
private def pool5_74 : List (List (List T)) := [chunk4_71]
private theorem checked5_74 : ∀ w ∈ chunk5_74, ¬ Need 5 w.toFinset := by
  have h : chunk5_74.all (routes 4 pool5_74.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_74,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_71 _ hm
private def chunk5_75 : List (List T) := [[wire15,wire240,wire4369,wire12066,wire44970],
  [wire15,wire240,wire4369,wire12066,wire48059],
  [wire15,wire240,wire4369,wire12066,wire62532],
  [wire15,wire240,wire4369,wire12066,wire63624]]
private def pool5_75 : List (List (List T)) := [chunk4_72, chunk4_142]
private theorem checked5_75 : ∀ w ∈ chunk5_75, ¬ Need 5 w.toFinset := by
  have h : chunk5_75.all (routes 4 pool5_75.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_75,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_72 _ hm
  · exact checked4_142 _ hm
private def chunk5_76 : List (List T) := [[wire15,wire240,wire4369,wire12079,wire17476],
  [wire15,wire240,wire4369,wire12274,wire34952],
  [wire15,wire240,wire4369,wire12834,wire17476],
  [wire15,wire240,wire4369,wire12834,wire34952]]
private def pool5_76 : List (List (List T)) := [chunk4_177]
private theorem checked5_76 : ∀ w ∈ chunk5_76, ¬ Need 5 w.toFinset := by
  have h : chunk5_76.all (routes 4 pool5_76.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_76,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_177 _ hm
private def chunk5_77 : List (List T) := [[wire15,wire240,wire4369,wire13107,wire17476],
  [wire15,wire240,wire4369,wire13107,wire20292],
  [wire15,wire240,wire4369,wire13107,wire21845],
  [wire15,wire240,wire4369,wire13107,wire26214]]
private def pool5_77 : List (List (List T)) := [chunk4_30, chunk4_31]
private theorem checked5_77 : ∀ w ∈ chunk5_77, ¬ Need 5 w.toFinset := by
  have h : chunk5_77.all (routes 4 pool5_77.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_77,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
private def chunk5_78 : List (List T) := [[wire15,wire240,wire4369,wire13107,wire30583],
  [wire15,wire240,wire4369,wire13107,wire34952],
  [wire15,wire240,wire4369,wire13107,wire36744],
  [wire15,wire240,wire4369,wire13107,wire39321]]
private def pool5_78 : List (List (List T)) := [chunk4_31]
private theorem checked5_78 : ∀ w ∈ chunk5_78, ¬ Need 5 w.toFinset := by
  have h : chunk5_78.all (routes 4 pool5_78.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_78,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_31 _ hm
private def chunk5_79 : List (List T) := [[wire15,wire240,wire4369,wire13107,wire43690],
  [wire15,wire240,wire4369,wire13107,wire48059],
  [wire15,wire240,wire4369,wire13107,wire62532],
  [wire15,wire240,wire4369,wire13107,wire63624]]
private def pool5_79 : List (List (List T)) := [chunk4_31]
private theorem checked5_79 : ∀ w ∈ chunk5_79, ¬ Need 5 w.toFinset := by
  have h : chunk5_79.all (routes 4 pool5_79.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_79,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_31 _ hm
private def chunk5_80 : List (List T) := [[wire15,wire240,wire4369,wire13119,wire17476],
  [wire15,wire240,wire4369,wire13299,wire34952],
  [wire15,wire240,wire4369,wire16179,wire17476],
  [wire15,wire240,wire4369,wire16179,wire34952]]
private def pool5_80 : List (List (List T)) := [chunk4_31, chunk4_32, chunk4_178]
private theorem checked5_80 : ∀ w ∈ chunk5_80, ¬ Need 5 w.toFinset := by
  have h : chunk5_80.all (routes 4 pool5_80.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_80,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_31 _ hm
  · exact checked4_32 _ hm
  · exact checked4_178 _ hm
private def chunk5_81 : List (List T) := [[wire15,wire240,wire4369,wire16388,wire34952],
  [wire15,wire240,wire4369,wire16452,wire34952],
  [wire15,wire240,wire4369,wire17412,wire34952],
  [wire15,wire240,wire4369,wire17476,wire17508]]
private def pool5_81 : List (List (List T)) := [chunk4_18, chunk4_33, chunk4_128, chunk4_130]
private theorem checked5_81 : ∀ w ∈ chunk5_81, ¬ Need 5 w.toFinset := by
  have h : chunk5_81.all (routes 4 pool5_81.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_81,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_18 _ hm
  · exact checked4_33 _ hm
  · exact checked4_128 _ hm
  · exact checked4_130 _ hm
private def chunk5_82 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire17604],
  [wire15,wire240,wire4369,wire17476,wire25122],
  [wire15,wire240,wire4369,wire17476,wire26214],
  [wire15,wire240,wire4369,wire17476,wire26223]]
private def pool5_82 : List (List (List T)) := [chunk4_32, chunk4_34, chunk4_35, chunk4_128, chunk4_130]
private theorem checked5_82 : ∀ w ∈ chunk5_82, ¬ Need 5 w.toFinset := by
  have h : chunk5_82.all (routes 4 pool5_82.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_82,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_32 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
  · exact checked4_128 _ hm
  · exact checked4_130 _ hm
private def chunk5_83 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire28518],
  [wire15,wire240,wire4369,wire17476,wire28791],
  [wire15,wire240,wire4369,wire17476,wire30576],
  [wire15,wire240,wire4369,wire17476,wire30583]]
private def pool5_83 : List (List (List T)) := [chunk4_14, chunk4_20]
private theorem checked5_83 : ∀ w ∈ chunk5_83, ¬ Need 5 w.toFinset := by
  have h : chunk5_83.all (routes 4 pool5_83.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_83,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_14 _ hm
  · exact checked4_20 _ hm
private def chunk5_84 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire30591],
  [wire15,wire240,wire4369,wire17476,wire32631],
  [wire15,wire240,wire4369,wire17476,wire32896],
  [wire15,wire240,wire4369,wire17476,wire32904]]
private def pool5_84 : List (List (List T)) := [chunk4_14]
private theorem checked5_84 : ∀ w ∈ chunk5_84, ¬ Need 5 w.toFinset := by
  have h : chunk5_84.all (routes 4 pool5_84.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_84,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_14 _ hm
private def chunk5_85 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire34944],
  [wire15,wire240,wire4369,wire17476,wire34952],
  [wire15,wire240,wire4369,wire17476,wire34952,wire65314],
  [wire15,wire240,wire4369,wire17476,wire34953]]
private def pool5_85 : List (List (List T)) := [chunk4_72, chunk4_142]
private theorem checked5_85 : ∀ w ∈ chunk5_85, ¬ Need 5 w.toFinset := by
  have h : chunk5_85.all (routes 4 pool5_85.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_85,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_72 _ hm
  · exact checked4_142 _ hm
private def chunk5_86 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire34954],
  [wire15,wire240,wire4369,wire17476,wire34956],
  [wire15,wire240,wire4369,wire17476,wire34959],
  [wire15,wire240,wire4369,wire17476,wire34968]]
private def pool5_86 : List (List (List T)) := [chunk4_72, chunk4_130]
private theorem checked5_86 : ∀ w ∈ chunk5_86, ¬ Need 5 w.toFinset := by
  have h : chunk5_86.all (routes 4 pool5_86.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_86,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_72 _ hm
  · exact checked4_130 _ hm
private def chunk5_87 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire35016],
  [wire15,wire240,wire4369,wire17476,wire35208],
  [wire15,wire240,wire4369,wire17476,wire35464],
  [wire15,wire240,wire4369,wire17476,wire35976]]
private def pool5_87 : List (List (List T)) := []
private theorem checked5_87 : ∀ w ∈ chunk5_87, ¬ Need 5 w.toFinset := by
  have h : chunk5_87.all (routes 4 pool5_87.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_87] at hv
private def chunk5_88 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire36744],
  [wire15,wire240,wire4369,wire17476,wire36744,wire61986],
  [wire15,wire240,wire4369,wire17476,wire36751],
  [wire15,wire240,wire4369,wire17476,wire39048]]
private def pool5_88 : List (List (List T)) := [chunk4_142]
private theorem checked5_88 : ∀ w ∈ chunk5_88, ¬ Need 5 w.toFinset := by
  have h : chunk5_88.all (routes 4 pool5_88.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_88,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_142 _ hm
private def chunk5_89 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire39321],
  [wire15,wire240,wire4369,wire17476,wire39327],
  [wire15,wire240,wire4369,wire17476,wire40857],
  [wire15,wire240,wire4369,wire17476,wire41506]]
private def pool5_89 : List (List (List T)) := [chunk4_35, chunk4_36]
private theorem checked5_89 : ∀ w ∈ chunk5_89, ¬ Need 5 w.toFinset := by
  have h : chunk5_89.all (routes 4 pool5_89.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_89,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
private def chunk5_90 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire43144],
  [wire15,wire240,wire4369,wire17476,wire51336],
  [wire15,wire240,wire4369,wire17476,wire52428],
  [wire15,wire240,wire4369,wire17476,wire52431]]
private def pool5_90 : List (List (List T)) := [chunk4_36]
private theorem checked5_90 : ∀ w ∈ chunk5_90, ¬ Need 5 w.toFinset := by
  have h : chunk5_90.all (routes 4 pool5_90.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_90,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_36 _ hm
private def chunk5_91 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire53196],
  [wire15,wire240,wire4369,wire17476,wire53469],
  [wire15,wire240,wire4369,wire17476,wire56784],
  [wire15,wire240,wire4369,wire17476,wire56797]]
private def pool5_91 : List (List (List T)) := [chunk4_178]
private theorem checked5_91 : ∀ w ∈ chunk5_91, ¬ Need 5 w.toFinset := by
  have h : chunk5_91.all (routes 4 pool5_91.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_91,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_178 _ hm
private def chunk5_92 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire56799],
  [wire15,wire240,wire4369,wire17476,wire57309],
  [wire15,wire240,wire4369,wire17476,wire61472],
  [wire15,wire240,wire4369,wire17476,wire61568]]
private def pool5_92 : List (List (List T)) := [chunk4_23]
private theorem checked5_92 : ∀ w ∈ chunk5_92, ¬ Need 5 w.toFinset := by
  have h : chunk5_92.all (routes 4 pool5_92.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_92,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_23 _ hm
private def chunk5_93 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire61986],
  [wire15,wire240,wire4369,wire17476,wire61999],
  [wire15,wire240,wire4369,wire17476,wire62259],
  [wire15,wire240,wire4369,wire17476,wire63078]]
private def pool5_93 : List (List (List T)) := [chunk4_178]
private theorem checked5_93 : ∀ w ∈ chunk5_93, ¬ Need 5 w.toFinset := by
  have h : chunk5_93.all (routes 4 pool5_93.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_93,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_178 _ hm
private def chunk5_94 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire63351],
  [wire15,wire240,wire4369,wire17476,wire63624],
  [wire15,wire240,wire4369,wire17476,wire63631],
  [wire15,wire240,wire4369,wire17476,wire63897]]
private def pool5_94 : List (List (List T)) := [chunk4_14]
private theorem checked5_94 : ∀ w ∈ chunk5_94, ¬ Need 5 w.toFinset := by
  have h : chunk5_94.all (routes 4 pool5_94.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_94,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_14 _ hm
private def chunk5_95 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire64716],
  [wire15,wire240,wire4369,wire17476,wire64989],
  [wire15,wire240,wire4369,wire17476,wire65314],
  [wire15,wire240,wire4369,wire17476,wire65327]]
private def pool5_95 : List (List (List T)) := [chunk4_72, chunk4_73, chunk4_179]
private theorem checked5_95 : ∀ w ∈ chunk5_95, ¬ Need 5 w.toFinset := by
  have h : chunk5_95.all (routes 4 pool5_95.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_95,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_72 _ hm
  · exact checked4_73 _ hm
  · exact checked4_179 _ hm
private def chunk5_96 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire65407],
  [wire15,wire240,wire4369,wire17476,wire65416],
  [wire15,wire240,wire4369,wire17476,wire65423],
  [wire15,wire240,wire4369,wire17476,wire65503]]
private def pool5_96 : List (List (List T)) := [chunk4_14, chunk4_59]
private theorem checked5_96 : ∀ w ∈ chunk5_96, ¬ Need 5 w.toFinset := by
  have h : chunk5_96.all (routes 4 pool5_96.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_96,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_14 _ hm
  · exact checked4_59 _ hm
private def chunk5_97 : List (List T) := [[wire15,wire240,wire4369,wire17477,wire34952],
  [wire15,wire240,wire4369,wire17484,wire34952],
  [wire15,wire240,wire4369,wire17492,wire34952],
  [wire15,wire240,wire4369,wire17508]]
private def pool5_97 : List (List (List T)) := [chunk4_18, chunk4_19, chunk4_23, chunk4_30, chunk4_34, chunk4_50, chunk4_58, chunk4_121, chunk4_130, chunk4_131, chunk4_142]
private theorem checked5_97 : ∀ w ∈ chunk5_97, ¬ Need 5 w.toFinset := by
  have h : chunk5_97.all (routes 4 pool5_97.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_97,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
  · exact checked4_23 _ hm
  · exact checked4_30 _ hm
  · exact checked4_34 _ hm
  · exact checked4_50 _ hm
  · exact checked4_58 _ hm
  · exact checked4_121 _ hm
  · exact checked4_130 _ hm
  · exact checked4_131 _ hm
  · exact checked4_142 _ hm
private def chunk5_98 : List (List T) := [[wire15,wire240,wire4369,wire17508,wire34952],
  [wire15,wire240,wire4369,wire17508,wire61440],
  [wire15,wire240,wire4369,wire17604,wire34952],
  [wire15,wire240,wire4369,wire17652,wire26214]]
private def pool5_98 : List (List (List T)) := [chunk4_13, chunk4_18, chunk4_23, chunk4_36, chunk4_58, chunk4_73]
private theorem checked5_98 : ∀ w ∈ chunk5_98, ¬ Need 5 w.toFinset := by
  have h : chunk5_98.all (routes 4 pool5_98.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_98,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_18 _ hm
  · exact checked4_23 _ hm
  · exact checked4_36 _ hm
  · exact checked4_58 _ hm
  · exact checked4_73 _ hm
private def chunk5_99 : List (List T) := [[wire15,wire240,wire4369,wire17652,wire30583],
  [wire15,wire240,wire4369,wire17652,wire34952],
  [wire15,wire240,wire4369,wire17652,wire34959],
  [wire15,wire240,wire4369,wire17652,wire36744]]
private def pool5_99 : List (List (List T)) := [chunk4_14, chunk4_18, chunk4_19, chunk4_179]
private theorem checked5_99 : ∀ w ∈ chunk5_99, ¬ Need 5 w.toFinset := by
  have h : chunk5_99.all (routes 4 pool5_99.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_99,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_14 _ hm
  · exact checked4_18 _ hm
  · exact checked4_19 _ hm
  · exact checked4_179 _ hm
private def chunk5_100 : List (List T) := [[wire15,wire240,wire4369,wire17652,wire39321],
  [wire15,wire240,wire4369,wire17652,wire63624],
  [wire15,wire240,wire4369,wire17732,wire34952],
  [wire15,wire240,wire4369,wire17988,wire34952]]
private def pool5_100 : List (List (List T)) := [chunk4_37, chunk4_73]
private theorem checked5_100 : ∀ w ∈ chunk5_100, ¬ Need 5 w.toFinset := by
  have h : chunk5_100.all (routes 4 pool5_100.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_100,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_37 _ hm
  · exact checked4_73 _ hm
private def chunk5_101 : List (List T) := [[wire15,wire240,wire4369,wire19524,wire34952],
  [wire15,wire240,wire4369,wire20292,wire26214],
  [wire15,wire240,wire4369,wire20292,wire28518],
  [wire15,wire240,wire4369,wire20292,wire30583]]
private def pool5_101 : List (List (List T)) := [chunk4_14]
private theorem checked5_101 : ∀ w ∈ chunk5_101, ¬ Need 5 w.toFinset := by
  have h : chunk5_101.all (routes 4 pool5_101.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_101,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_14 _ hm
private def chunk5_102 : List (List T) := [[wire15,wire240,wire4369,wire20292,wire34952],
  [wire15,wire240,wire4369,wire20292,wire34952,wire61986],
  [wire15,wire240,wire4369,wire20292,wire34959],
  [wire15,wire240,wire4369,wire20292,wire36744]]
private def pool5_102 : List (List (List T)) := [chunk4_73]
private theorem checked5_102 : ∀ w ∈ chunk5_102, ¬ Need 5 w.toFinset := by
  have h : chunk5_102.all (routes 4 pool5_102.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_102,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_73 _ hm
private def chunk5_103 : List (List T) := [[wire15,wire240,wire4369,wire20292,wire39321],
  [wire15,wire240,wire4369,wire20292,wire52428],
  [wire15,wire240,wire4369,wire20292,wire53196],
  [wire15,wire240,wire4369,wire20292,wire56797]]
private def pool5_103 : List (List (List T)) := []
private theorem checked5_103 : ∀ w ∈ chunk5_103, ¬ Need 5 w.toFinset := by
  have h : chunk5_103.all (routes 4 pool5_103.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_103] at hv
private def chunk5_104 : List (List T) := [[wire15,wire240,wire4369,wire20292,wire61986],
  [wire15,wire240,wire4369,wire20292,wire63624],
  [wire15,wire240,wire4369,wire20468,wire34952],
  [wire15,wire240,wire4369,wire21572,wire34952]]
private def pool5_104 : List (List (List T)) := [chunk4_74]
private theorem checked5_104 : ∀ w ∈ chunk5_104, ¬ Need 5 w.toFinset := by
  have h : chunk5_104.all (routes 4 pool5_104.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_104,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_74 _ hm
private def chunk5_105 : List (List T) := [[wire15,wire240,wire4369,wire21845,wire26214],
  [wire15,wire240,wire4369,wire21845,wire30583],
  [wire15,wire240,wire4369,wire21845,wire34952],
  [wire15,wire240,wire4369,wire21845,wire34959]]
private def pool5_105 : List (List (List T)) := [chunk4_15, chunk4_35, chunk4_36, chunk4_143]
private theorem checked5_105 : ∀ w ∈ chunk5_105, ¬ Need 5 w.toFinset := by
  have h : chunk5_105.all (routes 4 pool5_105.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_105,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_15 _ hm
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_143 _ hm
private def chunk5_106 : List (List T) := [[wire15,wire240,wire4369,wire21845,wire36744],
  [wire15,wire240,wire4369,wire21845,wire39321],
  [wire15,wire240,wire4369,wire21845,wire52428],
  [wire15,wire240,wire4369,wire21845,wire56797]]
private def pool5_106 : List (List (List T)) := [chunk4_35, chunk4_36]
private theorem checked5_106 : ∀ w ∈ chunk5_106, ¬ Need 5 w.toFinset := by
  have h : chunk5_106.all (routes 4 pool5_106.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_106,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
private def chunk5_107 : List (List T) := [[wire15,wire240,wire4369,wire21845,wire61986],
  [wire15,wire240,wire4369,wire21845,wire63624],
  [wire15,wire240,wire4369,wire22005,wire34952],
  [wire15,wire240,wire4369,wire24405,wire34952]]
private def pool5_107 : List (List (List T)) := [chunk4_37]
private theorem checked5_107 : ∀ w ∈ chunk5_107, ¬ Need 5 w.toFinset := by
  have h : chunk5_107.all (routes 4 pool5_107.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_107,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_37 _ hm
private def chunk5_108 : List (List T) := [[wire15,wire240,wire4369,wire25122,wire34952],
  [wire15,wire240,wire4369,wire25668,wire34952],
  [wire15,wire240,wire4369,wire26214,wire43690],
  [wire15,wire240,wire4369,wire26214,wire48059]]
private def pool5_108 : List (List (List T)) := [chunk4_7]
private theorem checked5_108 : ∀ w ∈ chunk5_108, ¬ Need 5 w.toFinset := by
  have h : chunk5_108.all (routes 4 pool5_108.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_108,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_7 _ hm
private def chunk5_109 : List (List T) := [[wire15,wire240,wire4369,wire26214,wire52428],
  [wire15,wire240,wire4369,wire26214,wire56797],
  [wire15,wire240,wire4369,wire26214,wire61986],
  [wire15,wire240,wire4369,wire26214,wire62532]]
private def pool5_109 : List (List (List T)) := []
private theorem checked5_109 : ∀ w ∈ chunk5_109, ¬ Need 5 w.toFinset := by
  have h : chunk5_109.all (routes 4 pool5_109.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_109] at hv
private def chunk5_110 : List (List T) := [[wire15,wire240,wire4369,wire30583,wire43690],
  [wire15,wire240,wire4369,wire30583,wire48059],
  [wire15,wire240,wire4369,wire30583,wire52428],
  [wire15,wire240,wire4369,wire30583,wire56797]]
private def pool5_110 : List (List (List T)) := [chunk4_7, chunk4_15]
private theorem checked5_110 : ∀ w ∈ chunk5_110, ¬ Need 5 w.toFinset := by
  have h : chunk5_110.all (routes 4 pool5_110.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_110,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_15 _ hm
private def chunk5_111 : List (List T) := [[wire15,wire240,wire4369,wire30583,wire61986],
  [wire15,wire240,wire4369,wire30583,wire62532],
  [wire15,wire240,wire4369,wire34952,wire34954],
  [wire15,wire240,wire4369,wire34952,wire34956]]
private def pool5_111 : List (List (List T)) := [chunk4_15, chunk4_21, chunk4_39, chunk4_40, chunk4_60, chunk4_62, chunk4_63]
private theorem checked5_111 : ∀ w ∈ chunk5_111, ¬ Need 5 w.toFinset := by
  have h : chunk5_111.all (routes 4 pool5_111.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_111,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_15 _ hm
  · exact checked4_21 _ hm
  · exact checked4_39 _ hm
  · exact checked4_40 _ hm
  · exact checked4_60 _ hm
  · exact checked4_62 _ hm
  · exact checked4_63 _ hm
private def chunk5_112 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire41506],
  [wire15,wire240,wire4369,wire34952,wire43690],
  [wire15,wire240,wire4369,wire34952,wire43770],
  [wire15,wire240,wire4369,wire34952,wire44970]]
private def pool5_112 : List (List (List T)) := [chunk4_41]
private theorem checked5_112 : ∀ w ∈ chunk5_112, ¬ Need 5 w.toFinset := by
  have h : chunk5_112.all (routes 4 pool5_112.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_112,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_41 _ hm
private def chunk5_113 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire45243],
  [wire15,wire240,wire4369,wire34952,wire47883],
  [wire15,wire240,wire4369,wire34952,wire48059],
  [wire15,wire240,wire4369,wire34952,wire48123]]
private def pool5_113 : List (List (List T)) := [chunk4_7, chunk4_22]
private theorem checked5_113 : ∀ w ∈ chunk5_113, ¬ Need 5 w.toFinset := by
  have h : chunk5_113.all (routes 4 pool5_113.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_113,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_22 _ hm
private def chunk5_114 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire49083],
  [wire15,wire240,wire4369,wire34952,wire50244],
  [wire15,wire240,wire4369,wire34952,wire52428],
  [wire15,wire240,wire4369,wire34952,wire52476]]
private def pool5_114 : List (List (List T)) := [chunk4_7, chunk4_41]
private theorem checked5_114 : ∀ w ∈ chunk5_114, ¬ Need 5 w.toFinset := by
  have h : chunk5_114.all (routes 4 pool5_114.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_114,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_41 _ hm
private def chunk5_115 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire53196],
  [wire15,wire240,wire4369,wire34952,wire53469],
  [wire15,wire240,wire4369,wire34952,wire56589],
  [wire15,wire240,wire4369,wire34952,wire56797]]
private def pool5_115 : List (List (List T)) := [chunk4_179]
private theorem checked5_115 : ∀ w ∈ chunk5_115, ¬ Need 5 w.toFinset := by
  have h : chunk5_115.all (routes 4 pool5_115.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_115,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_179 _ hm
private def chunk5_116 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire56829],
  [wire15,wire240,wire4369,wire34952,wire57309],
  [wire15,wire240,wire4369,wire34952,wire61442],
  [wire15,wire240,wire4369,wire34952,wire61444]]
private def pool5_116 : List (List (List T)) := [chunk4_23]
private theorem checked5_116 : ∀ w ∈ chunk5_116, ¬ Need 5 w.toFinset := by
  have h : chunk5_116.all (routes 4 pool5_116.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_116,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_23 _ hm
private def chunk5_117 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire61986],
  [wire15,wire240,wire4369,wire34952,wire62194],
  [wire15,wire240,wire4369,wire34952,wire62259],
  [wire15,wire240,wire4369,wire34952,wire62532]]
private def pool5_117 : List (List (List T)) := [chunk4_179]
private theorem checked5_117 : ∀ w ∈ chunk5_117, ¬ Need 5 w.toFinset := by
  have h : chunk5_117.all (routes 4 pool5_117.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_117,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_179 _ hm
private def chunk5_118 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire62708],
  [wire15,wire240,wire4369,wire34952,wire62805],
  [wire15,wire240,wire4369,wire34952,wire64170],
  [wire15,wire240,wire4369,wire34952,wire64443]]
private def pool5_118 : List (List (List T)) := [chunk4_7]
private theorem checked5_118 : ∀ w ∈ chunk5_118, ¬ Need 5 w.toFinset := by
  have h : chunk5_118.all (routes 4 pool5_118.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_118,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_7 _ hm
private def chunk5_119 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire64716],
  [wire15,wire240,wire4369,wire34952,wire64989],
  [wire15,wire240,wire4369,wire34952,wire65314],
  [wire15,wire240,wire4369,wire34952,wire65348]]
private def pool5_119 : List (List (List T)) := [chunk4_135, chunk4_143]
private theorem checked5_119 : ∀ w ∈ chunk5_119, ¬ Need 5 w.toFinset := by
  have h : chunk5_119.all (routes 4 pool5_119.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_119,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_135 _ hm
  · exact checked4_143 _ hm
private def chunk5_120 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire65522],
  [wire15,wire240,wire4369,wire34952,wire65524],
  [wire15,wire240,wire4369,wire34952,wire65531],
  [wire15,wire240,wire4369,wire34952,wire65533]]
private def pool5_120 : List (List (List T)) := [chunk4_7, chunk4_135, chunk4_143, chunk4_180]
private theorem checked5_120 : ∀ w ∈ chunk5_120, ¬ Need 5 w.toFinset := by
  have h : chunk5_120.all (routes 4 pool5_120.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_120,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_135 _ hm
  · exact checked4_143 _ hm
  · exact checked4_180 _ hm
private def chunk5_121 : List (List T) := [[wire15,wire240,wire4369,wire34954],
  [wire15,wire240,wire4369,wire34954,wire61440],
  [wire15,wire240,wire4369,wire34959,wire43690],
  [wire15,wire240,wire4369,wire34959,wire48059]]
private def pool5_121 : List (List (List T)) := [chunk4_6, chunk4_8, chunk4_20, chunk4_21, chunk4_22, chunk4_23, chunk4_27, chunk4_40, chunk4_42, chunk4_50, chunk4_62, chunk4_121, chunk4_135, chunk4_143]
private theorem checked5_121 : ∀ w ∈ chunk5_121, ¬ Need 5 w.toFinset := by
  have h : chunk5_121.all (routes 4 pool5_121.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_121,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_8 _ hm
  · exact checked4_20 _ hm
  · exact checked4_21 _ hm
  · exact checked4_22 _ hm
  · exact checked4_23 _ hm
  · exact checked4_27 _ hm
  · exact checked4_40 _ hm
  · exact checked4_42 _ hm
  · exact checked4_50 _ hm
  · exact checked4_62 _ hm
  · exact checked4_121 _ hm
  · exact checked4_135 _ hm
  · exact checked4_143 _ hm
private def chunk5_122 : List (List T) := [[wire15,wire240,wire4369,wire34959,wire62532],
  [wire15,wire240,wire4369,wire36744,wire43690],
  [wire15,wire240,wire4369,wire36744,wire44970],
  [wire15,wire240,wire4369,wire36744,wire48059]]
private def pool5_122 : List (List (List T)) := [chunk4_8]
private theorem checked5_122 : ∀ w ∈ chunk5_122, ¬ Need 5 w.toFinset := by
  have h : chunk5_122.all (routes 4 pool5_122.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_122,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_8 _ hm
private def chunk5_123 : List (List T) := [[wire15,wire240,wire4369,wire36744,wire52428],
  [wire15,wire240,wire4369,wire36744,wire53196],
  [wire15,wire240,wire4369,wire36744,wire56797],
  [wire15,wire240,wire4369,wire36744,wire61986]]
private def pool5_123 : List (List (List T)) := [chunk4_144]
private theorem checked5_123 : ∀ w ∈ chunk5_123, ¬ Need 5 w.toFinset := by
  have h : chunk5_123.all (routes 4 pool5_123.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_123,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_144 _ hm
private def chunk5_124 : List (List T) := [[wire15,wire240,wire4369,wire36744,wire62532],
  [wire15,wire240,wire4369,wire39321,wire43690],
  [wire15,wire240,wire4369,wire39321,wire48059],
  [wire15,wire240,wire4369,wire39321,wire52428]]
private def pool5_124 : List (List (List T)) := [chunk4_8, chunk4_41]
private theorem checked5_124 : ∀ w ∈ chunk5_124, ¬ Need 5 w.toFinset := by
  have h : chunk5_124.all (routes 4 pool5_124.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_124,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_8 _ hm
  · exact checked4_41 _ hm
private def chunk5_125 : List (List T) := [[wire15,wire240,wire4369,wire39321,wire56797],
  [wire15,wire240,wire4369,wire39321,wire61986],
  [wire15,wire240,wire4369,wire39321,wire62532],
  [wire15,wire240,wire4369,wire43690,wire52428]]
private def pool5_125 : List (List (List T)) := []
private theorem checked5_125 : ∀ w ∈ chunk5_125, ¬ Need 5 w.toFinset := by
  have h : chunk5_125.all (routes 4 pool5_125.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_125] at hv
private def chunk5_126 : List (List T) := [[wire15,wire240,wire4369,wire43690,wire56797],
  [wire15,wire240,wire4369,wire43690,wire61986],
  [wire15,wire240,wire4369,wire43690,wire63624],
  [wire15,wire240,wire4369,wire48059,wire52428]]
private def pool5_126 : List (List (List T)) := []
private theorem checked5_126 : ∀ w ∈ chunk5_126, ¬ Need 5 w.toFinset := by
  have h : chunk5_126.all (routes 4 pool5_126.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_126] at hv
private def chunk5_127 : List (List T) := [[wire15,wire240,wire4369,wire48059,wire56797],
  [wire15,wire240,wire4369,wire48059,wire61986],
  [wire15,wire240,wire4369,wire48059,wire63624],
  [wire15,wire240,wire4369,wire52428,wire62532]]
private def pool5_127 : List (List (List T)) := [chunk4_9]
private theorem checked5_127 : ∀ w ∈ chunk5_127, ¬ Need 5 w.toFinset := by
  have h : chunk5_127.all (routes 4 pool5_127.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_127,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_9 _ hm
private def chunk5_128 : List (List T) := [[wire15,wire240,wire4369,wire52428,wire63624],
  [wire15,wire240,wire4369,wire56797,wire62532],
  [wire15,wire240,wire4369,wire56797,wire63624],
  [wire15,wire240,wire4369,wire61986,wire62532]]
private def pool5_128 : List (List (List T)) := []
private theorem checked5_128 : ∀ w ∈ chunk5_128, ¬ Need 5 w.toFinset := by
  have h : chunk5_128.all (routes 4 pool5_128.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_128] at hv
private def chunk5_129 : List (List T) := [[wire15,wire240,wire4369,wire61986,wire63078],
  [wire15,wire240,wire4369,wire61986,wire63624],
  [wire15,wire240,wire4369,wire61986,wire64170],
  [wire15,wire240,wire4369,wire62532,wire63078]]
private def pool5_129 : List (List (List T)) := []
private theorem checked5_129 : ∀ w ∈ chunk5_129, ¬ Need 5 w.toFinset := by
  have h : chunk5_129.all (routes 4 pool5_129.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_129] at hv
private def chunk5_130 : List (List T) := [[wire15,wire240,wire4369,wire62532,wire63624],
  [wire15,wire240,wire4369,wire62532,wire64716],
  [wire15,wire240,wire4369,wire63624,wire64170],
  [wire15,wire240,wire4369,wire63624,wire64716]]
private def pool5_130 : List (List (List T)) := []
private theorem checked5_130 : ∀ w ∈ chunk5_130, ¬ Need 5 w.toFinset := by
  have h : chunk5_130.all (routes 4 pool5_130.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_130] at hv
private def chunk5_131 : List (List T) := [[wire15,wire240,wire4371,wire8738,wire17476],
  [wire15,wire240,wire4371,wire8738,wire34952],
  [wire15,wire240,wire4373,wire8738,wire17476],
  [wire15,wire240,wire4373,wire8738,wire34952]]
private def pool5_131 : List (List (List T)) := [chunk4_23, chunk4_24]
private theorem checked5_131 : ∀ w ∈ chunk5_131, ¬ Need 5 w.toFinset := by
  have h : chunk5_131.all (routes 4 pool5_131.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_131,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_23 _ hm
  · exact checked4_24 _ hm
private def chunk5_132 : List (List T) := [[wire15,wire240,wire4373,wire17476,wire34952],
  [wire15,wire240,wire4373,wire34952],
  [wire15,wire240,wire4373,wire34952,wire61440],
  [wire15,wire240,wire4377,wire8738,wire34952]]
private def pool5_132 : List (List (List T)) := [chunk4_17, chunk4_24, chunk4_25, chunk4_26, chunk4_39, chunk4_50, chunk4_68, chunk4_69, chunk4_122, chunk4_140]
private theorem checked5_132 : ∀ w ∈ chunk5_132, ¬ Need 5 w.toFinset := by
  have h : chunk5_132.all (routes 4 pool5_132.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_132,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_17 _ hm
  · exact checked4_24 _ hm
  · exact checked4_25 _ hm
  · exact checked4_26 _ hm
  · exact checked4_39 _ hm
  · exact checked4_50 _ hm
  · exact checked4_68 _ hm
  · exact checked4_69 _ hm
  · exact checked4_122 _ hm
  · exact checked4_140 _ hm
private def chunk5_133 : List (List T) := [[wire15,wire240,wire4377,wire17476,wire34952],
  [wire15,wire240,wire4383,wire8738,wire21845],
  [wire15,wire240,wire4383,wire8738,wire30583],
  [wire15,wire240,wire4383,wire8738,wire34952]]
private def pool5_133 : List (List (List T)) := [chunk4_31, chunk4_141, chunk4_180]
private theorem checked5_133 : ∀ w ∈ chunk5_133, ¬ Need 5 w.toFinset := by
  have h : chunk5_133.all (routes 4 pool5_133.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_133,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_31 _ hm
  · exact checked4_141 _ hm
  · exact checked4_180 _ hm
private def chunk5_134 : List (List T) := [[wire15,wire240,wire4383,wire8738,wire36744],
  [wire15,wire240,wire4383,wire8738,wire43690],
  [wire15,wire240,wire4383,wire8738,wire63624],
  [wire15,wire240,wire4383,wire8946,wire34952]]
private def pool5_134 : List (List (List T)) := [chunk4_32, chunk4_141, chunk4_181]
private theorem checked5_134 : ∀ w ∈ chunk5_134, ¬ Need 5 w.toFinset := by
  have h : chunk5_134.all (routes 4 pool5_134.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_134,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_32 _ hm
  · exact checked4_141 _ hm
  · exact checked4_181 _ hm
private def chunk5_135 : List (List T) := [[wire15,wire240,wire4383,wire12066,wire34952],
  [wire15,wire240,wire4383,wire21845,wire34952],
  [wire15,wire240,wire4383,wire34952,wire43690],
  [wire15,wire240,wire4383,wire34952,wire56797]]
private def pool5_135 : List (List (List T)) := [chunk4_6, chunk4_12, chunk4_25, chunk4_26, chunk4_36, chunk4_42, chunk4_143, chunk4_181, chunk4_182]
private theorem checked5_135 : ∀ w ∈ chunk5_135, ¬ Need 5 w.toFinset := by
  have h : chunk5_135.all (routes 4 pool5_135.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_135,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_12 _ hm
  · exact checked4_25 _ hm
  · exact checked4_26 _ hm
  · exact checked4_36 _ hm
  · exact checked4_42 _ hm
  · exact checked4_143 _ hm
  · exact checked4_181 _ hm
  · exact checked4_182 _ hm
private def chunk5_136 : List (List T) := [[wire15,wire240,wire4383,wire34952,wire61986],
  [wire15,wire240,wire4401,wire8738,wire17476],
  [wire15,wire240,wire4401,wire8738,wire34952],
  [wire15,wire240,wire4433,wire8738,wire17476]]
private def pool5_136 : List (List (List T)) := [chunk4_27, chunk4_182]
private theorem checked5_136 : ∀ w ∈ chunk5_136, ¬ Need 5 w.toFinset := by
  have h : chunk5_136.all (routes 4 pool5_136.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_136,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_27 _ hm
  · exact checked4_182 _ hm
private def chunk5_137 : List (List T) := [[wire15,wire240,wire4433,wire17476,wire34952],
  [wire15,wire240,wire4497,wire8738,wire17476],
  [wire15,wire240,wire4497,wire8738,wire34952],
  [wire15,wire240,wire4497,wire17476]]
private def pool5_137 : List (List (List T)) := [chunk4_3, chunk4_28, chunk4_29, chunk4_32, chunk4_33, chunk4_51, chunk4_70, chunk4_122, chunk4_144]
private theorem checked5_137 : ∀ w ∈ chunk5_137, ¬ Need 5 w.toFinset := by
  have h : chunk5_137.all (routes 4 pool5_137.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_137,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_28 _ hm
  · exact checked4_29 _ hm
  · exact checked4_32 _ hm
  · exact checked4_33 _ hm
  · exact checked4_51 _ hm
  · exact checked4_70 _ hm
  · exact checked4_122 _ hm
  · exact checked4_144 _ hm
private def chunk5_138 : List (List T) := [[wire15,wire240,wire4497,wire17476,wire34952],
  [wire15,wire240,wire4497,wire17476,wire61440],
  [wire15,wire240,wire4593,wire8738,wire17476],
  [wire15,wire240,wire4593,wire8738,wire20292]]
private def pool5_138 : List (List (List T)) := [chunk4_30, chunk4_183]
private theorem checked5_138 : ∀ w ∈ chunk5_138, ¬ Need 5 w.toFinset := by
  have h : chunk5_138.all (routes 4 pool5_138.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_138,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_30 _ hm
  · exact checked4_183 _ hm
private def chunk5_139 : List (List T) := [[wire15,wire240,wire4593,wire8738,wire26214],
  [wire15,wire240,wire4593,wire8738,wire39321],
  [wire15,wire240,wire4593,wire8738,wire48059],
  [wire15,wire240,wire4593,wire8738,wire62532]]
private def pool5_139 : List (List (List T)) := [chunk4_32, chunk4_71, chunk4_183, chunk4_184]
private theorem checked5_139 : ∀ w ∈ chunk5_139, ¬ Need 5 w.toFinset := by
  have h : chunk5_139.all (routes 4 pool5_139.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_139,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_32 _ hm
  · exact checked4_71 _ hm
  · exact checked4_183 _ hm
  · exact checked4_184 _ hm
private def chunk5_140 : List (List T) := [[wire15,wire240,wire4593,wire8751,wire17476],
  [wire15,wire240,wire4593,wire12066,wire17476],
  [wire15,wire240,wire4593,wire17476,wire26214],
  [wire15,wire240,wire4593,wire17476,wire39321]]
private def pool5_140 : List (List (List T)) := [chunk4_18, chunk4_28, chunk4_36, chunk4_37, chunk4_73, chunk4_184, chunk4_185]
private theorem checked5_140 : ∀ w ∈ chunk5_140, ¬ Need 5 w.toFinset := by
  have h : chunk5_140.all (routes 4 pool5_140.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_140,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_18 _ hm
  · exact checked4_28 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
  · exact checked4_73 _ hm
  · exact checked4_184 _ hm
  · exact checked4_185 _ hm
private def chunk5_141 : List (List T) := [[wire15,wire240,wire4593,wire17476,wire56797],
  [wire15,wire240,wire4593,wire17476,wire61986],
  [wire15,wire240,wire4881,wire8738,wire17476],
  [wire15,wire240,wire4881,wire8738,wire34952]]
private def pool5_141 : List (List (List T)) := [chunk4_18, chunk4_30, chunk4_185]
private theorem checked5_141 : ∀ w ∈ chunk5_141, ¬ Need 5 w.toFinset := by
  have h : chunk5_141.all (routes 4 pool5_141.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_141,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_18 _ hm
  · exact checked4_30 _ hm
  · exact checked4_185 _ hm
private def chunk5_142 : List (List T) := [[wire15,wire240,wire5393,wire8738,wire17476],
  [wire15,wire240,wire5393,wire17476,wire34952],
  [wire15,wire240,wire6417,wire8738,wire34952],
  [wire15,wire240,wire6417,wire17476,wire34952]]
private def pool5_142 : List (List (List T)) := []
private theorem checked5_142 : ∀ w ∈ chunk5_142, ¬ Need 5 w.toFinset := by
  have h : chunk5_142.all (routes 4 pool5_142.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_142] at hv
private def chunk5_143 : List (List T) := [[wire15,wire240,wire8738,wire12561,wire17476],
  [wire15,wire240,wire8738,wire12561,wire34952],
  [wire15,wire240,wire8738,wire13107,wire17476],
  [wire15,wire240,wire8738,wire13107,wire20292]]
private def pool5_143 : List (List (List T)) := [chunk4_31]
private theorem checked5_143 : ∀ w ∈ chunk5_143, ¬ Need 5 w.toFinset := by
  have h : chunk5_143.all (routes 4 pool5_143.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_143,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_31 _ hm
private def chunk5_144 : List (List T) := [[wire15,wire240,wire8738,wire13107,wire21845],
  [wire15,wire240,wire8738,wire13107,wire26214],
  [wire15,wire240,wire8738,wire13107,wire30583],
  [wire15,wire240,wire8738,wire13107,wire34952]]
private def pool5_144 : List (List (List T)) := [chunk4_30, chunk4_31]
private theorem checked5_144 : ∀ w ∈ chunk5_144, ¬ Need 5 w.toFinset := by
  have h : chunk5_144.all (routes 4 pool5_144.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_144,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
private def chunk5_145 : List (List T) := [[wire15,wire240,wire8738,wire13107,wire36744],
  [wire15,wire240,wire8738,wire13107,wire39321],
  [wire15,wire240,wire8738,wire13107,wire43690],
  [wire15,wire240,wire8738,wire13107,wire48059]]
private def pool5_145 : List (List (List T)) := [chunk4_31]
private theorem checked5_145 : ∀ w ∈ chunk5_145, ¬ Need 5 w.toFinset := by
  have h : chunk5_145.all (routes 4 pool5_145.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_145,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_31 _ hm
private def chunk5_146 : List (List T) := [[wire15,wire240,wire8738,wire13107,wire62532],
  [wire15,wire240,wire8738,wire13107,wire63624],
  [wire15,wire240,wire8738,wire13119,wire34952],
  [wire15,wire240,wire8738,wire13299,wire17476]]
private def pool5_146 : List (List (List T)) := [chunk4_32, chunk4_185, chunk4_186]
private theorem checked5_146 : ∀ w ∈ chunk5_146, ¬ Need 5 w.toFinset := by
  have h : chunk5_146.all (routes 4 pool5_146.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_146,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_32 _ hm
  · exact checked4_185 _ hm
  · exact checked4_186 _ hm
private def chunk5_147 : List (List T) := [[wire15,wire240,wire8738,wire17472,wire34952],
  [wire15,wire240,wire8738,wire17476,wire20753],
  [wire15,wire240,wire8738,wire17476,wire21845],
  [wire15,wire240,wire8738,wire17476,wire22005]]
private def pool5_147 : List (List (List T)) := [chunk4_35, chunk4_36, chunk4_37, chunk4_74, chunk4_145, chunk4_146, chunk4_147]
private theorem checked5_147 : ∀ w ∈ chunk5_147, ¬ Need 5 w.toFinset := by
  have h : chunk5_147.all (routes 4 pool5_147.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_147,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
  · exact checked4_74 _ hm
  · exact checked4_145 _ hm
  · exact checked4_146 _ hm
  · exact checked4_147 _ hm
private def chunk5_148 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire30471],
  [wire15,wire240,wire8738,wire17476,wire30583],
  [wire15,wire240,wire8738,wire17476,wire30711],
  [wire15,wire240,wire8738,wire17476,wire34824]]
private def pool5_148 : List (List (List T)) := [chunk4_33, chunk4_75, chunk4_146, chunk4_147]
private theorem checked5_148 : ∀ w ∈ chunk5_148, ¬ Need 5 w.toFinset := by
  have h : chunk5_148.all (routes 4 pool5_148.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_148,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_33 _ hm
  · exact checked4_75 _ hm
  · exact checked4_146 _ hm
  · exact checked4_147 _ hm
private def chunk5_149 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire34952],
  [wire15,wire240,wire8738,wire17476,wire34954],
  [wire15,wire240,wire8738,wire17476,wire34956],
  [wire15,wire240,wire8738,wire17476,wire34968]]
private def pool5_149 : List (List (List T)) := [chunk4_37, chunk4_75, chunk4_147, chunk4_152]
private theorem checked5_149 : ∀ w ∈ chunk5_149, ¬ Need 5 w.toFinset := by
  have h : chunk5_149.all (routes 4 pool5_149.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_149,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_37 _ hm
  · exact checked4_75 _ hm
  · exact checked4_147 _ hm
  · exact checked4_152 _ hm
private def chunk5_150 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire34984],
  [wire15,wire240,wire8738,wire17476,wire35016],
  [wire15,wire240,wire8738,wire17476,wire35064],
  [wire15,wire240,wire8738,wire17476,wire35464]]
private def pool5_150 : List (List (List T)) := [chunk4_75, chunk4_148]
private theorem checked5_150 : ∀ w ∈ chunk5_150, ¬ Need 5 w.toFinset := by
  have h : chunk5_150.all (routes 4 pool5_150.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_150,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_148 _ hm
private def chunk5_151 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire35976],
  [wire15,wire240,wire8738,wire17476,wire43144],
  [wire15,wire240,wire8738,wire17476,wire43690],
  [wire15,wire240,wire8738,wire17476,wire43770]]
private def pool5_151 : List (List (List T)) := [chunk4_13, chunk4_38, chunk4_149]
private theorem checked5_151 : ∀ w ∈ chunk5_151, ¬ Need 5 w.toFinset := by
  have h : chunk5_151.all (routes 4 pool5_151.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_151,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_13 _ hm
  · exact checked4_38 _ hm
  · exact checked4_149 _ hm
private def chunk5_152 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire51336],
  [wire15,wire240,wire8738,wire17476,wire52428],
  [wire15,wire240,wire8738,wire17476,wire52476],
  [wire15,wire240,wire8738,wire17476,wire60942]]
private def pool5_152 : List (List (List T)) := [chunk4_33, chunk4_38, chunk4_186]
private theorem checked5_152 : ∀ w ∈ chunk5_152, ¬ Need 5 w.toFinset := by
  have h : chunk5_152.all (routes 4 pool5_152.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_152,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_33 _ hm
  · exact checked4_38 _ hm
  · exact checked4_186 _ hm
private def chunk5_153 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire61166],
  [wire15,wire240,wire8738,wire17476,wire61182],
  [wire15,wire240,wire8738,wire17477,wire34952],
  [wire15,wire240,wire8738,wire17478,wire34952]]
private def pool5_153 : List (List (List T)) := [chunk4_75, chunk4_76, chunk4_147]
private theorem checked5_153 : ∀ w ∈ chunk5_153, ¬ Need 5 w.toFinset := by
  have h : chunk5_153.all (routes 4 pool5_153.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_153,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_76 _ hm
  · exact checked4_147 _ hm
private def chunk5_154 : List (List T) := [[wire15,wire240,wire8738,wire17484,wire34952],
  [wire15,wire240,wire8738,wire17487,wire21845],
  [wire15,wire240,wire8738,wire17487,wire30583],
  [wire15,wire240,wire8738,wire17487,wire34952]]
private def pool5_154 : List (List (List T)) := [chunk4_35, chunk4_76, chunk4_145, chunk4_146, chunk4_147, chunk4_152]
private theorem checked5_154 : ∀ w ∈ chunk5_154, ¬ Need 5 w.toFinset := by
  have h : chunk5_154.all (routes 4 pool5_154.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_154,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_76 _ hm
  · exact checked4_145 _ hm
  · exact checked4_146 _ hm
  · exact checked4_147 _ hm
  · exact checked4_152 _ hm
private def chunk5_155 : List (List T) := [[wire15,wire240,wire8738,wire17487,wire35064],
  [wire15,wire240,wire8738,wire17487,wire43690],
  [wire15,wire240,wire8738,wire17508,wire34952],
  [wire15,wire240,wire8738,wire17604,wire34952]]
private def pool5_155 : List (List (List T)) := [chunk4_0, chunk4_34, chunk4_35, chunk4_39, chunk4_76, chunk4_77, chunk4_81, chunk4_148, chunk4_149, chunk4_150, chunk4_153, chunk4_186]
private theorem checked5_155 : ∀ w ∈ chunk5_155, ¬ Need 5 w.toFinset := by
  have h : chunk5_155.all (routes 4 pool5_155.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_155,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_34 _ hm
  · exact checked4_35 _ hm
  · exact checked4_39 _ hm
  · exact checked4_76 _ hm
  · exact checked4_77 _ hm
  · exact checked4_81 _ hm
  · exact checked4_148 _ hm
  · exact checked4_149 _ hm
  · exact checked4_150 _ hm
  · exact checked4_153 _ hm
  · exact checked4_186 _ hm
private def chunk5_156 : List (List T) := [[wire15,wire240,wire8738,wire17988,wire34952],
  [wire15,wire240,wire8738,wire19524,wire34952],
  [wire15,wire240,wire8738,wire20292,wire52428],
  [wire15,wire240,wire8738,wire20292,wire61166]]
private def pool5_156 : List (List (List T)) := [chunk4_77]
private theorem checked5_156 : ∀ w ∈ chunk5_156, ¬ Need 5 w.toFinset := by
  have h : chunk5_156.all (routes 4 pool5_156.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_156,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_77 _ hm
private def chunk5_157 : List (List T) := [[wire15,wire240,wire8738,wire21845,wire26214],
  [wire15,wire240,wire8738,wire21845,wire39321],
  [wire15,wire240,wire8738,wire21845,wire48059],
  [wire15,wire240,wire8738,wire21845,wire52428]]
private def pool5_157 : List (List (List T)) := [chunk4_35]
private theorem checked5_157 : ∀ w ∈ chunk5_157, ¬ Need 5 w.toFinset := by
  have h : chunk5_157.all (routes 4 pool5_157.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_157,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_35 _ hm
private def chunk5_158 : List (List T) := [[wire15,wire240,wire8738,wire21845,wire61166],
  [wire15,wire240,wire8738,wire25668,wire34952],
  [wire15,wire240,wire8738,wire26214,wire30583],
  [wire15,wire240,wire8738,wire26214,wire34952]]
private def pool5_158 : List (List (List T)) := [chunk4_38, chunk4_77, chunk4_78]
private theorem checked5_158 : ∀ w ∈ chunk5_158, ¬ Need 5 w.toFinset := by
  have h : chunk5_158.all (routes 4 pool5_158.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_158,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_38 _ hm
  · exact checked4_77 _ hm
  · exact checked4_78 _ hm
private def chunk5_159 : List (List T) := [[wire15,wire240,wire8738,wire26214,wire35064],
  [wire15,wire240,wire8738,wire26214,wire43690],
  [wire15,wire240,wire8738,wire26214,wire52428],
  [wire15,wire240,wire8738,wire26214,wire61166]]
private def pool5_159 : List (List (List T)) := [chunk4_38, chunk4_78, chunk4_82]
private theorem checked5_159 : ∀ w ∈ chunk5_159, ¬ Need 5 w.toFinset := by
  have h : chunk5_159.all (routes 4 pool5_159.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_159,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_38 _ hm
  · exact checked4_78 _ hm
  · exact checked4_82 _ hm
private def chunk5_160 : List (List T) := [[wire15,wire240,wire8738,wire26223,wire34952],
  [wire15,wire240,wire8738,wire30583,wire39321],
  [wire15,wire240,wire8738,wire30583,wire48059],
  [wire15,wire240,wire8738,wire30583,wire52428]]
private def pool5_160 : List (List (List T)) := [chunk4_1, chunk4_39, chunk4_78]
private theorem checked5_160 : ∀ w ∈ chunk5_160, ¬ Need 5 w.toFinset := by
  have h : chunk5_160.all (routes 4 pool5_160.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_160,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_39 _ hm
  · exact checked4_78 _ hm
private def chunk5_161 : List (List T) := [[wire15,wire240,wire8738,wire30583,wire61166],
  [wire15,wire240,wire8738,wire34952,wire37137],
  [wire15,wire240,wire8738,wire34952,wire39321],
  [wire15,wire240,wire8738,wire34952,wire39327]]
private def pool5_161 : List (List (List T)) := [chunk4_41, chunk4_42, chunk4_79]
private theorem checked5_161 : ∀ w ∈ chunk5_161, ¬ Need 5 w.toFinset := by
  have h : chunk5_161.all (routes 4 pool5_161.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_161,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_41 _ hm
  · exact checked4_42 _ hm
  · exact checked4_79 _ hm
private def chunk5_162 : List (List T) := [[wire15,wire240,wire8738,wire34952,wire48048],
  [wire15,wire240,wire8738,wire34952,wire48059],
  [wire15,wire240,wire8738,wire34952,wire48063],
  [wire15,wire240,wire8738,wire34952,wire50244]]
private def pool5_162 : List (List (List T)) := [chunk4_79, chunk4_80]
private theorem checked5_162 : ∀ w ∈ chunk5_162, ¬ Need 5 w.toFinset := by
  have h : chunk5_162.all (routes 4 pool5_162.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_162,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_79 _ hm
  · exact checked4_80 _ hm
private def chunk5_163 : List (List T) := [[wire15,wire240,wire8738,wire34952,wire52428],
  [wire15,wire240,wire8738,wire34952,wire52431],
  [wire15,wire240,wire8738,wire34952,wire61152],
  [wire15,wire240,wire8738,wire34952,wire61166]]
private def pool5_163 : List (List (List T)) := [chunk4_39, chunk4_42, chunk4_186]
private theorem checked5_163 : ∀ w ∈ chunk5_163, ¬ Need 5 w.toFinset := by
  have h : chunk5_163.all (routes 4 pool5_163.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_163,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_39 _ hm
  · exact checked4_42 _ hm
  · exact checked4_186 _ hm
private def chunk5_164 : List (List T) := [[wire15,wire240,wire8738,wire34952,wire61167],
  [wire15,wire240,wire8738,wire35064,wire39321],
  [wire15,wire240,wire8738,wire35064,wire48059],
  [wire15,wire240,wire8738,wire36744,wire52428]]
private def pool5_164 : List (List (List T)) := [chunk4_41, chunk4_79, chunk4_82]
private theorem checked5_164 : ∀ w ∈ chunk5_164, ¬ Need 5 w.toFinset := by
  have h : chunk5_164.all (routes 4 pool5_164.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_164,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_41 _ hm
  · exact checked4_79 _ hm
  · exact checked4_82 _ hm
private def chunk5_165 : List (List T) := [[wire15,wire240,wire8738,wire36744,wire61166],
  [wire15,wire240,wire8738,wire39321,wire43690],
  [wire15,wire240,wire8738,wire39321,wire52428],
  [wire15,wire240,wire8738,wire39321,wire61166]]
private def pool5_165 : List (List (List T)) := [chunk4_41]
private theorem checked5_165 : ∀ w ∈ chunk5_165, ¬ Need 5 w.toFinset := by
  have h : chunk5_165.all (routes 4 pool5_165.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_165,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_41 _ hm
private def chunk5_166 : List (List T) := [[wire15,wire240,wire8738,wire43690,wire48059],
  [wire15,wire240,wire8738,wire43690,wire52428],
  [wire15,wire240,wire8738,wire43690,wire61166],
  [wire15,wire240,wire8738,wire48059,wire52428]]
private def pool5_166 : List (List (List T)) := [chunk4_42]
private theorem checked5_166 : ∀ w ∈ chunk5_166, ¬ Need 5 w.toFinset := by
  have h : chunk5_166.all (routes 4 pool5_166.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_166,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_42 _ hm
private def chunk5_167 : List (List T) := [[wire15,wire240,wire8738,wire48059,wire61166],
  [wire15,wire240,wire8738,wire52428,wire62532],
  [wire15,wire240,wire8738,wire52428,wire63624],
  [wire15,wire240,wire8738,wire61166,wire62532]]
private def pool5_167 : List (List (List T)) := []
private theorem checked5_167 : ∀ w ∈ chunk5_167, ¬ Need 5 w.toFinset := by
  have h : chunk5_167.all (routes 4 pool5_167.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_167] at hv
private def chunk5_168 : List (List T) := [[wire15,wire240,wire8738,wire61166,wire63624],
  [wire15,wire240,wire8742,wire17476,wire34952],
  [wire15,wire240,wire8746,wire17476,wire34952],
  [wire15,wire240,wire8751,wire17476,wire21845]]
private def pool5_168 : List (List (List T)) := [chunk4_35, chunk4_80, chunk4_81, chunk4_152, chunk4_187]
private theorem checked5_168 : ∀ w ∈ chunk5_168, ¬ Need 5 w.toFinset := by
  have h : chunk5_168.all (routes 4 pool5_168.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_168,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_80 _ hm
  · exact checked4_81 _ hm
  · exact checked4_152 _ hm
  · exact checked4_187 _ hm
private def chunk5_169 : List (List T) := [[wire15,wire240,wire8751,wire17476,wire43690],
  [wire15,wire240,wire8751,wire17476,wire61166],
  [wire15,wire240,wire8802,wire17476,wire34952],
  [wire15,wire240,wire8866,wire17476,wire34952]]
private def pool5_169 : List (List (List T)) := [chunk4_39, chunk4_81, chunk4_153, chunk4_187]
private theorem checked5_169 : ∀ w ∈ chunk5_169, ¬ Need 5 w.toFinset := by
  have h : chunk5_169.all (routes 4 pool5_169.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_169,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_39 _ hm
  · exact checked4_81 _ hm
  · exact checked4_153 _ hm
  · exact checked4_187 _ hm
private def chunk5_170 : List (List T) := [[wire15,wire240,wire8946,wire26214,wire34952],
  [wire15,wire240,wire8946,wire34952,wire39321],
  [wire15,wire240,wire8946,wire34952,wire61166],
  [wire15,wire240,wire9762,wire17476,wire34952]]
private def pool5_170 : List (List (List T)) := [chunk4_38, chunk4_41, chunk4_82, chunk4_187, chunk4_188]
private theorem checked5_170 : ∀ w ∈ chunk5_170, ¬ Need 5 w.toFinset := by
  have h : chunk5_170.all (routes 4 pool5_170.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_170,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_38 _ hm
  · exact checked4_41 _ hm
  · exact checked4_82 _ hm
  · exact checked4_187 _ hm
  · exact checked4_188 _ hm
private def chunk5_171 : List (List T) := [[wire15,wire240,wire10786,wire17476,wire34952],
  [wire15,wire240,wire12066,wire17476,wire21845],
  [wire15,wire240,wire12066,wire17476,wire43690],
  [wire15,wire240,wire12066,wire17476,wire61166]]
private def pool5_171 : List (List (List T)) := [chunk4_153, chunk4_154]
private theorem checked5_171 : ∀ w ∈ chunk5_171, ¬ Need 5 w.toFinset := by
  have h : chunk5_171.all (routes 4 pool5_171.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_171,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_153 _ hm
  · exact checked4_154 _ hm
private def chunk5_172 : List (List T) := [[wire15,wire240,wire12066,wire26214,wire34952],
  [wire15,wire240,wire12066,wire34952,wire39321],
  [wire15,wire240,wire12066,wire34952,wire61166],
  [wire15,wire240,wire13107,wire17476,wire21845]]
private def pool5_172 : List (List (List T)) := [chunk4_30, chunk4_82, chunk4_83, chunk4_154]
private theorem checked5_172 : ∀ w ∈ chunk5_172, ¬ Need 5 w.toFinset := by
  have h : chunk5_172.all (routes 4 pool5_172.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_172,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_30 _ hm
  · exact checked4_82 _ hm
  · exact checked4_83 _ hm
  · exact checked4_154 _ hm
private def chunk5_173 : List (List T) := [[wire15,wire240,wire13107,wire17476,wire26214],
  [wire15,wire240,wire13107,wire17476,wire39321],
  [wire15,wire240,wire13107,wire17476,wire43690],
  [wire15,wire240,wire13107,wire17476,wire56797]]
private def pool5_173 : List (List (List T)) := [chunk4_31, chunk4_154, chunk4_155]
private theorem checked5_173 : ∀ w ∈ chunk5_173, ¬ Need 5 w.toFinset := by
  have h : chunk5_173.all (routes 4 pool5_173.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_173,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_31 _ hm
  · exact checked4_154 _ hm
  · exact checked4_155 _ hm
private def chunk5_174 : List (List T) := [[wire15,wire240,wire13107,wire17476,wire61166],
  [wire15,wire240,wire13107,wire21845],
  [wire15,wire240,wire13107,wire21845,wire34952],
  [wire15,wire240,wire13107,wire21845,wire61440]]
private def pool5_174 : List (List (List T)) := [chunk4_30, chunk4_31, chunk4_36, chunk4_51, chunk4_83, chunk4_122, chunk4_155]
private theorem checked5_174 : ∀ w ∈ chunk5_174, ¬ Need 5 w.toFinset := by
  have h : chunk5_174.all (routes 4 pool5_174.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_174,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
  · exact checked4_36 _ hm
  · exact checked4_51 _ hm
  · exact checked4_83 _ hm
  · exact checked4_122 _ hm
  · exact checked4_155 _ hm
private def chunk5_175 : List (List T) := [[wire15,wire240,wire13107,wire26214],
  [wire15,wire240,wire13107,wire26214,wire34952],
  [wire15,wire240,wire13107,wire26214,wire61440],
  [wire15,wire240,wire13107,wire34952,wire39321]]
private def pool5_175 : List (List (List T)) := [chunk4_31, chunk4_32, chunk4_38, chunk4_51, chunk4_84, chunk4_122, chunk4_156]
private theorem checked5_175 : ∀ w ∈ chunk5_175, ¬ Need 5 w.toFinset := by
  have h : chunk5_175.all (routes 4 pool5_175.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_175,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_31 _ hm
  · exact checked4_32 _ hm
  · exact checked4_38 _ hm
  · exact checked4_51 _ hm
  · exact checked4_84 _ hm
  · exact checked4_122 _ hm
  · exact checked4_156 _ hm
private def chunk5_176 : List (List T) := [[wire15,wire240,wire13107,wire34952,wire43690],
  [wire15,wire240,wire13107,wire34952,wire56797],
  [wire15,wire240,wire13107,wire34952,wire61166],
  [wire15,wire240,wire13107,wire39321]]
private def pool5_176 : List (List (List T)) := [chunk4_31, chunk4_32, chunk4_41, chunk4_51, chunk4_85, chunk4_123, chunk4_156]
private theorem checked5_176 : ∀ w ∈ chunk5_176, ¬ Need 5 w.toFinset := by
  have h : chunk5_176.all (routes 4 pool5_176.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_176,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_31 _ hm
  · exact checked4_32 _ hm
  · exact checked4_41 _ hm
  · exact checked4_51 _ hm
  · exact checked4_85 _ hm
  · exact checked4_123 _ hm
  · exact checked4_156 _ hm
private def chunk5_177 : List (List T) := [[wire15,wire240,wire13107,wire39321,wire61440],
  [wire15,wire240,wire13107,wire43690],
  [wire15,wire240,wire13107,wire43690,wire61440],
  [wire15,wire240,wire17476,wire20753,wire34952]]
private def pool5_177 : List (List (List T)) := [chunk4_30, chunk4_31, chunk4_32, chunk4_42, chunk4_52, chunk4_86, chunk4_123, chunk4_157]
private theorem checked5_177 : ∀ w ∈ chunk5_177, ¬ Need 5 w.toFinset := by
  have h : chunk5_177.all (routes 4 pool5_177.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_177,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_30 _ hm
  · exact checked4_31 _ hm
  · exact checked4_32 _ hm
  · exact checked4_42 _ hm
  · exact checked4_52 _ hm
  · exact checked4_86 _ hm
  · exact checked4_123 _ hm
  · exact checked4_157 _ hm
private def chunk5_178 : List (List T) := [[wire15,wire240,wire17476,wire21845,wire26214],
  [wire15,wire240,wire17476,wire21845,wire30583],
  [wire15,wire240,wire17476,wire21845,wire34952],
  [wire15,wire240,wire17476,wire21845,wire34959]]
private def pool5_178 : List (List (List T)) := [chunk4_16, chunk4_35, chunk4_36, chunk4_157, chunk4_158]
private theorem checked5_178 : ∀ w ∈ chunk5_178, ¬ Need 5 w.toFinset := by
  have h : chunk5_178.all (routes 4 pool5_178.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_178,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_16 _ hm
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_157 _ hm
  · exact checked4_158 _ hm
private def chunk5_179 : List (List T) := [[wire15,wire240,wire17476,wire21845,wire36744],
  [wire15,wire240,wire17476,wire21845,wire39321],
  [wire15,wire240,wire17476,wire21845,wire52428],
  [wire15,wire240,wire17476,wire21845,wire56797]]
private def pool5_179 : List (List (List T)) := [chunk4_35, chunk4_36, chunk4_158, chunk4_159]
private theorem checked5_179 : ∀ w ∈ chunk5_179, ¬ Need 5 w.toFinset := by
  have h : chunk5_179.all (routes 4 pool5_179.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_179,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_158 _ hm
  · exact checked4_159 _ hm
private def chunk5_180 : List (List T) := [[wire15,wire240,wire17476,wire21845,wire61986],
  [wire15,wire240,wire17476,wire21845,wire63624],
  [wire15,wire240,wire17476,wire25122,wire34952],
  [wire15,wire240,wire17476,wire26214,wire30583]]
private def pool5_180 : List (List (List T)) := [chunk4_86, chunk4_160]
private theorem checked5_180 : ∀ w ∈ chunk5_180, ¬ Need 5 w.toFinset := by
  have h : chunk5_180.all (routes 4 pool5_180.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_180,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_86 _ hm
  · exact checked4_160 _ hm
private def chunk5_181 : List (List T) := [[wire15,wire240,wire17476,wire26214,wire34952],
  [wire15,wire240,wire17476,wire26214,wire35064],
  [wire15,wire240,wire17476,wire26214,wire43690],
  [wire15,wire240,wire17476,wire26214,wire52428]]
private def pool5_181 : List (List (List T)) := [chunk4_38, chunk4_87, chunk4_90, chunk4_160]
private theorem checked5_181 : ∀ w ∈ chunk5_181, ¬ Need 5 w.toFinset := by
  have h : chunk5_181.all (routes 4 pool5_181.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_181,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_38 _ hm
  · exact checked4_87 _ hm
  · exact checked4_90 _ hm
  · exact checked4_160 _ hm
private def chunk5_182 : List (List T) := [[wire15,wire240,wire17476,wire26214,wire61166],
  [wire15,wire240,wire17476,wire30583,wire39321],
  [wire15,wire240,wire17476,wire30583,wire43690],
  [wire15,wire240,wire17476,wire30583,wire56797]]
private def pool5_182 : List (List (List T)) := [chunk4_16, chunk4_161]
private theorem checked5_182 : ∀ w ∈ chunk5_182, ¬ Need 5 w.toFinset := by
  have h : chunk5_182.all (routes 4 pool5_182.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_182,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_16 _ hm
  · exact checked4_161 _ hm
private def chunk5_183 : List (List T) := [[wire15,wire240,wire17476,wire30583,wire61166],
  [wire15,wire240,wire17476,wire34952,wire37137],
  [wire15,wire240,wire17476,wire34952,wire39321],
  [wire15,wire240,wire17476,wire34952,wire41506]]
private def pool5_183 : List (List (List T)) := [chunk4_16, chunk4_41, chunk4_88, chunk4_161]
private theorem checked5_183 : ∀ w ∈ chunk5_183, ¬ Need 5 w.toFinset := by
  have h : chunk5_183.all (routes 4 pool5_183.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_183,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_16 _ hm
  · exact checked4_41 _ hm
  · exact checked4_88 _ hm
  · exact checked4_161 _ hm
private def chunk5_184 : List (List T) := [[wire15,wire240,wire17476,wire34952,wire43690],
  [wire15,wire240,wire17476,wire34952,wire56797],
  [wire15,wire240,wire17476,wire34952,wire61166],
  [wire15,wire240,wire17476,wire34959,wire43690]]
private def pool5_184 : List (List (List T)) := [chunk4_42, chunk4_88, chunk4_162]
private theorem checked5_184 : ∀ w ∈ chunk5_184, ¬ Need 5 w.toFinset := by
  have h : chunk5_184.all (routes 4 pool5_184.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_184,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_42 _ hm
  · exact checked4_88 _ hm
  · exact checked4_162 _ hm
private def chunk5_185 : List (List T) := [[wire15,wire240,wire17476,wire34959,wire61166],
  [wire15,wire240,wire17476,wire35064,wire39321],
  [wire15,wire240,wire17476,wire35064,wire56797],
  [wire15,wire240,wire17476,wire36744,wire43690]]
private def pool5_185 : List (List (List T)) := [chunk4_41, chunk4_88, chunk4_90, chunk4_162, chunk4_163]
private theorem checked5_185 : ∀ w ∈ chunk5_185, ¬ Need 5 w.toFinset := by
  have h : chunk5_185.all (routes 4 pool5_185.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_185,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_41 _ hm
  · exact checked4_88 _ hm
  · exact checked4_90 _ hm
  · exact checked4_162 _ hm
  · exact checked4_163 _ hm
private def chunk5_186 : List (List T) := [[wire15,wire240,wire17476,wire36744,wire61166],
  [wire15,wire240,wire17476,wire39321,wire43690],
  [wire15,wire240,wire17476,wire39321,wire52428],
  [wire15,wire240,wire17476,wire39321,wire61166]]
private def pool5_186 : List (List (List T)) := [chunk4_41, chunk4_163]
private theorem checked5_186 : ∀ w ∈ chunk5_186, ¬ Need 5 w.toFinset := by
  have h : chunk5_186.all (routes 4 pool5_186.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_186,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_41 _ hm
  · exact checked4_163 _ hm
private def chunk5_187 : List (List T) := [[wire15,wire240,wire17476,wire43690,wire52428],
  [wire15,wire240,wire17476,wire43690,wire56797],
  [wire15,wire240,wire17476,wire43690,wire61986],
  [wire15,wire240,wire17476,wire43690,wire63624]]
private def pool5_187 : List (List (List T)) := [chunk4_42, chunk4_163, chunk4_164]
private theorem checked5_187 : ∀ w ∈ chunk5_187, ¬ Need 5 w.toFinset := by
  have h : chunk5_187.all (routes 4 pool5_187.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_187,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_42 _ hm
  · exact checked4_163 _ hm
  · exact checked4_164 _ hm
private def chunk5_188 : List (List T) := [[wire15,wire240,wire17476,wire52428,wire56797],
  [wire15,wire240,wire17476,wire52428,wire61166],
  [wire15,wire240,wire17476,wire56797,wire61166],
  [wire15,wire240,wire17476,wire61166,wire61986]]
private def pool5_188 : List (List (List T)) := []
private theorem checked5_188 : ∀ w ∈ chunk5_188, ¬ Need 5 w.toFinset := by
  have h : chunk5_188.all (routes 4 pool5_188.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_188] at hv
private def chunk5_189 : List (List T) := [[wire15,wire240,wire17476,wire61166,wire63624],
  [wire15,wire240,wire17487,wire21845,wire34952],
  [wire15,wire240,wire17487,wire34952,wire43690],
  [wire15,wire240,wire17487,wire34952,wire56797]]
private def pool5_189 : List (List (List T)) := [chunk4_36, chunk4_42, chunk4_89, chunk4_158, chunk4_162]
private theorem checked5_189 : ∀ w ∈ chunk5_189, ¬ Need 5 w.toFinset := by
  have h : chunk5_189.all (routes 4 pool5_189.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_189,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_36 _ hm
  · exact checked4_42 _ hm
  · exact checked4_89 _ hm
  · exact checked4_158 _ hm
  · exact checked4_162 _ hm
private def chunk5_190 : List (List T) := [[wire15,wire240,wire17652,wire26214,wire34952],
  [wire15,wire240,wire17652,wire34952,wire39321],
  [wire15,wire240,wire17652,wire34952,wire61166],
  [wire15,wire240,wire20292,wire26214,wire34952]]
private def pool5_190 : List (List (List T)) := [chunk4_38, chunk4_41, chunk4_90]
private theorem checked5_190 : ∀ w ∈ chunk5_190, ¬ Need 5 w.toFinset := by
  have h : chunk5_190.all (routes 4 pool5_190.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_190,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_38 _ hm
  · exact checked4_41 _ hm
  · exact checked4_90 _ hm
private def chunk5_191 : List (List T) := [[wire15,wire240,wire20292,wire34952,wire39321],
  [wire15,wire240,wire20292,wire34952,wire61166],
  [wire15,wire240,wire21845,wire26214],
  [wire15,wire240,wire21845,wire26214,wire34952]]
private def pool5_191 : List (List (List T)) := [chunk4_35, chunk4_36, chunk4_38, chunk4_52, chunk4_90, chunk4_91, chunk4_123, chunk4_165]
private theorem checked5_191 : ∀ w ∈ chunk5_191, ¬ Need 5 w.toFinset := by
  have h : chunk5_191.all (routes 4 pool5_191.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_191,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_38 _ hm
  · exact checked4_52 _ hm
  · exact checked4_90 _ hm
  · exact checked4_91 _ hm
  · exact checked4_123 _ hm
  · exact checked4_165 _ hm
private def chunk5_192 : List (List T) := [[wire15,wire240,wire21845,wire26214,wire61440],
  [wire15,wire240,wire21845,wire34952,wire39321],
  [wire15,wire240,wire21845,wire34952,wire48059],
  [wire15,wire240,wire21845,wire34952,wire52428]]
private def pool5_192 : List (List (List T)) := [chunk4_35, chunk4_36, chunk4_91, chunk4_92]
private theorem checked5_192 : ∀ w ∈ chunk5_192, ¬ Need 5 w.toFinset := by
  have h : chunk5_192.all (routes 4 pool5_192.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_192,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_91 _ hm
  · exact checked4_92 _ hm
private def chunk5_193 : List (List T) := [[wire15,wire240,wire21845,wire34952,wire61166],
  [wire15,wire240,wire21845,wire39321],
  [wire15,wire240,wire21845,wire39321,wire61440],
  [wire15,wire240,wire21845,wire52428]]
private def pool5_193 : List (List (List T)) := [chunk4_30, chunk4_35, chunk4_36, chunk4_37, chunk4_41, chunk4_42, chunk4_52, chunk4_92, chunk4_93, chunk4_123, chunk4_124, chunk4_166]
private theorem checked5_193 : ∀ w ∈ chunk5_193, ¬ Need 5 w.toFinset := by
  have h : chunk5_193.all (routes 4 pool5_193.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_193,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_30 _ hm
  · exact checked4_35 _ hm
  · exact checked4_36 _ hm
  · exact checked4_37 _ hm
  · exact checked4_41 _ hm
  · exact checked4_42 _ hm
  · exact checked4_52 _ hm
  · exact checked4_92 _ hm
  · exact checked4_93 _ hm
  · exact checked4_123 _ hm
  · exact checked4_124 _ hm
  · exact checked4_166 _ hm
private def chunk5_194 : List (List T) := [[wire15,wire240,wire21845,wire52428,wire61440],
  [wire15,wire240,wire26214,wire34952,wire43690],
  [wire15,wire240,wire26214,wire34952,wire48059],
  [wire15,wire240,wire26214,wire34952,wire52428]]
private def pool5_194 : List (List (List T)) := [chunk4_9, chunk4_38, chunk4_93, chunk4_94]
private theorem checked5_194 : ∀ w ∈ chunk5_194, ¬ Need 5 w.toFinset := by
  have h : chunk5_194.all (routes 4 pool5_194.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_194,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_38 _ hm
  · exact checked4_93 _ hm
  · exact checked4_94 _ hm
private def chunk5_195 : List (List T) := [[wire15,wire240,wire26214,wire34952,wire56797],
  [wire15,wire240,wire26214,wire34952,wire61986],
  [wire15,wire240,wire26214,wire34952,wire62532],
  [wire15,wire240,wire26214,wire43690]]
private def pool5_195 : List (List (List T)) := [chunk4_35, chunk4_38, chunk4_39, chunk4_41, chunk4_53, chunk4_94, chunk4_95, chunk4_124, chunk4_167]
private theorem checked5_195 : ∀ w ∈ chunk5_195, ¬ Need 5 w.toFinset := by
  have h : chunk5_195.all (routes 4 pool5_195.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_195,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_38 _ hm
  · exact checked4_39 _ hm
  · exact checked4_41 _ hm
  · exact checked4_53 _ hm
  · exact checked4_94 _ hm
  · exact checked4_95 _ hm
  · exact checked4_124 _ hm
  · exact checked4_167 _ hm
private def chunk5_196 : List (List T) := [[wire15,wire240,wire26214,wire43690,wire61440],
  [wire15,wire240,wire26214,wire52428],
  [wire15,wire240,wire26214,wire52428,wire61440],
  [wire15,wire240,wire34952,wire39321,wire43690]]
private def pool5_196 : List (List (List T)) := [chunk4_31, chunk4_38, chunk4_41, chunk4_53, chunk4_96, chunk4_124, chunk4_168]
private theorem checked5_196 : ∀ w ∈ chunk5_196, ¬ Need 5 w.toFinset := by
  have h : chunk5_196.all (routes 4 pool5_196.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_196,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_31 _ hm
  · exact checked4_38 _ hm
  · exact checked4_41 _ hm
  · exact checked4_53 _ hm
  · exact checked4_96 _ hm
  · exact checked4_124 _ hm
  · exact checked4_168 _ hm
private def chunk5_197 : List (List T) := [[wire15,wire240,wire34952,wire39321,wire48059],
  [wire15,wire240,wire34952,wire39321,wire52428],
  [wire15,wire240,wire34952,wire39321,wire56797],
  [wire15,wire240,wire34952,wire39321,wire61986]]
private def pool5_197 : List (List (List T)) := [chunk4_9, chunk4_41, chunk4_96, chunk4_97]
private theorem checked5_197 : ∀ w ∈ chunk5_197, ¬ Need 5 w.toFinset := by
  have h : chunk5_197.all (routes 4 pool5_197.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_197,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_41 _ hm
  · exact checked4_96 _ hm
  · exact checked4_97 _ hm
private def chunk5_198 : List (List T) := [[wire15,wire240,wire34952,wire39321,wire62532],
  [wire15,wire240,wire34952,wire43690,wire48059],
  [wire15,wire240,wire34952,wire43690,wire52428],
  [wire15,wire240,wire34952,wire43690,wire61166]]
private def pool5_198 : List (List (List T)) := [chunk4_42, chunk4_98]
private theorem checked5_198 : ∀ w ∈ chunk5_198, ¬ Need 5 w.toFinset := by
  have h : chunk5_198.all (routes 4 pool5_198.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_198,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_42 _ hm
  · exact checked4_98 _ hm
private def chunk5_199 : List (List T) := [[wire15,wire240,wire34952,wire48059,wire56797],
  [wire15,wire240,wire34952,wire48059,wire61166],
  [wire15,wire240,wire34952,wire52428,wire56797],
  [wire15,wire240,wire34952,wire52428,wire61166]]
private def pool5_199 : List (List (List T)) := [chunk4_9, chunk4_98]
private theorem checked5_199 : ∀ w ∈ chunk5_199, ¬ Need 5 w.toFinset := by
  have h : chunk5_199.all (routes 4 pool5_199.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_199,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_9 _ hm
  · exact checked4_98 _ hm
private def chunk5_200 : List (List T) := [[wire15,wire240,wire34952,wire56797,wire61166],
  [wire15,wire240,wire34952,wire61166,wire61986],
  [wire15,wire240,wire34952,wire61166,wire62532],
  [wire15,wire240,wire39321,wire43690]]
private def pool5_200 : List (List (List T)) := [chunk4_35, chunk4_38, chunk4_41, chunk4_42, chunk4_53, chunk4_99, chunk4_124, chunk4_170]
private theorem checked5_200 : ∀ w ∈ chunk5_200, ¬ Need 5 w.toFinset := by
  have h : chunk5_200.all (routes 4 pool5_200.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_200,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_35 _ hm
  · exact checked4_38 _ hm
  · exact checked4_41 _ hm
  · exact checked4_42 _ hm
  · exact checked4_53 _ hm
  · exact checked4_99 _ hm
  · exact checked4_124 _ hm
  · exact checked4_170 _ hm
private def chunk5_201 : List (List T) := [[wire15,wire240,wire39321,wire43690,wire61440],
  [wire15,wire240,wire39321,wire52428],
  [wire15,wire240,wire39321,wire52428,wire61440],
  [wire15,wire240,wire43690,wire52428]]
private def pool5_201 : List (List (List T)) := [chunk4_31, chunk4_36, chunk4_38, chunk4_41, chunk4_42, chunk4_53, chunk4_54, chunk4_99, chunk4_100, chunk4_125, chunk4_170, chunk4_171]
private theorem checked5_201 : ∀ w ∈ chunk5_201, ¬ Need 5 w.toFinset := by
  have h : chunk5_201.all (routes 4 pool5_201.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_201,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_31 _ hm
  · exact checked4_36 _ hm
  · exact checked4_38 _ hm
  · exact checked4_41 _ hm
  · exact checked4_42 _ hm
  · exact checked4_53 _ hm
  · exact checked4_54 _ hm
  · exact checked4_99 _ hm
  · exact checked4_100 _ hm
  · exact checked4_125 _ hm
  · exact checked4_170 _ hm
  · exact checked4_171 _ hm
private def chunk5_202 : List (List T) := [[wire15,wire240,wire43690,wire52428,wire61440],
  [wire15,wire241,wire4369,wire8738,wire17476],
  [wire15,wire241,wire4369,wire8738,wire34952],
  [wire15,wire241,wire4369,wire17476,wire34952]]
private def pool5_202 : List (List (List T)) := [chunk4_171]
private theorem checked5_202 : ∀ w ∈ chunk5_202, ¬ Need 5 w.toFinset := by
  have h : chunk5_202.all (routes 4 pool5_202.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_202,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_171 _ hm
private def chunk5_203 : List (List T) := [[wire15,wire241,wire8738,wire17476,wire34952],
  [wire15,wire242,wire3840,wire4369,wire34952],
  [wire15,wire242,wire4369,wire8738,wire17476],
  [wire15,wire242,wire4369,wire8738,wire34952]]
private def pool5_203 : List (List (List T)) := [chunk4_42, chunk4_43, chunk4_172]
private theorem checked5_203 : ∀ w ∈ chunk5_203, ¬ Need 5 w.toFinset := by
  have h : chunk5_203.all (routes 4 pool5_203.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_203,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_42 _ hm
  · exact checked4_43 _ hm
  · exact checked4_172 _ hm
private def chunk5_204 : List (List T) := [[wire15,wire242,wire4369,wire17476,wire34952],
  [wire15,wire242,wire4369,wire34952],
  [wire15,wire242,wire4369,wire34952,wire61440],
  [wire15,wire242,wire8738,wire17476,wire34952]]
private def pool5_204 : List (List (List T)) := [chunk4_43, chunk4_44, chunk4_45, chunk4_60, chunk4_61, chunk4_75, chunk4_172, chunk4_173]
private theorem checked5_204 : ∀ w ∈ chunk5_204, ¬ Need 5 w.toFinset := by
  have h : chunk5_204.all (routes 4 pool5_204.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_204,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_43 _ hm
  · exact checked4_44 _ hm
  · exact checked4_45 _ hm
  · exact checked4_60 _ hm
  · exact checked4_61 _ hm
  · exact checked4_75 _ hm
  · exact checked4_172 _ hm
  · exact checked4_173 _ hm
private def chunk5_205 : List (List T) := [[wire15,wire244,wire3840,wire4369,wire34952],
  [wire15,wire244,wire4369,wire8738,wire17476],
  [wire15,wire244,wire4369,wire8738,wire34952],
  [wire15,wire244,wire4369,wire17476,wire34952]]
private def pool5_205 : List (List (List T)) := [chunk4_46, chunk4_47]
private theorem checked5_205 : ∀ w ∈ chunk5_205, ¬ Need 5 w.toFinset := by
  have h : chunk5_205.all (routes 4 pool5_205.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_205,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_46 _ hm
  · exact checked4_47 _ hm
private def chunk5_206 : List (List T) := [[wire15,wire244,wire4369,wire34952],
  [wire15,wire244,wire4369,wire34952,wire61440],
  [wire15,wire244,wire8738,wire17476,wire34952],
  [wire15,wire248,wire4369,wire8738,wire17476]]
private def pool5_206 : List (List (List T)) := [chunk4_17, chunk4_46, chunk4_47, chunk4_48, chunk4_60, chunk4_61, chunk4_75, chunk4_173, chunk4_174]
private theorem checked5_206 : ∀ w ∈ chunk5_206, ¬ Need 5 w.toFinset := by
  have h : chunk5_206.all (routes 4 pool5_206.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_206,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_17 _ hm
  · exact checked4_46 _ hm
  · exact checked4_47 _ hm
  · exact checked4_48 _ hm
  · exact checked4_60 _ hm
  · exact checked4_61 _ hm
  · exact checked4_75 _ hm
  · exact checked4_173 _ hm
  · exact checked4_174 _ hm
private def chunk5_207 : List (List T) := [[wire15,wire248,wire4369,wire8738,wire34952],
  [wire15,wire248,wire4369,wire17476,wire34952],
  [wire15,wire248,wire8738,wire17476,wire34952],
  [wire15,wire255,wire4369,wire8738,wire17476]]
private def pool5_207 : List (List (List T)) := [chunk4_75, chunk4_174]
private theorem checked5_207 : ∀ w ∈ chunk5_207, ¬ Need 5 w.toFinset := by
  have h : chunk5_207.all (routes 4 pool5_207.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_207,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_174 _ hm
private def chunk5_208 : List (List T) := [[wire15,wire255,wire4369,wire8738,wire20292],
  [wire15,wire255,wire4369,wire8738,wire21845],
  [wire15,wire255,wire4369,wire8738,wire26214],
  [wire15,wire255,wire4369,wire8738,wire30583]]
private def pool5_208 : List (List (List T)) := [chunk4_16, chunk4_51, chunk4_174, chunk4_175, chunk4_180]
private theorem checked5_208 : ∀ w ∈ chunk5_208, ¬ Need 5 w.toFinset := by
  have h : chunk5_208.all (routes 4 pool5_208.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_208,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_16 _ hm
  · exact checked4_51 _ hm
  · exact checked4_174 _ hm
  · exact checked4_175 _ hm
  · exact checked4_180 _ hm
private def chunk5_209 : List (List T) := [[wire15,wire255,wire4369,wire8738,wire34952],
  [wire15,wire255,wire4369,wire8738,wire36744],
  [wire15,wire255,wire4369,wire8738,wire39321],
  [wire15,wire255,wire4369,wire8738,wire43690]]
private def pool5_209 : List (List (List T)) := [chunk4_51, chunk4_52, chunk4_175, chunk4_180, chunk4_181]
private theorem checked5_209 : ∀ w ∈ chunk5_209, ¬ Need 5 w.toFinset := by
  have h : chunk5_209.all (routes 4 pool5_209.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_209,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_51 _ hm
  · exact checked4_52 _ hm
  · exact checked4_175 _ hm
  · exact checked4_180 _ hm
  · exact checked4_181 _ hm
private def chunk5_210 : List (List T) := [[wire15,wire255,wire4369,wire8738,wire48059],
  [wire15,wire255,wire4369,wire8738,wire62532],
  [wire15,wire255,wire4369,wire8738,wire63624],
  [wire15,wire255,wire4369,wire8751,wire17476]]
private def pool5_210 : List (List (List T)) := [chunk4_174, chunk4_175, chunk4_181]
private theorem checked5_210 : ∀ w ∈ chunk5_210, ¬ Need 5 w.toFinset := by
  have h : chunk5_210.all (routes 4 pool5_210.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_210,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_174 _ hm
  · exact checked4_175 _ hm
  · exact checked4_181 _ hm
private def chunk5_211 : List (List T) := [[wire15,wire255,wire4369,wire8946,wire34952],
  [wire15,wire255,wire4369,wire12066,wire17476],
  [wire15,wire255,wire4369,wire12066,wire34952],
  [wire15,wire255,wire4369,wire13107,wire17476]]
private def pool5_211 : List (List (List T)) := [chunk4_43, chunk4_51, chunk4_176, chunk4_177, chunk4_178, chunk4_181]
private theorem checked5_211 : ∀ w ∈ chunk5_211, ¬ Need 5 w.toFinset := by
  have h : chunk5_211.all (routes 4 pool5_211.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_211,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_43 _ hm
  · exact checked4_51 _ hm
  · exact checked4_176 _ hm
  · exact checked4_177 _ hm
  · exact checked4_178 _ hm
  · exact checked4_181 _ hm
private def chunk5_212 : List (List T) := [[wire15,wire255,wire4369,wire13107,wire34952],
  [wire15,wire255,wire4369,wire17476,wire26214],
  [wire15,wire255,wire4369,wire17476,wire30583],
  [wire15,wire255,wire4369,wire17476,wire34952]]
private def pool5_212 : List (List (List T)) := [chunk4_17, chunk4_51, chunk4_52]
private theorem checked5_212 : ∀ w ∈ chunk5_212, ¬ Need 5 w.toFinset := by
  have h : chunk5_212.all (routes 4 pool5_212.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_212,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_17 _ hm
  · exact checked4_51 _ hm
  · exact checked4_52 _ hm
private def chunk5_213 : List (List T) := [[wire15,wire255,wire4369,wire17476,wire34959],
  [wire15,wire255,wire4369,wire17476,wire36744],
  [wire15,wire255,wire4369,wire17476,wire39321],
  [wire15,wire255,wire4369,wire17476,wire52428]]
private def pool5_213 : List (List (List T)) := [chunk4_52]
private theorem checked5_213 : ∀ w ∈ chunk5_213, ¬ Need 5 w.toFinset := by
  have h : chunk5_213.all (routes 4 pool5_213.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_213,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_52 _ hm
private def chunk5_214 : List (List T) := [[wire15,wire255,wire4369,wire17476,wire56797],
  [wire15,wire255,wire4369,wire17476,wire61986],
  [wire15,wire255,wire4369,wire17476,wire63624],
  [wire15,wire255,wire4369,wire17652,wire34952]]
private def pool5_214 : List (List (List T)) := [chunk4_46, chunk4_178, chunk4_179]
private theorem checked5_214 : ∀ w ∈ chunk5_214, ¬ Need 5 w.toFinset := by
  have h : chunk5_214.all (routes 4 pool5_214.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_214,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_46 _ hm
  · exact checked4_178 _ hm
  · exact checked4_179 _ hm
private def chunk5_215 : List (List T) := [[wire15,wire255,wire4369,wire20292,wire34952],
  [wire15,wire255,wire4369,wire21845,wire34952],
  [wire15,wire255,wire4369,wire34952,wire43690],
  [wire15,wire255,wire4369,wire34952,wire48059]]
private def pool5_215 : List (List (List T)) := [chunk4_52, chunk4_53, chunk4_182]
private theorem checked5_215 : ∀ w ∈ chunk5_215, ¬ Need 5 w.toFinset := by
  have h : chunk5_215.all (routes 4 pool5_215.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_215,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_52 _ hm
  · exact checked4_53 _ hm
  · exact checked4_182 _ hm
private def chunk5_216 : List (List T) := [[wire15,wire255,wire4369,wire34952,wire52428],
  [wire15,wire255,wire4369,wire34952,wire56797],
  [wire15,wire255,wire4369,wire34952,wire61986],
  [wire15,wire255,wire4369,wire34952,wire62532]]
private def pool5_216 : List (List (List T)) := [chunk4_11, chunk4_12, chunk4_53, chunk4_182]
private theorem checked5_216 : ∀ w ∈ chunk5_216, ¬ Need 5 w.toFinset := by
  have h : chunk5_216.all (routes 4 pool5_216.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_216,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_53 _ hm
  · exact checked4_182 _ hm
private def chunk5_217 : List (List T) := [[wire15,wire255,wire4383,wire8738,wire34952],
  [wire15,wire255,wire4593,wire8738,wire17476],
  [wire15,wire255,wire8738,wire13107,wire17476],
  [wire15,wire255,wire8738,wire13107,wire34952]]
private def pool5_217 : List (List (List T)) := [chunk4_1, chunk4_51, chunk4_52, chunk4_180, chunk4_183, chunk4_185]
private theorem checked5_217 : ∀ w ∈ chunk5_217, ¬ Need 5 w.toFinset := by
  have h : chunk5_217.all (routes 4 pool5_217.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_217,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_51 _ hm
  · exact checked4_52 _ hm
  · exact checked4_180 _ hm
  · exact checked4_183 _ hm
  · exact checked4_185 _ hm
private def chunk5_218 : List (List T) := [[wire15,wire255,wire8738,wire17476,wire21845],
  [wire15,wire255,wire8738,wire17476,wire30583],
  [wire15,wire255,wire8738,wire17476,wire34952],
  [wire15,wire255,wire8738,wire17476,wire35064]]
private def pool5_218 : List (List (List T)) := [chunk4_52, chunk4_75, chunk4_186, chunk4_187]
private theorem checked5_218 : ∀ w ∈ chunk5_218, ¬ Need 5 w.toFinset := by
  have h : chunk5_218.all (routes 4 pool5_218.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_218,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_52 _ hm
  · exact checked4_75 _ hm
  · exact checked4_186 _ hm
  · exact checked4_187 _ hm
private def chunk5_219 : List (List T) := [[wire15,wire255,wire8738,wire17476,wire43690],
  [wire15,wire255,wire8738,wire17476,wire52428],
  [wire15,wire255,wire8738,wire17476,wire61166],
  [wire15,wire255,wire8738,wire17487,wire34952]]
private def pool5_219 : List (List (List T)) := [chunk4_53, chunk4_187]
private theorem checked5_219 : ∀ w ∈ chunk5_219, ¬ Need 5 w.toFinset := by
  have h : chunk5_219.all (routes 4 pool5_219.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_219,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_53 _ hm
  · exact checked4_187 _ hm
private def chunk5_220 : List (List T) := [[wire15,wire255,wire8738,wire26214,wire34952],
  [wire15,wire255,wire8738,wire34952,wire39321],
  [wire15,wire255,wire8738,wire34952,wire48059],
  [wire15,wire255,wire8738,wire34952,wire52428]]
private def pool5_220 : List (List (List T)) := [chunk4_53, chunk4_54]
private theorem checked5_220 : ∀ w ∈ chunk5_220, ¬ Need 5 w.toFinset := by
  have h : chunk5_220.all (routes 4 pool5_220.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_220,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_53 _ hm
  · exact checked4_54 _ hm
private def chunk5_221 : List (List T) := [[wire15,wire255,wire8738,wire34952,wire61166],
  [wire15,wire255,wire17476,wire21845,wire34952],
  [wire15,wire255,wire17476,wire26214,wire34952],
  [wire15,wire255,wire17476,wire34952,wire39321]]
private def pool5_221 : List (List (List T)) := [chunk4_52, chunk4_53]
private theorem checked5_221 : ∀ w ∈ chunk5_221, ¬ Need 5 w.toFinset := by
  have h : chunk5_221.all (routes 4 pool5_221.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_221,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_52 _ hm
  · exact checked4_53 _ hm
private def chunk5_222 : List (List T) := [[wire15,wire255,wire17476,wire34952,wire43690],
  [wire15,wire255,wire17476,wire34952,wire56797],
  [wire15,wire255,wire17476,wire34952,wire61166],
  [wire15,wire256,wire8738,wire17476,wire35064]]
private def pool5_222 : List (List (List T)) := [chunk4_54, chunk4_188]
private theorem checked5_222 : ∀ w ∈ chunk5_222, ¬ Need 5 w.toFinset := by
  have h : chunk5_222.all (routes 4 pool5_222.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_222,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_54 _ hm
  · exact checked4_188 _ hm
private def chunk5_223 : List (List T) := [[wire15,wire512,wire8738,wire17476,wire35064],
  [wire15,wire1024,wire8738,wire17476,wire35064],
  [wire15,wire1911,wire3840,wire4369,wire8738],
  [wire15,wire1911,wire3840,wire4369,wire17476]]
private def pool5_223 : List (List (List T)) := [chunk4_75, chunk4_77, chunk4_82, chunk4_188, chunk4_189]
private theorem checked5_223 : ∀ w ∈ chunk5_223, ¬ Need 5 w.toFinset := by
  have h : chunk5_223.all (routes 4 pool5_223.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_223,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_77 _ hm
  · exact checked4_82 _ hm
  · exact checked4_188 _ hm
  · exact checked4_189 _ hm
private def chunk5_224 : List (List T) := [[wire15,wire2048,wire8738,wire17476,wire35064],
  [wire15,wire2288,wire4369,wire8738,wire17476],
  [wire15,wire2288,wire4369,wire8738,wire34952],
  [wire15,wire2288,wire4369,wire17476,wire34952]]
private def pool5_224 : List (List (List T)) := [chunk4_75, chunk4_189]
private theorem checked5_224 : ∀ w ∈ chunk5_224, ¬ Need 5 w.toFinset := by
  have h : chunk5_224.all (routes 4 pool5_224.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_224,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_189 _ hm
private def chunk5_225 : List (List T) := [[wire15,wire2288,wire8738,wire17476,wire34952],
  [wire15,wire3840,wire4369,wire8738,wire63624],
  [wire15,wire3840,wire4369,wire8738,wire65416],
  [wire15,wire3840,wire4369,wire8946,wire63624]]
private def pool5_225 : List (List (List T)) := [chunk4_55, chunk4_56, chunk4_75, chunk4_190, chunk4_191, chunk4_192]
private theorem checked5_225 : ∀ w ∈ chunk5_225, ¬ Need 5 w.toFinset := by
  have h : chunk5_225.all (routes 4 pool5_225.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_225,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_56 _ hm
  · exact checked4_75 _ hm
  · exact checked4_190 _ hm
  · exact checked4_191 _ hm
  · exact checked4_192 _ hm
private def chunk5_226 : List (List T) := [[wire15,wire3840,wire4369,wire12066,wire63624],
  [wire15,wire3840,wire4369,wire13107,wire63624],
  [wire15,wire3840,wire4369,wire17476,wire61568],
  [wire15,wire3840,wire4369,wire17476,wire63624]]
private def pool5_226 : List (List (List T)) := [chunk4_5, chunk4_56, chunk4_57, chunk4_192]
private theorem checked5_226 : ∀ w ∈ chunk5_226, ¬ Need 5 w.toFinset := by
  have h : chunk5_226.all (routes 4 pool5_226.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_226,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_56 _ hm
  · exact checked4_57 _ hm
  · exact checked4_192 _ hm
private def chunk5_227 : List (List T) := [[wire15,wire3840,wire4369,wire17476,wire63631],
  [wire15,wire3840,wire4369,wire17476,wire65416],
  [wire15,wire3840,wire4369,wire17476,wire65423],
  [wire15,wire3840,wire4369,wire17508,wire61440]]
private def pool5_227 : List (List (List T)) := [chunk4_57, chunk4_58, chunk4_59]
private theorem checked5_227 : ∀ w ∈ chunk5_227, ¬ Need 5 w.toFinset := by
  have h : chunk5_227.all (routes 4 pool5_227.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_227,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_58 _ hm
  · exact checked4_59 _ hm
private def chunk5_228 : List (List T) := [[wire15,wire3840,wire4369,wire17652,wire63624],
  [wire15,wire3840,wire4369,wire20292,wire63624],
  [wire15,wire3840,wire4369,wire21845,wire63624],
  [wire15,wire3840,wire4369,wire34952,wire61442]]
private def pool5_228 : List (List (List T)) := [chunk4_54, chunk4_59, chunk4_60, chunk4_61, chunk4_63, chunk4_192, chunk4_200]
private theorem checked5_228 : ∀ w ∈ chunk5_228, ¬ Need 5 w.toFinset := by
  have h : chunk5_228.all (routes 4 pool5_228.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_228,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_54 _ hm
  · exact checked4_59 _ hm
  · exact checked4_60 _ hm
  · exact checked4_61 _ hm
  · exact checked4_63 _ hm
  · exact checked4_192 _ hm
  · exact checked4_200 _ hm
private def chunk5_229 : List (List T) := [[wire15,wire3840,wire4369,wire34952,wire61444],
  [wire15,wire3840,wire4369,wire34954,wire61440],
  [wire15,wire3840,wire4369,wire43690,wire63624],
  [wire15,wire3840,wire4369,wire48059,wire63624]]
private def pool5_229 : List (List (List T)) := [chunk4_54, chunk4_61, chunk4_62, chunk4_63, chunk4_64, chunk4_65, chunk4_193]
private theorem checked5_229 : ∀ w ∈ chunk5_229, ¬ Need 5 w.toFinset := by
  have h : chunk5_229.all (routes 4 pool5_229.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_229,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_54 _ hm
  · exact checked4_61 _ hm
  · exact checked4_62 _ hm
  · exact checked4_63 _ hm
  · exact checked4_64 _ hm
  · exact checked4_65 _ hm
  · exact checked4_193 _ hm
private def chunk5_230 : List (List T) := [[wire15,wire3840,wire4369,wire52428,wire63624],
  [wire15,wire3840,wire4369,wire56797,wire63624],
  [wire15,wire3840,wire4369,wire61986,wire62532],
  [wire15,wire3840,wire4369,wire61986,wire63624]]
private def pool5_230 : List (List (List T)) := [chunk4_11, chunk4_12, chunk4_65, chunk4_66, chunk4_190, chunk4_193]
private theorem checked5_230 : ∀ w ∈ chunk5_230, ¬ Need 5 w.toFinset := by
  have h : chunk5_230.all (routes 4 pool5_230.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_230,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_12 _ hm
  · exact checked4_65 _ hm
  · exact checked4_66 _ hm
  · exact checked4_190 _ hm
  · exact checked4_193 _ hm
private def chunk5_231 : List (List T) := [[wire15,wire3840,wire4369,wire62532,wire63624],
  [wire15,wire3840,wire4369,wire63624,wire64170],
  [wire15,wire3840,wire4369,wire63624,wire64716],
  [wire15,wire3840,wire4373,wire34952,wire61440]]
private def pool5_231 : List (List (List T)) := [chunk4_11, chunk4_54, chunk4_66, chunk4_67, chunk4_69, chunk4_194]
private theorem checked5_231 : ∀ w ∈ chunk5_231, ¬ Need 5 w.toFinset := by
  have h : chunk5_231.all (routes 4 pool5_231.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_231,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_54 _ hm
  · exact checked4_66 _ hm
  · exact checked4_67 _ hm
  · exact checked4_69 _ hm
  · exact checked4_194 _ hm
private def chunk5_232 : List (List T) := [[wire15,wire3840,wire4383,wire8738,wire63624],
  [wire15,wire3840,wire4497,wire17476,wire61440],
  [wire15,wire3840,wire4593,wire8738,wire34952,wire62532],
  [wire15,wire3840,wire4593,wire8738,wire62532]]
private def pool5_232 : List (List (List T)) := [chunk4_1, chunk4_5, chunk4_69, chunk4_70, chunk4_71, chunk4_72, chunk4_191]
private theorem checked5_232 : ∀ w ∈ chunk5_232, ¬ Need 5 w.toFinset := by
  have h : chunk5_232.all (routes 4 pool5_232.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_232,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_5 _ hm
  · exact checked4_69 _ hm
  · exact checked4_70 _ hm
  · exact checked4_71 _ hm
  · exact checked4_72 _ hm
  · exact checked4_191 _ hm
private def chunk5_233 : List (List T) := [[wire15,wire3840,wire4593,wire17476,wire34952,wire61986],
  [wire15,wire3840,wire4593,wire17476,wire61986],
  [wire15,wire3840,wire8738,wire13107,wire63624],
  [wire15,wire3840,wire8738,wire17476,wire30471]]
private def pool5_233 : List (List (List T)) := [chunk4_72, chunk4_73, chunk4_74, chunk4_197]
private theorem checked5_233 : ∀ w ∈ chunk5_233, ¬ Need 5 w.toFinset := by
  have h : chunk5_233.all (routes 4 pool5_233.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_233,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_72 _ hm
  · exact checked4_73 _ hm
  · exact checked4_74 _ hm
  · exact checked4_197 _ hm
private def chunk5_234 : List (List T) := [[wire15,wire3840,wire8738,wire17476,wire35064],
  [wire15,wire3840,wire8738,wire17487,wire35064],
  [wire15,wire3840,wire8738,wire26214,wire35064],
  [wire15,wire3840,wire8738,wire35064,wire39321]]
private def pool5_234 : List (List (List T)) := [chunk4_0, chunk4_82, chunk4_83, chunk4_197, chunk4_201]
private theorem checked5_234 : ∀ w ∈ chunk5_234, ¬ Need 5 w.toFinset := by
  have h : chunk5_234.all (routes 4 pool5_234.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_234,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_82 _ hm
  · exact checked4_83 _ hm
  · exact checked4_197 _ hm
  · exact checked4_201 _ hm
private def chunk5_235 : List (List T) := [[wire15,wire3840,wire8738,wire35064,wire48059],
  [wire15,wire3840,wire8738,wire52428,wire63624],
  [wire15,wire3840,wire8738,wire61166,wire63624],
  [wire15,wire3840,wire13107,wire21845,wire61440]]
private def pool5_235 : List (List (List T)) := [chunk4_80, chunk4_83, chunk4_198]
private theorem checked5_235 : ∀ w ∈ chunk5_235, ¬ Need 5 w.toFinset := by
  have h : chunk5_235.all (routes 4 pool5_235.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_235,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_80 _ hm
  · exact checked4_83 _ hm
  · exact checked4_198 _ hm
private def chunk5_236 : List (List T) := [[wire15,wire3840,wire13107,wire26214,wire61440],
  [wire15,wire3840,wire13107,wire39321,wire61440],
  [wire15,wire3840,wire13107,wire43690,wire61440],
  [wire15,wire3840,wire17476,wire21845,wire63624]]
private def pool5_236 : List (List (List T)) := [chunk4_84, chunk4_85, chunk4_86, chunk4_199]
private theorem checked5_236 : ∀ w ∈ chunk5_236, ¬ Need 5 w.toFinset := by
  have h : chunk5_236.all (routes 4 pool5_236.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_236,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_84 _ hm
  · exact checked4_85 _ hm
  · exact checked4_86 _ hm
  · exact checked4_199 _ hm
private def chunk5_237 : List (List T) := [[wire15,wire3840,wire17476,wire26214,wire35064],
  [wire15,wire3840,wire17476,wire35064,wire39321],
  [wire15,wire3840,wire17476,wire35064,wire56797],
  [wire15,wire3840,wire17476,wire43690,wire63624]]
private def pool5_237 : List (List (List T)) := [chunk4_88, chunk4_90, chunk4_200]
private theorem checked5_237 : ∀ w ∈ chunk5_237, ¬ Need 5 w.toFinset := by
  have h : chunk5_237.all (routes 4 pool5_237.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_237,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_88 _ hm
  · exact checked4_90 _ hm
  · exact checked4_200 _ hm
private def chunk5_238 : List (List T) := [[wire15,wire3840,wire17476,wire61166,wire63624],
  [wire15,wire3840,wire21845,wire26214,wire61440],
  [wire15,wire3840,wire21845,wire39321,wire61440],
  [wire15,wire3840,wire21845,wire52428,wire61440]]
private def pool5_238 : List (List (List T)) := [chunk4_89, chunk4_91, chunk4_92]
private theorem checked5_238 : ∀ w ∈ chunk5_238, ¬ Need 5 w.toFinset := by
  have h : chunk5_238.all (routes 4 pool5_238.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_238,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_89 _ hm
  · exact checked4_91 _ hm
  · exact checked4_92 _ hm
private def chunk5_239 : List (List T) := [[wire15,wire3840,wire26214,wire43690,wire61440],
  [wire15,wire3840,wire26214,wire52428,wire61440],
  [wire15,wire3840,wire39321,wire43690,wire61440],
  [wire15,wire3840,wire39321,wire52428,wire61440]]
private def pool5_239 : List (List (List T)) := [chunk4_95, chunk4_98, chunk4_99]
private theorem checked5_239 : ∀ w ∈ chunk5_239, ¬ Need 5 w.toFinset := by
  have h : chunk5_239.all (routes 4 pool5_239.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_239,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_95 _ hm
  · exact checked4_98 _ hm
  · exact checked4_99 _ hm
private def chunk5_240 : List (List T) := [[wire15,wire3840,wire43690,wire52428,wire61440],
  [wire15,wire3842,wire4369,wire34952,wire61440],
  [wire15,wire3844,wire4369,wire34952,wire61440],
  [wire15,wire3855,wire4369,wire8738,wire63624]]
private def pool5_240 : List (List (List T)) := [chunk4_54, chunk4_55, chunk4_61, chunk4_63, chunk4_99, chunk4_200]
private theorem checked5_240 : ∀ w ∈ chunk5_240, ¬ Need 5 w.toFinset := by
  have h : chunk5_240.all (routes 4 pool5_240.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_240,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_54 _ hm
  · exact checked4_55 _ hm
  · exact checked4_61 _ hm
  · exact checked4_63 _ hm
  · exact checked4_99 _ hm
  · exact checked4_200 _ hm
private def chunk5_241 : List (List T) := [[wire15,wire3855,wire4369,wire17476,wire63624],
  [wire15,wire3855,wire8738,wire17476,wire35064],
  [wire15,wire3968,wire4369,wire17476,wire61440],
  [wire15,wire4080,wire4369,wire8738,wire36744]]
private def pool5_241 : List (List (List T)) := [chunk4_5, chunk4_57, chunk4_58, chunk4_75, chunk4_201]
private theorem checked5_241 : ∀ w ∈ chunk5_241, ¬ Need 5 w.toFinset := by
  have h : chunk5_241.all (routes 4 pool5_241.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_241,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_57 _ hm
  · exact checked4_58 _ hm
  · exact checked4_75 _ hm
  · exact checked4_201 _ hm
private def chunk5_242 : List (List T) := [[wire15,wire4080,wire4369,wire17476,wire36744],
  [wire15,wire4080,wire8738,wire17476,wire35064],
  [wire15,wire4095,wire4369,wire8738,wire36744],
  [wire15,wire4095,wire4369,wire17476,wire36744]]
private def pool5_242 : List (List (List T)) := [chunk4_201, chunk4_202]
private theorem checked5_242 : ∀ w ∈ chunk5_242, ¬ Need 5 w.toFinset := by
  have h : chunk5_242.all (routes 4 pool5_242.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_242,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_201 _ hm
  · exact checked4_202 _ hm
private def chunk5_243 : List (List T) := [[wire15,wire4095,wire8738,wire17476,wire35064],
  [wire15,wire4096,wire8738,wire17476,wire35064],
  [wire15,wire4353,wire8738,wire17476,wire65295],
  [wire15,wire4369,wire4593,wire8946,wire34952]]
private def pool5_243 : List (List (List T)) := [chunk4_71, chunk4_75, chunk4_202]
private theorem checked5_243 : ∀ w ∈ chunk5_243, ¬ Need 5 w.toFinset := by
  have h : chunk5_243.all (routes 4 pool5_243.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_243,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_71 _ hm
  · exact checked4_75 _ hm
  · exact checked4_202 _ hm
private def chunk5_244 : List (List T) := [[wire15,wire4369,wire4593,wire17652,wire34952],
  [wire15,wire4369,wire8706,wire34952,wire65295],
  [wire15,wire4369,wire8738,wire17476,wire30471],
  [wire15,wire4369,wire8738,wire17476,wire33008]]
private def pool5_244 : List (List (List T)) := [chunk4_64, chunk4_73, chunk4_204]
private theorem checked5_244 : ∀ w ∈ chunk5_244, ¬ Need 5 w.toFinset := by
  have h : chunk5_244.all (routes 4 pool5_244.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_244,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_64 _ hm
  · exact checked4_73 _ hm
  · exact checked4_204 _ hm
private def chunk5_245 : List (List T) := [[wire15,wire4369,wire8738,wire17476,wire35064],
  [wire15,wire4369,wire8738,wire17476,wire35064,wire65280],
  [wire15,wire4369,wire8738,wire17476,wire35071],
  [wire15,wire4369,wire8738,wire17476,wire65280]]
private def pool5_245 : List (List (List T)) := [chunk4_55, chunk4_204, chunk4_205, chunk4_206]
private theorem checked5_245 : ∀ w ∈ chunk5_245, ¬ Need 5 w.toFinset := by
  have h : chunk5_245.all (routes 4 pool5_245.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_245,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_204 _ hm
  · exact checked4_205 _ hm
  · exact checked4_206 _ hm
private def chunk5_246 : List (List T) := [[wire15,wire4369,wire8738,wire17476,wire65295],
  [wire15,wire4369,wire8738,wire17476,wire65416],
  [wire15,wire4369,wire8738,wire17476,wire65423],
  [wire15,wire4369,wire8738,wire17487,wire35064]]
private def pool5_246 : List (List (List T)) := [chunk4_0, chunk4_204, chunk4_216]
private theorem checked5_246 : ∀ w ∈ chunk5_246, ¬ Need 5 w.toFinset := by
  have h : chunk5_246.all (routes 4 pool5_246.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_246,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_204 _ hm
  · exact checked4_216 _ hm
private def chunk5_247 : List (List T) := [[wire15,wire4369,wire8738,wire20292,wire65280],
  [wire15,wire4369,wire8738,wire20292,wire65295],
  [wire15,wire4369,wire8738,wire21845,wire35064],
  [wire15,wire4369,wire8738,wire21845,wire65280]]
private def pool5_247 : List (List (List T)) := [chunk4_83, chunk4_206, chunk4_217]
private theorem checked5_247 : ∀ w ∈ chunk5_247, ¬ Need 5 w.toFinset := by
  have h : chunk5_247.all (routes 4 pool5_247.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_247,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_83 _ hm
  · exact checked4_206 _ hm
  · exact checked4_217 _ hm
private def chunk5_248 : List (List T) := [[wire15,wire4369,wire8738,wire21845,wire65295],
  [wire15,wire4369,wire8738,wire26214,wire35064],
  [wire15,wire4369,wire8738,wire26214,wire65280],
  [wire15,wire4369,wire8738,wire26214,wire65295]]
private def pool5_248 : List (List (List T)) := [chunk4_83, chunk4_84]
private theorem checked5_248 : ∀ w ∈ chunk5_248, ¬ Need 5 w.toFinset := by
  have h : chunk5_248.all (routes 4 pool5_248.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_248,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_83 _ hm
  · exact checked4_84 _ hm
private def chunk5_249 : List (List T) := [[wire15,wire4369,wire8738,wire28791,wire61440],
  [wire15,wire4369,wire8738,wire30471,wire34952],
  [wire15,wire4369,wire8738,wire30583,wire35064],
  [wire15,wire4369,wire8738,wire30583,wire65280]]
private def pool5_249 : List (List (List T)) := [chunk4_78, chunk4_217]
private theorem checked5_249 : ∀ w ∈ chunk5_249, ¬ Need 5 w.toFinset := by
  have h : chunk5_249.all (routes 4 pool5_249.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_249,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_78 _ hm
  · exact checked4_217 _ hm
private def chunk5_250 : List (List T) := [[wire15,wire4369,wire8738,wire30583,wire65295],
  [wire15,wire4369,wire8738,wire33008,wire34952],
  [wire15,wire4369,wire8738,wire34952,wire35064],
  [wire15,wire4369,wire8738,wire34952,wire35071]]
private def pool5_250 : List (List (List T)) := [chunk4_79, chunk4_217]
private theorem checked5_250 : ∀ w ∈ chunk5_250, ¬ Need 5 w.toFinset := by
  have h : chunk5_250.all (routes 4 pool5_250.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_250,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_79 _ hm
  · exact checked4_217 _ hm
private def chunk5_251 : List (List T) := [[wire15,wire4369,wire8738,wire34952,wire65280],
  [wire15,wire4369,wire8738,wire34952,wire65295],
  [wire15,wire4369,wire8738,wire34952,wire65416],
  [wire15,wire4369,wire8738,wire34952,wire65423]]
private def pool5_251 : List (List (List T)) := [chunk4_55, chunk4_64, chunk4_218]
private theorem checked5_251 : ∀ w ∈ chunk5_251, ¬ Need 5 w.toFinset := by
  have h : chunk5_251.all (routes 4 pool5_251.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_251,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_64 _ hm
  · exact checked4_218 _ hm
private def chunk5_252 : List (List T) := [[wire15,wire4369,wire8738,wire34959,wire35064],
  [wire15,wire4369,wire8738,wire35064,wire36744],
  [wire15,wire4369,wire8738,wire35064,wire39321],
  [wire15,wire4369,wire8738,wire35064,wire43690]]
private def pool5_252 : List (List (List T)) := [chunk4_79, chunk4_84, chunk4_85, chunk4_218]
private theorem checked5_252 : ∀ w ∈ chunk5_252, ¬ Need 5 w.toFinset := by
  have h : chunk5_252.all (routes 4 pool5_252.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_252,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_79 _ hm
  · exact checked4_84 _ hm
  · exact checked4_85 _ hm
  · exact checked4_218 _ hm
private def chunk5_253 : List (List T) := [[wire15,wire4369,wire8738,wire35064,wire48059],
  [wire15,wire4369,wire8738,wire35064,wire63624],
  [wire15,wire4369,wire8738,wire36744,wire36856],
  [wire15,wire4369,wire8738,wire36744,wire61440]]
private def pool5_253 : List (List (List T)) := [chunk4_55, chunk4_79, chunk4_218]
private theorem checked5_253 : ∀ w ∈ chunk5_253, ¬ Need 5 w.toFinset := by
  have h : chunk5_253.all (routes 4 pool5_253.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_253,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_79 _ hm
  · exact checked4_218 _ hm
private def chunk5_254 : List (List T) := [[wire15,wire4369,wire8738,wire36744,wire61455],
  [wire15,wire4369,wire8738,wire36744,wire63624],
  [wire15,wire4369,wire8738,wire36744,wire65280],
  [wire15,wire4369,wire8738,wire36744,wire65295]]
private def pool5_254 : List (List (List T)) := [chunk4_55, chunk4_219]
private theorem checked5_254 : ∀ w ∈ chunk5_254, ¬ Need 5 w.toFinset := by
  have h : chunk5_254.all (routes 4 pool5_254.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_254,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_219 _ hm
private def chunk5_255 : List (List T) := [[wire15,wire4369,wire8738,wire36744,wire65416],
  [wire15,wire4369,wire8738,wire39321,wire65280],
  [wire15,wire4369,wire8738,wire39321,wire65295],
  [wire15,wire4369,wire8738,wire43690,wire65280]]
private def pool5_255 : List (List (List T)) := [chunk4_55, chunk4_64, chunk4_85, chunk4_207, chunk4_219]
private theorem checked5_255 : ∀ w ∈ chunk5_255, ¬ Need 5 w.toFinset := by
  have h : chunk5_255.all (routes 4 pool5_255.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_255,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_64 _ hm
  · exact checked4_85 _ hm
  · exact checked4_207 _ hm
  · exact checked4_219 _ hm
private def chunk5_256 : List (List T) := [[wire15,wire4369,wire8738,wire43690,wire65295],
  [wire15,wire4369,wire8738,wire48059,wire65280],
  [wire15,wire4369,wire8738,wire48059,wire65295],
  [wire15,wire4369,wire8738,wire61440,wire65416]]
private def pool5_256 : List (List (List T)) := [chunk4_55, chunk4_66, chunk4_86, chunk4_207, chunk4_220]
private theorem checked5_256 : ∀ w ∈ chunk5_256, ¬ Need 5 w.toFinset := by
  have h : chunk5_256.all (routes 4 pool5_256.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_256,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_66 _ hm
  · exact checked4_86 _ hm
  · exact checked4_207 _ hm
  · exact checked4_220 _ hm
private def chunk5_257 : List (List T) := [[wire15,wire4369,wire8738,wire61680,wire63624],
  [wire15,wire4369,wire8738,wire61695,wire63624],
  [wire15,wire4369,wire8738,wire62532,wire65280],
  [wire15,wire4369,wire8738,wire62532,wire65295]]
private def pool5_257 : List (List (List T)) := [chunk4_207, chunk4_220]
private theorem checked5_257 : ∀ w ∈ chunk5_257, ¬ Need 5 w.toFinset := by
  have h : chunk5_257.all (routes 4 pool5_257.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_257,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_207 _ hm
  · exact checked4_220 _ hm
private def chunk5_258 : List (List T) := [[wire15,wire4369,wire8738,wire63624,wire63736],
  [wire15,wire4369,wire8738,wire63624,wire65280],
  [wire15,wire4369,wire8738,wire63624,wire65295],
  [wire15,wire4369,wire8738,wire63624,wire65416]]
private def pool5_258 : List (List (List T)) := [chunk4_55, chunk4_67, chunk4_220]
private theorem checked5_258 : ∀ w ∈ chunk5_258, ¬ Need 5 w.toFinset := by
  have h : chunk5_258.all (routes 4 pool5_258.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_258,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_55 _ hm
  · exact checked4_67 _ hm
  · exact checked4_220 _ hm
private def chunk5_259 : List (List T) := [[wire15,wire4369,wire8738,wire65280,wire65348],
  [wire15,wire4369,wire8738,wire65280,wire65416],
  [wire15,wire4369,wire8738,wire65416],
  [wire15,wire4369,wire8751,wire17476,wire35064]]
private def pool5_259 : List (List (List T)) := [chunk4_0, chunk4_16, chunk4_55, chunk4_57, chunk4_66, chunk4_67, chunk4_68, chunk4_69, chunk4_74, chunk4_80, chunk4_203, chunk4_204, chunk4_205, chunk4_206, chunk4_207, chunk4_221]
private theorem checked5_259 : ∀ w ∈ chunk5_259, ¬ Need 5 w.toFinset := by
  have h : chunk5_259.all (routes 4 pool5_259.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_259,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_16 _ hm
  · exact checked4_55 _ hm
  · exact checked4_57 _ hm
  · exact checked4_66 _ hm
  · exact checked4_67 _ hm
  · exact checked4_68 _ hm
  · exact checked4_69 _ hm
  · exact checked4_74 _ hm
  · exact checked4_80 _ hm
  · exact checked4_203 _ hm
  · exact checked4_204 _ hm
  · exact checked4_205 _ hm
  · exact checked4_206 _ hm
  · exact checked4_207 _ hm
  · exact checked4_221 _ hm
private def chunk5_260 : List (List T) := [[wire15,wire4369,wire8751,wire17476,wire65280],
  [wire15,wire4369,wire8751,wire17476,wire65295],
  [wire15,wire4369,wire8946,wire17652,wire34952],
  [wire15,wire4369,wire8946,wire34952,wire35064]]
private def pool5_260 : List (List (List T)) := [chunk4_82, chunk4_206, chunk4_208]
private theorem checked5_260 : ∀ w ∈ chunk5_260, ¬ Need 5 w.toFinset := by
  have h : chunk5_260.all (routes 4 pool5_260.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_260,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_82 _ hm
  · exact checked4_206 _ hm
  · exact checked4_208 _ hm
private def chunk5_261 : List (List T) := [[wire15,wire4369,wire8946,wire34952,wire65280],
  [wire15,wire4369,wire8946,wire34952,wire65295],
  [wire15,wire4369,wire8946,wire36744,wire61440],
  [wire15,wire4369,wire12066,wire17476,wire65280]]
private def pool5_261 : List (List (List T)) := [chunk4_56, chunk4_210]
private theorem checked5_261 : ∀ w ∈ chunk5_261, ¬ Need 5 w.toFinset := by
  have h : chunk5_261.all (routes 4 pool5_261.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_261,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_56 _ hm
  · exact checked4_210 _ hm
private def chunk5_262 : List (List T) := [[wire15,wire4369,wire12066,wire17476,wire65295],
  [wire15,wire4369,wire12066,wire20292,wire61440],
  [wire15,wire4369,wire12066,wire34952,wire35064],
  [wire15,wire4369,wire12066,wire34952,wire65280]]
private def pool5_262 : List (List (List T)) := [chunk4_56, chunk4_83, chunk4_210, chunk4_221]
private theorem checked5_262 : ∀ w ∈ chunk5_262, ¬ Need 5 w.toFinset := by
  have h : chunk5_262.all (routes 4 pool5_262.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_262,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_56 _ hm
  · exact checked4_83 _ hm
  · exact checked4_210 _ hm
  · exact checked4_221 _ hm
private def chunk5_263 : List (List T) := [[wire15,wire4369,wire12066,wire34952,wire65295],
  [wire15,wire4369,wire12066,wire36744,wire61440],
  [wire15,wire4369,wire13107,wire17476,wire35064],
  [wire15,wire4369,wire13107,wire17476,wire65280]]
private def pool5_263 : List (List (List T)) := [chunk4_56, chunk4_83, chunk4_211, chunk4_221]
private theorem checked5_263 : ∀ w ∈ chunk5_263, ¬ Need 5 w.toFinset := by
  have h : chunk5_263.all (routes 4 pool5_263.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_263,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_56 _ hm
  · exact checked4_83 _ hm
  · exact checked4_211 _ hm
  · exact checked4_221 _ hm
private def chunk5_264 : List (List T) := [[wire15,wire4369,wire13107,wire17476,wire65295],
  [wire15,wire4369,wire13107,wire34952,wire35064],
  [wire15,wire4369,wire13107,wire34952,wire65280],
  [wire15,wire4369,wire13107,wire34952,wire65295]]
private def pool5_264 : List (List (List T)) := [chunk4_57, chunk4_83, chunk4_84, chunk4_85]
private theorem checked5_264 : ∀ w ∈ chunk5_264, ¬ Need 5 w.toFinset := by
  have h : chunk5_264.all (routes 4 pool5_264.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_264,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_83 _ hm
  · exact checked4_84 _ hm
  · exact checked4_85 _ hm
private def chunk5_265 : List (List T) := [[wire15,wire4369,wire13107,wire36744,wire61440],
  [wire15,wire4369,wire17412,wire34952,wire65295],
  [wire15,wire4369,wire17476,wire26214,wire35064],
  [wire15,wire4369,wire17476,wire26214,wire65280]]
private def pool5_265 : List (List (List T)) := [chunk4_57, chunk4_91]
private theorem checked5_265 : ∀ w ∈ chunk5_265, ¬ Need 5 w.toFinset := by
  have h : chunk5_265.all (routes 4 pool5_265.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_265,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_91 _ hm
private def chunk5_266 : List (List T) := [[wire15,wire4369,wire17476,wire26214,wire65295],
  [wire15,wire4369,wire17476,wire28791,wire61440],
  [wire15,wire4369,wire17476,wire30471,wire34952],
  [wire15,wire4369,wire17476,wire30583,wire35064]]
private def pool5_266 : List (List (List T)) := [chunk4_14, chunk4_58, chunk4_87, chunk4_91]
private theorem checked5_266 : ∀ w ∈ chunk5_266, ¬ Need 5 w.toFinset := by
  have h : chunk5_266.all (routes 4 pool5_266.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_266,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_14 _ hm
  · exact checked4_58 _ hm
  · exact checked4_87 _ hm
  · exact checked4_91 _ hm
private def chunk5_267 : List (List T) := [[wire15,wire4369,wire17476,wire30583,wire65280],
  [wire15,wire4369,wire17476,wire30583,wire65295],
  [wire15,wire4369,wire17476,wire33008,wire34952],
  [wire15,wire4369,wire17476,wire34952,wire35064]]
private def pool5_267 : List (List (List T)) := [chunk4_88]
private theorem checked5_267 : ∀ w ∈ chunk5_267, ¬ Need 5 w.toFinset := by
  have h : chunk5_267.all (routes 4 pool5_267.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_267,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_88 _ hm
private def chunk5_268 : List (List T) := [[wire15,wire4369,wire17476,wire34952,wire35071],
  [wire15,wire4369,wire17476,wire34952,wire65280],
  [wire15,wire4369,wire17476,wire34952,wire65295],
  [wire15,wire4369,wire17476,wire34952,wire65416]]
private def pool5_268 : List (List (List T)) := [chunk4_57, chunk4_58, chunk4_65]
private theorem checked5_268 : ∀ w ∈ chunk5_268, ¬ Need 5 w.toFinset := by
  have h : chunk5_268.all (routes 4 pool5_268.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_268,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_58 _ hm
  · exact checked4_65 _ hm
private def chunk5_269 : List (List T) := [[wire15,wire4369,wire17476,wire34952,wire65423],
  [wire15,wire4369,wire17476,wire34959,wire35064],
  [wire15,wire4369,wire17476,wire34959,wire35071],
  [wire15,wire4369,wire17476,wire34959,wire65280]]
private def pool5_269 : List (List (List T)) := [chunk4_58]
private theorem checked5_269 : ∀ w ∈ chunk5_269, ¬ Need 5 w.toFinset := by
  have h : chunk5_269.all (routes 4 pool5_269.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_269,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_58 _ hm
private def chunk5_270 : List (List T) := [[wire15,wire4369,wire17476,wire34959,wire65295],
  [wire15,wire4369,wire17476,wire35064,wire36744],
  [wire15,wire4369,wire17476,wire35064,wire39321],
  [wire15,wire4369,wire17476,wire35064,wire52428]]
private def pool5_270 : List (List (List T)) := [chunk4_58, chunk4_88, chunk4_91, chunk4_92, chunk4_213]
private theorem checked5_270 : ∀ w ∈ chunk5_270, ¬ Need 5 w.toFinset := by
  have h : chunk5_270.all (routes 4 pool5_270.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_270,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_58 _ hm
  · exact checked4_88 _ hm
  · exact checked4_91 _ hm
  · exact checked4_92 _ hm
  · exact checked4_213 _ hm
private def chunk5_271 : List (List T) := [[wire15,wire4369,wire17476,wire35064,wire56797],
  [wire15,wire4369,wire17476,wire35064,wire63624],
  [wire15,wire4369,wire17476,wire36744,wire36856],
  [wire15,wire4369,wire17476,wire36744,wire61440]]
private def pool5_271 : List (List (List T)) := [chunk4_57, chunk4_88, chunk4_213]
private theorem checked5_271 : ∀ w ∈ chunk5_271, ¬ Need 5 w.toFinset := by
  have h : chunk5_271.all (routes 4 pool5_271.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_271,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_88 _ hm
  · exact checked4_213 _ hm
private def chunk5_272 : List (List T) := [[wire15,wire4369,wire17476,wire36744,wire61455],
  [wire15,wire4369,wire17476,wire36744,wire63624],
  [wire15,wire4369,wire17476,wire36744,wire65280],
  [wire15,wire4369,wire17476,wire36744,wire65295]]
private def pool5_272 : List (List (List T)) := [chunk4_57, chunk4_58]
private theorem checked5_272 : ∀ w ∈ chunk5_272, ¬ Need 5 w.toFinset := by
  have h : chunk5_272.all (routes 4 pool5_272.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_272,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_58 _ hm
private def chunk5_273 : List (List T) := [[wire15,wire4369,wire17476,wire36744,wire65416],
  [wire15,wire4369,wire17476,wire36751,wire61440],
  [wire15,wire4369,wire17476,wire39321,wire65280],
  [wire15,wire4369,wire17476,wire39321,wire65295]]
private def pool5_273 : List (List (List T)) := [chunk4_57, chunk4_58, chunk4_65, chunk4_92]
private theorem checked5_273 : ∀ w ∈ chunk5_273, ¬ Need 5 w.toFinset := by
  have h : chunk5_273.all (routes 4 pool5_273.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_273,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_58 _ hm
  · exact checked4_65 _ hm
  · exact checked4_92 _ hm
private def chunk5_274 : List (List T) := [[wire15,wire4369,wire17476,wire52428,wire65280],
  [wire15,wire4369,wire17476,wire52428,wire65295],
  [wire15,wire4369,wire17476,wire56797,wire65280],
  [wire15,wire4369,wire17476,wire56797,wire65295]]
private def pool5_274 : List (List (List T)) := [chunk4_92, chunk4_93]
private theorem checked5_274 : ∀ w ∈ chunk5_274, ¬ Need 5 w.toFinset := by
  have h : chunk5_274.all (routes 4 pool5_274.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_274,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_92 _ hm
  · exact checked4_93 _ hm
private def chunk5_275 : List (List T) := [[wire15,wire4369,wire17476,wire61440,wire65416],
  [wire15,wire4369,wire17476,wire61440,wire65423],
  [wire15,wire4369,wire17476,wire61680,wire63624],
  [wire15,wire4369,wire17476,wire61695,wire63624]]
private def pool5_275 : List (List (List T)) := [chunk4_57, chunk4_58, chunk4_66]
private theorem checked5_275 : ∀ w ∈ chunk5_275, ¬ Need 5 w.toFinset := by
  have h : chunk5_275.all (routes 4 pool5_275.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_275,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_58 _ hm
  · exact checked4_66 _ hm
private def chunk5_276 : List (List T) := [[wire15,wire4369,wire17476,wire61986,wire65280],
  [wire15,wire4369,wire17476,wire61986,wire65295],
  [wire15,wire4369,wire17476,wire63624,wire63736],
  [wire15,wire4369,wire17476,wire63624,wire65280]]
private def pool5_276 : List (List (List T)) := [chunk4_57, chunk4_212]
private theorem checked5_276 : ∀ w ∈ chunk5_276, ¬ Need 5 w.toFinset := by
  have h : chunk5_276.all (routes 4 pool5_276.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_276,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_212 _ hm
private def chunk5_277 : List (List T) := [[wire15,wire4369,wire17476,wire63624,wire65295],
  [wire15,wire4369,wire17476,wire63624,wire65416],
  [wire15,wire4369,wire17476,wire65280,wire65314],
  [wire15,wire4369,wire17476,wire65280,wire65416]]
private def pool5_277 : List (List (List T)) := [chunk4_57, chunk4_58, chunk4_67, chunk4_68, chunk4_212]
private theorem checked5_277 : ∀ w ∈ chunk5_277, ¬ Need 5 w.toFinset := by
  have h : chunk5_277.all (routes 4 pool5_277.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_277,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_57 _ hm
  · exact checked4_58 _ hm
  · exact checked4_67 _ hm
  · exact checked4_68 _ hm
  · exact checked4_212 _ hm
private def chunk5_278 : List (List T) := [[wire15,wire4369,wire17476,wire65295,wire65327],
  [wire15,wire4369,wire17476,wire65295,wire65423],
  [wire15,wire4369,wire17476,wire65416],
  [wire15,wire4369,wire17476,wire65423]]
private def pool5_278 : List (List (List T)) := [chunk4_3, chunk4_14, chunk4_17, chunk4_57, chunk4_58, chunk4_60, chunk4_65, chunk4_68, chunk4_86, chunk4_89, chunk4_203, chunk4_211, chunk4_212, chunk4_213]
private theorem checked5_278 : ∀ w ∈ chunk5_278, ¬ Need 5 w.toFinset := by
  have h : chunk5_278.all (routes 4 pool5_278.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_278,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_3 _ hm
  · exact checked4_14 _ hm
  · exact checked4_17 _ hm
  · exact checked4_57 _ hm
  · exact checked4_58 _ hm
  · exact checked4_60 _ hm
  · exact checked4_65 _ hm
  · exact checked4_68 _ hm
  · exact checked4_86 _ hm
  · exact checked4_89 _ hm
  · exact checked4_203 _ hm
  · exact checked4_211 _ hm
  · exact checked4_212 _ hm
  · exact checked4_213 _ hm
private def chunk5_279 : List (List T) := [[wire15,wire4369,wire17652,wire34952,wire35064],
  [wire15,wire4369,wire17652,wire34952,wire65280],
  [wire15,wire4369,wire17652,wire34952,wire65295],
  [wire15,wire4369,wire17652,wire36744,wire61440]]
private def pool5_279 : List (List (List T)) := [chunk4_59, chunk4_90, chunk4_213]
private theorem checked5_279 : ∀ w ∈ chunk5_279, ¬ Need 5 w.toFinset := by
  have h : chunk5_279.all (routes 4 pool5_279.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_279,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_59 _ hm
  · exact checked4_90 _ hm
  · exact checked4_213 _ hm
private def chunk5_280 : List (List T) := [[wire15,wire4369,wire20292,wire34952,wire35064],
  [wire15,wire4369,wire20292,wire34952,wire65280],
  [wire15,wire4369,wire20292,wire34952,wire65295],
  [wire15,wire4369,wire20292,wire36744,wire61440]]
private def pool5_280 : List (List (List T)) := [chunk4_59, chunk4_90]
private theorem checked5_280 : ∀ w ∈ chunk5_280, ¬ Need 5 w.toFinset := by
  have h : chunk5_280.all (routes 4 pool5_280.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_280,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_59 _ hm
  · exact checked4_90 _ hm
private def chunk5_281 : List (List T) := [[wire15,wire4369,wire21845,wire34952,wire35064],
  [wire15,wire4369,wire21845,wire34952,wire65280],
  [wire15,wire4369,wire21845,wire34952,wire65295],
  [wire15,wire4369,wire21845,wire36744,wire61440]]
private def pool5_281 : List (List (List T)) := [chunk4_60, chunk4_91, chunk4_92, chunk4_222]
private theorem checked5_281 : ∀ w ∈ chunk5_281, ¬ Need 5 w.toFinset := by
  have h : chunk5_281.all (routes 4 pool5_281.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_281,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_60 _ hm
  · exact checked4_91 _ hm
  · exact checked4_92 _ hm
  · exact checked4_222 _ hm
private def chunk5_282 : List (List T) := [[wire15,wire4369,wire34952,wire35064,wire43690],
  [wire15,wire4369,wire34952,wire35064,wire43770],
  [wire15,wire4369,wire34952,wire35064,wire48059],
  [wire15,wire4369,wire34952,wire35064,wire52428]]
private def pool5_282 : List (List (List T)) := [chunk4_10, chunk4_96, chunk4_97]
private theorem checked5_282 : ∀ w ∈ chunk5_282, ¬ Need 5 w.toFinset := by
  have h : chunk5_282.all (routes 4 pool5_282.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_282,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_96 _ hm
  · exact checked4_97 _ hm
private def chunk5_283 : List (List T) := [[wire15,wire4369,wire34952,wire35064,wire52476],
  [wire15,wire4369,wire34952,wire35064,wire56797],
  [wire15,wire4369,wire34952,wire35064,wire61986],
  [wire15,wire4369,wire34952,wire35064,wire62532]]
private def pool5_283 : List (List (List T)) := [chunk4_97, chunk4_98]
private theorem checked5_283 : ∀ w ∈ chunk5_283, ¬ Need 5 w.toFinset := by
  have h : chunk5_283.all (routes 4 pool5_283.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_283,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_97 _ hm
  · exact checked4_98 _ hm
private def chunk5_284 : List (List T) := [[wire15,wire4369,wire34952,wire43690,wire65280],
  [wire15,wire4369,wire34952,wire43690,wire65295],
  [wire15,wire4369,wire34952,wire48059,wire65280],
  [wire15,wire4369,wire34952,wire48059,wire65295]]
private def pool5_284 : List (List (List T)) := [chunk4_10, chunk4_64, chunk4_65, chunk4_98, chunk4_99, chunk4_222]
private theorem checked5_284 : ∀ w ∈ chunk5_284, ¬ Need 5 w.toFinset := by
  have h : chunk5_284.all (routes 4 pool5_284.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_284,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_64 _ hm
  · exact checked4_65 _ hm
  · exact checked4_98 _ hm
  · exact checked4_99 _ hm
  · exact checked4_222 _ hm
private def chunk5_285 : List (List T) := [[wire15,wire4369,wire34952,wire52428,wire65280],
  [wire15,wire4369,wire34952,wire52428,wire65295],
  [wire15,wire4369,wire34952,wire56797,wire65280],
  [wire15,wire4369,wire34952,wire56797,wire65295]]
private def pool5_285 : List (List (List T)) := [chunk4_11, chunk4_13, chunk4_65, chunk4_66, chunk4_99, chunk4_222]
private theorem checked5_285 : ∀ w ∈ chunk5_285, ¬ Need 5 w.toFinset := by
  have h : chunk5_285.all (routes 4 pool5_285.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_285,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_11 _ hm
  · exact checked4_13 _ hm
  · exact checked4_65 _ hm
  · exact checked4_66 _ hm
  · exact checked4_99 _ hm
  · exact checked4_222 _ hm
private def chunk5_286 : List (List T) := [[wire15,wire4369,wire34952,wire61986,wire65280],
  [wire15,wire4369,wire34952,wire61986,wire65295],
  [wire15,wire4369,wire34952,wire62532,wire65280],
  [wire15,wire4369,wire34952,wire62532,wire65295]]
private def pool5_286 : List (List (List T)) := [chunk4_66, chunk4_223]
private theorem checked5_286 : ∀ w ∈ chunk5_286, ¬ Need 5 w.toFinset := by
  have h : chunk5_286.all (routes 4 pool5_286.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_286,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_66 _ hm
  · exact checked4_223 _ hm
private def chunk5_287 : List (List T) := [[wire15,wire4369,wire34952,wire65280,wire65314],
  [wire15,wire4369,wire34952,wire65280,wire65348],
  [wire15,wire4369,wire36744,wire43690,wire61440],
  [wire15,wire4369,wire36744,wire44970,wire61440]]
private def pool5_287 : List (List (List T)) := [chunk4_64, chunk4_67, chunk4_68, chunk4_215, chunk4_223]
private theorem checked5_287 : ∀ w ∈ chunk5_287, ¬ Need 5 w.toFinset := by
  have h : chunk5_287.all (routes 4 pool5_287.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_287,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_64 _ hm
  · exact checked4_67 _ hm
  · exact checked4_68 _ hm
  · exact checked4_215 _ hm
  · exact checked4_223 _ hm
private def chunk5_288 : List (List T) := [[wire15,wire4369,wire36744,wire48059,wire61440],
  [wire15,wire4369,wire36744,wire52428,wire61440],
  [wire15,wire4369,wire36744,wire53196,wire61440],
  [wire15,wire4369,wire36744,wire56797,wire61440]]
private def pool5_288 : List (List (List T)) := [chunk4_12, chunk4_13, chunk4_65, chunk4_66, chunk4_224]
private theorem checked5_288 : ∀ w ∈ chunk5_288, ¬ Need 5 w.toFinset := by
  have h : chunk5_288.all (routes 4 pool5_288.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_288,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_12 _ hm
  · exact checked4_13 _ hm
  · exact checked4_65 _ hm
  · exact checked4_66 _ hm
  · exact checked4_224 _ hm
private def chunk5_289 : List (List T) := [[wire15,wire4369,wire36744,wire61440,wire61986],
  [wire15,wire4369,wire36744,wire61440,wire62532],
  [wire15,wire4383,wire8738,wire17476,wire35064],
  [wire15,wire4383,wire8738,wire34952,wire35064]]
private def pool5_289 : List (List (List T)) := [chunk4_66, chunk4_75, chunk4_79, chunk4_216, chunk4_217, chunk4_218, chunk4_224]
private theorem checked5_289 : ∀ w ∈ chunk5_289, ¬ Need 5 w.toFinset := by
  have h : chunk5_289.all (routes 4 pool5_289.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_289,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_66 _ hm
  · exact checked4_75 _ hm
  · exact checked4_79 _ hm
  · exact checked4_216 _ hm
  · exact checked4_217 _ hm
  · exact checked4_218 _ hm
  · exact checked4_224 _ hm
private def chunk5_290 : List (List T) := [[wire15,wire4383,wire8738,wire34952,wire65280],
  [wire15,wire4383,wire8738,wire34952,wire65295],
  [wire15,wire4383,wire8738,wire36744,wire61440],
  [wire15,wire4593,wire8738,wire8946,wire17476]]
private def pool5_290 : List (List (List T)) := [chunk4_2, chunk4_69, chunk4_71, chunk4_218]
private theorem checked5_290 : ∀ w ∈ chunk5_290, ¬ Need 5 w.toFinset := by
  have h : chunk5_290.all (routes 4 pool5_290.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_290,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_69 _ hm
  · exact checked4_71 _ hm
  · exact checked4_218 _ hm
private def chunk5_291 : List (List T) := [[wire15,wire4593,wire8738,wire17476,wire17652],
  [wire15,wire4593,wire8738,wire17476,wire34952,wire65280],
  [wire15,wire4593,wire8738,wire17476,wire35064],
  [wire15,wire4593,wire8738,wire17476,wire65280]]
private def pool5_291 : List (List (List T)) := [chunk4_70, chunk4_71, chunk4_72, chunk4_73, chunk4_224, chunk4_225]
private theorem checked5_291 : ∀ w ∈ chunk5_291, ¬ Need 5 w.toFinset := by
  have h : chunk5_291.all (routes 4 pool5_291.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_291,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_70 _ hm
  · exact checked4_71 _ hm
  · exact checked4_72 _ hm
  · exact checked4_73 _ hm
  · exact checked4_224 _ hm
  · exact checked4_225 _ hm
private def chunk5_292 : List (List T) := [[wire15,wire4593,wire8738,wire17476,wire65295],
  [wire15,wire4593,wire8738,wire20292,wire34952,wire61440],
  [wire15,wire4593,wire8738,wire20292,wire61440],
  [wire15,wire4593,wire12066,wire17476,wire34952,wire61440]]
private def pool5_292 : List (List (List T)) := [chunk4_70, chunk4_71, chunk4_72, chunk4_73, chunk4_74]
private theorem checked5_292 : ∀ w ∈ chunk5_292, ¬ Need 5 w.toFinset := by
  have h : chunk5_292.all (routes 4 pool5_292.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_292,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_70 _ hm
  · exact checked4_71 _ hm
  · exact checked4_72 _ hm
  · exact checked4_73 _ hm
  · exact checked4_74 _ hm
private def chunk5_293 : List (List T) := [[wire15,wire4593,wire12066,wire17476,wire61440],
  [wire15,wire7953,wire8738,wire17476,wire35064],
  [wire15,wire8192,wire8738,wire17476,wire35064],
  [wire15,wire8738,wire8751,wire17476,wire35064]]
private def pool5_293 : List (List (List T)) := [chunk4_2, chunk4_72, chunk4_75, chunk4_77, chunk4_78, chunk4_232, chunk4_233]
private theorem checked5_293 : ∀ w ∈ chunk5_293, ¬ Need 5 w.toFinset := by
  have h : chunk5_293.all (routes 4 pool5_293.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_293,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_72 _ hm
  · exact checked4_75 _ hm
  · exact checked4_77 _ hm
  · exact checked4_78 _ hm
  · exact checked4_232 _ hm
  · exact checked4_233 _ hm
private def chunk5_294 : List (List T) := [[wire15,wire8738,wire8946,wire17476,wire35064],
  [wire15,wire8738,wire12066,wire17476,wire35064],
  [wire15,wire8738,wire13107,wire17476,wire35064],
  [wire15,wire8738,wire13107,wire17476,wire65280]]
private def pool5_294 : List (List (List T)) := [chunk4_75, chunk4_82, chunk4_84, chunk4_233]
private theorem checked5_294 : ∀ w ∈ chunk5_294, ¬ Need 5 w.toFinset := by
  have h : chunk5_294.all (routes 4 pool5_294.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_294,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_82 _ hm
  · exact checked4_84 _ hm
  · exact checked4_233 _ hm
private def chunk5_295 : List (List T) := [[wire15,wire8738,wire13107,wire17476,wire65295],
  [wire15,wire8738,wire13107,wire34952,wire35064],
  [wire15,wire8738,wire13107,wire34952,wire65280],
  [wire15,wire8738,wire13107,wire34952,wire65295]]
private def pool5_295 : List (List (List T)) := [chunk4_74, chunk4_79, chunk4_84, chunk4_85, chunk4_86, chunk4_234]
private theorem checked5_295 : ∀ w ∈ chunk5_295, ¬ Need 5 w.toFinset := by
  have h : chunk5_295.all (routes 4 pool5_295.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_295,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_74 _ hm
  · exact checked4_79 _ hm
  · exact checked4_84 _ hm
  · exact checked4_85 _ hm
  · exact checked4_86 _ hm
  · exact checked4_234 _ hm
private def chunk5_296 : List (List T) := [[wire15,wire8738,wire13107,wire36744,wire61440],
  [wire15,wire8738,wire16384,wire17476,wire35064],
  [wire15,wire8738,wire17476,wire17487,wire35064],
  [wire15,wire8738,wire17476,wire17652,wire35064]]
private def pool5_296 : List (List (List T)) := [chunk4_6, chunk4_74, chunk4_75, chunk4_76, chunk4_86, chunk4_90, chunk4_234, chunk4_235, chunk4_236, chunk4_237, chunk4_243]
private theorem checked5_296 : ∀ w ∈ chunk5_296, ¬ Need 5 w.toFinset := by
  have h : chunk5_296.all (routes 4 pool5_296.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_296,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_74 _ hm
  · exact checked4_75 _ hm
  · exact checked4_76 _ hm
  · exact checked4_86 _ hm
  · exact checked4_90 _ hm
  · exact checked4_234 _ hm
  · exact checked4_235 _ hm
  · exact checked4_236 _ hm
  · exact checked4_237 _ hm
  · exact checked4_243 _ hm
private def chunk5_297 : List (List T) := [[wire15,wire8738,wire17476,wire20292,wire35064],
  [wire15,wire8738,wire17476,wire21845,wire35064],
  [wire15,wire8738,wire17476,wire21845,wire65280],
  [wire15,wire8738,wire17476,wire21845,wire65295]]
private def pool5_297 : List (List (List T)) := [chunk4_75, chunk4_90, chunk4_91, chunk4_238, chunk4_253]
private theorem checked5_297 : ∀ w ∈ chunk5_297, ¬ Need 5 w.toFinset := by
  have h : chunk5_297.all (routes 4 pool5_297.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_297,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_90 _ hm
  · exact checked4_91 _ hm
  · exact checked4_238 _ hm
  · exact checked4_253 _ hm
private def chunk5_298 : List (List T) := [[wire15,wire8738,wire17476,wire26214,wire35064],
  [wire15,wire8738,wire17476,wire30471],
  [wire15,wire8738,wire17476,wire30471,wire34952],
  [wire15,wire8738,wire17476,wire30471,wire35064]]
private def pool5_298 : List (List (List T)) := [chunk4_74, chunk4_75, chunk4_76, chunk4_77, chunk4_78, chunk4_87, chunk4_235, chunk4_236, chunk4_239, chunk4_240]
private theorem checked5_298 : ∀ w ∈ chunk5_298, ¬ Need 5 w.toFinset := by
  have h : chunk5_298.all (routes 4 pool5_298.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_298,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_74 _ hm
  · exact checked4_75 _ hm
  · exact checked4_76 _ hm
  · exact checked4_77 _ hm
  · exact checked4_78 _ hm
  · exact checked4_87 _ hm
  · exact checked4_235 _ hm
  · exact checked4_236 _ hm
  · exact checked4_239 _ hm
  · exact checked4_240 _ hm
private def chunk5_299 : List (List T) := [[wire15,wire8738,wire17476,wire30471,wire61440],
  [wire15,wire8738,wire17476,wire30583,wire35064],
  [wire15,wire8738,wire17476,wire30583,wire65280],
  [wire15,wire8738,wire17476,wire30583,wire65295]]
private def pool5_299 : List (List (List T)) := [chunk4_74, chunk4_75, chunk4_240, chunk4_241]
private theorem checked5_299 : ∀ w ∈ chunk5_299, ¬ Need 5 w.toFinset := by
  have h : chunk5_299.all (routes 4 pool5_299.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_299,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_74 _ hm
  · exact checked4_75 _ hm
  · exact checked4_240 _ hm
  · exact checked4_241 _ hm
private def chunk5_300 : List (List T) := [[wire15,wire8738,wire17476,wire32768,wire35064],
  [wire15,wire8738,wire17476,wire33008,wire34952],
  [wire15,wire8738,wire17476,wire34824,wire65295],
  [wire15,wire8738,wire17476,wire34952,wire35064]]
private def pool5_300 : List (List (List T)) := [chunk4_75, chunk4_88, chunk4_241, chunk4_242]
private theorem checked5_300 : ∀ w ∈ chunk5_300, ¬ Need 5 w.toFinset := by
  have h : chunk5_300.all (routes 4 pool5_300.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_300,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_88 _ hm
  · exact checked4_241 _ hm
  · exact checked4_242 _ hm
private def chunk5_301 : List (List T) := [[wire15,wire8738,wire17476,wire34952,wire35071],
  [wire15,wire8738,wire17476,wire34952,wire65280],
  [wire15,wire8738,wire17476,wire34952,wire65295],
  [wire15,wire8738,wire17476,wire34952,wire65416]]
private def pool5_301 : List (List (List T)) := [chunk4_80, chunk4_88, chunk4_242]
private theorem checked5_301 : ∀ w ∈ chunk5_301, ¬ Need 5 w.toFinset := by
  have h : chunk5_301.all (routes 4 pool5_301.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_301,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_80 _ hm
  · exact checked4_88 _ hm
  · exact checked4_242 _ hm
private def chunk5_302 : List (List T) := [[wire15,wire8738,wire17476,wire34952,wire65423],
  [wire15,wire8738,wire17476,wire34959,wire35064],
  [wire15,wire8738,wire17476,wire35064],
  [wire15,wire8738,wire17476,wire35064,wire35071]]
private def pool5_302 : List (List (List T)) := [chunk4_74, chunk4_75, chunk4_76, chunk4_78, chunk4_79, chunk4_87, chunk4_88, chunk4_89, chunk4_236, chunk4_242, chunk4_243]
private theorem checked5_302 : ∀ w ∈ chunk5_302, ¬ Need 5 w.toFinset := by
  have h : chunk5_302.all (routes 4 pool5_302.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_302,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_74 _ hm
  · exact checked4_75 _ hm
  · exact checked4_76 _ hm
  · exact checked4_78 _ hm
  · exact checked4_79 _ hm
  · exact checked4_87 _ hm
  · exact checked4_88 _ hm
  · exact checked4_89 _ hm
  · exact checked4_236 _ hm
  · exact checked4_242 _ hm
  · exact checked4_243 _ hm
private def chunk5_303 : List (List T) := [[wire15,wire8738,wire17476,wire35064,wire36744],
  [wire15,wire8738,wire17476,wire35064,wire36856],
  [wire15,wire8738,wire17476,wire35064,wire39321],
  [wire15,wire8738,wire17476,wire35064,wire39417]]
private def pool5_303 : List (List (List T)) := [chunk4_75, chunk4_243, chunk4_244]
private theorem checked5_303 : ∀ w ∈ chunk5_303, ¬ Need 5 w.toFinset := by
  have h : chunk5_303.all (routes 4 pool5_303.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_303,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_243 _ hm
  · exact checked4_244 _ hm
private def chunk5_304 : List (List T) := [[wire15,wire8738,wire17476,wire35064,wire43690],
  [wire15,wire8738,wire17476,wire35064,wire43770],
  [wire15,wire8738,wire17476,wire35064,wire48059],
  [wire15,wire8738,wire17476,wire35064,wire52428]]
private def pool5_304 : List (List (List T)) := [chunk4_10, chunk4_13, chunk4_75, chunk4_79, chunk4_93, chunk4_94, chunk4_244, chunk4_245]
private theorem checked5_304 : ∀ w ∈ chunk5_304, ¬ Need 5 w.toFinset := by
  have h : chunk5_304.all (routes 4 pool5_304.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_304,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_10 _ hm
  · exact checked4_13 _ hm
  · exact checked4_75 _ hm
  · exact checked4_79 _ hm
  · exact checked4_93 _ hm
  · exact checked4_94 _ hm
  · exact checked4_244 _ hm
  · exact checked4_245 _ hm
private def chunk5_305 : List (List T) := [[wire15,wire8738,wire17476,wire35064,wire52476],
  [wire15,wire8738,wire17476,wire35064,wire56797],
  [wire15,wire8738,wire17476,wire35064,wire61166],
  [wire15,wire8738,wire17476,wire35064,wire61440]]
private def pool5_305 : List (List (List T)) := [chunk4_75, chunk4_88, chunk4_94, chunk4_246, chunk4_247]
private theorem checked5_305 : ∀ w ∈ chunk5_305, ¬ Need 5 w.toFinset := by
  have h : chunk5_305.all (routes 4 pool5_305.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_305,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_88 _ hm
  · exact checked4_94 _ hm
  · exact checked4_246 _ hm
  · exact checked4_247 _ hm
private def chunk5_306 : List (List T) := [[wire15,wire8738,wire17476,wire35064,wire61455],
  [wire15,wire8738,wire17476,wire35064,wire61680],
  [wire15,wire8738,wire17476,wire35064,wire61695],
  [wire15,wire8738,wire17476,wire35064,wire61713]]
private def pool5_306 : List (List (List T)) := [chunk4_75, chunk4_247, chunk4_248]
private theorem checked5_306 : ∀ w ∈ chunk5_306, ¬ Need 5 w.toFinset := by
  have h : chunk5_306.all (routes 4 pool5_306.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_306,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_247 _ hm
  · exact checked4_248 _ hm
private def chunk5_307 : List (List T) := [[wire15,wire8738,wire17476,wire35064,wire61986],
  [wire15,wire8738,wire17476,wire35064,wire62532],
  [wire15,wire8738,wire17476,wire35064,wire63624],
  [wire15,wire8738,wire17476,wire35064,wire63736]]
private def pool5_307 : List (List (List T)) := [chunk4_75, chunk4_94, chunk4_95, chunk4_248, chunk4_249]
private theorem checked5_307 : ∀ w ∈ chunk5_307, ¬ Need 5 w.toFinset := by
  have h : chunk5_307.all (routes 4 pool5_307.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_307,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_94 _ hm
  · exact checked4_95 _ hm
  · exact checked4_248 _ hm
  · exact checked4_249 _ hm
private def chunk5_308 : List (List T) := [[wire15,wire8738,wire17476,wire35064,wire65280],
  [wire15,wire8738,wire17476,wire35064,wire65295],
  [wire15,wire8738,wire17476,wire35064,wire65520],
  [wire15,wire8738,wire17476,wire35064,wire65535]]
private def pool5_308 : List (List (List T)) := [chunk4_74, chunk4_75, chunk4_236, chunk4_249, chunk4_250]
private theorem checked5_308 : ∀ w ∈ chunk5_308, ¬ Need 5 w.toFinset := by
  have h : chunk5_308.all (routes 4 pool5_308.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_308,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_74 _ hm
  · exact checked4_75 _ hm
  · exact checked4_236 _ hm
  · exact checked4_249 _ hm
  · exact checked4_250 _ hm
private def chunk5_309 : List (List T) := [[wire15,wire8738,wire17476,wire36744,wire63624],
  [wire15,wire8738,wire17476,wire43690,wire65280],
  [wire15,wire8738,wire17476,wire43690,wire65295],
  [wire15,wire8738,wire17476,wire52428,wire65280]]
private def pool5_309 : List (List (List T)) := [chunk4_95, chunk4_250, chunk4_253]
private theorem checked5_309 : ∀ w ∈ chunk5_309, ¬ Need 5 w.toFinset := by
  have h : chunk5_309.all (routes 4 pool5_309.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_309,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_95 _ hm
  · exact checked4_250 _ hm
  · exact checked4_253 _ hm
private def chunk5_310 : List (List T) := [[wire15,wire8738,wire17476,wire52428,wire65295],
  [wire15,wire8738,wire17476,wire61166,wire65280],
  [wire15,wire8738,wire17476,wire61166,wire65295],
  [wire15,wire8738,wire17487,wire34952,wire35064]]
private def pool5_310 : List (List (List T)) := [chunk4_6, chunk4_76, chunk4_96, chunk4_242, chunk4_253]
private theorem checked5_310 : ∀ w ∈ chunk5_310, ¬ Need 5 w.toFinset := by
  have h : chunk5_310.all (routes 4 pool5_310.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_310,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_6 _ hm
  · exact checked4_76 _ hm
  · exact checked4_96 _ hm
  · exact checked4_242 _ hm
  · exact checked4_253 _ hm
private def chunk5_311 : List (List T) := [[wire15,wire8738,wire17487,wire34952,wire65280],
  [wire15,wire8738,wire17487,wire34952,wire65295],
  [wire15,wire8738,wire17487,wire35064],
  [wire15,wire8738,wire17487,wire35064,wire61440]]
private def pool5_311 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_6, chunk4_76, chunk4_78, chunk4_79, chunk4_89, chunk4_233, chunk4_242, chunk4_243, chunk4_247, chunk4_250]
private theorem checked5_311 : ∀ w ∈ chunk5_311, ¬ Need 5 w.toFinset := by
  have h : chunk5_311.all (routes 4 pool5_311.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_311,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_6 _ hm
  · exact checked4_76 _ hm
  · exact checked4_78 _ hm
  · exact checked4_79 _ hm
  · exact checked4_89 _ hm
  · exact checked4_233 _ hm
  · exact checked4_242 _ hm
  · exact checked4_243 _ hm
  · exact checked4_247 _ hm
  · exact checked4_250 _ hm
private def chunk5_312 : List (List T) := [[wire15,wire8738,wire26214,wire34952,wire35064],
  [wire15,wire8738,wire26214,wire34952,wire65280],
  [wire15,wire8738,wire26214,wire34952,wire65295],
  [wire15,wire8738,wire26214,wire35064]]
private def pool5_312 : List (List (List T)) := [chunk4_0, chunk4_77, chunk4_78, chunk4_79, chunk4_93, chunk4_94, chunk4_95, chunk4_251]
private theorem checked5_312 : ∀ w ∈ chunk5_312, ¬ Need 5 w.toFinset := by
  have h : chunk5_312.all (routes 4 pool5_312.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_312,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_77 _ hm
  · exact checked4_78 _ hm
  · exact checked4_79 _ hm
  · exact checked4_93 _ hm
  · exact checked4_94 _ hm
  · exact checked4_95 _ hm
  · exact checked4_251 _ hm
private def chunk5_313 : List (List T) := [[wire15,wire8738,wire26214,wire35064,wire61440],
  [wire15,wire8738,wire34952,wire35064,wire39321],
  [wire15,wire8738,wire34952,wire35064,wire48059],
  [wire15,wire8738,wire34952,wire35064,wire52428]]
private def pool5_313 : List (List (List T)) := [chunk4_79, chunk4_94, chunk4_96, chunk4_98]
private theorem checked5_313 : ∀ w ∈ chunk5_313, ¬ Need 5 w.toFinset := by
  have h : chunk5_313.all (routes 4 pool5_313.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_313,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_79 _ hm
  · exact checked4_94 _ hm
  · exact checked4_96 _ hm
  · exact checked4_98 _ hm
private def chunk5_314 : List (List T) := [[wire15,wire8738,wire34952,wire35064,wire61166],
  [wire15,wire8738,wire34952,wire39321,wire65280],
  [wire15,wire8738,wire34952,wire39321,wire65295],
  [wire15,wire8738,wire34952,wire48059,wire65280]]
private def pool5_314 : List (List (List T)) := [chunk4_98, chunk4_99]
private theorem checked5_314 : ∀ w ∈ chunk5_314, ¬ Need 5 w.toFinset := by
  have h : chunk5_314.all (routes 4 pool5_314.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_314,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_98 _ hm
  · exact checked4_99 _ hm
private def chunk5_315 : List (List T) := [[wire15,wire8738,wire34952,wire48059,wire65295],
  [wire15,wire8738,wire34952,wire52428,wire65280],
  [wire15,wire8738,wire34952,wire52428,wire65295],
  [wire15,wire8738,wire34952,wire61166,wire65280]]
private def pool5_315 : List (List (List T)) := [chunk4_80, chunk4_99, chunk4_100]
private theorem checked5_315 : ∀ w ∈ chunk5_315, ¬ Need 5 w.toFinset := by
  have h : chunk5_315.all (routes 4 pool5_315.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_315,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_80 _ hm
  · exact checked4_99 _ hm
  · exact checked4_100 _ hm
private def chunk5_316 : List (List T) := [[wire15,wire8738,wire34952,wire61166,wire65295],
  [wire15,wire8738,wire35064,wire39321],
  [wire15,wire8738,wire35064,wire39321,wire61440],
  [wire15,wire8738,wire35064,wire48059]]
private def pool5_316 : List (List (List T)) := [chunk4_1, chunk4_11, chunk4_75, chunk4_78, chunk4_79, chunk4_80, chunk4_96, chunk4_97, chunk4_98, chunk4_252]
private theorem checked5_316 : ∀ w ∈ chunk5_316, ¬ Need 5 w.toFinset := by
  have h : chunk5_316.all (routes 4 pool5_316.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_316,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_11 _ hm
  · exact checked4_75 _ hm
  · exact checked4_78 _ hm
  · exact checked4_79 _ hm
  · exact checked4_80 _ hm
  · exact checked4_96 _ hm
  · exact checked4_97 _ hm
  · exact checked4_98 _ hm
  · exact checked4_252 _ hm
private def chunk5_317 : List (List T) := [[wire15,wire8738,wire35064,wire48059,wire61440],
  [wire15,wire8738,wire36744,wire52428,wire61440],
  [wire15,wire8738,wire36744,wire61166,wire61440],
  [wire15,wire17476,wire21845,wire34952,wire35064]]
private def pool5_317 : List (List (List T)) := [chunk4_80, chunk4_88, chunk4_92, chunk4_256]
private theorem checked5_317 : ∀ w ∈ chunk5_317, ¬ Need 5 w.toFinset := by
  have h : chunk5_317.all (routes 4 pool5_317.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_317,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_80 _ hm
  · exact checked4_88 _ hm
  · exact checked4_92 _ hm
  · exact checked4_256 _ hm
private def chunk5_318 : List (List T) := [[wire15,wire17476,wire21845,wire34952,wire65280],
  [wire15,wire17476,wire21845,wire34952,wire65295],
  [wire15,wire17476,wire21845,wire36744,wire61440],
  [wire15,wire17476,wire26214,wire34952,wire35064]]
private def pool5_318 : List (List (List T)) := [chunk4_86, chunk4_87, chunk4_92, chunk4_93, chunk4_94, chunk4_256]
private theorem checked5_318 : ∀ w ∈ chunk5_318, ¬ Need 5 w.toFinset := by
  have h : chunk5_318.all (routes 4 pool5_318.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_318,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_86 _ hm
  · exact checked4_87 _ hm
  · exact checked4_92 _ hm
  · exact checked4_93 _ hm
  · exact checked4_94 _ hm
  · exact checked4_256 _ hm
private def chunk5_319 : List (List T) := [[wire15,wire17476,wire26214,wire34952,wire65280],
  [wire15,wire17476,wire26214,wire34952,wire65295],
  [wire15,wire17476,wire26214,wire35064],
  [wire15,wire17476,wire26214,wire35064,wire61440]]
private def pool5_319 : List (List (List T)) := [chunk4_4, chunk4_87, chunk4_88, chunk4_93, chunk4_94, chunk4_95, chunk4_96, chunk4_254, chunk4_255]
private theorem checked5_319 : ∀ w ∈ chunk5_319, ¬ Need 5 w.toFinset := by
  have h : chunk5_319.all (routes 4 pool5_319.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_319,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_87 _ hm
  · exact checked4_88 _ hm
  · exact checked4_93 _ hm
  · exact checked4_94 _ hm
  · exact checked4_95 _ hm
  · exact checked4_96 _ hm
  · exact checked4_254 _ hm
  · exact checked4_255 _ hm
private def chunk5_320 : List (List T) := [[wire15,wire17476,wire34952,wire35064,wire39321],
  [wire15,wire17476,wire34952,wire35064,wire43690],
  [wire15,wire17476,wire34952,wire35064,wire56797],
  [wire15,wire17476,wire34952,wire35064,wire61166]]
private def pool5_320 : List (List (List T)) := [chunk4_88, chunk4_97, chunk4_98, chunk4_256, chunk4_257]
private theorem checked5_320 : ∀ w ∈ chunk5_320, ¬ Need 5 w.toFinset := by
  have h : chunk5_320.all (routes 4 pool5_320.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_320,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_88 _ hm
  · exact checked4_97 _ hm
  · exact checked4_98 _ hm
  · exact checked4_256 _ hm
  · exact checked4_257 _ hm
private def chunk5_321 : List (List T) := [[wire15,wire17476,wire34952,wire39321,wire65280],
  [wire15,wire17476,wire34952,wire39321,wire65295],
  [wire15,wire17476,wire34952,wire43690,wire65280],
  [wire15,wire17476,wire34952,wire43690,wire65295]]
private def pool5_321 : List (List (List T)) := [chunk4_88, chunk4_89, chunk4_99, chunk4_100, chunk4_257]
private theorem checked5_321 : ∀ w ∈ chunk5_321, ¬ Need 5 w.toFinset := by
  have h : chunk5_321.all (routes 4 pool5_321.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_321,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_88 _ hm
  · exact checked4_89 _ hm
  · exact checked4_99 _ hm
  · exact checked4_100 _ hm
  · exact checked4_257 _ hm
private def chunk5_322 : List (List T) := [[wire15,wire17476,wire34952,wire56797,wire65280],
  [wire15,wire17476,wire34952,wire56797,wire65295],
  [wire15,wire17476,wire34952,wire61166,wire65280],
  [wire15,wire17476,wire34952,wire61166,wire65295]]
private def pool5_322 : List (List (List T)) := [chunk4_89, chunk4_257]
private theorem checked5_322 : ∀ w ∈ chunk5_322, ¬ Need 5 w.toFinset := by
  have h : chunk5_322.all (routes 4 pool5_322.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_322,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_89 _ hm
  · exact checked4_257 _ hm
private def chunk5_323 : List (List T) := [[wire15,wire17476,wire35064,wire39321],
  [wire15,wire17476,wire35064,wire39321,wire61440],
  [wire15,wire17476,wire35064,wire56797],
  [wire15,wire17476,wire35064,wire56797,wire61440]]
private def pool5_323 : List (List (List T)) := [chunk4_4, chunk4_75, chunk4_87, chunk4_88, chunk4_89, chunk4_96, chunk4_97, chunk4_98, chunk4_255, chunk4_256, chunk4_257, chunk4_258]
private theorem checked5_323 : ∀ w ∈ chunk5_323, ¬ Need 5 w.toFinset := by
  have h : chunk5_323.all (routes 4 pool5_323.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_323,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_4 _ hm
  · exact checked4_75 _ hm
  · exact checked4_87 _ hm
  · exact checked4_88 _ hm
  · exact checked4_89 _ hm
  · exact checked4_96 _ hm
  · exact checked4_97 _ hm
  · exact checked4_98 _ hm
  · exact checked4_255 _ hm
  · exact checked4_256 _ hm
  · exact checked4_257 _ hm
  · exact checked4_258 _ hm
private def chunk5_324 : List (List T) := [[wire15,wire17476,wire36744,wire43690,wire61440],
  [wire15,wire17476,wire36744,wire61166,wire61440],
  [wire16,wire240,wire8738,wire17487,wire34952],
  [wire31,wire240,wire4369,wire8738,wire17476]]
private def pool5_324 : List (List (List T)) := [chunk4_88, chunk4_89, chunk4_100, chunk4_147]
private theorem checked5_324 : ∀ w ∈ chunk5_324, ¬ Need 5 w.toFinset := by
  have h : chunk5_324.all (routes 4 pool5_324.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_324,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_88 _ hm
  · exact checked4_89 _ hm
  · exact checked4_100 _ hm
  · exact checked4_147 _ hm
private def chunk5_325 : List (List T) := [[wire31,wire240,wire4369,wire8738,wire34952],
  [wire31,wire240,wire4369,wire17476,wire34952],
  [wire31,wire240,wire8738,wire17476,wire34952],
  [wire32,wire47,wire240,wire4369,wire17476]]
private def pool5_325 : List (List (List T)) := [chunk4_100, chunk4_103, chunk4_104, chunk4_105]
private theorem checked5_325 : ∀ w ∈ chunk5_325, ¬ Need 5 w.toFinset := by
  have h : chunk5_325.all (routes 4 pool5_325.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_325,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_100 _ hm
  · exact checked4_103 _ hm
  · exact checked4_104 _ hm
  · exact checked4_105 _ hm
private def chunk5_326 : List (List T) := [[wire32,wire240,wire255,wire4369,wire17476],
  [wire32,wire240,wire3840,wire4369,wire62532],
  [wire32,wire240,wire4369,wire17476,wire17487],
  [wire32,wire240,wire4369,wire17476,wire65280]]
private def pool5_326 : List (List (List T)) := [chunk4_101, chunk4_102, chunk4_121, chunk4_125, chunk4_126, chunk4_128, chunk4_129, chunk4_130, chunk4_131]
private theorem checked5_326 : ∀ w ∈ chunk5_326, ¬ Need 5 w.toFinset := by
  have h : chunk5_326.all (routes 4 pool5_326.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_326,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_101 _ hm
  · exact checked4_102 _ hm
  · exact checked4_121 _ hm
  · exact checked4_125 _ hm
  · exact checked4_126 _ hm
  · exact checked4_128 _ hm
  · exact checked4_129 _ hm
  · exact checked4_130 _ hm
  · exact checked4_131 _ hm
private def chunk5_327 : List (List T) := [[wire32,wire240,wire4369,wire17476,wire65520],
  [wire32,wire240,wire4369,wire20292,wire61440],
  [wire32,wire240,wire8738,wire17487,wire34952],
  [wire32,wire3840,wire4593,wire17476,wire61440]]
private def pool5_327 : List (List (List T)) := [chunk4_101, chunk4_102, chunk4_103, chunk4_131, chunk4_132, chunk4_147, chunk4_148, chunk4_149, chunk4_195, chunk4_201]
private theorem checked5_327 : ∀ w ∈ chunk5_327, ¬ Need 5 w.toFinset := by
  have h : chunk5_327.all (routes 4 pool5_327.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_327,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_101 _ hm
  · exact checked4_102 _ hm
  · exact checked4_103 _ hm
  · exact checked4_131 _ hm
  · exact checked4_132 _ hm
  · exact checked4_147 _ hm
  · exact checked4_148 _ hm
  · exact checked4_149 _ hm
  · exact checked4_195 _ hm
  · exact checked4_201 _ hm
private def chunk5_328 : List (List T) := [[wire34,wire240,wire255,wire4369,wire17476],
  [wire34,wire240,wire255,wire4369,wire34952],
  [wire47,wire240,wire3840,wire4369,wire17476],
  [wire47,wire240,wire4369,wire8738,wire17476]]
private def pool5_328 : List (List (List T)) := [chunk4_103, chunk4_104, chunk4_107, chunk4_172]
private theorem checked5_328 : ∀ w ∈ chunk5_328, ¬ Need 5 w.toFinset := by
  have h : chunk5_328.all (routes 4 pool5_328.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_328,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_103 _ hm
  · exact checked4_104 _ hm
  · exact checked4_107 _ hm
  · exact checked4_172 _ hm
private def chunk5_329 : List (List T) := [[wire47,wire240,wire4369,wire8738,wire34952],
  [wire47,wire240,wire4369,wire17476],
  [wire47,wire240,wire4369,wire17476,wire34952],
  [wire47,wire240,wire4369,wire17476,wire61440]]
private def pool5_329 : List (List (List T)) := [chunk4_103, chunk4_104, chunk4_105, chunk4_106, chunk4_107, chunk4_128, chunk4_129]
private theorem checked5_329 : ∀ w ∈ chunk5_329, ¬ Need 5 w.toFinset := by
  have h : chunk5_329.all (routes 4 pool5_329.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_329,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_103 _ hm
  · exact checked4_104 _ hm
  · exact checked4_105 _ hm
  · exact checked4_106 _ hm
  · exact checked4_107 _ hm
  · exact checked4_128 _ hm
  · exact checked4_129 _ hm
private def chunk5_330 : List (List T) := [[wire47,wire240,wire8738,wire17476,wire34952],
  [wire47,wire3840,wire4369,wire17476,wire61440],
  [wire64,wire240,wire8738,wire17487,wire34952],
  [wire68,wire240,wire255,wire4369,wire8738]]
private def pool5_330 : List (List (List T)) := [chunk4_106, chunk4_107, chunk4_108, chunk4_109, chunk4_147, chunk4_148, chunk4_149, chunk4_153]
private theorem checked5_330 : ∀ w ∈ chunk5_330, ¬ Need 5 w.toFinset := by
  have h : chunk5_330.all (routes 4 pool5_330.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_330,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_106 _ hm
  · exact checked4_107 _ hm
  · exact checked4_108 _ hm
  · exact checked4_109 _ hm
  · exact checked4_147 _ hm
  · exact checked4_148 _ hm
  · exact checked4_149 _ hm
  · exact checked4_153 _ hm
private def chunk5_331 : List (List T) := [[wire68,wire240,wire255,wire4369,wire34952],
  [wire79,wire240,wire4369,wire8738,wire17476],
  [wire79,wire240,wire4369,wire8738,wire34952],
  [wire79,wire240,wire4369,wire17476,wire34952]]
private def pool5_331 : List (List (List T)) := [chunk4_109]
private theorem checked5_331 : ∀ w ∈ chunk5_331, ¬ Need 5 w.toFinset := by
  have h : chunk5_331.all (routes 4 pool5_331.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_331,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_109 _ hm
private def chunk5_332 : List (List T) := [[wire79,wire240,wire8738,wire17476,wire34952],
  [wire128,wire143,wire240,wire4369,wire17476],
  [wire128,wire240,wire255,wire4369,wire17476],
  [wire128,wire240,wire3840,wire4369,wire62532]]
private def pool5_332 : List (List (List T)) := [chunk4_110, chunk4_112, chunk4_114, chunk4_115, chunk4_116, chunk4_122, chunk4_125, chunk4_126, chunk4_147]
private theorem checked5_332 : ∀ w ∈ chunk5_332, ¬ Need 5 w.toFinset := by
  have h : chunk5_332.all (routes 4 pool5_332.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_332,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_110 _ hm
  · exact checked4_112 _ hm
  · exact checked4_114 _ hm
  · exact checked4_115 _ hm
  · exact checked4_116 _ hm
  · exact checked4_122 _ hm
  · exact checked4_125 _ hm
  · exact checked4_126 _ hm
  · exact checked4_147 _ hm
private def chunk5_333 : List (List T) := [[wire128,wire240,wire4369,wire17476,wire17487],
  [wire128,wire240,wire4369,wire17476,wire65280],
  [wire128,wire240,wire4369,wire17476,wire65520],
  [wire128,wire240,wire4369,wire20292,wire61440]]
private def pool5_333 : List (List (List T)) := [chunk4_112, chunk4_128, chunk4_129, chunk4_130, chunk4_131, chunk4_144, chunk4_145]
private theorem checked5_333 : ∀ w ∈ chunk5_333, ¬ Need 5 w.toFinset := by
  have h : chunk5_333.all (routes 4 pool5_333.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_333,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_112 _ hm
  · exact checked4_128 _ hm
  · exact checked4_129 _ hm
  · exact checked4_130 _ hm
  · exact checked4_131 _ hm
  · exact checked4_144 _ hm
  · exact checked4_145 _ hm
private def chunk5_334 : List (List T) := [[wire128,wire240,wire8738,wire17487,wire34952],
  [wire136,wire240,wire255,wire4369,wire8738],
  [wire136,wire240,wire255,wire4369,wire17476],
  [wire143,wire240,wire3840,wire4369,wire17476]]
private def pool5_334 : List (List (List T)) := [chunk4_112, chunk4_113, chunk4_114, chunk4_115, chunk4_147, chunk4_150, chunk4_153]
private theorem checked5_334 : ∀ w ∈ chunk5_334, ¬ Need 5 w.toFinset := by
  have h : chunk5_334.all (routes 4 pool5_334.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_334,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_112 _ hm
  · exact checked4_113 _ hm
  · exact checked4_114 _ hm
  · exact checked4_115 _ hm
  · exact checked4_147 _ hm
  · exact checked4_150 _ hm
  · exact checked4_153 _ hm
private def chunk5_335 : List (List T) := [[wire143,wire240,wire4369,wire8738,wire17476],
  [wire143,wire240,wire4369,wire8738,wire34952],
  [wire143,wire240,wire4369,wire17476],
  [wire143,wire240,wire4369,wire17476,wire34952]]
private def pool5_335 : List (List (List T)) := [chunk4_5, chunk4_114, chunk4_115, chunk4_116, chunk4_117, chunk4_128, chunk4_129]
private theorem checked5_335 : ∀ w ∈ chunk5_335, ¬ Need 5 w.toFinset := by
  have h : chunk5_335.all (routes 4 pool5_335.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_335,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_5 _ hm
  · exact checked4_114 _ hm
  · exact checked4_115 _ hm
  · exact checked4_116 _ hm
  · exact checked4_117 _ hm
  · exact checked4_128 _ hm
  · exact checked4_129 _ hm
private def chunk5_336 : List (List T) := [[wire143,wire240,wire4369,wire17476,wire61440],
  [wire143,wire240,wire8738,wire17476,wire34952],
  [wire192,wire3840,wire4369,wire17476,wire61440],
  [wire208,wire3840,wire4369,wire17476,wire61440]]
private def pool5_336 : List (List (List T)) := [chunk4_116, chunk4_117, chunk4_119, chunk4_120, chunk4_150, chunk4_194]
private theorem checked5_336 : ∀ w ∈ chunk5_336, ¬ Need 5 w.toFinset := by
  have h : chunk5_336.all (routes 4 pool5_336.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_336,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_116 _ hm
  · exact checked4_117 _ hm
  · exact checked4_119 _ hm
  · exact checked4_120 _ hm
  · exact checked4_150 _ hm
  · exact checked4_194 _ hm
private def chunk5_337 : List (List T) := [[wire240,wire255,wire4369,wire8738,wire17476],
  [wire240,wire255,wire4369,wire8738,wire20292],
  [wire240,wire255,wire4369,wire8738,wire21845],
  [wire240,wire255,wire4369,wire8738,wire26214]]
private def pool5_337 : List (List (List T)) := [chunk4_122, chunk4_176, chunk4_183]
private theorem checked5_337 : ∀ w ∈ chunk5_337, ¬ Need 5 w.toFinset := by
  have h : chunk5_337.all (routes 4 pool5_337.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_337,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_122 _ hm
  · exact checked4_176 _ hm
  · exact checked4_183 _ hm
private def chunk5_338 : List (List T) := [[wire240,wire255,wire4369,wire8738,wire30583],
  [wire240,wire255,wire4369,wire8738,wire34952],
  [wire240,wire255,wire4369,wire8738,wire36744],
  [wire240,wire255,wire4369,wire8738,wire39321]]
private def pool5_338 : List (List (List T)) := [chunk4_123, chunk4_176, chunk4_177, chunk4_183]
private theorem checked5_338 : ∀ w ∈ chunk5_338, ¬ Need 5 w.toFinset := by
  have h : chunk5_338.all (routes 4 pool5_338.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_338,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_123 _ hm
  · exact checked4_176 _ hm
  · exact checked4_177 _ hm
  · exact checked4_183 _ hm
private def chunk5_339 : List (List T) := [[wire240,wire255,wire4369,wire8738,wire43690],
  [wire240,wire255,wire4369,wire8738,wire48059],
  [wire240,wire255,wire4369,wire8738,wire62532],
  [wire240,wire255,wire4369,wire8738,wire63624]]
private def pool5_339 : List (List (List T)) := [chunk4_118, chunk4_123, chunk4_177, chunk4_184]
private theorem checked5_339 : ∀ w ∈ chunk5_339, ¬ Need 5 w.toFinset := by
  have h : chunk5_339.all (routes 4 pool5_339.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_339,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_118 _ hm
  · exact checked4_123 _ hm
  · exact checked4_177 _ hm
  · exact checked4_184 _ hm
private def chunk5_340 : List (List T) := [[wire240,wire255,wire4369,wire8751,wire17476],
  [wire240,wire255,wire4369,wire8946,wire34952],
  [wire240,wire255,wire4369,wire12066,wire17476],
  [wire240,wire255,wire4369,wire12066,wire34952]]
private def pool5_340 : List (List (List T)) := [chunk4_103, chunk4_174, chunk4_176, chunk4_177, chunk4_184]
private theorem checked5_340 : ∀ w ∈ chunk5_340, ¬ Need 5 w.toFinset := by
  have h : chunk5_340.all (routes 4 pool5_340.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_340,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_103 _ hm
  · exact checked4_174 _ hm
  · exact checked4_176 _ hm
  · exact checked4_177 _ hm
  · exact checked4_184 _ hm
private def chunk5_341 : List (List T) := [[wire240,wire255,wire4369,wire13107,wire17476],
  [wire240,wire255,wire4369,wire13107,wire34952],
  [wire240,wire255,wire4369,wire17476,wire26214],
  [wire240,wire255,wire4369,wire17476,wire30583]]
private def pool5_341 : List (List (List T)) := [chunk4_122, chunk4_123, chunk4_178, chunk4_184]
private theorem checked5_341 : ∀ w ∈ chunk5_341, ¬ Need 5 w.toFinset := by
  have h : chunk5_341.all (routes 4 pool5_341.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_341,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_122 _ hm
  · exact checked4_123 _ hm
  · exact checked4_178 _ hm
  · exact checked4_184 _ hm
private def chunk5_342 : List (List T) := [[wire240,wire255,wire4369,wire17476,wire34952],
  [wire240,wire255,wire4369,wire17476,wire34959],
  [wire240,wire255,wire4369,wire17476,wire36744],
  [wire240,wire255,wire4369,wire17476,wire39321]]
private def pool5_342 : List (List (List T)) := [chunk4_114, chunk4_123, chunk4_179, chunk4_185]
private theorem checked5_342 : ∀ w ∈ chunk5_342, ¬ Need 5 w.toFinset := by
  have h : chunk5_342.all (routes 4 pool5_342.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_342,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_114 _ hm
  · exact checked4_123 _ hm
  · exact checked4_179 _ hm
  · exact checked4_185 _ hm
private def chunk5_343 : List (List T) := [[wire240,wire255,wire4369,wire17476,wire52428],
  [wire240,wire255,wire4369,wire17476,wire56797],
  [wire240,wire255,wire4369,wire17476,wire61986],
  [wire240,wire255,wire4369,wire17476,wire63624]]
private def pool5_343 : List (List (List T)) := [chunk4_118, chunk4_120, chunk4_124, chunk4_185]
private theorem checked5_343 : ∀ w ∈ chunk5_343, ¬ Need 5 w.toFinset := by
  have h : chunk5_343.all (routes 4 pool5_343.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_343,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_118 _ hm
  · exact checked4_120 _ hm
  · exact checked4_124 _ hm
  · exact checked4_185 _ hm
private def chunk5_344 : List (List T) := [[wire240,wire255,wire4369,wire17652,wire34952],
  [wire240,wire255,wire4369,wire20292,wire34952],
  [wire240,wire255,wire4369,wire21845,wire34952],
  [wire240,wire255,wire4369,wire34952,wire43690]]
private def pool5_344 : List (List (List T)) := [chunk4_123, chunk4_124]
private theorem checked5_344 : ∀ w ∈ chunk5_344, ¬ Need 5 w.toFinset := by
  have h : chunk5_344.all (routes 4 pool5_344.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_344,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_123 _ hm
  · exact checked4_124 _ hm
private def chunk5_345 : List (List T) := [[wire240,wire255,wire4369,wire34952,wire48059],
  [wire240,wire255,wire4369,wire34952,wire52428],
  [wire240,wire255,wire4369,wire34952,wire56797],
  [wire240,wire255,wire4369,wire34952,wire61986]]
private def pool5_345 : List (List (List T)) := [chunk4_118, chunk4_125, chunk4_179]
private theorem checked5_345 : ∀ w ∈ chunk5_345, ¬ Need 5 w.toFinset := by
  have h : chunk5_345.all (routes 4 pool5_345.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_345,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_118 _ hm
  · exact checked4_125 _ hm
  · exact checked4_179 _ hm
private def chunk5_346 : List (List T) := [[wire240,wire255,wire4369,wire34952,wire62532],
  [wire240,wire255,wire4383,wire8738,wire34952],
  [wire240,wire255,wire4593,wire8738,wire17476],
  [wire240,wire255,wire8738,wire13107,wire17476]]
private def pool5_346 : List (List (List T)) := [chunk4_101, chunk4_122, chunk4_180, chunk4_183, chunk4_186]
private theorem checked5_346 : ∀ w ∈ chunk5_346, ¬ Need 5 w.toFinset := by
  have h : chunk5_346.all (routes 4 pool5_346.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_346,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_101 _ hm
  · exact checked4_122 _ hm
  · exact checked4_180 _ hm
  · exact checked4_183 _ hm
  · exact checked4_186 _ hm
private def chunk5_347 : List (List T) := [[wire240,wire255,wire8738,wire13107,wire34952],
  [wire240,wire255,wire8738,wire17476,wire21845],
  [wire240,wire255,wire8738,wire17476,wire30583],
  [wire240,wire255,wire8738,wire17476,wire34952]]
private def pool5_347 : List (List (List T)) := [chunk4_123]
private theorem checked5_347 : ∀ w ∈ chunk5_347, ¬ Need 5 w.toFinset := by
  have h : chunk5_347.all (routes 4 pool5_347.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_347,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_123 _ hm
private def chunk5_348 : List (List T) := [[wire240,wire255,wire8738,wire17476,wire35064],
  [wire240,wire255,wire8738,wire17476,wire43690],
  [wire240,wire255,wire8738,wire17476,wire52428],
  [wire240,wire255,wire8738,wire17476,wire61166]]
private def pool5_348 : List (List (List T)) := [chunk4_124]
private theorem checked5_348 : ∀ w ∈ chunk5_348, ¬ Need 5 w.toFinset := by
  have h : chunk5_348.all (routes 4 pool5_348.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_348,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_124 _ hm
private def chunk5_349 : List (List T) := [[wire240,wire255,wire8738,wire17487,wire34952],
  [wire240,wire255,wire8738,wire26214,wire34952],
  [wire240,wire255,wire8738,wire34952,wire39321],
  [wire240,wire255,wire8738,wire34952,wire48059]]
private def pool5_349 : List (List (List T)) := [chunk4_124, chunk4_147, chunk4_186, chunk4_187, chunk4_188]
private theorem checked5_349 : ∀ w ∈ chunk5_349, ¬ Need 5 w.toFinset := by
  have h : chunk5_349.all (routes 4 pool5_349.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_349,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_124 _ hm
  · exact checked4_147 _ hm
  · exact checked4_186 _ hm
  · exact checked4_187 _ hm
  · exact checked4_188 _ hm
private def chunk5_350 : List (List T) := [[wire240,wire255,wire8738,wire34952,wire52428],
  [wire240,wire255,wire8738,wire34952,wire61166],
  [wire240,wire255,wire17476,wire21845,wire34952],
  [wire240,wire255,wire17476,wire26214,wire34952]]
private def pool5_350 : List (List (List T)) := [chunk4_124, chunk4_125, chunk4_188]
private theorem checked5_350 : ∀ w ∈ chunk5_350, ¬ Need 5 w.toFinset := by
  have h : chunk5_350.all (routes 4 pool5_350.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_350,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_124 _ hm
  · exact checked4_125 _ hm
  · exact checked4_188 _ hm
private def chunk5_351 : List (List T) := [[wire240,wire255,wire17476,wire34952,wire39321],
  [wire240,wire255,wire17476,wire34952,wire43690],
  [wire240,wire255,wire17476,wire34952,wire56797],
  [wire240,wire255,wire17476,wire34952,wire61166]]
private def pool5_351 : List (List (List T)) := [chunk4_125]
private theorem checked5_351 : ∀ w ∈ chunk5_351, ¬ Need 5 w.toFinset := by
  have h : chunk5_351.all (routes 4 pool5_351.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_351,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_125 _ hm
private def chunk5_352 : List (List T) := [[wire240,wire256,wire8738,wire17487,wire34952],
  [wire240,wire512,wire8738,wire17487,wire34952],
  [wire240,wire1024,wire8738,wire17487,wire34952],
  [wire240,wire1039,wire4369,wire8738,wire17476]]
private def pool5_352 : List (List (List T)) := [chunk4_147, chunk4_148, chunk4_188, chunk4_189]
private theorem checked5_352 : ∀ w ∈ chunk5_352, ¬ Need 5 w.toFinset := by
  have h : chunk5_352.all (routes 4 pool5_352.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_352,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_148 _ hm
  · exact checked4_188 _ hm
  · exact checked4_189 _ hm
private def chunk5_353 : List (List T) := [[wire240,wire1039,wire4369,wire8738,wire34952],
  [wire240,wire1039,wire4369,wire17476,wire34952],
  [wire240,wire1039,wire8738,wire17476,wire34952],
  [wire240,wire2048,wire8738,wire17487,wire34952]]
private def pool5_353 : List (List (List T)) := [chunk4_147, chunk4_153, chunk4_189, chunk4_190]
private theorem checked5_353 : ∀ w ∈ chunk5_353, ¬ Need 5 w.toFinset := by
  have h : chunk5_353.all (routes 4 pool5_353.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_353,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_153 _ hm
  · exact checked4_189 _ hm
  · exact checked4_190 _ hm
private def chunk5_354 : List (List T) := [[wire240,wire3003,wire3840,wire4369,wire8738],
  [wire240,wire3003,wire3840,wire4369,wire34952],
  [wire240,wire3840,wire4369,wire8738,wire62532],
  [wire240,wire3840,wire4369,wire8738,wire65348]]
private def pool5_354 : List (List (List T)) := [chunk4_126, chunk4_128, chunk4_190, chunk4_194]
private theorem checked5_354 : ∀ w ∈ chunk5_354, ¬ Need 5 w.toFinset := by
  have h : chunk5_354.all (routes 4 pool5_354.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_354,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_126 _ hm
  · exact checked4_128 _ hm
  · exact checked4_190 _ hm
  · exact checked4_194 _ hm
private def chunk5_355 : List (List T) := [[wire240,wire3840,wire4369,wire8751,wire62532],
  [wire240,wire3840,wire4369,wire12066,wire62532],
  [wire240,wire3840,wire4369,wire13107,wire62532],
  [wire240,wire3840,wire4369,wire17476,wire61472]]
private def pool5_355 : List (List (List T)) := [chunk4_125, chunk4_127, chunk4_128, chunk4_129, chunk4_131, chunk4_195]
private theorem checked5_355 : ∀ w ∈ chunk5_355, ¬ Need 5 w.toFinset := by
  have h : chunk5_355.all (routes 4 pool5_355.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_355,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_125 _ hm
  · exact checked4_127 _ hm
  · exact checked4_128 _ hm
  · exact checked4_129 _ hm
  · exact checked4_131 _ hm
  · exact checked4_195 _ hm
private def chunk5_356 : List (List T) := [[wire240,wire3840,wire4369,wire17476,wire61568],
  [wire240,wire3840,wire4369,wire17508,wire61440],
  [wire240,wire3840,wire4369,wire26214,wire62532],
  [wire240,wire3840,wire4369,wire30583,wire62532]]
private def pool5_356 : List (List (List T)) := [chunk4_125, chunk4_129, chunk4_131, chunk4_132, chunk4_133, chunk4_195]
private theorem checked5_356 : ∀ w ∈ chunk5_356, ¬ Need 5 w.toFinset := by
  have h : chunk5_356.all (routes 4 pool5_356.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_356,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_125 _ hm
  · exact checked4_129 _ hm
  · exact checked4_131 _ hm
  · exact checked4_132 _ hm
  · exact checked4_133 _ hm
  · exact checked4_195 _ hm
private def chunk5_357 : List (List T) := [[wire240,wire3840,wire4369,wire34952,wire61444],
  [wire240,wire3840,wire4369,wire34952,wire62532],
  [wire240,wire3840,wire4369,wire34952,wire62708],
  [wire240,wire3840,wire4369,wire34952,wire65348]]
private def pool5_357 : List (List (List T)) := [chunk4_113, chunk4_134, chunk4_135]
private theorem checked5_357 : ∀ w ∈ chunk5_357, ¬ Need 5 w.toFinset := by
  have h : chunk5_357.all (routes 4 pool5_357.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_357,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_113 _ hm
  · exact checked4_134 _ hm
  · exact checked4_135 _ hm
private def chunk5_358 : List (List T) := [[wire240,wire3840,wire4369,wire34952,wire65524],
  [wire240,wire3840,wire4369,wire34954,wire61440],
  [wire240,wire3840,wire4369,wire34959,wire62532],
  [wire240,wire3840,wire4369,wire36744,wire62532]]
private def pool5_358 : List (List (List T)) := [chunk4_134, chunk4_135, chunk4_136, chunk4_201]
private theorem checked5_358 : ∀ w ∈ chunk5_358, ¬ Need 5 w.toFinset := by
  have h : chunk5_358.all (routes 4 pool5_358.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_358,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_134 _ hm
  · exact checked4_135 _ hm
  · exact checked4_136 _ hm
  · exact checked4_201 _ hm
private def chunk5_359 : List (List T) := [[wire240,wire3840,wire4369,wire39321,wire62532],
  [wire240,wire3840,wire4369,wire52428,wire62532],
  [wire240,wire3840,wire4369,wire56797,wire62532],
  [wire240,wire3840,wire4369,wire61986,wire62532]]
private def pool5_359 : List (List (List T)) := [chunk4_119, chunk4_120, chunk4_136, chunk4_137, chunk4_196]
private theorem checked5_359 : ∀ w ∈ chunk5_359, ¬ Need 5 w.toFinset := by
  have h : chunk5_359.all (routes 4 pool5_359.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_359,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_119 _ hm
  · exact checked4_120 _ hm
  · exact checked4_136 _ hm
  · exact checked4_137 _ hm
  · exact checked4_196 _ hm
private def chunk5_360 : List (List T) := [[wire240,wire3840,wire4369,wire61986,wire63624],
  [wire240,wire3840,wire4369,wire62532,wire63078],
  [wire240,wire3840,wire4369,wire62532,wire63624],
  [wire240,wire3840,wire4369,wire62532,wire64716]]
private def pool5_360 : List (List (List T)) := [chunk4_119, chunk4_137, chunk4_138, chunk4_190, chunk4_196]
private theorem checked5_360 : ∀ w ∈ chunk5_360, ¬ Need 5 w.toFinset := by
  have h : chunk5_360.all (routes 4 pool5_360.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_360,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_119 _ hm
  · exact checked4_137 _ hm
  · exact checked4_138 _ hm
  · exact checked4_190 _ hm
  · exact checked4_196 _ hm
private def chunk5_361 : List (List T) := [[wire240,wire3840,wire4373,wire34952,wire61440],
  [wire240,wire3840,wire4383,wire8738,wire17476,wire63624],
  [wire240,wire3840,wire4383,wire8738,wire63624],
  [wire240,wire3840,wire4383,wire17476,wire34952,wire61986]]
private def pool5_361 : List (List (List T)) := [chunk4_113, chunk4_140, chunk4_141, chunk4_142]
private theorem checked5_361 : ∀ w ∈ chunk5_361, ¬ Need 5 w.toFinset := by
  have h : chunk5_361.all (routes 4 pool5_361.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_361,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_113 _ hm
  · exact checked4_140 _ hm
  · exact checked4_141 _ hm
  · exact checked4_142 _ hm
private def chunk5_362 : List (List T) := [[wire240,wire3840,wire4383,wire34952,wire61986],
  [wire240,wire3840,wire4497,wire17476,wire61440],
  [wire240,wire3840,wire4593,wire8738,wire62532],
  [wire240,wire3840,wire8738,wire13107,wire62532]]
private def pool5_362 : List (List (List T)) := [chunk4_102, chunk4_125, chunk4_143, chunk4_144, chunk4_145, chunk4_194, chunk4_197]
private theorem checked5_362 : ∀ w ∈ chunk5_362, ¬ Need 5 w.toFinset := by
  have h : chunk5_362.all (routes 4 pool5_362.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_362,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_102 _ hm
  · exact checked4_125 _ hm
  · exact checked4_143 _ hm
  · exact checked4_144 _ hm
  · exact checked4_145 _ hm
  · exact checked4_194 _ hm
  · exact checked4_197 _ hm
private def chunk5_363 : List (List T) := [[wire240,wire3840,wire8738,wire17487,wire21845],
  [wire240,wire3840,wire8738,wire17487,wire30583],
  [wire240,wire3840,wire8738,wire17487,wire34952],
  [wire240,wire3840,wire8738,wire17487,wire35064]]
private def pool5_363 : List (List (List T)) := [chunk4_0, chunk4_154, chunk4_197, chunk4_201]
private theorem checked5_363 : ∀ w ∈ chunk5_363, ¬ Need 5 w.toFinset := by
  have h : chunk5_363.all (routes 4 pool5_363.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_363,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_154 _ hm
  · exact checked4_197 _ hm
  · exact checked4_201 _ hm
private def chunk5_364 : List (List T) := [[wire240,wire3840,wire8738,wire17487,wire43690],
  [wire240,wire3840,wire8738,wire34952,wire48048],
  [wire240,wire3840,wire8738,wire52428,wire62532],
  [wire240,wire3840,wire8738,wire61166,wire62532]]
private def pool5_364 : List (List (List T)) := [chunk4_151, chunk4_154, chunk4_198]
private theorem checked5_364 : ∀ w ∈ chunk5_364, ¬ Need 5 w.toFinset := by
  have h : chunk5_364.all (routes 4 pool5_364.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_364,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_151 _ hm
  · exact checked4_154 _ hm
  · exact checked4_198 _ hm
private def chunk5_365 : List (List T) := [[wire240,wire3840,wire13107,wire21845,wire61440],
  [wire240,wire3840,wire13107,wire26214,wire61440],
  [wire240,wire3840,wire13107,wire39321,wire61440],
  [wire240,wire3840,wire13107,wire43690,wire61440]]
private def pool5_365 : List (List (List T)) := [chunk4_155, chunk4_156, chunk4_157, chunk4_199]
private theorem checked5_365 : ∀ w ∈ chunk5_365, ¬ Need 5 w.toFinset := by
  have h : chunk5_365.all (routes 4 pool5_365.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_365,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_155 _ hm
  · exact checked4_156 _ hm
  · exact checked4_157 _ hm
  · exact checked4_199 _ hm
private def chunk5_366 : List (List T) := [[wire240,wire3840,wire17487,wire21845,wire34952],
  [wire240,wire3840,wire17487,wire34952,wire43690],
  [wire240,wire3840,wire17487,wire34952,wire56797],
  [wire240,wire3840,wire21845,wire26214,wire61440]]
private def pool5_366 : List (List (List T)) := [chunk4_158, chunk4_163, chunk4_165, chunk4_200]
private theorem checked5_366 : ∀ w ∈ chunk5_366, ¬ Need 5 w.toFinset := by
  have h : chunk5_366.all (routes 4 pool5_366.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_366,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_158 _ hm
  · exact checked4_163 _ hm
  · exact checked4_165 _ hm
  · exact checked4_200 _ hm
private def chunk5_367 : List (List T) := [[wire240,wire3840,wire21845,wire39321,wire61440],
  [wire240,wire3840,wire21845,wire52428,wire61440],
  [wire240,wire3840,wire26214,wire34952,wire62532],
  [wire240,wire3840,wire26214,wire43690,wire61440]]
private def pool5_367 : List (List (List T)) := [chunk4_165, chunk4_166, chunk4_167]
private theorem checked5_367 : ∀ w ∈ chunk5_367, ¬ Need 5 w.toFinset := by
  have h : chunk5_367.all (routes 4 pool5_367.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_367,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_165 _ hm
  · exact checked4_166 _ hm
  · exact checked4_167 _ hm
private def chunk5_368 : List (List T) := [[wire240,wire3840,wire26214,wire52428,wire61440],
  [wire240,wire3840,wire34952,wire39321,wire62532],
  [wire240,wire3840,wire34952,wire61166,wire62532],
  [wire240,wire3840,wire39321,wire43690,wire61440]]
private def pool5_368 : List (List (List T)) := [chunk4_168, chunk4_169, chunk4_170]
private theorem checked5_368 : ∀ w ∈ chunk5_368, ¬ Need 5 w.toFinset := by
  have h : chunk5_368.all (routes 4 pool5_368.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_368,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_168 _ hm
  · exact checked4_169 _ hm
  · exact checked4_170 _ hm
private def chunk5_369 : List (List T) := [[wire240,wire3840,wire39321,wire52428,wire61440],
  [wire240,wire3840,wire43690,wire52428,wire61440],
  [wire240,wire3844,wire4369,wire34952,wire61440],
  [wire240,wire3855,wire4369,wire8738,wire20292]]
private def pool5_369 : List (List (List T)) := [chunk4_113, chunk4_134, chunk4_170, chunk4_171]
private theorem checked5_369 : ∀ w ∈ chunk5_369, ¬ Need 5 w.toFinset := by
  have h : chunk5_369.all (routes 4 pool5_369.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_369,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_113 _ hm
  · exact checked4_134 _ hm
  · exact checked4_170 _ hm
  · exact checked4_171 _ hm
private def chunk5_370 : List (List T) := [[wire240,wire3855,wire4369,wire20292,wire34952],
  [wire240,wire3855,wire8738,wire17487,wire34952],
  [wire240,wire3872,wire4369,wire17476,wire61440],
  [wire240,wire3968,wire4369,wire17476,wire61440]]
private def pool5_370 : List (List (List T)) := [chunk4_126, chunk4_129, chunk4_132, chunk4_201]
private theorem checked5_370 : ∀ w ∈ chunk5_370, ¬ Need 5 w.toFinset := by
  have h : chunk5_370.all (routes 4 pool5_370.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_370,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_126 _ hm
  · exact checked4_129 _ hm
  · exact checked4_132 _ hm
  · exact checked4_201 _ hm
private def chunk5_371 : List (List T) := [[wire240,wire4080,wire4369,wire8738,wire62532],
  [wire240,wire4080,wire4369,wire34952,wire62532],
  [wire240,wire4080,wire8738,wire17487,wire34952],
  [wire240,wire4095,wire4369,wire8738,wire20292]]
private def pool5_371 : List (List (List T)) := [chunk4_134, chunk4_147, chunk4_201, chunk4_202]
private theorem checked5_371 : ∀ w ∈ chunk5_371, ¬ Need 5 w.toFinset := by
  have h : chunk5_371.all (routes 4 pool5_371.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_371,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_134 _ hm
  · exact checked4_147 _ hm
  · exact checked4_201 _ hm
  · exact checked4_202 _ hm
private def chunk5_372 : List (List T) := [[wire240,wire4095,wire4369,wire20292,wire34952],
  [wire240,wire4095,wire8738,wire17487,wire34952],
  [wire240,wire4096,wire8738,wire17487,wire34952],
  [wire240,wire4368,wire8738,wire34952,wire65520]]
private def pool5_372 : List (List (List T)) := [chunk4_147, chunk4_202]
private theorem checked5_372 : ∀ w ∈ chunk5_372, ¬ Need 5 w.toFinset := by
  have h : chunk5_372.all (routes 4 pool5_372.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_372,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_202 _ hm
private def chunk5_373 : List (List T) := [[wire240,wire4369,wire4383,wire8751,wire17476],
  [wire240,wire4369,wire4383,wire17476,wire34959],
  [wire240,wire4369,wire8736,wire17476,wire65520],
  [wire240,wire4369,wire8738,wire16399,wire17476]]
private def pool5_373 : List (List (List T)) := [chunk4_132, chunk4_141, chunk4_143]
private theorem checked5_373 : ∀ w ∈ chunk5_373, ¬ Need 5 w.toFinset := by
  have h : chunk5_373.all (routes 4 pool5_373.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_373,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_132 _ hm
  · exact checked4_141 _ hm
  · exact checked4_143 _ hm
private def chunk5_374 : List (List T) := [[wire240,wire4369,wire8738,wire16399,wire34952],
  [wire240,wire4369,wire8738,wire17476,wire17487],
  [wire240,wire4369,wire8738,wire17476,wire17663],
  [wire240,wire4369,wire8738,wire17476,wire48048]]
private def pool5_374 : List (List (List T)) := [chunk4_145, chunk4_150, chunk4_224]
private theorem checked5_374 : ∀ w ∈ chunk5_374, ¬ Need 5 w.toFinset := by
  have h : chunk5_374.all (routes 4 pool5_374.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_374,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_145 _ hm
  · exact checked4_150 _ hm
  · exact checked4_224 _ hm
private def chunk5_375 : List (List T) := [[wire240,wire4369,wire8738,wire17476,wire65280],
  [wire240,wire4369,wire8738,wire17476,wire65348],
  [wire240,wire4369,wire8738,wire17476,wire65520],
  [wire240,wire4369,wire8738,wire17476,wire65524]]
private def pool5_375 : List (List (List T)) := [chunk4_126, chunk4_132, chunk4_224, chunk4_225]
private theorem checked5_375 : ∀ w ∈ chunk5_375, ¬ Need 5 w.toFinset := by
  have h : chunk5_375.all (routes 4 pool5_375.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_375,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_126 _ hm
  · exact checked4_132 _ hm
  · exact checked4_224 _ hm
  · exact checked4_225 _ hm
private def chunk5_376 : List (List T) := [[wire240,wire4369,wire8738,wire17487,wire17652],
  [wire240,wire4369,wire8738,wire17487,wire20292],
  [wire240,wire4369,wire8738,wire17487,wire21845],
  [wire240,wire4369,wire8738,wire17487,wire26214]]
private def pool5_376 : List (List (List T)) := [chunk4_145, chunk4_146, chunk4_154, chunk4_225]
private theorem checked5_376 : ∀ w ∈ chunk5_376, ¬ Need 5 w.toFinset := by
  have h : chunk5_376.all (routes 4 pool5_376.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_376,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_145 _ hm
  · exact checked4_146 _ hm
  · exact checked4_154 _ hm
  · exact checked4_225 _ hm
private def chunk5_377 : List (List T) := [[wire240,wire4369,wire8738,wire17487,wire30583],
  [wire240,wire4369,wire8738,wire17487,wire34952],
  [wire240,wire4369,wire8738,wire17487,wire34952,wire65280],
  [wire240,wire4369,wire8738,wire17487,wire35064]]
private def pool5_377 : List (List (List T)) := [chunk4_100, chunk4_126, chunk4_146, chunk4_204, chunk4_205, chunk4_225]
private theorem checked5_377 : ∀ w ∈ chunk5_377, ¬ Need 5 w.toFinset := by
  have h : chunk5_377.all (routes 4 pool5_377.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_377,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_100 _ hm
  · exact checked4_126 _ hm
  · exact checked4_146 _ hm
  · exact checked4_204 _ hm
  · exact checked4_205 _ hm
  · exact checked4_225 _ hm
private def chunk5_378 : List (List T) := [[wire240,wire4369,wire8738,wire17487,wire39321],
  [wire240,wire4369,wire8738,wire17487,wire43690],
  [wire240,wire4369,wire8738,wire17487,wire48059],
  [wire240,wire4369,wire8738,wire17487,wire62532]]
private def pool5_378 : List (List (List T)) := [chunk4_155]
private theorem checked5_378 : ∀ w ∈ chunk5_378, ¬ Need 5 w.toFinset := by
  have h : chunk5_378.all (routes 4 pool5_378.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_378,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_155 _ hm
private def chunk5_379 : List (List T) := [[wire240,wire4369,wire8738,wire17663,wire34952],
  [wire240,wire4369,wire8738,wire20292,wire20303],
  [wire240,wire4369,wire8738,wire20292,wire61440],
  [wire240,wire4369,wire8738,wire20292,wire61680]]
private def pool5_379 : List (List (List T)) := [chunk4_126, chunk4_208, chunk4_225]
private theorem checked5_379 : ∀ w ∈ chunk5_379, ¬ Need 5 w.toFinset := by
  have h : chunk5_379.all (routes 4 pool5_379.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_379,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_126 _ hm
  · exact checked4_208 _ hm
  · exact checked4_225 _ hm
private def chunk5_380 : List (List T) := [[wire240,wire4369,wire8738,wire20292,wire62532],
  [wire240,wire4369,wire8738,wire20292,wire65280],
  [wire240,wire4369,wire8738,wire20292,wire65348],
  [wire240,wire4369,wire8738,wire20292,wire65520]]
private def pool5_380 : List (List (List T)) := [chunk4_126, chunk4_133, chunk4_226]
private theorem checked5_380 : ∀ w ∈ chunk5_380, ¬ Need 5 w.toFinset := by
  have h : chunk5_380.all (routes 4 pool5_380.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_380,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_126 _ hm
  · exact checked4_133 _ hm
  · exact checked4_226 _ hm
private def chunk5_381 : List (List T) := [[wire240,wire4369,wire8738,wire21845,wire65280],
  [wire240,wire4369,wire8738,wire21845,wire65520],
  [wire240,wire4369,wire8738,wire26214,wire65280],
  [wire240,wire4369,wire8738,wire26214,wire65520]]
private def pool5_381 : List (List (List T)) := [chunk4_155, chunk4_156, chunk4_208, chunk4_226]
private theorem checked5_381 : ∀ w ∈ chunk5_381, ¬ Need 5 w.toFinset := by
  have h : chunk5_381.all (routes 4 pool5_381.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_381,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_155 _ hm
  · exact checked4_156 _ hm
  · exact checked4_208 _ hm
  · exact checked4_226 _ hm
private def chunk5_382 : List (List T) := [[wire240,wire4369,wire8738,wire30583,wire65280],
  [wire240,wire4369,wire8738,wire30583,wire65520],
  [wire240,wire4369,wire8738,wire34952,wire48048],
  [wire240,wire4369,wire8738,wire34952,wire65280]]
private def pool5_382 : List (List (List T)) := [chunk4_205, chunk4_208]
private theorem checked5_382 : ∀ w ∈ chunk5_382, ¬ Need 5 w.toFinset := by
  have h : chunk5_382.all (routes 4 pool5_382.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_382,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_205 _ hm
  · exact checked4_208 _ hm
private def chunk5_383 : List (List T) := [[wire240,wire4369,wire8738,wire34952,wire65348],
  [wire240,wire4369,wire8738,wire34952,wire65520],
  [wire240,wire4369,wire8738,wire34952,wire65524],
  [wire240,wire4369,wire8738,wire36744,wire65280]]
private def pool5_383 : List (List (List T)) := [chunk4_209, chunk4_227]
private theorem checked5_383 : ∀ w ∈ chunk5_383, ¬ Need 5 w.toFinset := by
  have h : chunk5_383.all (routes 4 pool5_383.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_383,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_209 _ hm
  · exact checked4_227 _ hm
private def chunk5_384 : List (List T) := [[wire240,wire4369,wire8738,wire36744,wire65520],
  [wire240,wire4369,wire8738,wire39321,wire65280],
  [wire240,wire4369,wire8738,wire39321,wire65520],
  [wire240,wire4369,wire8738,wire43690,wire65280]]
private def pool5_384 : List (List (List T)) := [chunk4_156, chunk4_157, chunk4_209, chunk4_227]
private theorem checked5_384 : ∀ w ∈ chunk5_384, ¬ Need 5 w.toFinset := by
  have h : chunk5_384.all (routes 4 pool5_384.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_384,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_156 _ hm
  · exact checked4_157 _ hm
  · exact checked4_209 _ hm
  · exact checked4_227 _ hm
private def chunk5_385 : List (List T) := [[wire240,wire4369,wire8738,wire43690,wire65520],
  [wire240,wire4369,wire8738,wire45243,wire61440],
  [wire240,wire4369,wire8738,wire48059,wire65280],
  [wire240,wire4369,wire8738,wire48059,wire65520]]
private def pool5_385 : List (List (List T)) := [chunk4_157, chunk4_227]
private theorem checked5_385 : ∀ w ∈ chunk5_385, ¬ Need 5 w.toFinset := by
  have h : chunk5_385.all (routes 4 pool5_385.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_385,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_157 _ hm
  · exact checked4_227 _ hm
private def chunk5_386 : List (List T) := [[wire240,wire4369,wire8738,wire61440,wire65348],
  [wire240,wire4369,wire8738,wire61455,wire62532],
  [wire240,wire4369,wire8738,wire61695,wire62532],
  [wire240,wire4369,wire8738,wire62532,wire62543]]
private def pool5_386 : List (List (List T)) := [chunk4_126, chunk4_137, chunk4_228]
private theorem checked5_386 : ∀ w ∈ chunk5_386, ¬ Need 5 w.toFinset := by
  have h : chunk5_386.all (routes 4 pool5_386.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_386,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_126 _ hm
  · exact checked4_137 _ hm
  · exact checked4_228 _ hm
private def chunk5_387 : List (List T) := [[wire240,wire4369,wire8738,wire62532,wire65280],
  [wire240,wire4369,wire8738,wire62532,wire65348],
  [wire240,wire4369,wire8738,wire62532,wire65520],
  [wire240,wire4369,wire8738,wire63624,wire65280]]
private def pool5_387 : List (List (List T)) := [chunk4_126, chunk4_137, chunk4_209, chunk4_228]
private theorem checked5_387 : ∀ w ∈ chunk5_387, ¬ Need 5 w.toFinset := by
  have h : chunk5_387.all (routes 4 pool5_387.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_387,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_126 _ hm
  · exact checked4_137 _ hm
  · exact checked4_209 _ hm
  · exact checked4_228 _ hm
private def chunk5_388 : List (List T) := [[wire240,wire4369,wire8738,wire63624,wire65520],
  [wire240,wire4369,wire8738,wire65280,wire65348],
  [wire240,wire4369,wire8738,wire65280,wire65416],
  [wire240,wire4369,wire8738,wire65348]]
private def pool5_388 : List (List (List T)) := [chunk4_101, chunk4_118, chunk4_126, chunk4_128, chunk4_137, chunk4_138, chunk4_139, chunk4_145, chunk4_151, chunk4_203, chunk4_204, chunk4_205, chunk4_209, chunk4_229]
private theorem checked5_388 : ∀ w ∈ chunk5_388, ¬ Need 5 w.toFinset := by
  have h : chunk5_388.all (routes 4 pool5_388.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_388,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_101 _ hm
  · exact checked4_118 _ hm
  · exact checked4_126 _ hm
  · exact checked4_128 _ hm
  · exact checked4_137 _ hm
  · exact checked4_138 _ hm
  · exact checked4_139 _ hm
  · exact checked4_145 _ hm
  · exact checked4_151 _ hm
  · exact checked4_203 _ hm
  · exact checked4_204 _ hm
  · exact checked4_205 _ hm
  · exact checked4_209 _ hm
  · exact checked4_229 _ hm
private def chunk5_389 : List (List T) := [[wire240,wire4369,wire8751,wire17476,wire17487],
  [wire240,wire4369,wire8751,wire17476,wire34959],
  [wire240,wire4369,wire8751,wire17476,wire65280],
  [wire240,wire4369,wire8751,wire17476,wire65520]]
private def pool5_389 : List (List (List T)) := [chunk4_127, chunk4_152, chunk4_206]
private theorem checked5_389 : ∀ w ∈ chunk5_389, ¬ Need 5 w.toFinset := by
  have h : chunk5_389.all (routes 4 pool5_389.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_389,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_127 _ hm
  · exact checked4_152 _ hm
  · exact checked4_206 _ hm
private def chunk5_390 : List (List T) := [[wire240,wire4369,wire8751,wire20292,wire61440],
  [wire240,wire4369,wire8946,wire17487,wire34952],
  [wire240,wire4369,wire8946,wire34952,wire65280],
  [wire240,wire4369,wire8946,wire34952,wire65520]]
private def pool5_390 : List (List (List T)) := [chunk4_127, chunk4_208]
private theorem checked5_390 : ∀ w ∈ chunk5_390, ¬ Need 5 w.toFinset := by
  have h : chunk5_390.all (routes 4 pool5_390.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_390,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_127 _ hm
  · exact checked4_208 _ hm
private def chunk5_391 : List (List T) := [[wire240,wire4369,wire12066,wire17476,wire17487],
  [wire240,wire4369,wire12066,wire17476,wire65280],
  [wire240,wire4369,wire12066,wire17476,wire65520],
  [wire240,wire4369,wire12066,wire20292,wire61440]]
private def pool5_391 : List (List (List T)) := [chunk4_128, chunk4_154, chunk4_229]
private theorem checked5_391 : ∀ w ∈ chunk5_391, ¬ Need 5 w.toFinset := by
  have h : chunk5_391.all (routes 4 pool5_391.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_391,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_128 _ hm
  · exact checked4_154 _ hm
  · exact checked4_229 _ hm
private def chunk5_392 : List (List T) := [[wire240,wire4369,wire12066,wire34952,wire65280],
  [wire240,wire4369,wire12066,wire34952,wire65520],
  [wire240,wire4369,wire12066,wire36744,wire61440],
  [wire240,wire4369,wire13107,wire17476,wire17487]]
private def pool5_392 : List (List (List T)) := [chunk4_154, chunk4_210]
private theorem checked5_392 : ∀ w ∈ chunk5_392, ¬ Need 5 w.toFinset := by
  have h : chunk5_392.all (routes 4 pool5_392.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_392,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_154 _ hm
  · exact checked4_210 _ hm
private def chunk5_393 : List (List T) := [[wire240,wire4369,wire13107,wire17476,wire65280],
  [wire240,wire4369,wire13107,wire17476,wire65520],
  [wire240,wire4369,wire13107,wire17487,wire34952],
  [wire240,wire4369,wire13107,wire20292,wire61440]]
private def pool5_393 : List (List (List T)) := [chunk4_128, chunk4_155, chunk4_211]
private theorem checked5_393 : ∀ w ∈ chunk5_393, ¬ Need 5 w.toFinset := by
  have h : chunk5_393.all (routes 4 pool5_393.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_393,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_128 _ hm
  · exact checked4_155 _ hm
  · exact checked4_211 _ hm
private def chunk5_394 : List (List T) := [[wire240,wire4369,wire13107,wire34952,wire65280],
  [wire240,wire4369,wire13107,wire34952,wire65520],
  [wire240,wire4369,wire16399,wire17476,wire34952],
  [wire240,wire4369,wire17476,wire17487,wire26214]]
private def pool5_394 : List (List (List T)) := [chunk4_156, chunk4_157, chunk4_211]
private theorem checked5_394 : ∀ w ∈ chunk5_394, ¬ Need 5 w.toFinset := by
  have h : chunk5_394.all (routes 4 pool5_394.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_394,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_156 _ hm
  · exact checked4_157 _ hm
  · exact checked4_211 _ hm
private def chunk5_395 : List (List T) := [[wire240,wire4369,wire17476,wire17487,wire26223],
  [wire240,wire4369,wire17476,wire17487,wire30583],
  [wire240,wire4369,wire17476,wire17487,wire34952],
  [wire240,wire4369,wire17476,wire17487,wire34959]]
private def pool5_395 : List (List (List T)) := [chunk4_110, chunk4_157, chunk4_158]
private theorem checked5_395 : ∀ w ∈ chunk5_395, ¬ Need 5 w.toFinset := by
  have h : chunk5_395.all (routes 4 pool5_395.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_395,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_110 _ hm
  · exact checked4_157 _ hm
  · exact checked4_158 _ hm
private def chunk5_396 : List (List T) := [[wire240,wire4369,wire17476,wire17487,wire36744],
  [wire240,wire4369,wire17476,wire17487,wire39321],
  [wire240,wire4369,wire17476,wire17487,wire52428],
  [wire240,wire4369,wire17476,wire17487,wire52431]]
private def pool5_396 : List (List (List T)) := [chunk4_158, chunk4_159]
private theorem checked5_396 : ∀ w ∈ chunk5_396, ¬ Need 5 w.toFinset := by
  have h : chunk5_396.all (routes 4 pool5_396.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_396,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_158 _ hm
  · exact checked4_159 _ hm
private def chunk5_397 : List (List T) := [[wire240,wire4369,wire17476,wire17487,wire56797],
  [wire240,wire4369,wire17476,wire17487,wire61986],
  [wire240,wire4369,wire17476,wire17487,wire63624],
  [wire240,wire4369,wire17476,wire17663,wire34952]]
private def pool5_397 : List (List (List T)) := [chunk4_159, chunk4_160]
private theorem checked5_397 : ∀ w ∈ chunk5_397, ¬ Need 5 w.toFinset := by
  have h : chunk5_397.all (routes 4 pool5_397.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_397,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_159 _ hm
  · exact checked4_160 _ hm
private def chunk5_398 : List (List T) := [[wire240,wire4369,wire17476,wire26214,wire65280],
  [wire240,wire4369,wire17476,wire26214,wire65520],
  [wire240,wire4369,wire17476,wire30583,wire65280],
  [wire240,wire4369,wire17476,wire30583,wire65520]]
private def pool5_398 : List (List (List T)) := [chunk4_111, chunk4_132, chunk4_133, chunk4_165, chunk4_230]
private theorem checked5_398 : ∀ w ∈ chunk5_398, ¬ Need 5 w.toFinset := by
  have h : chunk5_398.all (routes 4 pool5_398.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_398,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_111 _ hm
  · exact checked4_132 _ hm
  · exact checked4_133 _ hm
  · exact checked4_165 _ hm
  · exact checked4_230 _ hm
private def chunk5_399 : List (List T) := [[wire240,wire4369,wire17476,wire34944,wire65520],
  [wire240,wire4369,wire17476,wire34952,wire48048],
  [wire240,wire4369,wire17476,wire34952,wire65280],
  [wire240,wire4369,wire17476,wire34952,wire65348]]
private def pool5_399 : List (List (List T)) := [chunk4_133, chunk4_134, chunk4_136, chunk4_165]
private theorem checked5_399 : ∀ w ∈ chunk5_399, ¬ Need 5 w.toFinset := by
  have h : chunk5_399.all (routes 4 pool5_399.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_399,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_133 _ hm
  · exact checked4_134 _ hm
  · exact checked4_136 _ hm
  · exact checked4_165 _ hm
private def chunk5_400 : List (List T) := [[wire240,wire4369,wire17476,wire34952,wire65520],
  [wire240,wire4369,wire17476,wire34952,wire65524],
  [wire240,wire4369,wire17476,wire34959,wire65280],
  [wire240,wire4369,wire17476,wire34959,wire65520]]
private def pool5_400 : List (List (List T)) := [chunk4_134, chunk4_135, chunk4_213]
private theorem checked5_400 : ∀ w ∈ chunk5_400, ¬ Need 5 w.toFinset := by
  have h : chunk5_400.all (routes 4 pool5_400.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_400,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_134 _ hm
  · exact checked4_135 _ hm
  · exact checked4_213 _ hm
private def chunk5_401 : List (List T) := [[wire240,wire4369,wire17476,wire36744,wire65280],
  [wire240,wire4369,wire17476,wire36744,wire65520],
  [wire240,wire4369,wire17476,wire39321,wire65280],
  [wire240,wire4369,wire17476,wire39321,wire65520]]
private def pool5_401 : List (List (List T)) := [chunk4_135, chunk4_136, chunk4_165, chunk4_166, chunk4_230]
private theorem checked5_401 : ∀ w ∈ chunk5_401, ¬ Need 5 w.toFinset := by
  have h : chunk5_401.all (routes 4 pool5_401.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_401,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_135 _ hm
  · exact checked4_136 _ hm
  · exact checked4_165 _ hm
  · exact checked4_166 _ hm
  · exact checked4_230 _ hm
private def chunk5_402 : List (List T) := [[wire240,wire4369,wire17476,wire52428,wire65280],
  [wire240,wire4369,wire17476,wire52428,wire65520],
  [wire240,wire4369,wire17476,wire56797,wire65280],
  [wire240,wire4369,wire17476,wire56797,wire65520]]
private def pool5_402 : List (List (List T)) := [chunk4_119, chunk4_120, chunk4_136, chunk4_137, chunk4_166, chunk4_230]
private theorem checked5_402 : ∀ w ∈ chunk5_402, ¬ Need 5 w.toFinset := by
  have h : chunk5_402.all (routes 4 pool5_402.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_402,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_119 _ hm
  · exact checked4_120 _ hm
  · exact checked4_136 _ hm
  · exact checked4_137 _ hm
  · exact checked4_166 _ hm
  · exact checked4_230 _ hm
private def chunk5_403 : List (List T) := [[wire240,wire4369,wire17476,wire61986,wire65280],
  [wire240,wire4369,wire17476,wire61986,wire65520],
  [wire240,wire4369,wire17476,wire63624,wire65280],
  [wire240,wire4369,wire17476,wire63624,wire65520]]
private def pool5_403 : List (List (List T)) := [chunk4_137, chunk4_138, chunk4_230]
private theorem checked5_403 : ∀ w ∈ chunk5_403, ¬ Need 5 w.toFinset := by
  have h : chunk5_403.all (routes 4 pool5_403.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_403,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_137 _ hm
  · exact checked4_138 _ hm
  · exact checked4_230 _ hm
private def chunk5_404 : List (List T) := [[wire240,wire4369,wire17476,wire65280,wire65314],
  [wire240,wire4369,wire17476,wire65280,wire65416],
  [wire240,wire4369,wire17487,wire17652,wire34952],
  [wire240,wire4369,wire17487,wire20292,wire34952]]
private def pool5_404 : List (List (List T)) := [chunk4_138, chunk4_139, chunk4_212, chunk4_231]
private theorem checked5_404 : ∀ w ∈ chunk5_404, ¬ Need 5 w.toFinset := by
  have h : chunk5_404.all (routes 4 pool5_404.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_404,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_138 _ hm
  · exact checked4_139 _ hm
  · exact checked4_212 _ hm
  · exact checked4_231 _ hm
private def chunk5_405 : List (List T) := [[wire240,wire4369,wire17487,wire21845,wire34952],
  [wire240,wire4369,wire17487,wire34952,wire43690],
  [wire240,wire4369,wire17487,wire34952,wire48059],
  [wire240,wire4369,wire17487,wire34952,wire52428]]
private def pool5_405 : List (List (List T)) := [chunk4_7, chunk4_158, chunk4_159, chunk4_162, chunk4_163, chunk4_213]
private theorem checked5_405 : ∀ w ∈ chunk5_405, ¬ Need 5 w.toFinset := by
  have h : chunk5_405.all (routes 4 pool5_405.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_405,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_158 _ hm
  · exact checked4_159 _ hm
  · exact checked4_162 _ hm
  · exact checked4_163 _ hm
  · exact checked4_213 _ hm
private def chunk5_406 : List (List T) := [[wire240,wire4369,wire17487,wire34952,wire56797],
  [wire240,wire4369,wire17487,wire34952,wire62532],
  [wire240,wire4369,wire17652,wire17663,wire34952],
  [wire240,wire4369,wire17652,wire34952,wire65280]]
private def pool5_406 : List (List (List T)) := [chunk4_134, chunk4_162, chunk4_213]
private theorem checked5_406 : ∀ w ∈ chunk5_406, ¬ Need 5 w.toFinset := by
  have h : chunk5_406.all (routes 4 pool5_406.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_406,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_134 _ hm
  · exact checked4_162 _ hm
  · exact checked4_213 _ hm
private def chunk5_407 : List (List T) := [[wire240,wire4369,wire17652,wire34952,wire65520],
  [wire240,wire4369,wire20292,wire20303,wire34952],
  [wire240,wire4369,wire20292,wire26214,wire61440],
  [wire240,wire4369,wire20292,wire28518,wire61440]]
private def pool5_407 : List (List (List T)) := [chunk4_132, chunk4_133, chunk4_134, chunk4_231]
private theorem checked5_407 : ∀ w ∈ chunk5_407, ¬ Need 5 w.toFinset := by
  have h : chunk5_407.all (routes 4 pool5_407.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_407,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_132 _ hm
  · exact checked4_133 _ hm
  · exact checked4_134 _ hm
  · exact checked4_231 _ hm
private def chunk5_408 : List (List T) := [[wire240,wire4369,wire20292,wire30583,wire61440],
  [wire240,wire4369,wire20292,wire34952,wire61440],
  [wire240,wire4369,wire20292,wire34952,wire61680],
  [wire240,wire4369,wire20292,wire34952,wire62532]]
private def pool5_408 : List (List (List T)) := [chunk4_133, chunk4_134]
private theorem checked5_408 : ∀ w ∈ chunk5_408, ¬ Need 5 w.toFinset := by
  have h : chunk5_408.all (routes 4 pool5_408.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_408,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_133 _ hm
  · exact checked4_134 _ hm
private def chunk5_409 : List (List T) := [[wire240,wire4369,wire20292,wire34952,wire65280],
  [wire240,wire4369,wire20292,wire34952,wire65348],
  [wire240,wire4369,wire20292,wire34952,wire65520],
  [wire240,wire4369,wire20292,wire34959,wire61440]]
private def pool5_409 : List (List (List T)) := [chunk4_134, chunk4_135, chunk4_137]
private theorem checked5_409 : ∀ w ∈ chunk5_409, ¬ Need 5 w.toFinset := by
  have h : chunk5_409.all (routes 4 pool5_409.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_409,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_134 _ hm
  · exact checked4_135 _ hm
  · exact checked4_137 _ hm
private def chunk5_410 : List (List T) := [[wire240,wire4369,wire20292,wire36744,wire61440],
  [wire240,wire4369,wire20292,wire39321,wire61440],
  [wire240,wire4369,wire20292,wire52428,wire61440],
  [wire240,wire4369,wire20292,wire53196,wire61440]]
private def pool5_410 : List (List (List T)) := [chunk4_119, chunk4_135, chunk4_136, chunk4_137, chunk4_231]
private theorem checked5_410 : ∀ w ∈ chunk5_410, ¬ Need 5 w.toFinset := by
  have h : chunk5_410.all (routes 4 pool5_410.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_410,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_119 _ hm
  · exact checked4_135 _ hm
  · exact checked4_136 _ hm
  · exact checked4_137 _ hm
  · exact checked4_231 _ hm
private def chunk5_411 : List (List T) := [[wire240,wire4369,wire20292,wire56797,wire61440],
  [wire240,wire4369,wire20292,wire61440,wire61986],
  [wire240,wire4369,wire20292,wire61440,wire63624],
  [wire240,wire4369,wire20468,wire34952,wire61440]]
private def pool5_411 : List (List (List T)) := [chunk4_120, chunk4_134, chunk4_137, chunk4_138, chunk4_214, chunk4_232]
private theorem checked5_411 : ∀ w ∈ chunk5_411, ¬ Need 5 w.toFinset := by
  have h : chunk5_411.all (routes 4 pool5_411.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_411,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_120 _ hm
  · exact checked4_134 _ hm
  · exact checked4_137 _ hm
  · exact checked4_138 _ hm
  · exact checked4_214 _ hm
  · exact checked4_232 _ hm
private def chunk5_412 : List (List T) := [[wire240,wire4369,wire21845,wire34952,wire65280],
  [wire240,wire4369,wire21845,wire34952,wire65520],
  [wire240,wire4369,wire34952,wire43690,wire65280],
  [wire240,wire4369,wire34952,wire43690,wire65520]]
private def pool5_412 : List (List (List T)) := [chunk4_165, chunk4_166, chunk4_170]
private theorem checked5_412 : ∀ w ∈ chunk5_412, ¬ Need 5 w.toFinset := by
  have h : chunk5_412.all (routes 4 pool5_412.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_412,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_165 _ hm
  · exact checked4_166 _ hm
  · exact checked4_170 _ hm
private def chunk5_413 : List (List T) := [[wire240,wire4369,wire34952,wire45243,wire61440],
  [wire240,wire4369,wire34952,wire48059,wire65280],
  [wire240,wire4369,wire34952,wire48059,wire65520],
  [wire240,wire4369,wire34952,wire52428,wire65280]]
private def pool5_413 : List (List (List T)) := [chunk4_170]
private theorem checked5_413 : ∀ w ∈ chunk5_413, ¬ Need 5 w.toFinset := by
  have h : chunk5_413.all (routes 4 pool5_413.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_413,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_170 _ hm
private def chunk5_414 : List (List T) := [[wire240,wire4369,wire34952,wire52428,wire65520],
  [wire240,wire4369,wire34952,wire56797,wire65280],
  [wire240,wire4369,wire34952,wire56797,wire65520],
  [wire240,wire4369,wire34952,wire61440,wire65348]]
private def pool5_414 : List (List (List T)) := [chunk4_134, chunk4_138, chunk4_170]
private theorem checked5_414 : ∀ w ∈ chunk5_414, ¬ Need 5 w.toFinset := by
  have h : chunk5_414.all (routes 4 pool5_414.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_414,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_134 _ hm
  · exact checked4_138 _ hm
  · exact checked4_170 _ hm
private def chunk5_415 : List (List T) := [[wire240,wire4369,wire34952,wire61440,wire65524],
  [wire240,wire4369,wire34952,wire61455,wire62532],
  [wire240,wire4369,wire34952,wire61695,wire62532],
  [wire240,wire4369,wire34952,wire61986,wire65280]]
private def pool5_415 : List (List (List T)) := [chunk4_134, chunk4_138, chunk4_215]
private theorem checked5_415 : ∀ w ∈ chunk5_415, ¬ Need 5 w.toFinset := by
  have h : chunk5_415.all (routes 4 pool5_415.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_415,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_134 _ hm
  · exact checked4_138 _ hm
  · exact checked4_215 _ hm
private def chunk5_416 : List (List T) := [[wire240,wire4369,wire34952,wire61986,wire65520],
  [wire240,wire4369,wire34952,wire62532,wire62543],
  [wire240,wire4369,wire34952,wire62532,wire65280],
  [wire240,wire4369,wire34952,wire62532,wire65348]]
private def pool5_416 : List (List (List T)) := [chunk4_134, chunk4_138]
private theorem checked5_416 : ∀ w ∈ chunk5_416, ¬ Need 5 w.toFinset := by
  have h : chunk5_416.all (routes 4 pool5_416.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_416,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_134 _ hm
  · exact checked4_138 _ hm
private def chunk5_417 : List (List T) := [[wire240,wire4369,wire34952,wire62532,wire65520],
  [wire240,wire4369,wire34952,wire65280,wire65314],
  [wire240,wire4369,wire34952,wire65280,wire65348],
  [wire240,wire4369,wire34952,wire65348]]
private def pool5_417 : List (List (List T)) := [chunk4_112, chunk4_118, chunk4_133, chunk4_134, chunk4_136, chunk4_139, chunk4_168, chunk4_169, chunk4_203, chunk4_215]
private theorem checked5_417 : ∀ w ∈ chunk5_417, ¬ Need 5 w.toFinset := by
  have h : chunk5_417.all (routes 4 pool5_417.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_417,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_112 _ hm
  · exact checked4_118 _ hm
  · exact checked4_133 _ hm
  · exact checked4_134 _ hm
  · exact checked4_136 _ hm
  · exact checked4_139 _ hm
  · exact checked4_168 _ hm
  · exact checked4_169 _ hm
  · exact checked4_203 _ hm
  · exact checked4_215 _ hm
private def chunk5_418 : List (List T) := [[wire240,wire4369,wire34952,wire65520,wire65522],
  [wire240,wire4369,wire34952,wire65520,wire65524],
  [wire240,wire4369,wire34952,wire65524],
  [wire240,wire4383,wire8738,wire8751,wire34952]]
private def pool5_418 : List (List (List T)) := [chunk4_7, chunk4_112, chunk4_133, chunk4_134, chunk4_136, chunk4_141, chunk4_168, chunk4_169, chunk4_214, chunk4_215]
private theorem checked5_418 : ∀ w ∈ chunk5_418, ¬ Need 5 w.toFinset := by
  have h : chunk5_418.all (routes 4 pool5_418.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_418,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_7 _ hm
  · exact checked4_112 _ hm
  · exact checked4_133 _ hm
  · exact checked4_134 _ hm
  · exact checked4_136 _ hm
  · exact checked4_141 _ hm
  · exact checked4_168 _ hm
  · exact checked4_169 _ hm
  · exact checked4_214 _ hm
  · exact checked4_215 _ hm
private def chunk5_419 : List (List T) := [[wire240,wire4383,wire8738,wire17476,wire34952,wire65280],
  [wire240,wire4383,wire8738,wire17476,wire36744,wire61440],
  [wire240,wire4383,wire8738,wire17487,wire34952],
  [wire240,wire4383,wire8738,wire34952,wire34959]]
private def pool5_419 : List (List (List T)) := [chunk4_140, chunk4_142, chunk4_143, chunk4_216, chunk4_217, chunk4_218]
private theorem checked5_419 : ∀ w ∈ chunk5_419, ¬ Need 5 w.toFinset := by
  have h : chunk5_419.all (routes 4 pool5_419.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_419,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_140 _ hm
  · exact checked4_142 _ hm
  · exact checked4_143 _ hm
  · exact checked4_216 _ hm
  · exact checked4_217 _ hm
  · exact checked4_218 _ hm
private def chunk5_420 : List (List T) := [[wire240,wire4383,wire8738,wire34952,wire65280],
  [wire240,wire4383,wire8738,wire34952,wire65520],
  [wire240,wire4383,wire8738,wire36744,wire61440],
  [wire240,wire4383,wire12066,wire17476,wire34952,wire61440]]
private def pool5_420 : List (List (List T)) := [chunk4_141, chunk4_142, chunk4_143, chunk4_144]
private theorem checked5_420 : ∀ w ∈ chunk5_420, ¬ Need 5 w.toFinset := by
  have h : chunk5_420.all (routes 4 pool5_420.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_420,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_141 _ hm
  · exact checked4_142 _ hm
  · exact checked4_143 _ hm
  · exact checked4_144 _ hm
private def chunk5_421 : List (List T) := [[wire240,wire4383,wire12066,wire34952,wire61440],
  [wire240,wire4593,wire8738,wire17476,wire17487],
  [wire240,wire4593,wire8738,wire17476,wire65280],
  [wire240,wire4593,wire8738,wire17476,wire65520]]
private def pool5_421 : List (List (List T)) := [chunk4_102, chunk4_142, chunk4_143, chunk4_145, chunk4_146, chunk4_224, chunk4_225]
private theorem checked5_421 : ∀ w ∈ chunk5_421, ¬ Need 5 w.toFinset := by
  have h : chunk5_421.all (routes 4 pool5_421.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_421,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_102 _ hm
  · exact checked4_142 _ hm
  · exact checked4_143 _ hm
  · exact checked4_145 _ hm
  · exact checked4_146 _ hm
  · exact checked4_224 _ hm
  · exact checked4_225 _ hm
private def chunk5_422 : List (List T) := [[wire240,wire4593,wire8738,wire17487,wire34952],
  [wire240,wire4593,wire8738,wire20292,wire61440],
  [wire240,wire7953,wire8738,wire17487,wire34952],
  [wire240,wire8192,wire8738,wire17487,wire34952]]
private def pool5_422 : List (List (List T)) := [chunk4_102, chunk4_145, chunk4_147, chunk4_149, chunk4_225, chunk4_232]
private theorem checked5_422 : ∀ w ∈ chunk5_422, ¬ Need 5 w.toFinset := by
  have h : chunk5_422.all (routes 4 pool5_422.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_422,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_102 _ hm
  · exact checked4_145 _ hm
  · exact checked4_147 _ hm
  · exact checked4_149 _ hm
  · exact checked4_225 _ hm
  · exact checked4_232 _ hm
private def chunk5_423 : List (List T) := [[wire240,wire8738,wire8751,wire17487,wire34952],
  [wire240,wire8738,wire8946,wire17487,wire34952],
  [wire240,wire8738,wire12066,wire17487,wire34952],
  [wire240,wire8738,wire13107,wire17476,wire17487]]
private def pool5_423 : List (List (List T)) := [chunk4_103, chunk4_146, chunk4_147, chunk4_149, chunk4_153, chunk4_154, chunk4_233]
private theorem checked5_423 : ∀ w ∈ chunk5_423, ¬ Need 5 w.toFinset := by
  have h : chunk5_423.all (routes 4 pool5_423.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_423,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_103 _ hm
  · exact checked4_146 _ hm
  · exact checked4_147 _ hm
  · exact checked4_149 _ hm
  · exact checked4_153 _ hm
  · exact checked4_154 _ hm
  · exact checked4_233 _ hm
private def chunk5_424 : List (List T) := [[wire240,wire8738,wire13107,wire17476,wire65280],
  [wire240,wire8738,wire13107,wire17476,wire65520],
  [wire240,wire8738,wire13107,wire17487,wire34952],
  [wire240,wire8738,wire13107,wire20292,wire61440]]
private def pool5_424 : List (List (List T)) := [chunk4_145, chunk4_147, chunk4_155, chunk4_156, chunk4_233, chunk4_234]
private theorem checked5_424 : ∀ w ∈ chunk5_424, ¬ Need 5 w.toFinset := by
  have h : chunk5_424.all (routes 4 pool5_424.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_424,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_145 _ hm
  · exact checked4_147 _ hm
  · exact checked4_155 _ hm
  · exact checked4_156 _ hm
  · exact checked4_233 _ hm
  · exact checked4_234 _ hm
private def chunk5_425 : List (List T) := [[wire240,wire8738,wire13107,wire34952,wire65280],
  [wire240,wire8738,wire13107,wire34952,wire65520],
  [wire240,wire8738,wire16384,wire17487,wire34952],
  [wire240,wire8738,wire16399,wire17476,wire34952]]
private def pool5_425 : List (List (List T)) := [chunk4_147, chunk4_157, chunk4_235]
private theorem checked5_425 : ∀ w ∈ chunk5_425, ¬ Need 5 w.toFinset := by
  have h : chunk5_425.all (routes 4 pool5_425.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_425,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_157 _ hm
  · exact checked4_235 _ hm
private def chunk5_426 : List (List T) := [[wire240,wire8738,wire17472,wire34952,wire65520],
  [wire240,wire8738,wire17476,wire17487,wire21845],
  [wire240,wire8738,wire17476,wire17487,wire30583],
  [wire240,wire8738,wire17476,wire17487,wire34952]]
private def pool5_426 : List (List (List T)) := [chunk4_145, chunk4_146, chunk4_147, chunk4_157, chunk4_166, chunk4_235, chunk4_236]
private theorem checked5_426 : ∀ w ∈ chunk5_426, ¬ Need 5 w.toFinset := by
  have h : chunk5_426.all (routes 4 pool5_426.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_426,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_145 _ hm
  · exact checked4_146 _ hm
  · exact checked4_147 _ hm
  · exact checked4_157 _ hm
  · exact checked4_166 _ hm
  · exact checked4_235 _ hm
  · exact checked4_236 _ hm
private def chunk5_427 : List (List T) := [[wire240,wire8738,wire17476,wire17487,wire35064],
  [wire240,wire8738,wire17476,wire17487,wire43690],
  [wire240,wire8738,wire17476,wire17487,wire52428],
  [wire240,wire8738,wire17476,wire17487,wire61166]]
private def pool5_427 : List (List (List T)) := [chunk4_108, chunk4_148, chunk4_149, chunk4_160, chunk4_236, chunk4_237]
private theorem checked5_427 : ∀ w ∈ chunk5_427, ¬ Need 5 w.toFinset := by
  have h : chunk5_427.all (routes 4 pool5_427.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_427,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_108 _ hm
  · exact checked4_148 _ hm
  · exact checked4_149 _ hm
  · exact checked4_160 _ hm
  · exact checked4_236 _ hm
  · exact checked4_237 _ hm
private def chunk5_428 : List (List T) := [[wire240,wire8738,wire17476,wire17663,wire34952],
  [wire240,wire8738,wire17476,wire21845,wire65280],
  [wire240,wire8738,wire17476,wire21845,wire65520],
  [wire240,wire8738,wire17476,wire30583,wire65280]]
private def pool5_428 : List (List (List T)) := [chunk4_165]
private theorem checked5_428 : ∀ w ∈ chunk5_428, ¬ Need 5 w.toFinset := by
  have h : chunk5_428.all (routes 4 pool5_428.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_428,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_165 _ hm
private def chunk5_429 : List (List T) := [[wire240,wire8738,wire17476,wire30583,wire65520],
  [wire240,wire8738,wire17476,wire34952,wire48048],
  [wire240,wire8738,wire17476,wire34952,wire65280],
  [wire240,wire8738,wire17476,wire34952,wire65348]]
private def pool5_429 : List (List (List T)) := [chunk4_151, chunk4_167, chunk4_236]
private theorem checked5_429 : ∀ w ∈ chunk5_429, ¬ Need 5 w.toFinset := by
  have h : chunk5_429.all (routes 4 pool5_429.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_429,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_151 _ hm
  · exact checked4_167 _ hm
  · exact checked4_236 _ hm
private def chunk5_430 : List (List T) := [[wire240,wire8738,wire17476,wire34952,wire65520],
  [wire240,wire8738,wire17476,wire34952,wire65524],
  [wire240,wire8738,wire17476,wire35064,wire65280],
  [wire240,wire8738,wire17476,wire35064,wire65520]]
private def pool5_430 : List (List (List T)) := [chunk4_167, chunk4_236, chunk4_237]
private theorem checked5_430 : ∀ w ∈ chunk5_430, ¬ Need 5 w.toFinset := by
  have h : chunk5_430.all (routes 4 pool5_430.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_430,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_167 _ hm
  · exact checked4_236 _ hm
  · exact checked4_237 _ hm
private def chunk5_431 : List (List T) := [[wire240,wire8738,wire17476,wire43690,wire65280],
  [wire240,wire8738,wire17476,wire43690,wire65520],
  [wire240,wire8738,wire17476,wire52428,wire65280],
  [wire240,wire8738,wire17476,wire52428,wire65520]]
private def pool5_431 : List (List (List T)) := [chunk4_151, chunk4_167, chunk4_168]
private theorem checked5_431 : ∀ w ∈ chunk5_431, ¬ Need 5 w.toFinset := by
  have h : chunk5_431.all (routes 4 pool5_431.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_431,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_151 _ hm
  · exact checked4_167 _ hm
  · exact checked4_168 _ hm
private def chunk5_432 : List (List T) := [[wire240,wire8738,wire17476,wire61166,wire65280],
  [wire240,wire8738,wire17476,wire61166,wire65520],
  [wire240,wire8738,wire17487,wire17652,wire34952],
  [wire240,wire8738,wire17487,wire17663,wire34952]]
private def pool5_432 : List (List (List T)) := [chunk4_147, chunk4_151, chunk4_237]
private theorem checked5_432 : ∀ w ∈ chunk5_432, ¬ Need 5 w.toFinset := by
  have h : chunk5_432.all (routes 4 pool5_432.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_432,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_151 _ hm
  · exact checked4_237 _ hm
private def chunk5_433 : List (List T) := [[wire240,wire8738,wire17487,wire20292,wire34952],
  [wire240,wire8738,wire17487,wire20303,wire34952],
  [wire240,wire8738,wire17487,wire21845],
  [wire240,wire8738,wire17487,wire21845,wire34952]]
private def pool5_433 : List (List (List T)) := [chunk4_101, chunk4_145, chunk4_146, chunk4_147, chunk4_149, chunk4_150, chunk4_157, chunk4_158, chunk4_159, chunk4_238]
private theorem checked5_433 : ∀ w ∈ chunk5_433, ¬ Need 5 w.toFinset := by
  have h : chunk5_433.all (routes 4 pool5_433.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_433,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_101 _ hm
  · exact checked4_145 _ hm
  · exact checked4_146 _ hm
  · exact checked4_147 _ hm
  · exact checked4_149 _ hm
  · exact checked4_150 _ hm
  · exact checked4_157 _ hm
  · exact checked4_158 _ hm
  · exact checked4_159 _ hm
  · exact checked4_238 _ hm
private def chunk5_434 : List (List T) := [[wire240,wire8738,wire17487,wire21845,wire61440],
  [wire240,wire8738,wire17487,wire21855,wire34952],
  [wire240,wire8738,wire17487,wire26214,wire34952],
  [wire240,wire8738,wire17487,wire26223,wire34952]]
private def pool5_434 : List (List (List T)) := [chunk4_1, chunk4_147, chunk4_160, chunk4_161, chunk4_239]
private theorem checked5_434 : ∀ w ∈ chunk5_434, ¬ Need 5 w.toFinset := by
  have h : chunk5_434.all (routes 4 pool5_434.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_434,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_147 _ hm
  · exact checked4_160 _ hm
  · exact checked4_161 _ hm
  · exact checked4_239 _ hm
private def chunk5_435 : List (List T) := [[wire240,wire8738,wire17487,wire30583],
  [wire240,wire8738,wire17487,wire30583,wire34952],
  [wire240,wire8738,wire17487,wire30583,wire61440],
  [wire240,wire8738,wire17487,wire32768,wire34952]]
private def pool5_435 : List (List (List T)) := [chunk4_111, chunk4_146, chunk4_147, chunk4_150, chunk4_161, chunk4_240, chunk4_241]
private theorem checked5_435 : ∀ w ∈ chunk5_435, ¬ Need 5 w.toFinset := by
  have h : chunk5_435.all (routes 4 pool5_435.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_435,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_111 _ hm
  · exact checked4_146 _ hm
  · exact checked4_147 _ hm
  · exact checked4_150 _ hm
  · exact checked4_161 _ hm
  · exact checked4_240 _ hm
  · exact checked4_241 _ hm
private def chunk5_436 : List (List T) := [[wire240,wire8738,wire17487,wire34952],
  [wire240,wire8738,wire17487,wire34952,wire34959],
  [wire240,wire8738,wire17487,wire34952,wire35064],
  [wire240,wire8738,wire17487,wire34952,wire36744]]
private def pool5_436 : List (List (List T)) := [chunk4_113, chunk4_146, chunk4_147, chunk4_148, chunk4_149, chunk4_150, chunk4_162, chunk4_163, chunk4_242, chunk4_243]
private theorem checked5_436 : ∀ w ∈ chunk5_436, ¬ Need 5 w.toFinset := by
  have h : chunk5_436.all (routes 4 pool5_436.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_436,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_113 _ hm
  · exact checked4_146 _ hm
  · exact checked4_147 _ hm
  · exact checked4_148 _ hm
  · exact checked4_149 _ hm
  · exact checked4_150 _ hm
  · exact checked4_162 _ hm
  · exact checked4_163 _ hm
  · exact checked4_242 _ hm
  · exact checked4_243 _ hm
private def chunk5_437 : List (List T) := [[wire240,wire8738,wire17487,wire34952,wire39321],
  [wire240,wire8738,wire17487,wire34952,wire43690],
  [wire240,wire8738,wire17487,wire34952,wire48048],
  [wire240,wire8738,wire17487,wire34952,wire48059]]
private def pool5_437 : List (List (List T)) := [chunk4_147, chunk4_149, chunk4_150, chunk4_162, chunk4_163, chunk4_244, chunk4_245]
private theorem checked5_437 : ∀ w ∈ chunk5_437, ¬ Need 5 w.toFinset := by
  have h : chunk5_437.all (routes 4 pool5_437.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_437,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_149 _ hm
  · exact checked4_150 _ hm
  · exact checked4_162 _ hm
  · exact checked4_163 _ hm
  · exact checked4_244 _ hm
  · exact checked4_245 _ hm
private def chunk5_438 : List (List T) := [[wire240,wire8738,wire17487,wire34952,wire52428],
  [wire240,wire8738,wire17487,wire34952,wire52431],
  [wire240,wire8738,wire17487,wire34952,wire56797],
  [wire240,wire8738,wire17487,wire34952,wire61166]]
private def pool5_438 : List (List (List T)) := [chunk4_147, chunk4_162, chunk4_163, chunk4_164, chunk4_245, chunk4_246]
private theorem checked5_438 : ∀ w ∈ chunk5_438, ¬ Need 5 w.toFinset := by
  have h : chunk5_438.all (routes 4 pool5_438.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_438,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_162 _ hm
  · exact checked4_163 _ hm
  · exact checked4_164 _ hm
  · exact checked4_245 _ hm
  · exact checked4_246 _ hm
private def chunk5_439 : List (List T) := [[wire240,wire8738,wire17487,wire34952,wire61440],
  [wire240,wire8738,wire17487,wire34952,wire61455],
  [wire240,wire8738,wire17487,wire34952,wire61680],
  [wire240,wire8738,wire17487,wire34952,wire61695]]
private def pool5_439 : List (List (List T)) := [chunk4_147, chunk4_247]
private theorem checked5_439 : ∀ w ∈ chunk5_439, ¬ Need 5 w.toFinset := by
  have h : chunk5_439.all (routes 4 pool5_439.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_439,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_247 _ hm
private def chunk5_440 : List (List T) := [[wire240,wire8738,wire17487,wire34952,wire61713],
  [wire240,wire8738,wire17487,wire34952,wire61986],
  [wire240,wire8738,wire17487,wire34952,wire62532],
  [wire240,wire8738,wire17487,wire34952,wire62543]]
private def pool5_440 : List (List (List T)) := [chunk4_147, chunk4_164, chunk4_248]
private theorem checked5_440 : ∀ w ∈ chunk5_440, ¬ Need 5 w.toFinset := by
  have h : chunk5_440.all (routes 4 pool5_440.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_440,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_164 _ hm
  · exact checked4_248 _ hm
private def chunk5_441 : List (List T) := [[wire240,wire8738,wire17487,wire34952,wire63624],
  [wire240,wire8738,wire17487,wire34952,wire65280],
  [wire240,wire8738,wire17487,wire34952,wire65295],
  [wire240,wire8738,wire17487,wire34952,wire65520]]
private def pool5_441 : List (List (List T)) := [chunk4_147, chunk4_164, chunk4_242, chunk4_249, chunk4_250]
private theorem checked5_441 : ∀ w ∈ chunk5_441, ¬ Need 5 w.toFinset := by
  have h : chunk5_441.all (routes 4 pool5_441.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_441,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_164 _ hm
  · exact checked4_242 _ hm
  · exact checked4_249 _ hm
  · exact checked4_250 _ hm
private def chunk5_442 : List (List T) := [[wire240,wire8738,wire17487,wire34952,wire65535],
  [wire240,wire8738,wire17487,wire35064],
  [wire240,wire8738,wire17487,wire35064,wire61440],
  [wire240,wire8738,wire17487,wire43690]]
private def pool5_442 : List (List (List T)) := [chunk4_0, chunk4_101, chunk4_102, chunk4_108, chunk4_145, chunk4_146, chunk4_147, chunk4_148, chunk4_149, chunk4_151, chunk4_161, chunk4_162, chunk4_164, chunk4_233, chunk4_237, chunk4_243, chunk4_247, chunk4_249, chunk4_250]
private theorem checked5_442 : ∀ w ∈ chunk5_442, ¬ Need 5 w.toFinset := by
  have h : chunk5_442.all (routes 4 pool5_442.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_442,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_101 _ hm
  · exact checked4_102 _ hm
  · exact checked4_108 _ hm
  · exact checked4_145 _ hm
  · exact checked4_146 _ hm
  · exact checked4_147 _ hm
  · exact checked4_148 _ hm
  · exact checked4_149 _ hm
  · exact checked4_151 _ hm
  · exact checked4_161 _ hm
  · exact checked4_162 _ hm
  · exact checked4_164 _ hm
  · exact checked4_233 _ hm
  · exact checked4_237 _ hm
  · exact checked4_243 _ hm
  · exact checked4_247 _ hm
  · exact checked4_249 _ hm
  · exact checked4_250 _ hm
private def chunk5_443 : List (List T) := [[wire240,wire8738,wire17487,wire43690,wire61440],
  [wire240,wire8738,wire20292,wire34952,wire62532],
  [wire240,wire8738,wire20292,wire52428,wire61440],
  [wire240,wire8738,wire20292,wire61166,wire61440]]
private def pool5_443 : List (List (List T)) := [chunk4_151, chunk4_164]
private theorem checked5_443 : ∀ w ∈ chunk5_443, ¬ Need 5 w.toFinset := by
  have h : chunk5_443.all (routes 4 pool5_443.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_443,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_151 _ hm
  · exact checked4_164 _ hm
private def chunk5_444 : List (List T) := [[wire240,wire8738,wire26214,wire34952,wire65280],
  [wire240,wire8738,wire26214,wire34952,wire65520],
  [wire240,wire8738,wire34952,wire39321,wire65280],
  [wire240,wire8738,wire34952,wire39321,wire65520]]
private def pool5_444 : List (List (List T)) := [chunk4_167, chunk4_170, chunk4_251, chunk4_252, chunk4_254]
private theorem checked5_444 : ∀ w ∈ chunk5_444, ¬ Need 5 w.toFinset := by
  have h : chunk5_444.all (routes 4 pool5_444.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_444,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_167 _ hm
  · exact checked4_170 _ hm
  · exact checked4_251 _ hm
  · exact checked4_252 _ hm
  · exact checked4_254 _ hm
private def chunk5_445 : List (List T) := [[wire240,wire8738,wire34952,wire48048],
  [wire240,wire8738,wire34952,wire48048,wire61440],
  [wire240,wire8738,wire34952,wire48059,wire65280],
  [wire240,wire8738,wire34952,wire48059,wire65520]]
private def pool5_445 : List (List (List T)) := [chunk4_147, chunk4_150, chunk4_151, chunk4_169, chunk4_251, chunk4_252]
private theorem checked5_445 : ∀ w ∈ chunk5_445, ¬ Need 5 w.toFinset := by
  have h : chunk5_445.all (routes 4 pool5_445.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_445,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_147 _ hm
  · exact checked4_150 _ hm
  · exact checked4_151 _ hm
  · exact checked4_169 _ hm
  · exact checked4_251 _ hm
  · exact checked4_252 _ hm
private def chunk5_446 : List (List T) := [[wire240,wire8738,wire34952,wire52428,wire65280],
  [wire240,wire8738,wire34952,wire52428,wire65520],
  [wire240,wire8738,wire34952,wire61166,wire65280],
  [wire240,wire8738,wire34952,wire61166,wire65520]]
private def pool5_446 : List (List (List T)) := [chunk4_171, chunk4_254]
private theorem checked5_446 : ∀ w ∈ chunk5_446, ¬ Need 5 w.toFinset := by
  have h : chunk5_446.all (routes 4 pool5_446.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_446,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_171 _ hm
  · exact checked4_254 _ hm
private def chunk5_447 : List (List T) := [[wire240,wire17476,wire17487,wire21845,wire34952],
  [wire240,wire17476,wire17487,wire26214,wire34952],
  [wire240,wire17476,wire17487,wire34952,wire39321],
  [wire240,wire17476,wire17487,wire34952,wire43690]]
private def pool5_447 : List (List (List T)) := [chunk4_158, chunk4_159, chunk4_160, chunk4_162, chunk4_163, chunk4_254, chunk4_255]
private theorem checked5_447 : ∀ w ∈ chunk5_447, ¬ Need 5 w.toFinset := by
  have h : chunk5_447.all (routes 4 pool5_447.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_447,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_158 _ hm
  · exact checked4_159 _ hm
  · exact checked4_160 _ hm
  · exact checked4_162 _ hm
  · exact checked4_163 _ hm
  · exact checked4_254 _ hm
  · exact checked4_255 _ hm
private def chunk5_448 : List (List T) := [[wire240,wire17476,wire17487,wire34952,wire56797],
  [wire240,wire17476,wire17487,wire34952,wire61166],
  [wire240,wire17476,wire21845,wire34952,wire65280],
  [wire240,wire17476,wire21845,wire34952,wire65520]]
private def pool5_448 : List (List (List T)) := [chunk4_162, chunk4_166, chunk4_255]
private theorem checked5_448 : ∀ w ∈ chunk5_448, ¬ Need 5 w.toFinset := by
  have h : chunk5_448.all (routes 4 pool5_448.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_448,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_162 _ hm
  · exact checked4_166 _ hm
  · exact checked4_255 _ hm
private def chunk5_449 : List (List T) := [[wire240,wire17476,wire26214,wire34952,wire65280],
  [wire240,wire17476,wire26214,wire34952,wire65520],
  [wire240,wire17476,wire34952,wire39321,wire65280],
  [wire240,wire17476,wire34952,wire39321,wire65520]]
private def pool5_449 : List (List (List T)) := [chunk4_167, chunk4_168, chunk4_170, chunk4_255]
private theorem checked5_449 : ∀ w ∈ chunk5_449, ¬ Need 5 w.toFinset := by
  have h : chunk5_449.all (routes 4 pool5_449.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_449,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_167 _ hm
  · exact checked4_168 _ hm
  · exact checked4_170 _ hm
  · exact checked4_255 _ hm
private def chunk5_450 : List (List T) := [[wire240,wire17476,wire34952,wire43690,wire65280],
  [wire240,wire17476,wire34952,wire43690,wire65520],
  [wire240,wire17476,wire34952,wire56797,wire65280],
  [wire240,wire17476,wire34952,wire56797,wire65520]]
private def pool5_450 : List (List (List T)) := [chunk4_171, chunk4_256]
private theorem checked5_450 : ∀ w ∈ chunk5_450, ¬ Need 5 w.toFinset := by
  have h : chunk5_450.all (routes 4 pool5_450.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_450,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_171 _ hm
  · exact checked4_256 _ hm
private def chunk5_451 : List (List T) := [[wire240,wire17476,wire34952,wire61166,wire65280],
  [wire240,wire17476,wire34952,wire61166,wire65520],
  [wire240,wire17487,wire21845,wire34952],
  [wire240,wire17487,wire21845,wire34952,wire61440]]
private def pool5_451 : List (List (List T)) := [chunk4_112, chunk4_158, chunk4_159, chunk4_160, chunk4_162, chunk4_165, chunk4_169, chunk4_256]
private theorem checked5_451 : ∀ w ∈ chunk5_451, ¬ Need 5 w.toFinset := by
  have h : chunk5_451.all (routes 4 pool5_451.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_451,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_112 _ hm
  · exact checked4_158 _ hm
  · exact checked4_159 _ hm
  · exact checked4_160 _ hm
  · exact checked4_162 _ hm
  · exact checked4_165 _ hm
  · exact checked4_169 _ hm
  · exact checked4_256 _ hm
private def chunk5_452 : List (List T) := [[wire240,wire17487,wire34952,wire43690],
  [wire240,wire17487,wire34952,wire43690,wire61440],
  [wire240,wire17487,wire34952,wire56797],
  [wire240,wire17487,wire34952,wire56797,wire61440]]
private def pool5_452 : List (List (List T)) := [chunk4_112, chunk4_147, chunk4_158, chunk4_161, chunk4_162, chunk4_164, chunk4_169, chunk4_256, chunk4_257, chunk4_258]
private theorem checked5_452 : ∀ w ∈ chunk5_452, ¬ Need 5 w.toFinset := by
  have h : chunk5_452.all (routes 4 pool5_452.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_452,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_112 _ hm
  · exact checked4_147 _ hm
  · exact checked4_158 _ hm
  · exact checked4_161 _ hm
  · exact checked4_162 _ hm
  · exact checked4_164 _ hm
  · exact checked4_169 _ hm
  · exact checked4_256 _ hm
  · exact checked4_257 _ hm
  · exact checked4_258 _ hm
private def chunk5_453 : List (List T) := [[wire240,wire20292,wire26214,wire34952,wire61440],
  [wire240,wire20292,wire34952,wire39321,wire61440],
  [wire240,wire20292,wire34952,wire61166,wire61440],
  [wire242,wire3840,wire4369,wire34952,wire61440]]
private def pool5_453 : List (List (List T)) := [chunk4_167, chunk4_168, chunk4_169, chunk4_172]
private theorem checked5_453 : ∀ w ∈ chunk5_453, ¬ Need 5 w.toFinset := by
  have h : chunk5_453.all (routes 4 pool5_453.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_453,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_167 _ hm
  · exact checked4_168 _ hm
  · exact checked4_169 _ hm
  · exact checked4_172 _ hm
private def chunk5_454 : List (List T) := [[wire255,wire3840,wire4369,wire8751,wire17476],
  [wire255,wire3840,wire4369,wire8946,wire34952],
  [wire255,wire3840,wire4383,wire8738,wire34952],
  [wire255,wire3840,wire4593,wire8738,wire17476]]
private def pool5_454 : List (List (List T)) := [chunk4_174, chunk4_176, chunk4_177, chunk4_181, chunk4_183, chunk4_184]
private theorem checked5_454 : ∀ w ∈ chunk5_454, ¬ Need 5 w.toFinset := by
  have h : chunk5_454.all (routes 4 pool5_454.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_454,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_174 _ hm
  · exact checked4_176 _ hm
  · exact checked4_177 _ hm
  · exact checked4_181 _ hm
  · exact checked4_183 _ hm
  · exact checked4_184 _ hm
private def chunk5_455 : List (List T) := [[wire255,wire3855,wire4369,wire8738,wire17476],
  [wire255,wire3855,wire4369,wire8738,wire34952],
  [wire255,wire3855,wire4369,wire17476,wire34952],
  [wire255,wire3855,wire8738,wire17476,wire34952]]
private def pool5_455 : List (List (List T)) := [chunk4_177]
private theorem checked5_455 : ∀ w ∈ chunk5_455, ¬ Need 5 w.toFinset := by
  have h : chunk5_455.all (routes 4 pool5_455.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_455,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_177 _ hm
private def chunk5_456 : List (List T) := [[wire255,wire4080,wire4369,wire8738,wire17476],
  [wire255,wire4080,wire4369,wire8738,wire34952],
  [wire255,wire4080,wire4369,wire17476,wire34952],
  [wire255,wire4080,wire8738,wire17476,wire34952]]
private def pool5_456 : List (List (List T)) := [chunk4_177]
private theorem checked5_456 : ∀ w ∈ chunk5_456, ¬ Need 5 w.toFinset := by
  have h : chunk5_456.all (routes 4 pool5_456.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_456,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_177 _ hm
private def chunk5_457 : List (List T) := [[wire255,wire4369,wire4383,wire8738,wire17476],
  [wire255,wire4369,wire4383,wire8738,wire34952],
  [wire255,wire4369,wire4383,wire17476,wire34952],
  [wire255,wire4369,wire4593,wire8738,wire17476]]
private def pool5_457 : List (List (List T)) := [chunk4_178, chunk4_180, chunk4_182, chunk4_183]
private theorem checked5_457 : ∀ w ∈ chunk5_457, ¬ Need 5 w.toFinset := by
  have h : chunk5_457.all (routes 4 pool5_457.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_457,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_178 _ hm
  · exact checked4_180 _ hm
  · exact checked4_182 _ hm
  · exact checked4_183 _ hm
private def chunk5_458 : List (List T) := [[wire255,wire4369,wire4593,wire8738,wire34952],
  [wire255,wire4369,wire4593,wire17476,wire34952],
  [wire255,wire4369,wire8738,wire8751,wire17476],
  [wire255,wire4369,wire8738,wire8751,wire34952]]
private def pool5_458 : List (List (List T)) := [chunk4_174, chunk4_175, chunk4_178, chunk4_183, chunk4_185]
private theorem checked5_458 : ∀ w ∈ chunk5_458, ¬ Need 5 w.toFinset := by
  have h : chunk5_458.all (routes 4 pool5_458.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_458,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_174 _ hm
  · exact checked4_175 _ hm
  · exact checked4_178 _ hm
  · exact checked4_183 _ hm
  · exact checked4_185 _ hm
private def chunk5_459 : List (List T) := [[wire255,wire4369,wire8738,wire8946,wire17476],
  [wire255,wire4369,wire8738,wire8946,wire34952],
  [wire255,wire4369,wire8738,wire17476,wire61455],
  [wire255,wire4369,wire8738,wire17476,wire61680]]
private def pool5_459 : List (List (List T)) := [chunk4_176, chunk4_178, chunk4_186]
private theorem checked5_459 : ∀ w ∈ chunk5_459, ¬ Need 5 w.toFinset := by
  have h : chunk5_459.all (routes 4 pool5_459.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_459,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_176 _ hm
  · exact checked4_178 _ hm
  · exact checked4_186 _ hm
private def chunk5_460 : List (List T) := [[wire255,wire4369,wire8738,wire17476,wire65295],
  [wire255,wire4369,wire8738,wire17476,wire65520],
  [wire255,wire4369,wire8738,wire34952,wire61455],
  [wire255,wire4369,wire8738,wire34952,wire61680]]
private def pool5_460 : List (List (List T)) := [chunk4_179]
private theorem checked5_460 : ∀ w ∈ chunk5_460, ¬ Need 5 w.toFinset := by
  have h : chunk5_460.all (routes 4 pool5_460.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_460,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_179 _ hm
private def chunk5_461 : List (List T) := [[wire255,wire4369,wire8738,wire34952,wire65295],
  [wire255,wire4369,wire8738,wire34952,wire65520],
  [wire255,wire4369,wire8751,wire17476],
  [wire255,wire4369,wire8751,wire17476,wire34952]]
private def pool5_461 : List (List (List T)) := [chunk4_106, chunk4_109, chunk4_174, chunk4_175, chunk4_178, chunk4_180, chunk4_187, chunk4_206]
private theorem checked5_461 : ∀ w ∈ chunk5_461, ¬ Need 5 w.toFinset := by
  have h : chunk5_461.all (routes 4 pool5_461.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_461,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_106 _ hm
  · exact checked4_109 _ hm
  · exact checked4_174 _ hm
  · exact checked4_175 _ hm
  · exact checked4_178 _ hm
  · exact checked4_180 _ hm
  · exact checked4_187 _ hm
  · exact checked4_206 _ hm
private def chunk5_462 : List (List T) := [[wire255,wire4369,wire8751,wire17476,wire61440],
  [wire255,wire4369,wire8946,wire17476,wire34952],
  [wire255,wire4369,wire8946,wire34952],
  [wire255,wire4369,wire8946,wire34952,wire61440]]
private def pool5_462 : List (List (List T)) := [chunk4_114, chunk4_172, chunk4_175, chunk4_176, chunk4_177, chunk4_178, chunk4_179, chunk4_188, chunk4_208]
private theorem checked5_462 : ∀ w ∈ chunk5_462, ¬ Need 5 w.toFinset := by
  have h : chunk5_462.all (routes 4 pool5_462.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_462,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_114 _ hm
  · exact checked4_172 _ hm
  · exact checked4_175 _ hm
  · exact checked4_176 _ hm
  · exact checked4_177 _ hm
  · exact checked4_178 _ hm
  · exact checked4_179 _ hm
  · exact checked4_188 _ hm
  · exact checked4_208 _ hm
private def chunk5_463 : List (List T) := [[wire255,wire4369,wire17476,wire34952,wire61455],
  [wire255,wire4369,wire17476,wire34952,wire61680],
  [wire255,wire4369,wire17476,wire34952,wire65295],
  [wire255,wire4369,wire17476,wire34952,wire65520]]
private def pool5_463 : List (List (List T)) := []
private theorem checked5_463 : ∀ w ∈ chunk5_463, ¬ Need 5 w.toFinset := by
  have h : chunk5_463.all (routes 4 pool5_463.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_463] at hv
private def chunk5_464 : List (List T) := [[wire255,wire4383,wire8738,wire17476,wire34952],
  [wire255,wire4383,wire8738,wire34952],
  [wire255,wire4383,wire8738,wire34952,wire61440],
  [wire255,wire4593,wire8738,wire17476]]
private def pool5_464 : List (List (List T)) := [chunk4_1, chunk4_101, chunk4_103, chunk4_109, chunk4_114, chunk4_180, chunk4_181, chunk4_182, chunk4_183, chunk4_184, chunk4_185, chunk4_186, chunk4_217, chunk4_218, chunk4_224]
private theorem checked5_464 : ∀ w ∈ chunk5_464, ¬ Need 5 w.toFinset := by
  have h : chunk5_464.all (routes 4 pool5_464.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_464,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_101 _ hm
  · exact checked4_103 _ hm
  · exact checked4_109 _ hm
  · exact checked4_114 _ hm
  · exact checked4_180 _ hm
  · exact checked4_181 _ hm
  · exact checked4_182 _ hm
  · exact checked4_183 _ hm
  · exact checked4_184 _ hm
  · exact checked4_185 _ hm
  · exact checked4_186 _ hm
  · exact checked4_217 _ hm
  · exact checked4_218 _ hm
  · exact checked4_224 _ hm
private def chunk5_465 : List (List T) := [[wire255,wire4593,wire8738,wire17476,wire34952],
  [wire255,wire4593,wire8738,wire17476,wire61440],
  [wire255,wire8738,wire8751,wire17476,wire34952],
  [wire255,wire8738,wire8946,wire17476,wire34952]]
private def pool5_465 : List (List (List T)) := [chunk4_184, chunk4_185, chunk4_187]
private theorem checked5_465 : ∀ w ∈ chunk5_465, ¬ Need 5 w.toFinset := by
  have h : chunk5_465.all (routes 4 pool5_465.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_465,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_184 _ hm
  · exact checked4_185 _ hm
  · exact checked4_187 _ hm
private def chunk5_466 : List (List T) := [[wire255,wire8738,wire17476,wire34952,wire61455],
  [wire255,wire8738,wire17476,wire34952,wire61680],
  [wire255,wire8738,wire17476,wire34952,wire65295],
  [wire255,wire8738,wire17476,wire34952,wire65520]]
private def pool5_466 : List (List (List T)) := []
private theorem checked5_466 : ∀ w ∈ chunk5_466, ¬ Need 5 w.toFinset := by
  have h : chunk5_466.all (routes 4 pool5_466.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_466] at hv
private def chunk5_467 : List (List T) := [[wire3840,wire3855,wire4369,wire8738,wire63624],
  [wire3840,wire3855,wire4369,wire17476,wire63624],
  [wire3840,wire3855,wire8738,wire17476,wire35064],
  [wire3840,wire4080,wire4369,wire8738,wire62532]]
private def pool5_467 : List (List (List T)) := [chunk4_200]
private theorem checked5_467 : ∀ w ∈ chunk5_467, ¬ Need 5 w.toFinset := by
  have h : chunk5_467.all (routes 4 pool5_467.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_467,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_200 _ hm
private def chunk5_468 : List (List T) := [[wire3840,wire4080,wire4369,wire34952,wire62532],
  [wire3840,wire4080,wire8738,wire17487,wire34952],
  [wire3840,wire4095,wire4369,wire8751,wire17476],
  [wire3840,wire4095,wire4369,wire8946,wire34952]]
private def pool5_468 : List (List (List T)) := [chunk4_201]
private theorem checked5_468 : ∀ w ∈ chunk5_468, ¬ Need 5 w.toFinset := by
  have h : chunk5_468.all (routes 4 pool5_468.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_468,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_201 _ hm
private def chunk5_469 : List (List T) := [[wire3840,wire4095,wire4383,wire8738,wire34952],
  [wire3840,wire4095,wire4593,wire8738,wire17476],
  [wire3840,wire4369,wire4383,wire8738,wire63624],
  [wire3840,wire4369,wire4383,wire17476,wire63624]]
private def pool5_469 : List (List (List T)) := [chunk4_191, chunk4_192, chunk4_202, chunk4_203]
private theorem checked5_469 : ∀ w ∈ chunk5_469, ¬ Need 5 w.toFinset := by
  have h : chunk5_469.all (routes 4 pool5_469.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_469,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_191 _ hm
  · exact checked4_192 _ hm
  · exact checked4_202 _ hm
  · exact checked4_203 _ hm
private def chunk5_470 : List (List T) := [[wire3840,wire4369,wire4593,wire8738,wire62532],
  [wire3840,wire4369,wire4593,wire34952,wire62532],
  [wire3840,wire4369,wire8738,wire8751,wire63624],
  [wire3840,wire4369,wire8738,wire8946,wire62532]]
private def pool5_470 : List (List (List T)) := [chunk4_194, chunk4_196, chunk4_197, chunk4_203, chunk4_204]
private theorem checked5_470 : ∀ w ∈ chunk5_470, ¬ Need 5 w.toFinset := by
  have h : chunk5_470.all (routes 4 pool5_470.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_470,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_194 _ hm
  · exact checked4_196 _ hm
  · exact checked4_197 _ hm
  · exact checked4_203 _ hm
  · exact checked4_204 _ hm
private def chunk5_471 : List (List T) := [[wire3840,wire4369,wire8738,wire17487,wire35064],
  [wire3840,wire4369,wire8738,wire17487,wire35064,wire61440],
  [wire3840,wire4369,wire8738,wire61455,wire62532],
  [wire3840,wire4369,wire8738,wire61680,wire63624]]
private def pool5_471 : List (List (List T)) := [chunk4_188, chunk4_190, chunk4_205, chunk4_232]
private theorem checked5_471 : ∀ w ∈ chunk5_471, ¬ Need 5 w.toFinset := by
  have h : chunk5_471.all (routes 4 pool5_471.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_471,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_188 _ hm
  · exact checked4_190 _ hm
  · exact checked4_205 _ hm
  · exact checked4_232 _ hm
private def chunk5_472 : List (List T) := [[wire3840,wire4369,wire8738,wire62532,wire65295],
  [wire3840,wire4369,wire8738,wire63624,wire65520],
  [wire3840,wire4369,wire8751,wire17476,wire61440],
  [wire3840,wire4369,wire8751,wire17476,wire65280]]
private def pool5_472 : List (List (List T)) := [chunk4_191, chunk4_205, chunk4_206, chunk4_210]
private theorem checked5_472 : ∀ w ∈ chunk5_472, ¬ Need 5 w.toFinset := by
  have h : chunk5_472.all (routes 4 pool5_472.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_472,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_191 _ hm
  · exact checked4_205 _ hm
  · exact checked4_206 _ hm
  · exact checked4_210 _ hm
private def chunk5_473 : List (List T) := [[wire3840,wire4369,wire8751,wire20292,wire61440],
  [wire3840,wire4369,wire8751,wire21845,wire61440],
  [wire3840,wire4369,wire8751,wire43690,wire61440],
  [wire3840,wire4369,wire8751,wire48059,wire61440]]
private def pool5_473 : List (List (List T)) := [chunk4_198, chunk4_199, chunk4_206, chunk4_207, chunk4_210]
private theorem checked5_473 : ∀ w ∈ chunk5_473, ¬ Need 5 w.toFinset := by
  have h : chunk5_473.all (routes 4 pool5_473.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_473,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_198 _ hm
  · exact checked4_199 _ hm
  · exact checked4_206 _ hm
  · exact checked4_207 _ hm
  · exact checked4_210 _ hm
private def chunk5_474 : List (List T) := [[wire3840,wire4369,wire8751,wire61440,wire62532],
  [wire3840,wire4369,wire8946,wire26214,wire61440],
  [wire3840,wire4369,wire8946,wire30583,wire61440],
  [wire3840,wire4369,wire8946,wire34952,wire61440]]
private def pool5_474 : List (List (List T)) := [chunk4_190, chunk4_199, chunk4_207, chunk4_208]
private theorem checked5_474 : ∀ w ∈ chunk5_474, ¬ Need 5 w.toFinset := by
  have h : chunk5_474.all (routes 4 pool5_474.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_474,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_190 _ hm
  · exact checked4_199 _ hm
  · exact checked4_207 _ hm
  · exact checked4_208 _ hm
private def chunk5_475 : List (List T) := [[wire3840,wire4369,wire8946,wire34952,wire65280],
  [wire3840,wire4369,wire8946,wire36744,wire61440],
  [wire3840,wire4369,wire8946,wire39321,wire61440],
  [wire3840,wire4369,wire8946,wire61440,wire63624]]
private def pool5_475 : List (List (List T)) := [chunk4_190, chunk4_199, chunk4_208, chunk4_209, chunk4_210]
private theorem checked5_475 : ∀ w ∈ chunk5_475, ¬ Need 5 w.toFinset := by
  have h : chunk5_475.all (routes 4 pool5_475.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_475,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_190 _ hm
  · exact checked4_199 _ hm
  · exact checked4_208 _ hm
  · exact checked4_209 _ hm
  · exact checked4_210 _ hm
private def chunk5_476 : List (List T) := [[wire3840,wire4369,wire12079,wire17476,wire61440],
  [wire3840,wire4369,wire12274,wire34952,wire61440],
  [wire3840,wire4369,wire13119,wire17476,wire61440],
  [wire3840,wire4369,wire13299,wire34952,wire61440]]
private def pool5_476 : List (List (List T)) := [chunk4_198, chunk4_199, chunk4_210, chunk4_211]
private theorem checked5_476 : ∀ w ∈ chunk5_476, ¬ Need 5 w.toFinset := by
  have h : chunk5_476.all (routes 4 pool5_476.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_476,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_198 _ hm
  · exact checked4_199 _ hm
  · exact checked4_210 _ hm
  · exact checked4_211 _ hm
private def chunk5_477 : List (List T) := [[wire3840,wire4369,wire17476,wire56784,wire61440],
  [wire3840,wire4369,wire17476,wire61440,wire61999],
  [wire3840,wire4369,wire17476,wire61440,wire65327],
  [wire3840,wire4369,wire17476,wire61680,wire63624]]
private def pool5_477 : List (List (List T)) := [chunk4_190, chunk4_191, chunk4_212, chunk4_214]
private theorem checked5_477 : ∀ w ∈ chunk5_477, ¬ Need 5 w.toFinset := by
  have h : chunk5_477.all (routes 4 pool5_477.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_477,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_190 _ hm
  · exact checked4_191 _ hm
  · exact checked4_212 _ hm
  · exact checked4_214 _ hm
private def chunk5_478 : List (List T) := [[wire3840,wire4369,wire17476,wire63624,wire65520],
  [wire3840,wire4369,wire17652,wire34959,wire61440],
  [wire3840,wire4369,wire34952,wire56589,wire61440],
  [wire3840,wire4369,wire34952,wire61440,wire62194]]
private def pool5_478 : List (List (List T)) := [chunk4_114, chunk4_190, chunk4_212, chunk4_213, chunk4_214, chunk4_215]
private theorem checked5_478 : ∀ w ∈ chunk5_478, ¬ Need 5 w.toFinset := by
  have h : chunk5_478.all (routes 4 pool5_478.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_478,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_114 _ hm
  · exact checked4_190 _ hm
  · exact checked4_212 _ hm
  · exact checked4_213 _ hm
  · exact checked4_214 _ hm
  · exact checked4_215 _ hm
private def chunk5_479 : List (List T) := [[wire3840,wire4369,wire34952,wire61440,wire65522],
  [wire3840,wire4369,wire34952,wire61455,wire62532],
  [wire3840,wire4369,wire34952,wire62532,wire65295],
  [wire3840,wire4383,wire8738,wire17476,wire63624]]
private def pool5_479 : List (List (List T)) := [chunk4_191, chunk4_215, chunk4_216]
private theorem checked5_479 : ∀ w ∈ chunk5_479, ¬ Need 5 w.toFinset := by
  have h : chunk5_479.all (routes 4 pool5_479.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_479,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_191 _ hm
  · exact checked4_215 _ hm
  · exact checked4_216 _ hm
private def chunk5_480 : List (List T) := [[wire3840,wire4383,wire8738,wire21845,wire61440],
  [wire3840,wire4383,wire8738,wire30583,wire61440],
  [wire3840,wire4383,wire8738,wire34952,wire61440],
  [wire3840,wire4383,wire8738,wire34952,wire63624]]
private def pool5_480 : List (List (List T)) := [chunk4_191, chunk4_193, chunk4_198, chunk4_217, chunk4_218, chunk4_219]
private theorem checked5_480 : ∀ w ∈ chunk5_480, ¬ Need 5 w.toFinset := by
  have h : chunk5_480.all (routes 4 pool5_480.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_480,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_191 _ hm
  · exact checked4_193 _ hm
  · exact checked4_198 _ hm
  · exact checked4_217 _ hm
  · exact checked4_218 _ hm
  · exact checked4_219 _ hm
private def chunk5_481 : List (List T) := [[wire3840,wire4383,wire8738,wire34952,wire65280],
  [wire3840,wire4383,wire8738,wire36744,wire61440],
  [wire3840,wire4383,wire8738,wire43690,wire61440],
  [wire3840,wire4383,wire8738,wire61440,wire63624]]
private def pool5_481 : List (List (List T)) := [chunk4_191, chunk4_192, chunk4_193, chunk4_199, chunk4_218, chunk4_219, chunk4_220, chunk4_221]
private theorem checked5_481 : ∀ w ∈ chunk5_481, ¬ Need 5 w.toFinset := by
  have h : chunk5_481.all (routes 4 pool5_481.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_481,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_191 _ hm
  · exact checked4_192 _ hm
  · exact checked4_193 _ hm
  · exact checked4_199 _ hm
  · exact checked4_218 _ hm
  · exact checked4_219 _ hm
  · exact checked4_220 _ hm
  · exact checked4_221 _ hm
private def chunk5_482 : List (List T) := [[wire3840,wire4383,wire8738,wire63624],
  [wire3840,wire4383,wire12066,wire34952,wire61440],
  [wire3840,wire4383,wire21845,wire34952,wire61440],
  [wire3840,wire4383,wire34952,wire43690,wire61440]]
private def pool5_482 : List (List (List T)) := [chunk4_1, chunk4_189, chunk4_191, chunk4_192, chunk4_193, chunk4_194, chunk4_197, chunk4_198, chunk4_220, chunk4_221, chunk4_222, chunk4_223]
private theorem checked5_482 : ∀ w ∈ chunk5_482, ¬ Need 5 w.toFinset := by
  have h : chunk5_482.all (routes 4 pool5_482.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_482,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_1 _ hm
  · exact checked4_189 _ hm
  · exact checked4_191 _ hm
  · exact checked4_192 _ hm
  · exact checked4_193 _ hm
  · exact checked4_194 _ hm
  · exact checked4_197 _ hm
  · exact checked4_198 _ hm
  · exact checked4_220 _ hm
  · exact checked4_221 _ hm
  · exact checked4_222 _ hm
  · exact checked4_223 _ hm
private def chunk5_483 : List (List T) := [[wire3840,wire4383,wire34952,wire56797,wire61440],
  [wire3840,wire4383,wire34952,wire61440,wire61986],
  [wire3840,wire4593,wire8738,wire17476,wire61440],
  [wire3840,wire4593,wire8738,wire17476,wire62532]]
private def pool5_483 : List (List (List T)) := [chunk4_191, chunk4_193, chunk4_194, chunk4_195, chunk4_222, chunk4_223, chunk4_224, chunk4_225, chunk4_226]
private theorem checked5_483 : ∀ w ∈ chunk5_483, ¬ Need 5 w.toFinset := by
  have h : chunk5_483.all (routes 4 pool5_483.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_483,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_191 _ hm
  · exact checked4_193 _ hm
  · exact checked4_194 _ hm
  · exact checked4_195 _ hm
  · exact checked4_222 _ hm
  · exact checked4_223 _ hm
  · exact checked4_224 _ hm
  · exact checked4_225 _ hm
  · exact checked4_226 _ hm
private def chunk5_484 : List (List T) := [[wire3840,wire4593,wire8738,wire17476,wire65280],
  [wire3840,wire4593,wire8738,wire20292,wire61440],
  [wire3840,wire4593,wire8738,wire26214,wire61440],
  [wire3840,wire4593,wire8738,wire34952,wire62532]]
private def pool5_484 : List (List (List T)) := [chunk4_194, chunk4_199, chunk4_224, chunk4_225, chunk4_226, chunk4_227, chunk4_229]
private theorem checked5_484 : ∀ w ∈ chunk5_484, ¬ Need 5 w.toFinset := by
  have h : chunk5_484.all (routes 4 pool5_484.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_484,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_194 _ hm
  · exact checked4_199 _ hm
  · exact checked4_224 _ hm
  · exact checked4_225 _ hm
  · exact checked4_226 _ hm
  · exact checked4_227 _ hm
  · exact checked4_229 _ hm
private def chunk5_485 : List (List T) := [[wire3840,wire4593,wire8738,wire39321,wire61440],
  [wire3840,wire4593,wire8738,wire48059,wire61440],
  [wire3840,wire4593,wire8738,wire61440,wire62532],
  [wire3840,wire4593,wire8738,wire62532]]
private def pool5_485 : List (List (List T)) := [chunk4_102, chunk4_190, chunk4_194, chunk4_195, chunk4_196, chunk4_197, chunk4_198, chunk4_199, chunk4_227, chunk4_228, chunk4_229]
private theorem checked5_485 : ∀ w ∈ chunk5_485, ¬ Need 5 w.toFinset := by
  have h : chunk5_485.all (routes 4 pool5_485.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_485,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_102 _ hm
  · exact checked4_190 _ hm
  · exact checked4_194 _ hm
  · exact checked4_195 _ hm
  · exact checked4_196 _ hm
  · exact checked4_197 _ hm
  · exact checked4_198 _ hm
  · exact checked4_199 _ hm
  · exact checked4_227 _ hm
  · exact checked4_228 _ hm
  · exact checked4_229 _ hm
private def chunk5_486 : List (List T) := [[wire3840,wire4593,wire12066,wire17476,wire61440],
  [wire3840,wire4593,wire17476,wire26214,wire61440],
  [wire3840,wire4593,wire17476,wire39321,wire61440],
  [wire3840,wire4593,wire17476,wire56797,wire61440]]
private def pool5_486 : List (List (List T)) := [chunk4_194, chunk4_195, chunk4_196, chunk4_229, chunk4_230, chunk4_231, chunk4_232]
private theorem checked5_486 : ∀ w ∈ chunk5_486, ¬ Need 5 w.toFinset := by
  have h : chunk5_486.all (routes 4 pool5_486.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_486,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_194 _ hm
  · exact checked4_195 _ hm
  · exact checked4_196 _ hm
  · exact checked4_229 _ hm
  · exact checked4_230 _ hm
  · exact checked4_231 _ hm
  · exact checked4_232 _ hm
private def chunk5_487 : List (List T) := [[wire3840,wire4593,wire17476,wire61440,wire61986],
  [wire3840,wire8738,wire13119,wire34952,wire61440],
  [wire3840,wire8738,wire13299,wire17476,wire61440],
  [wire3840,wire8738,wire17476,wire17487,wire35064]]
private def pool5_487 : List (List (List T)) := [chunk4_189, chunk4_196, chunk4_197, chunk4_199, chunk4_230, chunk4_232, chunk4_234, chunk4_238]
private theorem checked5_487 : ∀ w ∈ chunk5_487, ¬ Need 5 w.toFinset := by
  have h : chunk5_487.all (routes 4 pool5_487.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_487,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_189 _ hm
  · exact checked4_196 _ hm
  · exact checked4_197 _ hm
  · exact checked4_199 _ hm
  · exact checked4_230 _ hm
  · exact checked4_232 _ hm
  · exact checked4_234 _ hm
  · exact checked4_238 _ hm
private def chunk5_488 : List (List T) := [[wire3840,wire8738,wire17476,wire35064,wire61680],
  [wire3840,wire8738,wire17476,wire35064,wire65520],
  [wire3840,wire8738,wire17476,wire60942,wire61440],
  [wire3840,wire8738,wire17487,wire34952,wire35064]]
private def pool5_488 : List (List (List T)) := [chunk4_189, chunk4_197, chunk4_198, chunk4_199, chunk4_236, chunk4_237, chunk4_243, chunk4_250]
private theorem checked5_488 : ∀ w ∈ chunk5_488, ¬ Need 5 w.toFinset := by
  have h : chunk5_488.all (routes 4 pool5_488.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_488,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_189 _ hm
  · exact checked4_197 _ hm
  · exact checked4_198 _ hm
  · exact checked4_199 _ hm
  · exact checked4_236 _ hm
  · exact checked4_237 _ hm
  · exact checked4_243 _ hm
  · exact checked4_250 _ hm
private def chunk5_489 : List (List T) := [[wire3840,wire8738,wire17487,wire34952,wire61455],
  [wire3840,wire8738,wire17487,wire34952,wire65295],
  [wire3840,wire8738,wire17487,wire35064],
  [wire3840,wire8738,wire17487,wire35064,wire61440]]
private def pool5_489 : List (List (List T)) := [chunk4_0, chunk4_188, chunk4_189, chunk4_197, chunk4_198, chunk4_200, chunk4_233, chunk4_238, chunk4_242, chunk4_243, chunk4_247, chunk4_249]
private theorem checked5_489 : ∀ w ∈ chunk5_489, ¬ Need 5 w.toFinset := by
  have h : chunk5_489.all (routes 4 pool5_489.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_489,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_188 _ hm
  · exact checked4_189 _ hm
  · exact checked4_197 _ hm
  · exact checked4_198 _ hm
  · exact checked4_200 _ hm
  · exact checked4_233 _ hm
  · exact checked4_238 _ hm
  · exact checked4_242 _ hm
  · exact checked4_243 _ hm
  · exact checked4_247 _ hm
  · exact checked4_249 _ hm
private def chunk5_490 : List (List T) := [[wire3840,wire8738,wire34952,wire61152,wire61440],
  [wire3840,wire8751,wire17476,wire21845,wire61440],
  [wire3840,wire8751,wire17476,wire43690,wire61440],
  [wire3840,wire8751,wire17476,wire61166,wire61440]]
private def pool5_490 : List (List (List T)) := [chunk4_198, chunk4_200, chunk4_251, chunk4_253]
private theorem checked5_490 : ∀ w ∈ chunk5_490, ¬ Need 5 w.toFinset := by
  have h : chunk5_490.all (routes 4 pool5_490.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_490,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_198 _ hm
  · exact checked4_200 _ hm
  · exact checked4_251 _ hm
  · exact checked4_253 _ hm
private def chunk5_491 : List (List T) := [[wire3840,wire8946,wire26214,wire34952,wire61440],
  [wire3840,wire8946,wire34952,wire39321,wire61440],
  [wire3840,wire8946,wire34952,wire61166,wire61440],
  [wire3855,wire4080,wire4369,wire8738,wire17476]]
private def pool5_491 : List (List (List T)) := [chunk4_254]
private theorem checked5_491 : ∀ w ∈ chunk5_491, ¬ Need 5 w.toFinset := by
  have h : chunk5_491.all (routes 4 pool5_491.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_491,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_254 _ hm
private def chunk5_492 : List (List T) := [[wire3855,wire4080,wire4369,wire8738,wire34952],
  [wire3855,wire4080,wire4369,wire17476,wire34952],
  [wire3855,wire4080,wire8738,wire17476,wire34952],
  [wire3855,wire4369,wire8738,wire17476,wire61455]]
private def pool5_492 : List (List (List T)) := []
private theorem checked5_492 : ∀ w ∈ chunk5_492, ¬ Need 5 w.toFinset := by
  have h : chunk5_492.all (routes 4 pool5_492.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_492] at hv
private def chunk5_493 : List (List T) := [[wire3855,wire4369,wire8738,wire17476,wire65280],
  [wire3855,wire4369,wire8738,wire20292,wire61440],
  [wire3855,wire4369,wire8738,wire34952,wire61455],
  [wire3855,wire4369,wire8738,wire34952,wire65280]]
private def pool5_493 : List (List (List T)) := [chunk4_210]
private theorem checked5_493 : ∀ w ∈ chunk5_493, ¬ Need 5 w.toFinset := by
  have h : chunk5_493.all (routes 4 pool5_493.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_493,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_210 _ hm
private def chunk5_494 : List (List T) := [[wire3855,wire4369,wire17476,wire34952,wire61455],
  [wire3855,wire4369,wire17476,wire34952,wire65280],
  [wire3855,wire4369,wire20292,wire34952,wire61440],
  [wire3855,wire8738,wire17476,wire34952,wire61455]]
private def pool5_494 : List (List (List T)) := [chunk4_200]
private theorem checked5_494 : ∀ w ∈ chunk5_494, ¬ Need 5 w.toFinset := by
  have h : chunk5_494.all (routes 4 pool5_494.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_494,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_200 _ hm
private def chunk5_495 : List (List T) := [[wire3855,wire8738,wire17476,wire34952,wire65280],
  [wire3855,wire8738,wire17487,wire34952,wire61440],
  [wire4080,wire4369,wire8738,wire17476,wire61680],
  [wire4080,wire4369,wire8738,wire17476,wire65280]]
private def pool5_495 : List (List (List T)) := [chunk4_242]
private theorem checked5_495 : ∀ w ∈ chunk5_495, ¬ Need 5 w.toFinset := by
  have h : chunk5_495.all (routes 4 pool5_495.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_495,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_242 _ hm
private def chunk5_496 : List (List T) := [[wire4080,wire4369,wire8738,wire34952,wire61680],
  [wire4080,wire4369,wire8738,wire34952,wire65280],
  [wire4080,wire4369,wire8738,wire36744,wire61440],
  [wire4080,wire4369,wire17476,wire34952,wire61680]]
private def pool5_496 : List (List (List T)) := [chunk4_210]
private theorem checked5_496 : ∀ w ∈ chunk5_496, ¬ Need 5 w.toFinset := by
  have h : chunk5_496.all (routes 4 pool5_496.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_496,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_210 _ hm
private def chunk5_497 : List (List T) := [[wire4080,wire4369,wire17476,wire34952,wire65280],
  [wire4080,wire4369,wire17476,wire36744,wire61440],
  [wire4080,wire8738,wire17476,wire34952,wire61680],
  [wire4080,wire8738,wire17476,wire34952,wire65280]]
private def pool5_497 : List (List (List T)) := [chunk4_201]
private theorem checked5_497 : ∀ w ∈ chunk5_497, ¬ Need 5 w.toFinset := by
  have h : chunk5_497.all (routes 4 pool5_497.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_497,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_201 _ hm
private def chunk5_498 : List (List T) := [[wire4080,wire8738,wire17476,wire35064,wire61440],
  [wire4369,wire4383,wire8738,wire17476,wire65280],
  [wire4369,wire4383,wire8738,wire34952,wire65280],
  [wire4369,wire4383,wire8738,wire36744,wire61440]]
private def pool5_498 : List (List (List T)) := [chunk4_203, chunk4_211, chunk4_217, chunk4_218, chunk4_236]
private theorem checked5_498 : ∀ w ∈ chunk5_498, ¬ Need 5 w.toFinset := by
  have h : chunk5_498.all (routes 4 pool5_498.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_498,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_203 _ hm
  · exact checked4_211 _ hm
  · exact checked4_217 _ hm
  · exact checked4_218 _ hm
  · exact checked4_236 _ hm
private def chunk5_499 : List (List T) := [[wire4369,wire4383,wire17476,wire34952,wire65280],
  [wire4369,wire4383,wire17476,wire36744,wire61440],
  [wire4369,wire4593,wire8738,wire17476,wire65280],
  [wire4369,wire4593,wire8738,wire20292,wire61440]]
private def pool5_499 : List (List (List T)) := [chunk4_203, chunk4_222, chunk4_224, chunk4_225]
private theorem checked5_499 : ∀ w ∈ chunk5_499, ¬ Need 5 w.toFinset := by
  have h : chunk5_499.all (routes 4 pool5_499.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_499,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_203 _ hm
  · exact checked4_222 _ hm
  · exact checked4_224 _ hm
  · exact checked4_225 _ hm
private def chunk5_500 : List (List T) := [[wire4369,wire4593,wire8738,wire34952,wire65280],
  [wire4369,wire4593,wire17476,wire34952,wire65280],
  [wire4369,wire4593,wire20292,wire34952,wire61440],
  [wire4369,wire8738,wire8751,wire17476,wire65280]]
private def pool5_500 : List (List (List T)) := [chunk4_203, chunk4_206, chunk4_211, chunk4_227, chunk4_230, chunk4_231]
private theorem checked5_500 : ∀ w ∈ chunk5_500, ¬ Need 5 w.toFinset := by
  have h : chunk5_500.all (routes 4 pool5_500.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_500,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_203 _ hm
  · exact checked4_206 _ hm
  · exact checked4_211 _ hm
  · exact checked4_227 _ hm
  · exact checked4_230 _ hm
  · exact checked4_231 _ hm
private def chunk5_501 : List (List T) := [[wire4369,wire8738,wire8751,wire34952,wire65280],
  [wire4369,wire8738,wire8751,wire36744,wire61440],
  [wire4369,wire8738,wire8946,wire17476,wire65280],
  [wire4369,wire8738,wire8946,wire20292,wire61440]]
private def pool5_501 : List (List (List T)) := [chunk4_204, chunk4_207, chunk4_208, chunk4_234]
private theorem checked5_501 : ∀ w ∈ chunk5_501, ¬ Need 5 w.toFinset := by
  have h : chunk5_501.all (routes 4 pool5_501.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_501,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_204 _ hm
  · exact checked4_207 _ hm
  · exact checked4_208 _ hm
  · exact checked4_234 _ hm
private def chunk5_502 : List (List T) := [[wire4369,wire8738,wire8946,wire34952,wire65280],
  [wire4369,wire8738,wire17476,wire17487,wire35064],
  [wire4369,wire8738,wire17476,wire17487,wire65295],
  [wire4369,wire8738,wire17476,wire35064,wire65520]]
private def pool5_502 : List (List (List T)) := [chunk4_0, chunk4_204, chunk4_208, chunk4_238]
private theorem checked5_502 : ∀ w ∈ chunk5_502, ¬ Need 5 w.toFinset := by
  have h : chunk5_502.all (routes 4 pool5_502.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_502,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_204 _ hm
  · exact checked4_208 _ hm
  · exact checked4_238 _ hm
private def chunk5_503 : List (List T) := [[wire4369,wire8738,wire17476,wire61455,wire61680],
  [wire4369,wire8738,wire17476,wire61455,wire65280],
  [wire4369,wire8738,wire17476,wire61680,wire65280],
  [wire4369,wire8738,wire17476,wire65280,wire65295]]
private def pool5_503 : List (List (List T)) := [chunk4_205, chunk4_212]
private theorem checked5_503 : ∀ w ∈ chunk5_503, ¬ Need 5 w.toFinset := by
  have h : chunk5_503.all (routes 4 pool5_503.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_503,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_205 _ hm
  · exact checked4_212 _ hm
private def chunk5_504 : List (List T) := [[wire4369,wire8738,wire17476,wire65280,wire65520],
  [wire4369,wire8738,wire17476,wire65295,wire65520],
  [wire4369,wire8738,wire17487,wire34952,wire35064],
  [wire4369,wire8738,wire17487,wire34952,wire65295]]
private def pool5_504 : List (List (List T)) := [chunk4_0, chunk4_204, chunk4_244]
private theorem checked5_504 : ∀ w ∈ chunk5_504, ¬ Need 5 w.toFinset := by
  have h : chunk5_504.all (routes 4 pool5_504.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_504,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_204 _ hm
  · exact checked4_244 _ hm
private def chunk5_505 : List (List T) := [[wire4369,wire8738,wire17487,wire35064],
  [wire4369,wire8738,wire17487,wire35064,wire61440],
  [wire4369,wire8738,wire20292,wire61440,wire61680],
  [wire4369,wire8738,wire20292,wire61440,wire65295]]
private def pool5_505 : List (List (List T)) := [chunk4_0, chunk4_100, chunk4_202, chunk4_204, chunk4_205, chunk4_211, chunk4_213, chunk4_214, chunk4_233, chunk4_239, chunk4_244, chunk4_246, chunk4_248]
private theorem checked5_505 : ∀ w ∈ chunk5_505, ¬ Need 5 w.toFinset := by
  have h : chunk5_505.all (routes 4 pool5_505.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_505,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_100 _ hm
  · exact checked4_202 _ hm
  · exact checked4_204 _ hm
  · exact checked4_205 _ hm
  · exact checked4_211 _ hm
  · exact checked4_213 _ hm
  · exact checked4_214 _ hm
  · exact checked4_233 _ hm
  · exact checked4_239 _ hm
  · exact checked4_244 _ hm
  · exact checked4_246 _ hm
  · exact checked4_248 _ hm
private def chunk5_506 : List (List T) := [[wire4369,wire8738,wire34952,wire35064,wire65520],
  [wire4369,wire8738,wire34952,wire61455,wire61680],
  [wire4369,wire8738,wire34952,wire61455,wire65280],
  [wire4369,wire8738,wire34952,wire61680,wire65280]]
private def pool5_506 : List (List (List T)) := [chunk4_215, chunk4_252]
private theorem checked5_506 : ∀ w ∈ chunk5_506, ¬ Need 5 w.toFinset := by
  have h : chunk5_506.all (routes 4 pool5_506.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_506,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_215 _ hm
  · exact checked4_252 _ hm
private def chunk5_507 : List (List T) := [[wire4369,wire8738,wire34952,wire65280,wire65295],
  [wire4369,wire8738,wire34952,wire65280,wire65520],
  [wire4369,wire8738,wire34952,wire65295,wire65520],
  [wire4369,wire8738,wire36744,wire61440,wire61455]]
private def pool5_507 : List (List (List T)) := [chunk4_205, chunk4_215]
private theorem checked5_507 : ∀ w ∈ chunk5_507, ¬ Need 5 w.toFinset := by
  have h : chunk5_507.all (routes 4 pool5_507.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_507,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl
  · exact checked4_205 _ hm
  · exact checked4_215 _ hm
private def chunk5_508 : List (List T) := [[wire4369,wire8738,wire36744,wire61440,wire65520],
  [wire4369,wire8751,wire17476,wire34952,wire65280],
  [wire4369,wire8751,wire17476,wire61440,wire61695],
  [wire4369,wire8751,wire17476,wire61440,wire65280]]
private def pool5_508 : List (List (List T)) := [chunk4_205, chunk4_206, chunk4_207, chunk4_212, chunk4_216]
private theorem checked5_508 : ∀ w ∈ chunk5_508, ¬ Need 5 w.toFinset := by
  have h : chunk5_508.all (routes 4 pool5_508.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_508,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked4_205 _ hm
  · exact checked4_206 _ hm
  · exact checked4_207 _ hm
  · exact checked4_212 _ hm
  · exact checked4_216 _ hm
private def chunk5_509 : List (List T) := [[wire4369,wire8751,wire17476,wire65280],
  [wire4369,wire8946,wire17476,wire34952,wire65280],
  [wire4369,wire8946,wire34952,wire61440,wire61695],
  [wire4369,wire8946,wire34952,wire61440,wire65280]]
private def pool5_509 : List (List (List T)) := [chunk4_174, chunk4_206, chunk4_207, chunk4_208, chunk4_209, chunk4_211, chunk4_212, chunk4_215, chunk4_253]
private theorem checked5_509 : ∀ w ∈ chunk5_509, ¬ Need 5 w.toFinset := by
  have h : chunk5_509.all (routes 4 pool5_509.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_509,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_174 _ hm
  · exact checked4_206 _ hm
  · exact checked4_207 _ hm
  · exact checked4_208 _ hm
  · exact checked4_209 _ hm
  · exact checked4_211 _ hm
  · exact checked4_212 _ hm
  · exact checked4_215 _ hm
  · exact checked4_253 _ hm
private def chunk5_510 : List (List T) := [[wire4369,wire8946,wire34952,wire65280],
  [wire4369,wire17476,wire17487,wire34952,wire35064],
  [wire4369,wire17476,wire17487,wire34952,wire65295],
  [wire4369,wire17476,wire34952,wire35064,wire65520]]
private def pool5_510 : List (List (List T)) := [chunk4_176, chunk4_208, chunk4_209, chunk4_211, chunk4_213, chunk4_214, chunk4_215, chunk4_254, chunk4_255, chunk4_256]
private theorem checked5_510 : ∀ w ∈ chunk5_510, ¬ Need 5 w.toFinset := by
  have h : chunk5_510.all (routes 4 pool5_510.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_510,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_176 _ hm
  · exact checked4_208 _ hm
  · exact checked4_209 _ hm
  · exact checked4_211 _ hm
  · exact checked4_213 _ hm
  · exact checked4_214 _ hm
  · exact checked4_215 _ hm
  · exact checked4_254 _ hm
  · exact checked4_255 _ hm
  · exact checked4_256 _ hm
private def chunk5_511 : List (List T) := [[wire4369,wire17476,wire34952,wire61455,wire61680],
  [wire4369,wire17476,wire34952,wire61455,wire65280],
  [wire4369,wire17476,wire34952,wire61680,wire65280],
  [wire4369,wire17476,wire34952,wire65280,wire65295]]
private def pool5_511 : List (List (List T)) := [chunk4_215]
private theorem checked5_511 : ∀ w ∈ chunk5_511, ¬ Need 5 w.toFinset := by
  have h : chunk5_511.all (routes 4 pool5_511.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_511,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_215 _ hm
private def chunk5_512 : List (List T) := [[wire4369,wire17476,wire34952,wire65280,wire65520],
  [wire4369,wire17476,wire34952,wire65295,wire65520],
  [wire4369,wire17476,wire36744,wire61440,wire61455],
  [wire4369,wire17476,wire36744,wire61440,wire65520]]
private def pool5_512 : List (List (List T)) := [chunk4_212, chunk4_213, chunk4_215, chunk4_216]
private theorem checked5_512 : ∀ w ∈ chunk5_512, ¬ Need 5 w.toFinset := by
  have h : chunk5_512.all (routes 4 pool5_512.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_512,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked4_212 _ hm
  · exact checked4_213 _ hm
  · exact checked4_215 _ hm
  · exact checked4_216 _ hm
private def chunk5_513 : List (List T) := [[wire4369,wire20292,wire34952,wire61440,wire61680],
  [wire4369,wire20292,wire34952,wire61440,wire65295],
  [wire4383,wire8738,wire17476,wire34952,wire65280],
  [wire4383,wire8738,wire17476,wire36744,wire61440]]
private def pool5_513 : List (List (List T)) := [chunk4_214, chunk4_215, chunk4_216]
private theorem checked5_513 : ∀ w ∈ chunk5_513, ¬ Need 5 w.toFinset := by
  have h : chunk5_513.all (routes 4 pool5_513.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_513,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact checked4_214 _ hm
  · exact checked4_215 _ hm
  · exact checked4_216 _ hm
private def chunk5_514 : List (List T) := [[wire4383,wire8738,wire34952,wire36744,wire61440],
  [wire4383,wire8738,wire34952,wire61440,wire61695],
  [wire4383,wire8738,wire34952,wire61440,wire65280],
  [wire4383,wire8738,wire34952,wire65280]]
private def pool5_514 : List (List (List T)) := [chunk4_2, chunk4_180, chunk4_217, chunk4_218, chunk4_219, chunk4_220, chunk4_221, chunk4_222, chunk4_223, chunk4_234, chunk4_251]
private theorem checked5_514 : ∀ w ∈ chunk5_514, ¬ Need 5 w.toFinset := by
  have h : chunk5_514.all (routes 4 pool5_514.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_514,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_180 _ hm
  · exact checked4_217 _ hm
  · exact checked4_218 _ hm
  · exact checked4_219 _ hm
  · exact checked4_220 _ hm
  · exact checked4_221 _ hm
  · exact checked4_222 _ hm
  · exact checked4_223 _ hm
  · exact checked4_234 _ hm
  · exact checked4_251 _ hm
private def chunk5_515 : List (List T) := [[wire4383,wire8738,wire36744,wire61440],
  [wire4593,wire8738,wire17476,wire20292,wire61440],
  [wire4593,wire8738,wire17476,wire34952,wire65280],
  [wire4593,wire8738,wire17476,wire61440,wire61695]]
private def pool5_515 : List (List (List T)) := [chunk4_2, chunk4_202, chunk4_217, chunk4_218, chunk4_219, chunk4_220, chunk4_221, chunk4_223, chunk4_224, chunk4_225, chunk4_226, chunk4_227, chunk4_228, chunk4_231, chunk4_234, chunk4_253]
private theorem checked5_515 : ∀ w ∈ chunk5_515, ¬ Need 5 w.toFinset := by
  have h : chunk5_515.all (routes 4 pool5_515.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_515,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_2 _ hm
  · exact checked4_202 _ hm
  · exact checked4_217 _ hm
  · exact checked4_218 _ hm
  · exact checked4_219 _ hm
  · exact checked4_220 _ hm
  · exact checked4_221 _ hm
  · exact checked4_223 _ hm
  · exact checked4_224 _ hm
  · exact checked4_225 _ hm
  · exact checked4_226 _ hm
  · exact checked4_227 _ hm
  · exact checked4_228 _ hm
  · exact checked4_231 _ hm
  · exact checked4_234 _ hm
  · exact checked4_253 _ hm
private def chunk5_516 : List (List T) := [[wire4593,wire8738,wire17476,wire61440,wire65280],
  [wire4593,wire8738,wire17476,wire65280],
  [wire4593,wire8738,wire20292,wire34952,wire61440],
  [wire4593,wire8738,wire20292,wire61440]]
private def pool5_516 : List (List (List T)) := [chunk4_102, chunk4_183, chunk4_202, chunk4_224, chunk4_225, chunk4_226, chunk4_227, chunk4_228, chunk4_229, chunk4_230, chunk4_231, chunk4_232, chunk4_234, chunk4_237, chunk4_250]
private theorem checked5_516 : ∀ w ∈ chunk5_516, ¬ Need 5 w.toFinset := by
  have h : chunk5_516.all (routes 4 pool5_516.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_516,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_102 _ hm
  · exact checked4_183 _ hm
  · exact checked4_202 _ hm
  · exact checked4_224 _ hm
  · exact checked4_225 _ hm
  · exact checked4_226 _ hm
  · exact checked4_227 _ hm
  · exact checked4_228 _ hm
  · exact checked4_229 _ hm
  · exact checked4_230 _ hm
  · exact checked4_231 _ hm
  · exact checked4_232 _ hm
  · exact checked4_234 _ hm
  · exact checked4_237 _ hm
  · exact checked4_250 _ hm
private def chunk5_517 : List (List T) := [[wire8738,wire8751,wire17476,wire34952,wire65280],
  [wire8738,wire8946,wire17476,wire34952,wire65280],
  [wire8738,wire17476,wire17487,wire34952,wire35064],
  [wire8738,wire17476,wire17487,wire34952,wire65295]]
private def pool5_517 : List (List (List T)) := [chunk4_0, chunk4_236, chunk4_242, chunk4_245, chunk4_253, chunk4_254]
private theorem checked5_517 : ∀ w ∈ chunk5_517, ¬ Need 5 w.toFinset := by
  have h : chunk5_517.all (routes 4 pool5_517.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_517,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_236 _ hm
  · exact checked4_242 _ hm
  · exact checked4_245 _ hm
  · exact checked4_253 _ hm
  · exact checked4_254 _ hm
private def chunk5_518 : List (List T) := [[wire8738,wire17476,wire17487,wire35064],
  [wire8738,wire17476,wire17487,wire35064,wire61440],
  [wire8738,wire17476,wire34952,wire35064,wire65520],
  [wire8738,wire17476,wire34952,wire61455,wire61680]]
private def pool5_518 : List (List (List T)) := [chunk4_0, chunk4_108, chunk4_235, chunk4_236, chunk4_239, chunk4_243, chunk4_245, chunk4_246, chunk4_247, chunk4_248, chunk4_254, chunk4_255]
private theorem checked5_518 : ∀ w ∈ chunk5_518, ¬ Need 5 w.toFinset := by
  have h : chunk5_518.all (routes 4 pool5_518.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_518,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_108 _ hm
  · exact checked4_235 _ hm
  · exact checked4_236 _ hm
  · exact checked4_239 _ hm
  · exact checked4_243 _ hm
  · exact checked4_245 _ hm
  · exact checked4_246 _ hm
  · exact checked4_247 _ hm
  · exact checked4_248 _ hm
  · exact checked4_254 _ hm
  · exact checked4_255 _ hm
private def chunk5_519 : List (List T) := [[wire8738,wire17476,wire34952,wire61455,wire65280],
  [wire8738,wire17476,wire34952,wire61680,wire65280],
  [wire8738,wire17476,wire34952,wire65280,wire65295],
  [wire8738,wire17476,wire34952,wire65280,wire65520]]
private def pool5_519 : List (List (List T)) := []
private theorem checked5_519 : ∀ w ∈ chunk5_519, ¬ Need 5 w.toFinset := by
  have h : chunk5_519.all (routes 4 pool5_519.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool5_519] at hv
private def chunk5_520 : List (List T) := [[wire8738,wire17476,wire34952,wire65295,wire65520],
  [wire8738,wire17476,wire35064,wire61440,wire61455],
  [wire8738,wire17476,wire35064,wire61440,wire65520],
  [wire8738,wire17476,wire35064,wire65520]]
private def pool5_520 : List (List (List T)) := [chunk4_75, chunk4_235, chunk4_236, chunk4_237, chunk4_251, chunk4_252, chunk4_255, chunk4_256]
private theorem checked5_520 : ∀ w ∈ chunk5_520, ¬ Need 5 w.toFinset := by
  have h : chunk5_520.all (routes 4 pool5_520.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_520,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_75 _ hm
  · exact checked4_235 _ hm
  · exact checked4_236 _ hm
  · exact checked4_237 _ hm
  · exact checked4_251 _ hm
  · exact checked4_252 _ hm
  · exact checked4_255 _ hm
  · exact checked4_256 _ hm
private def chunk5_521 : List (List T) := [[wire8738,wire17487,wire34952,wire35064],
  [wire8738,wire17487,wire34952,wire35064,wire61440],
  [wire8738,wire17487,wire34952,wire61440,wire61680],
  [wire8738,wire17487,wire34952,wire61440,wire65295]]
private def pool5_521 : List (List (List T)) := [chunk4_0, chunk4_6, chunk4_240, chunk4_241, chunk4_242, chunk4_243, chunk4_244, chunk4_245, chunk4_247, chunk4_249, chunk4_251, chunk4_256, chunk4_257]
private theorem checked5_521 : ∀ w ∈ chunk5_521, ¬ Need 5 w.toFinset := by
  have h : chunk5_521.all (routes 4 pool5_521.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_521,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_6 _ hm
  · exact checked4_240 _ hm
  · exact checked4_241 _ hm
  · exact checked4_242 _ hm
  · exact checked4_243 _ hm
  · exact checked4_244 _ hm
  · exact checked4_245 _ hm
  · exact checked4_247 _ hm
  · exact checked4_249 _ hm
  · exact checked4_251 _ hm
  · exact checked4_256 _ hm
  · exact checked4_257 _ hm
private def chunk5_522 : List (List T) := [[wire8738,wire17487,wire34952,wire65295],
  [wire8738,wire17487,wire35064],
  [wire8738,wire17487,wire35064,wire61440]]
private def pool5_522 : List (List (List T)) := [chunk4_0, chunk4_2, chunk4_102, chunk4_109, chunk4_147, chunk4_202, chunk4_232, chunk4_235, chunk4_239, chunk4_240, chunk4_241, chunk4_242, chunk4_243, chunk4_244, chunk4_245, chunk4_246, chunk4_247, chunk4_248, chunk4_249, chunk4_250, chunk4_251, chunk4_252, chunk4_257, chunk4_258]
private theorem checked5_522 : ∀ w ∈ chunk5_522, ¬ Need 5 w.toFinset := by
  have h : chunk5_522.all (routes 4 pool5_522.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_522,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hm
  · exact checked4_2 _ hm
  · exact checked4_102 _ hm
  · exact checked4_109 _ hm
  · exact checked4_147 _ hm
  · exact checked4_202 _ hm
  · exact checked4_232 _ hm
  · exact checked4_235 _ hm
  · exact checked4_239 _ hm
  · exact checked4_240 _ hm
  · exact checked4_241 _ hm
  · exact checked4_242 _ hm
  · exact checked4_243 _ hm
  · exact checked4_244 _ hm
  · exact checked4_245 _ hm
  · exact checked4_246 _ hm
  · exact checked4_247 _ hm
  · exact checked4_248 _ hm
  · exact checked4_249 _ hm
  · exact checked4_250 _ hm
  · exact checked4_251 _ hm
  · exact checked4_252 _ hm
  · exact checked4_257 _ hm
  · exact checked4_258 _ hm
#print axioms checked5_522
private def chunk6_0 : List (List T) := [[wire0,wire15,wire240,wire4369,wire8738,wire17476],
  [wire0,wire15,wire240,wire4369,wire8738,wire34952],
  [wire0,wire15,wire240,wire4369,wire17476,wire34952],
  [wire0,wire15,wire240,wire8738,wire17476,wire34952]]
private def pool6_0 : List (List (List T)) := [chunk5_0, chunk5_51, chunk5_57, chunk5_85, chunk5_149]
private theorem checked6_0 : ∀ w ∈ chunk6_0, ¬ Need 6 w.toFinset := by
  have h : chunk6_0.all (routes 5 pool6_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_85 _ hm
  · exact checked5_149 _ hm
private def chunk6_1 : List (List T) := [[wire1,wire15,wire240,wire4369,wire8738,wire17476],
  [wire1,wire15,wire240,wire4369,wire8738,wire34952],
  [wire1,wire15,wire240,wire4369,wire17476,wire34952],
  [wire1,wire15,wire240,wire8738,wire17476,wire34952]]
private def pool6_1 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_51, chunk5_52, chunk5_57, chunk5_65, chunk5_85, chunk5_97, chunk5_149, chunk5_153, chunk5_202, chunk5_203]
private theorem checked6_1 : ∀ w ∈ chunk6_1, ¬ Need 6 w.toFinset := by
  have h : chunk6_1.all (routes 5 pool6_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_57 _ hm
  · exact checked5_65 _ hm
  · exact checked5_85 _ hm
  · exact checked5_97 _ hm
  · exact checked5_149 _ hm
  · exact checked5_153 _ hm
  · exact checked5_202 _ hm
  · exact checked5_203 _ hm
private def chunk6_2 : List (List T) := [[wire2,wire15,wire240,wire3840,wire4369,wire34952],
  [wire2,wire15,wire240,wire4369,wire8738,wire17476],
  [wire2,wire15,wire240,wire4369,wire8738,wire34952],
  [wire2,wire15,wire240,wire4369,wire17476,wire34952]]
private def pool6_2 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_6, chunk5_7, chunk5_43, chunk5_47, chunk5_51, chunk5_52, chunk5_57, chunk5_85, chunk5_86, chunk5_131, chunk5_203, chunk5_204]
private theorem checked6_2 : ∀ w ∈ chunk6_2, ¬ Need 6 w.toFinset := by
  have h : chunk6_2.all (routes 5 pool6_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_43 _ hm
  · exact checked5_47 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_57 _ hm
  · exact checked5_85 _ hm
  · exact checked5_86 _ hm
  · exact checked5_131 _ hm
  · exact checked5_203 _ hm
  · exact checked5_204 _ hm
private def chunk6_3 : List (List T) := [[wire2,wire15,wire240,wire4369,wire34952],
  [wire2,wire15,wire240,wire4369,wire34952,wire61440],
  [wire2,wire15,wire240,wire8738,wire17476,wire34952],
  [wire2,wire15,wire3840,wire4369,wire34952,wire61440]]
private def pool6_3 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_3, chunk5_4, chunk5_5, chunk5_6, chunk5_7, chunk5_8, chunk5_38, chunk5_49, chunk5_111, chunk5_116, chunk5_120, chunk5_121, chunk5_149, chunk5_153, chunk5_204, chunk5_228, chunk5_229, chunk5_240]
private theorem checked6_3 : ∀ w ∈ chunk6_3, ¬ Need 6 w.toFinset := by
  have h : chunk6_3.all (routes 5 pool6_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_7 _ hm
  · exact checked5_8 _ hm
  · exact checked5_38 _ hm
  · exact checked5_49 _ hm
  · exact checked5_111 _ hm
  · exact checked5_116 _ hm
  · exact checked5_120 _ hm
  · exact checked5_121 _ hm
  · exact checked5_149 _ hm
  · exact checked5_153 _ hm
  · exact checked5_204 _ hm
  · exact checked5_228 _ hm
  · exact checked5_229 _ hm
  · exact checked5_240 _ hm
private def chunk6_4 : List (List T) := [[wire2,wire240,wire3840,wire4369,wire34952,wire61440],
  [wire4,wire15,wire240,wire3840,wire4369,wire34952],
  [wire4,wire15,wire240,wire4369,wire8738,wire17476],
  [wire4,wire15,wire240,wire4369,wire8738,wire34952]]
private def pool6_4 : List (List (List T)) := [chunk5_7, chunk5_9, chunk5_10, chunk5_43, chunk5_47, chunk5_51, chunk5_57, chunk5_65, chunk5_131, chunk5_205, chunk5_358, chunk5_453]
private theorem checked6_4 : ∀ w ∈ chunk6_4, ¬ Need 6 w.toFinset := by
  have h : chunk6_4.all (routes 5 pool6_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_7 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_43 _ hm
  · exact checked5_47 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_65 _ hm
  · exact checked5_131 _ hm
  · exact checked5_205 _ hm
  · exact checked5_358 _ hm
  · exact checked5_453 _ hm
private def chunk6_5 : List (List T) := [[wire4,wire15,wire240,wire4369,wire17476,wire34952],
  [wire4,wire15,wire240,wire4369,wire34952],
  [wire4,wire15,wire240,wire4369,wire34952,wire61440],
  [wire4,wire15,wire240,wire8738,wire17476,wire34952]]
private def pool6_5 : List (List (List T)) := [chunk5_8, chunk5_9, chunk5_10, chunk5_11, chunk5_12, chunk5_13, chunk5_14, chunk5_15, chunk5_39, chunk5_49, chunk5_85, chunk5_86, chunk5_111, chunk5_116, chunk5_120, chunk5_132, chunk5_149, chunk5_168, chunk5_205, chunk5_206]
private theorem checked6_5 : ∀ w ∈ chunk6_5, ¬ Need 6 w.toFinset := by
  have h : chunk6_5.all (routes 5 pool6_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_11 _ hm
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_39 _ hm
  · exact checked5_49 _ hm
  · exact checked5_85 _ hm
  · exact checked5_86 _ hm
  · exact checked5_111 _ hm
  · exact checked5_116 _ hm
  · exact checked5_120 _ hm
  · exact checked5_132 _ hm
  · exact checked5_149 _ hm
  · exact checked5_168 _ hm
  · exact checked5_205 _ hm
  · exact checked5_206 _ hm
private def chunk6_6 : List (List T) := [[wire4,wire15,wire3840,wire4369,wire34952,wire61440],
  [wire4,wire240,wire3840,wire4369,wire34952,wire61440],
  [wire8,wire15,wire240,wire4369,wire8738,wire17476],
  [wire8,wire15,wire240,wire4369,wire8738,wire34952]]
private def pool6_6 : List (List (List T)) := [chunk5_12, chunk5_13, chunk5_14, chunk5_15, chunk5_16, chunk5_51, chunk5_57, chunk5_65, chunk5_66, chunk5_132, chunk5_206, chunk5_207, chunk5_229, chunk5_231, chunk5_240, chunk5_357, chunk5_361, chunk5_369]
private theorem checked6_6 : ∀ w ∈ chunk6_6, ¬ Need 6 w.toFinset := by
  have h : chunk6_6.all (routes 5 pool6_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_12 _ hm
  · exact checked5_13 _ hm
  · exact checked5_14 _ hm
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_65 _ hm
  · exact checked5_66 _ hm
  · exact checked5_132 _ hm
  · exact checked5_206 _ hm
  · exact checked5_207 _ hm
  · exact checked5_229 _ hm
  · exact checked5_231 _ hm
  · exact checked5_240 _ hm
  · exact checked5_357 _ hm
  · exact checked5_361 _ hm
  · exact checked5_369 _ hm
private def chunk6_7 : List (List T) := [[wire8,wire15,wire240,wire4369,wire17476,wire34952],
  [wire8,wire15,wire240,wire8738,wire17476,wire34952],
  [wire15,wire16,wire240,wire4369,wire8738,wire17476],
  [wire15,wire16,wire240,wire4369,wire8738,wire34952]]
private def pool6_7 : List (List (List T)) := [chunk5_15, chunk5_16, chunk5_20, chunk5_51, chunk5_52, chunk5_57, chunk5_58, chunk5_67, chunk5_68, chunk5_85, chunk5_97, chunk5_133, chunk5_149, chunk5_154, chunk5_168, chunk5_207, chunk5_324, chunk5_325]
private theorem checked6_7 : ∀ w ∈ chunk6_7, ¬ Need 6 w.toFinset := by
  have h : chunk6_7.all (routes 5 pool6_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_16 _ hm
  · exact checked5_20 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_57 _ hm
  · exact checked5_58 _ hm
  · exact checked5_67 _ hm
  · exact checked5_68 _ hm
  · exact checked5_85 _ hm
  · exact checked5_97 _ hm
  · exact checked5_133 _ hm
  · exact checked5_149 _ hm
  · exact checked5_154 _ hm
  · exact checked5_168 _ hm
  · exact checked5_207 _ hm
  · exact checked5_324 _ hm
  · exact checked5_325 _ hm
private def chunk6_8 : List (List T) := [[wire15,wire16,wire240,wire4369,wire17476,wire34952],
  [wire15,wire16,wire240,wire8738,wire17476,wire34952],
  [wire15,wire32,wire240,wire3840,wire4369,wire17476],
  [wire15,wire32,wire240,wire4369,wire8738,wire17476]]
private def pool6_8 : List (List (List T)) := [chunk5_21, chunk5_22, chunk5_24, chunk5_43, chunk5_47, chunk5_51, chunk5_53, chunk5_85, chunk5_86, chunk5_97, chunk5_136, chunk5_149, chunk5_324, chunk5_325, chunk5_328]
private theorem checked6_8 : ∀ w ∈ chunk6_8, ¬ Need 6 w.toFinset := by
  have h : chunk6_8.all (routes 5 pool6_8.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_8,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_24 _ hm
  · exact checked5_43 _ hm
  · exact checked5_47 _ hm
  · exact checked5_51 _ hm
  · exact checked5_53 _ hm
  · exact checked5_85 _ hm
  · exact checked5_86 _ hm
  · exact checked5_97 _ hm
  · exact checked5_136 _ hm
  · exact checked5_149 _ hm
  · exact checked5_324 _ hm
  · exact checked5_325 _ hm
  · exact checked5_328 _ hm
private def chunk6_9 : List (List T) := [[wire15,wire32,wire240,wire4369,wire8738,wire34952],
  [wire15,wire32,wire240,wire4369,wire17476],
  [wire15,wire32,wire240,wire4369,wire17476,wire34952],
  [wire15,wire32,wire240,wire4369,wire17476,wire61440]]
private def pool6_9 : List (List (List T)) := [chunk5_21, chunk5_22, chunk5_23, chunk5_24, chunk5_25, chunk5_27, chunk5_49, chunk5_57, chunk5_58, chunk5_81, chunk5_85, chunk5_92, chunk5_96, chunk5_97, chunk5_98, chunk5_136, chunk5_325, chunk5_326, chunk5_327, chunk5_329]
private theorem checked6_9 : ∀ w ∈ chunk6_9, ¬ Need 6 w.toFinset := by
  have h : chunk6_9.all (routes 5 pool6_9.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_9,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_21 _ hm
  · exact checked5_22 _ hm
  · exact checked5_23 _ hm
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_27 _ hm
  · exact checked5_49 _ hm
  · exact checked5_57 _ hm
  · exact checked5_58 _ hm
  · exact checked5_81 _ hm
  · exact checked5_85 _ hm
  · exact checked5_92 _ hm
  · exact checked5_96 _ hm
  · exact checked5_97 _ hm
  · exact checked5_98 _ hm
  · exact checked5_136 _ hm
  · exact checked5_325 _ hm
  · exact checked5_326 _ hm
  · exact checked5_327 _ hm
  · exact checked5_329 _ hm
private def chunk6_10 : List (List T) := [[wire15,wire32,wire240,wire8738,wire17476,wire34952],
  [wire15,wire32,wire3840,wire4369,wire17476,wire61440],
  [wire15,wire64,wire240,wire4369,wire8738,wire17476],
  [wire15,wire64,wire240,wire4369,wire8738,wire34952]]
private def pool6_10 : List (List (List T)) := [chunk5_24, chunk5_25, chunk5_26, chunk5_27, chunk5_28, chunk5_51, chunk5_57, chunk5_68, chunk5_136, chunk5_149, chunk5_150, chunk5_155, chunk5_227, chunk5_327, chunk5_330, chunk5_331]
private theorem checked6_10 : ∀ w ∈ chunk6_10, ¬ Need 6 w.toFinset := by
  have h : chunk6_10.all (routes 5 pool6_10.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_10,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_24 _ hm
  · exact checked5_25 _ hm
  · exact checked5_26 _ hm
  · exact checked5_27 _ hm
  · exact checked5_28 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_68 _ hm
  · exact checked5_136 _ hm
  · exact checked5_149 _ hm
  · exact checked5_150 _ hm
  · exact checked5_155 _ hm
  · exact checked5_227 _ hm
  · exact checked5_327 _ hm
  · exact checked5_330 _ hm
  · exact checked5_331 _ hm
private def chunk6_11 : List (List T) := [[wire15,wire64,wire240,wire4369,wire17476,wire34952],
  [wire15,wire64,wire240,wire8738,wire17476,wire34952],
  [wire15,wire128,wire240,wire3840,wire4369,wire17476],
  [wire15,wire128,wire240,wire4369,wire8738,wire17476]]
private def pool6_11 : List (List (List T)) := [chunk5_28, chunk5_33, chunk5_44, chunk5_48, chunk5_51, chunk5_85, chunk5_87, chunk5_137, chunk5_149, chunk5_150, chunk5_169, chunk5_330, chunk5_331, chunk5_332, chunk5_334, chunk5_335]
private theorem checked6_11 : ∀ w ∈ chunk6_11, ¬ Need 6 w.toFinset := by
  have h : chunk6_11.all (routes 5 pool6_11.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_11,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_28 _ hm
  · exact checked5_33 _ hm
  · exact checked5_44 _ hm
  · exact checked5_48 _ hm
  · exact checked5_51 _ hm
  · exact checked5_85 _ hm
  · exact checked5_87 _ hm
  · exact checked5_137 _ hm
  · exact checked5_149 _ hm
  · exact checked5_150 _ hm
  · exact checked5_169 _ hm
  · exact checked5_330 _ hm
  · exact checked5_331 _ hm
  · exact checked5_332 _ hm
  · exact checked5_334 _ hm
  · exact checked5_335 _ hm
private def chunk6_12 : List (List T) := [[wire15,wire128,wire240,wire4369,wire8738,wire34952],
  [wire15,wire128,wire240,wire4369,wire17476],
  [wire15,wire128,wire240,wire4369,wire17476,wire34952],
  [wire15,wire128,wire240,wire4369,wire17476,wire61440]]
private def pool6_12 : List (List (List T)) := [chunk5_8, chunk5_32, chunk5_33, chunk5_34, chunk5_35, chunk5_36, chunk5_37, chunk5_49, chunk5_57, chunk5_68, chunk5_82, chunk5_85, chunk5_92, chunk5_96, chunk5_98, chunk5_137, chunk5_138, chunk5_332, chunk5_333, chunk5_335, chunk5_336]
private theorem checked6_12 : ∀ w ∈ chunk6_12, ¬ Need 6 w.toFinset := by
  have h : chunk6_12.all (routes 5 pool6_12.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_12,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_34 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_37 _ hm
  · exact checked5_49 _ hm
  · exact checked5_57 _ hm
  · exact checked5_68 _ hm
  · exact checked5_82 _ hm
  · exact checked5_85 _ hm
  · exact checked5_92 _ hm
  · exact checked5_96 _ hm
  · exact checked5_98 _ hm
  · exact checked5_137 _ hm
  · exact checked5_138 _ hm
  · exact checked5_332 _ hm
  · exact checked5_333 _ hm
  · exact checked5_335 _ hm
  · exact checked5_336 _ hm
private def chunk6_13 : List (List T) := [[wire15,wire128,wire240,wire8738,wire17476,wire34952],
  [wire15,wire128,wire3840,wire4369,wire17476,wire61440],
  [wire15,wire240,wire255,wire4369,wire8738,wire17476],
  [wire15,wire240,wire255,wire4369,wire8738,wire34952]]
private def pool6_13 : List (List (List T)) := [chunk5_6, chunk5_14, chunk5_24, chunk5_26, chunk5_28, chunk5_35, chunk5_36, chunk5_51, chunk5_57, chunk5_149, chunk5_155, chunk5_169, chunk5_207, chunk5_209, chunk5_211, chunk5_217, chunk5_226, chunk5_232, chunk5_241, chunk5_334, chunk5_336, chunk5_337, chunk5_338, chunk5_340, chunk5_346]
private theorem checked6_13 : ∀ w ∈ chunk6_13, ¬ Need 6 w.toFinset := by
  have h : chunk6_13.all (routes 5 pool6_13.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_13,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_14 _ hm
  · exact checked5_24 _ hm
  · exact checked5_26 _ hm
  · exact checked5_28 _ hm
  · exact checked5_35 _ hm
  · exact checked5_36 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_149 _ hm
  · exact checked5_155 _ hm
  · exact checked5_169 _ hm
  · exact checked5_207 _ hm
  · exact checked5_209 _ hm
  · exact checked5_211 _ hm
  · exact checked5_217 _ hm
  · exact checked5_226 _ hm
  · exact checked5_232 _ hm
  · exact checked5_241 _ hm
  · exact checked5_334 _ hm
  · exact checked5_336 _ hm
  · exact checked5_337 _ hm
  · exact checked5_338 _ hm
  · exact checked5_340 _ hm
  · exact checked5_346 _ hm
private def chunk6_14 : List (List T) := [[wire15,wire240,wire255,wire4369,wire17476,wire34952],
  [wire15,wire240,wire255,wire8738,wire17476,wire34952],
  [wire15,wire240,wire256,wire4369,wire8738,wire17476],
  [wire15,wire240,wire256,wire4369,wire8738,wire34952]]
private def pool6_14 : List (List (List T)) := [chunk5_14, chunk5_29, chunk5_35, chunk5_37, chunk5_51, chunk5_53, chunk5_57, chunk5_58, chunk5_70, chunk5_85, chunk5_149, chunk5_212, chunk5_214, chunk5_218, chunk5_342, chunk5_347, chunk5_349]
private theorem checked6_14 : ∀ w ∈ chunk6_14, ¬ Need 6 w.toFinset := by
  have h : chunk6_14.all (routes 5 pool6_14.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_14,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_29 _ hm
  · exact checked5_35 _ hm
  · exact checked5_37 _ hm
  · exact checked5_51 _ hm
  · exact checked5_53 _ hm
  · exact checked5_57 _ hm
  · exact checked5_58 _ hm
  · exact checked5_70 _ hm
  · exact checked5_85 _ hm
  · exact checked5_149 _ hm
  · exact checked5_212 _ hm
  · exact checked5_214 _ hm
  · exact checked5_218 _ hm
  · exact checked5_342 _ hm
  · exact checked5_347 _ hm
  · exact checked5_349 _ hm
private def chunk6_15 : List (List T) := [[wire15,wire240,wire256,wire4369,wire17476,wire34952],
  [wire15,wire240,wire256,wire8738,wire17476,wire34952],
  [wire15,wire240,wire512,wire4369,wire8738,wire17476],
  [wire15,wire240,wire512,wire4369,wire8738,wire34952]]
private def pool6_15 : List (List (List T)) := [chunk5_51, chunk5_53, chunk5_57, chunk5_58, chunk5_85, chunk5_87, chunk5_100, chunk5_141, chunk5_222, chunk5_352]
private theorem checked6_15 : ∀ w ∈ chunk6_15, ¬ Need 6 w.toFinset := by
  have h : chunk6_15.all (routes 5 pool6_15.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_15,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_53 _ hm
  · exact checked5_57 _ hm
  · exact checked5_58 _ hm
  · exact checked5_85 _ hm
  · exact checked5_87 _ hm
  · exact checked5_100 _ hm
  · exact checked5_141 _ hm
  · exact checked5_222 _ hm
  · exact checked5_352 _ hm
private def chunk6_16 : List (List T) := [[wire15,wire240,wire512,wire4369,wire17476,wire34952],
  [wire15,wire240,wire512,wire8738,wire17476,wire34952],
  [wire15,wire240,wire1024,wire4369,wire8738,wire17476],
  [wire15,wire240,wire1024,wire4369,wire8738,wire34952]]
private def pool6_16 : List (List (List T)) := [chunk5_51, chunk5_59, chunk5_71, chunk5_87, chunk5_100, chunk5_142, chunk5_149, chunk5_150, chunk5_156, chunk5_223, chunk5_352, chunk5_353]
private theorem checked6_16 : ∀ w ∈ chunk6_16, ¬ Need 6 w.toFinset := by
  have h : chunk6_16.all (routes 5 pool6_16.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_16,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_59 _ hm
  · exact checked5_71 _ hm
  · exact checked5_87 _ hm
  · exact checked5_100 _ hm
  · exact checked5_142 _ hm
  · exact checked5_149 _ hm
  · exact checked5_150 _ hm
  · exact checked5_156 _ hm
  · exact checked5_223 _ hm
  · exact checked5_352 _ hm
  · exact checked5_353 _ hm
private def chunk6_17 : List (List T) := [[wire15,wire240,wire1024,wire4369,wire17476,wire34952],
  [wire15,wire240,wire1024,wire8738,wire17476,wire34952],
  [wire15,wire240,wire2048,wire4369,wire8738,wire17476],
  [wire15,wire240,wire2048,wire4369,wire8738,wire34952]]
private def pool6_17 : List (List (List T)) := [chunk5_53, chunk5_57, chunk5_71, chunk5_85, chunk5_87, chunk5_142, chunk5_149, chunk5_151, chunk5_170, chunk5_223, chunk5_224, chunk5_352, chunk5_353]
private theorem checked6_17 : ∀ w ∈ chunk6_17, ¬ Need 6 w.toFinset := by
  have h : chunk6_17.all (routes 5 pool6_17.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_17,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_53 _ hm
  · exact checked5_57 _ hm
  · exact checked5_71 _ hm
  · exact checked5_85 _ hm
  · exact checked5_87 _ hm
  · exact checked5_142 _ hm
  · exact checked5_149 _ hm
  · exact checked5_151 _ hm
  · exact checked5_170 _ hm
  · exact checked5_223 _ hm
  · exact checked5_224 _ hm
  · exact checked5_352 _ hm
  · exact checked5_353 _ hm
private def chunk6_18 : List (List T) := [[wire15,wire240,wire2048,wire4369,wire17476,wire34952],
  [wire15,wire240,wire2048,wire8738,wire17476,wire34952],
  [wire15,wire240,wire3840,wire4369,wire8738,wire17476],
  [wire15,wire240,wire3840,wire4369,wire8738,wire17476,wire63624]]
private def pool6_18 : List (List (List T)) := [chunk5_52, chunk5_54, chunk5_72, chunk5_85, chunk5_101, chunk5_142, chunk5_149, chunk5_156, chunk5_171, chunk5_224, chunk5_225, chunk5_353, chunk5_361]
private theorem checked6_18 : ∀ w ∈ chunk6_18, ¬ Need 6 w.toFinset := by
  have h : chunk6_18.all (routes 5 pool6_18.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_18,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_52 _ hm
  · exact checked5_54 _ hm
  · exact checked5_72 _ hm
  · exact checked5_85 _ hm
  · exact checked5_101 _ hm
  · exact checked5_142 _ hm
  · exact checked5_149 _ hm
  · exact checked5_156 _ hm
  · exact checked5_171 _ hm
  · exact checked5_224 _ hm
  · exact checked5_225 _ hm
  · exact checked5_353 _ hm
  · exact checked5_361 _ hm
private def chunk6_19 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire8738,wire20292],
  [wire15,wire240,wire3840,wire4369,wire8738,wire21845],
  [wire15,wire240,wire3840,wire4369,wire8738,wire26214],
  [wire15,wire240,wire3840,wire4369,wire8738,wire30583]]
private def pool6_19 : List (List (List T)) := [chunk5_44, chunk5_54, chunk5_55, chunk5_56, chunk5_72, chunk5_73, chunk5_369]
private theorem checked6_19 : ∀ w ∈ chunk6_19, ¬ Need 6 w.toFinset := by
  have h : chunk6_19.all (routes 5 pool6_19.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_19,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_44 _ hm
  · exact checked5_54 _ hm
  · exact checked5_55 _ hm
  · exact checked5_56 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_369 _ hm
private def chunk6_20 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire8738,wire34952],
  [wire15,wire240,wire3840,wire4369,wire8738,wire34952,wire62532],
  [wire15,wire240,wire3840,wire4369,wire8738,wire36744],
  [wire15,wire240,wire3840,wire4369,wire8738,wire39321]]
private def pool6_20 : List (List (List T)) := [chunk5_44, chunk5_57, chunk5_59, chunk5_60, chunk5_73, chunk5_74, chunk5_232, chunk5_241]
private theorem checked6_20 : ∀ w ∈ chunk6_20, ¬ Need 6 w.toFinset := by
  have h : chunk6_20.all (routes 5 pool6_20.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_20,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_44 _ hm
  · exact checked5_57 _ hm
  · exact checked5_59 _ hm
  · exact checked5_60 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_232 _ hm
  · exact checked5_241 _ hm
private def chunk6_21 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire8738,wire43690],
  [wire15,wire240,wire3840,wire4369,wire8738,wire48059],
  [wire15,wire240,wire3840,wire4369,wire8738,wire62532],
  [wire15,wire240,wire3840,wire4369,wire8738,wire63624]]
private def pool6_21 : List (List (List T)) := [chunk5_45, chunk5_61, chunk5_64, chunk5_74, chunk5_75, chunk5_225, chunk5_232, chunk5_355, chunk5_361]
private theorem checked6_21 : ∀ w ∈ chunk6_21, ¬ Need 6 w.toFinset := by
  have h : chunk6_21.all (routes 5 pool6_21.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_21,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_45 _ hm
  · exact checked5_61 _ hm
  · exact checked5_64 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
  · exact checked5_225 _ hm
  · exact checked5_232 _ hm
  · exact checked5_355 _ hm
  · exact checked5_361 _ hm
private def chunk6_22 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire8751,wire17476],
  [wire15,wire240,wire3840,wire4369,wire8946,wire34952],
  [wire15,wire240,wire3840,wire4369,wire12066,wire17476],
  [wire15,wire240,wire3840,wire4369,wire12066,wire34952]]
private def pool6_22 : List (List (List T)) := [chunk5_66, chunk5_69, chunk5_72, chunk5_73, chunk5_74, chunk5_76, chunk5_454]
private theorem checked6_22 : ∀ w ∈ chunk6_22, ¬ Need 6 w.toFinset := by
  have h : chunk6_22.all (routes 5 pool6_22.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_22,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_66 _ hm
  · exact checked5_69 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_76 _ hm
  · exact checked5_454 _ hm
private def chunk6_23 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire13107,wire17476],
  [wire15,wire240,wire3840,wire4369,wire13107,wire34952],
  [wire15,wire240,wire3840,wire4369,wire17476,wire26214],
  [wire15,wire240,wire3840,wire4369,wire17476,wire30583]]
private def pool6_23 : List (List (List T)) := [chunk5_30, chunk5_44, chunk5_45, chunk5_77, chunk5_78, chunk5_80, chunk5_83, chunk5_84, chunk5_101]
private theorem checked6_23 : ∀ w ∈ chunk6_23, ¬ Need 6 w.toFinset := by
  have h : chunk6_23.all (routes 5 pool6_23.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_23,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_30 _ hm
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
  · exact checked5_77 _ hm
  · exact checked5_78 _ hm
  · exact checked5_80 _ hm
  · exact checked5_83 _ hm
  · exact checked5_84 _ hm
  · exact checked5_101 _ hm
private def chunk6_24 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire17476,wire34952],
  [wire15,wire240,wire3840,wire4369,wire17476,wire34952,wire61986],
  [wire15,wire240,wire3840,wire4369,wire17476,wire34959],
  [wire15,wire240,wire3840,wire4369,wire17476,wire36744]]
private def pool6_24 : List (List (List T)) := [chunk5_85, chunk5_88, chunk5_102, chunk5_233, chunk5_242, chunk5_361]
private theorem checked6_24 : ∀ w ∈ chunk6_24, ¬ Need 6 w.toFinset := by
  have h : chunk6_24.all (routes 5 pool6_24.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_24,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_85 _ hm
  · exact checked5_88 _ hm
  · exact checked5_102 _ hm
  · exact checked5_233 _ hm
  · exact checked5_242 _ hm
  · exact checked5_361 _ hm
private def chunk6_25 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire17476,wire39321],
  [wire15,wire240,wire3840,wire4369,wire17476,wire52428],
  [wire15,wire240,wire3840,wire4369,wire17476,wire56797],
  [wire15,wire240,wire3840,wire4369,wire17476,wire61986]]
private def pool6_25 : List (List (List T)) := [chunk5_45, chunk5_89, chunk5_91, chunk5_92, chunk5_95, chunk5_103, chunk5_104, chunk5_233]
private theorem checked6_25 : ∀ w ∈ chunk6_25, ¬ Need 6 w.toFinset := by
  have h : chunk6_25.all (routes 5 pool6_25.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_25,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_45 _ hm
  · exact checked5_89 _ hm
  · exact checked5_91 _ hm
  · exact checked5_92 _ hm
  · exact checked5_95 _ hm
  · exact checked5_103 _ hm
  · exact checked5_104 _ hm
  · exact checked5_233 _ hm
private def chunk6_26 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire17476,wire63624],
  [wire15,wire240,wire3840,wire4369,wire17652,wire34952],
  [wire15,wire240,wire3840,wire4369,wire20292,wire34952],
  [wire15,wire240,wire3840,wire4369,wire21845,wire34952]]
private def pool6_26 : List (List (List T)) := [chunk5_45, chunk5_96, chunk5_99, chunk5_102, chunk5_104, chunk5_106, chunk5_107, chunk5_228, chunk5_370]
private theorem checked6_26 : ∀ w ∈ chunk6_26, ¬ Need 6 w.toFinset := by
  have h : chunk6_26.all (routes 5 pool6_26.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_26,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_45 _ hm
  · exact checked5_96 _ hm
  · exact checked5_99 _ hm
  · exact checked5_102 _ hm
  · exact checked5_104 _ hm
  · exact checked5_106 _ hm
  · exact checked5_107 _ hm
  · exact checked5_228 _ hm
  · exact checked5_370 _ hm
private def chunk6_27 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire34952,wire43690],
  [wire15,wire240,wire3840,wire4369,wire34952,wire48059],
  [wire15,wire240,wire3840,wire4369,wire34952,wire52428],
  [wire15,wire240,wire3840,wire4369,wire34952,wire56797]]
private def pool6_27 : List (List (List T)) := [chunk5_17, chunk5_46, chunk5_112, chunk5_114, chunk5_115, chunk5_116, chunk5_122, chunk5_123]
private theorem checked6_27 : ∀ w ∈ chunk6_27, ¬ Need 6 w.toFinset := by
  have h : chunk6_27.all (routes 5 pool6_27.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_27,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_17 _ hm
  · exact checked5_46 _ hm
  · exact checked5_112 _ hm
  · exact checked5_114 _ hm
  · exact checked5_115 _ hm
  · exact checked5_116 _ hm
  · exact checked5_122 _ hm
  · exact checked5_123 _ hm
private def chunk6_28 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire34952,wire61986],
  [wire15,wire240,wire3840,wire4369,wire34952,wire62532],
  [wire15,wire240,wire3840,wire4383,wire8738,wire34952],
  [wire15,wire240,wire3840,wire4593,wire8738,wire17476]]
private def pool6_28 : List (List (List T)) := [chunk5_119, chunk5_123, chunk5_124, chunk5_134, chunk5_135, chunk5_138, chunk5_140, chunk5_358, chunk5_362, chunk5_454]
private theorem checked6_28 : ∀ w ∈ chunk6_28, ¬ Need 6 w.toFinset := by
  have h : chunk6_28.all (routes 5 pool6_28.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_28,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_119 _ hm
  · exact checked5_123 _ hm
  · exact checked5_124 _ hm
  · exact checked5_134 _ hm
  · exact checked5_135 _ hm
  · exact checked5_138 _ hm
  · exact checked5_140 _ hm
  · exact checked5_358 _ hm
  · exact checked5_362 _ hm
  · exact checked5_454 _ hm
private def chunk6_29 : List (List T) := [[wire15,wire240,wire3840,wire8738,wire13107,wire17476],
  [wire15,wire240,wire3840,wire8738,wire13107,wire34952],
  [wire15,wire240,wire3840,wire8738,wire17476,wire21845],
  [wire15,wire240,wire3840,wire8738,wire17476,wire30583]]
private def pool6_29 : List (List (List T)) := [chunk5_44, chunk5_45, chunk5_143, chunk5_145, chunk5_171, chunk5_363]
private theorem checked6_29 : ∀ w ∈ chunk6_29, ¬ Need 6 w.toFinset := by
  have h : chunk6_29.all (routes 5 pool6_29.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_29,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_44 _ hm
  · exact checked5_45 _ hm
  · exact checked5_143 _ hm
  · exact checked5_145 _ hm
  · exact checked5_171 _ hm
  · exact checked5_363 _ hm
private def chunk6_30 : List (List T) := [[wire15,wire240,wire3840,wire8738,wire17476,wire34952],
  [wire15,wire240,wire3840,wire8738,wire17476,wire35064],
  [wire15,wire240,wire3840,wire8738,wire17476,wire43690],
  [wire15,wire240,wire3840,wire8738,wire17476,wire52428]]
private def pool6_30 : List (List (List T)) := [chunk5_0, chunk5_46, chunk5_156, chunk5_171, chunk5_234, chunk5_242, chunk5_363, chunk5_364]
private theorem checked6_30 : ∀ w ∈ chunk6_30, ¬ Need 6 w.toFinset := by
  have h : chunk6_30.all (routes 5 pool6_30.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_30,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_46 _ hm
  · exact checked5_156 _ hm
  · exact checked5_171 _ hm
  · exact checked5_234 _ hm
  · exact checked5_242 _ hm
  · exact checked5_363 _ hm
  · exact checked5_364 _ hm
private def chunk6_31 : List (List T) := [[wire15,wire240,wire3840,wire8738,wire17476,wire61166],
  [wire15,wire240,wire3840,wire8738,wire17487,wire34952],
  [wire15,wire240,wire3840,wire8738,wire26214,wire34952],
  [wire15,wire240,wire3840,wire8738,wire34952,wire39321]]
private def pool6_31 : List (List (List T)) := [chunk5_0, chunk5_46, chunk5_156, chunk5_171, chunk5_172, chunk5_234, chunk5_363, chunk5_370]
private theorem checked6_31 : ∀ w ∈ chunk6_31, ¬ Need 6 w.toFinset := by
  have h : chunk6_31.all (routes 5 pool6_31.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_31,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_46 _ hm
  · exact checked5_156 _ hm
  · exact checked5_171 _ hm
  · exact checked5_172 _ hm
  · exact checked5_234 _ hm
  · exact checked5_363 _ hm
  · exact checked5_370 _ hm
private def chunk6_32 : List (List T) := [[wire15,wire240,wire3840,wire8738,wire34952,wire48059],
  [wire15,wire240,wire3840,wire8738,wire34952,wire52428],
  [wire15,wire240,wire3840,wire8738,wire34952,wire61166],
  [wire15,wire240,wire3840,wire17476,wire21845,wire34952]]
private def pool6_32 : List (List (List T)) := [chunk5_45, chunk5_47, chunk5_164, chunk5_165, chunk5_172, chunk5_179, chunk5_235, chunk5_366]
private theorem checked6_32 : ∀ w ∈ chunk6_32, ¬ Need 6 w.toFinset := by
  have h : chunk6_32.all (routes 5 pool6_32.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_32,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_45 _ hm
  · exact checked5_47 _ hm
  · exact checked5_164 _ hm
  · exact checked5_165 _ hm
  · exact checked5_172 _ hm
  · exact checked5_179 _ hm
  · exact checked5_235 _ hm
  · exact checked5_366 _ hm
private def chunk6_33 : List (List T) := [[wire15,wire240,wire3840,wire17476,wire26214,wire34952],
  [wire15,wire240,wire3840,wire17476,wire34952,wire39321],
  [wire15,wire240,wire3840,wire17476,wire34952,wire43690],
  [wire15,wire240,wire3840,wire17476,wire34952,wire56797]]
private def pool6_33 : List (List (List T)) := [chunk5_46, chunk5_47, chunk5_185, chunk5_190, chunk5_191, chunk5_237, chunk5_366]
private theorem checked6_33 : ∀ w ∈ chunk6_33, ¬ Need 6 w.toFinset := by
  have h : chunk6_33.all (routes 5 pool6_33.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_33,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_46 _ hm
  · exact checked5_47 _ hm
  · exact checked5_185 _ hm
  · exact checked5_190 _ hm
  · exact checked5_191 _ hm
  · exact checked5_237 _ hm
  · exact checked5_366 _ hm
private def chunk6_34 : List (List T) := [[wire15,wire240,wire3840,wire17476,wire34952,wire61166],
  [wire15,wire240,wire3855,wire4369,wire8738,wire17476],
  [wire15,wire240,wire3855,wire4369,wire8738,wire34952],
  [wire15,wire240,wire3855,wire4369,wire17476,wire34952]]
private def pool6_34 : List (List (List T)) := [chunk5_39, chunk5_40, chunk5_51, chunk5_57, chunk5_76, chunk5_85, chunk5_88, chunk5_186, chunk5_191, chunk5_455]
private theorem checked6_34 : ∀ w ∈ chunk6_34, ¬ Need 6 w.toFinset := by
  have h : chunk6_34.all (routes 5 pool6_34.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_34,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_76 _ hm
  · exact checked5_85 _ hm
  · exact checked5_88 _ hm
  · exact checked5_186 _ hm
  · exact checked5_191 _ hm
  · exact checked5_455 _ hm
private def chunk6_35 : List (List T) := [[wire15,wire240,wire3855,wire8738,wire17476,wire34952],
  [wire15,wire240,wire4080,wire4369,wire8738,wire17476],
  [wire15,wire240,wire4080,wire4369,wire8738,wire34952],
  [wire15,wire240,wire4080,wire4369,wire17476,wire34952]]
private def pool6_35 : List (List (List T)) := [chunk5_39, chunk5_41, chunk5_51, chunk5_57, chunk5_76, chunk5_85, chunk5_104, chunk5_149, chunk5_241, chunk5_370, chunk5_455, chunk5_456]
private theorem checked6_35 : ∀ w ∈ chunk6_35, ¬ Need 6 w.toFinset := by
  have h : chunk6_35.all (routes 5 pool6_35.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_35,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_39 _ hm
  · exact checked5_41 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_76 _ hm
  · exact checked5_85 _ hm
  · exact checked5_104 _ hm
  · exact checked5_149 _ hm
  · exact checked5_241 _ hm
  · exact checked5_370 _ hm
  · exact checked5_455 _ hm
  · exact checked5_456 _ hm
private def chunk6_36 : List (List T) := [[wire15,wire240,wire4080,wire8738,wire17476,wire34952],
  [wire15,wire240,wire4095,wire4369,wire8738,wire17476],
  [wire15,wire240,wire4095,wire4369,wire8738,wire34952],
  [wire15,wire240,wire4095,wire4369,wire17476,wire34952]]
private def pool6_36 : List (List (List T)) := [chunk5_39, chunk5_40, chunk5_41, chunk5_42, chunk5_51, chunk5_57, chunk5_85, chunk5_149, chunk5_242, chunk5_371, chunk5_456]
private theorem checked6_36 : ∀ w ∈ chunk6_36, ¬ Need 6 w.toFinset := by
  have h : chunk6_36.all (routes 5 pool6_36.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_36,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_39 _ hm
  · exact checked5_40 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_85 _ hm
  · exact checked5_149 _ hm
  · exact checked5_242 _ hm
  · exact checked5_371 _ hm
  · exact checked5_456 _ hm
private def chunk6_37 : List (List T) := [[wire15,wire240,wire4095,wire8738,wire17476,wire34952],
  [wire15,wire240,wire4096,wire4369,wire8738,wire17476],
  [wire15,wire240,wire4096,wire4369,wire8738,wire34952],
  [wire15,wire240,wire4096,wire4369,wire17476,wire34952]]
private def pool6_37 : List (List (List T)) := [chunk5_51, chunk5_54, chunk5_57, chunk5_59, chunk5_76, chunk5_85, chunk5_88, chunk5_104, chunk5_149, chunk5_243, chunk5_372]
private theorem checked6_37 : ∀ w ∈ chunk6_37, ¬ Need 6 w.toFinset := by
  have h : chunk6_37.all (routes 5 pool6_37.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_37,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_54 _ hm
  · exact checked5_57 _ hm
  · exact checked5_59 _ hm
  · exact checked5_76 _ hm
  · exact checked5_85 _ hm
  · exact checked5_88 _ hm
  · exact checked5_104 _ hm
  · exact checked5_149 _ hm
  · exact checked5_243 _ hm
  · exact checked5_372 _ hm
private def chunk6_38 : List (List T) := [[wire15,wire240,wire4096,wire8738,wire17476,wire34952],
  [wire15,wire240,wire4369,wire4383,wire8738,wire17476],
  [wire15,wire240,wire4369,wire4383,wire8738,wire34952],
  [wire15,wire240,wire4369,wire4383,wire17476,wire34952]]
private def pool6_38 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_2, chunk5_9, chunk5_51, chunk5_57, chunk5_80, chunk5_85, chunk5_89, chunk5_133, chunk5_135, chunk5_243, chunk5_372, chunk5_373, chunk5_457]
private theorem checked6_38 : ∀ w ∈ chunk6_38, ¬ Need 6 w.toFinset := by
  have h : chunk6_38.all (routes 5 pool6_38.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_38,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_9 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_80 _ hm
  · exact checked5_85 _ hm
  · exact checked5_89 _ hm
  · exact checked5_133 _ hm
  · exact checked5_135 _ hm
  · exact checked5_243 _ hm
  · exact checked5_372 _ hm
  · exact checked5_373 _ hm
  · exact checked5_457 _ hm
private def chunk6_39 : List (List T) := [[wire15,wire240,wire4369,wire4593,wire8738,wire17476],
  [wire15,wire240,wire4369,wire4593,wire8738,wire34952],
  [wire15,wire240,wire4369,wire4593,wire17476,wire34952],
  [wire15,wire240,wire4369,wire7953,wire8738,wire17476]]
private def pool6_39 : List (List (List T)) := [chunk5_20, chunk5_21, chunk5_32, chunk5_51, chunk5_55, chunk5_57, chunk5_80, chunk5_85, chunk5_107, chunk5_138, chunk5_139, chunk5_140, chunk5_243, chunk5_244, chunk5_457, chunk5_458]
private theorem checked6_39 : ∀ w ∈ chunk6_39, ¬ Need 6 w.toFinset := by
  have h : chunk6_39.all (routes 5 pool6_39.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_39,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_20 _ hm
  · exact checked5_21 _ hm
  · exact checked5_32 _ hm
  · exact checked5_51 _ hm
  · exact checked5_55 _ hm
  · exact checked5_57 _ hm
  · exact checked5_80 _ hm
  · exact checked5_85 _ hm
  · exact checked5_107 _ hm
  · exact checked5_138 _ hm
  · exact checked5_139 _ hm
  · exact checked5_140 _ hm
  · exact checked5_243 _ hm
  · exact checked5_244 _ hm
  · exact checked5_457 _ hm
  · exact checked5_458 _ hm
private def chunk6_40 : List (List T) := [[wire15,wire240,wire4369,wire7953,wire8738,wire34952],
  [wire15,wire240,wire4369,wire7953,wire17476,wire34952],
  [wire15,wire240,wire4369,wire8192,wire8738,wire17476],
  [wire15,wire240,wire4369,wire8192,wire8738,wire34952]]
private def pool6_40 : List (List (List T)) := [chunk5_51, chunk5_55, chunk5_57, chunk5_60, chunk5_80, chunk5_85, chunk5_89, chunk5_107, chunk5_143]
private theorem checked6_40 : ∀ w ∈ chunk6_40, ¬ Need 6 w.toFinset := by
  have h : chunk6_40.all (routes 5 pool6_40.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_40,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_55 _ hm
  · exact checked5_57 _ hm
  · exact checked5_60 _ hm
  · exact checked5_80 _ hm
  · exact checked5_85 _ hm
  · exact checked5_89 _ hm
  · exact checked5_107 _ hm
  · exact checked5_143 _ hm
private def chunk6_41 : List (List T) := [[wire15,wire240,wire4369,wire8192,wire17476,wire34952],
  [wire15,wire240,wire4369,wire8738,wire8751,wire17476],
  [wire15,wire240,wire4369,wire8738,wire8751,wire34952],
  [wire15,wire240,wire4369,wire8738,wire8946,wire17476]]
private def pool6_41 : List (List (List T)) := [chunk5_6, chunk5_24, chunk5_51, chunk5_57, chunk5_66, chunk5_67, chunk5_69, chunk5_90, chunk5_108, chunk5_146, chunk5_290, chunk5_418, chunk5_458, chunk5_459]
private theorem checked6_41 : ∀ w ∈ chunk6_41, ¬ Need 6 w.toFinset := by
  have h : chunk6_41.all (routes 5 pool6_41.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_41,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_6 _ hm
  · exact checked5_24 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_66 _ hm
  · exact checked5_67 _ hm
  · exact checked5_69 _ hm
  · exact checked5_90 _ hm
  · exact checked5_108 _ hm
  · exact checked5_146 _ hm
  · exact checked5_290 _ hm
  · exact checked5_418 _ hm
  · exact checked5_458 _ hm
  · exact checked5_459 _ hm
private def chunk6_42 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire8946,wire34952],
  [wire15,wire240,wire4369,wire8738,wire12066,wire17476],
  [wire15,wire240,wire4369,wire8738,wire12066,wire34952],
  [wire15,wire240,wire4369,wire8738,wire13107,wire17476]]
private def pool6_42 : List (List (List T)) := [chunk5_51, chunk5_55, chunk5_56, chunk5_57, chunk5_61, chunk5_69, chunk5_72, chunk5_73, chunk5_74, chunk5_77, chunk5_143, chunk5_144, chunk5_459]
private theorem checked6_42 : ∀ w ∈ chunk6_42, ¬ Need 6 w.toFinset := by
  have h : chunk6_42.all (routes 5 pool6_42.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_42,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_55 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
  · exact checked5_61 _ hm
  · exact checked5_69 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_77 _ hm
  · exact checked5_143 _ hm
  · exact checked5_144 _ hm
  · exact checked5_459 _ hm
private def chunk6_43 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire13107,wire34952],
  [wire15,wire240,wire4369,wire8738,wire16384,wire17476],
  [wire15,wire240,wire4369,wire8738,wire16384,wire34952],
  [wire15,wire240,wire4369,wire8738,wire17476]]
private def pool6_43 : List (List (List T)) := [chunk5_21, chunk5_51, chunk5_54, chunk5_55, chunk5_57, chunk5_61, chunk5_62, chunk5_66, chunk5_77, chunk5_78, chunk5_79, chunk5_82, chunk5_91, chunk5_108, chunk5_138, chunk5_143, chunk5_144, chunk5_145, chunk5_147, chunk5_153, chunk5_207, chunk5_246, chunk5_337, chunk5_373, chunk5_374, chunk5_375]
private theorem checked6_43 : ∀ w ∈ chunk6_43, ¬ Need 6 w.toFinset := by
  have h : chunk6_43.all (routes 5 pool6_43.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_43,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_21 _ hm
  · exact checked5_51 _ hm
  · exact checked5_54 _ hm
  · exact checked5_55 _ hm
  · exact checked5_57 _ hm
  · exact checked5_61 _ hm
  · exact checked5_62 _ hm
  · exact checked5_66 _ hm
  · exact checked5_77 _ hm
  · exact checked5_78 _ hm
  · exact checked5_79 _ hm
  · exact checked5_82 _ hm
  · exact checked5_91 _ hm
  · exact checked5_108 _ hm
  · exact checked5_138 _ hm
  · exact checked5_143 _ hm
  · exact checked5_144 _ hm
  · exact checked5_145 _ hm
  · exact checked5_147 _ hm
  · exact checked5_153 _ hm
  · exact checked5_207 _ hm
  · exact checked5_246 _ hm
  · exact checked5_337 _ hm
  · exact checked5_373 _ hm
  · exact checked5_374 _ hm
  · exact checked5_375 _ hm
private def chunk6_44 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire17487],
  [wire15,wire240,wire4369,wire8738,wire17476,wire17652],
  [wire15,wire240,wire4369,wire8738,wire17476,wire20292],
  [wire15,wire240,wire4369,wire8738,wire17476,wire21845]]
private def pool6_44 : List (List (List T)) := [chunk5_21, chunk5_27, chunk5_51, chunk5_54, chunk5_82, chunk5_83, chunk5_98, chunk5_101, chunk5_105, chunk5_147, chunk5_154, chunk5_172, chunk5_291, chunk5_374, chunk5_376, chunk5_389]
private theorem checked6_44 : ∀ w ∈ chunk6_44, ¬ Need 6 w.toFinset := by
  have h : chunk6_44.all (routes 5 pool6_44.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_44,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_21 _ hm
  · exact checked5_27 _ hm
  · exact checked5_51 _ hm
  · exact checked5_54 _ hm
  · exact checked5_82 _ hm
  · exact checked5_83 _ hm
  · exact checked5_98 _ hm
  · exact checked5_101 _ hm
  · exact checked5_105 _ hm
  · exact checked5_147 _ hm
  · exact checked5_154 _ hm
  · exact checked5_172 _ hm
  · exact checked5_291 _ hm
  · exact checked5_374 _ hm
  · exact checked5_376 _ hm
  · exact checked5_389 _ hm
private def chunk6_45 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire26214],
  [wire15,wire240,wire4369,wire8738,wire17476,wire30583],
  [wire15,wire240,wire4369,wire8738,wire17476,wire32768],
  [wire15,wire240,wire4369,wire8738,wire17476,wire34952]]
private def pool6_45 : List (List (List T)) := [chunk5_30, chunk5_51, chunk5_55, chunk5_56, chunk5_62, chunk5_82, chunk5_83, chunk5_89, chunk5_148, chunk5_157, chunk5_173, chunk5_244, chunk5_245, chunk5_376, chunk5_377]
private theorem checked6_45 : ∀ w ∈ chunk6_45, ¬ Need 6 w.toFinset := by
  have h : chunk6_45.all (routes 5 pool6_45.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_45,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_30 _ hm
  · exact checked5_51 _ hm
  · exact checked5_55 _ hm
  · exact checked5_56 _ hm
  · exact checked5_62 _ hm
  · exact checked5_82 _ hm
  · exact checked5_83 _ hm
  · exact checked5_89 _ hm
  · exact checked5_148 _ hm
  · exact checked5_157 _ hm
  · exact checked5_173 _ hm
  · exact checked5_244 _ hm
  · exact checked5_245 _ hm
  · exact checked5_376 _ hm
  · exact checked5_377 _ hm
private def chunk6_46 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire34952,wire65280],
  [wire15,wire240,wire4369,wire8738,wire17476,wire34959],
  [wire15,wire240,wire4369,wire8738,wire17476,wire35064],
  [wire15,wire240,wire4369,wire8738,wire17476,wire36744]]
private def pool6_46 : List (List (List T)) := [chunk5_21, chunk5_25, chunk5_28, chunk5_48, chunk5_51, chunk5_52, chunk5_57, chunk5_85, chunk5_245, chunk5_291, chunk5_377, chunk5_389, chunk5_419]
private theorem checked6_46 : ∀ w ∈ chunk6_46, ¬ Need 6 w.toFinset := by
  have h : chunk6_46.all (routes 5 pool6_46.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_46,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_21 _ hm
  · exact checked5_25 _ hm
  · exact checked5_28 _ hm
  · exact checked5_48 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_57 _ hm
  · exact checked5_85 _ hm
  · exact checked5_245 _ hm
  · exact checked5_291 _ hm
  · exact checked5_377 _ hm
  · exact checked5_389 _ hm
  · exact checked5_419 _ hm
private def chunk6_47 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire36744,wire61440],
  [wire15,wire240,wire4369,wire8738,wire17476,wire39321],
  [wire15,wire240,wire4369,wire8738,wire17476,wire43690],
  [wire15,wire240,wire4369,wire8738,wire17476,wire48059]]
private def pool6_47 : List (List (List T)) := [chunk5_17, chunk5_51, chunk5_52, chunk5_59, chunk5_61, chunk5_88, chunk5_108, chunk5_157, chunk5_173, chunk5_378, chunk5_419]
private theorem checked6_47 : ∀ w ∈ chunk6_47, ¬ Need 6 w.toFinset := by
  have h : chunk6_47.all (routes 5 pool6_47.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_47,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_17 _ hm
  · exact checked5_51 _ hm
  · exact checked5_52 _ hm
  · exact checked5_59 _ hm
  · exact checked5_61 _ hm
  · exact checked5_88 _ hm
  · exact checked5_108 _ hm
  · exact checked5_157 _ hm
  · exact checked5_173 _ hm
  · exact checked5_378 _ hm
  · exact checked5_419 _ hm
private def chunk6_48 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire52428],
  [wire15,wire240,wire4369,wire8738,wire17476,wire56797],
  [wire15,wire240,wire4369,wire8738,wire17476,wire61166],
  [wire15,wire240,wire4369,wire8738,wire17476,wire61440]]
private def pool6_48 : List (List (List T)) := [chunk5_51, chunk5_62, chunk5_91, chunk5_93, chunk5_109, chunk5_153, chunk5_157, chunk5_158, chunk5_173, chunk5_174]
private theorem checked6_48 : ∀ w ∈ chunk6_48, ¬ Need 6 w.toFinset := by
  have h : chunk6_48.all (routes 5 pool6_48.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_48,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_62 _ hm
  · exact checked5_91 _ hm
  · exact checked5_93 _ hm
  · exact checked5_109 _ hm
  · exact checked5_153 _ hm
  · exact checked5_157 _ hm
  · exact checked5_158 _ hm
  · exact checked5_173 _ hm
  · exact checked5_174 _ hm
private def chunk6_49 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire61455],
  [wire15,wire240,wire4369,wire8738,wire17476,wire61680],
  [wire15,wire240,wire4369,wire8738,wire17476,wire61695],
  [wire15,wire240,wire4369,wire8738,wire17476,wire61713]]
private def pool6_49 : List (List (List T)) := [chunk5_50, chunk5_51, chunk5_62, chunk5_93, chunk5_459]
private theorem checked6_49 : ∀ w ∈ chunk6_49, ¬ Need 6 w.toFinset := by
  have h : chunk6_49.all (routes 5 pool6_49.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_49,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_50 _ hm
  · exact checked5_51 _ hm
  · exact checked5_62 _ hm
  · exact checked5_93 _ hm
  · exact checked5_459 _ hm
private def chunk6_50 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire61986],
  [wire15,wire240,wire4369,wire8738,wire17476,wire62532],
  [wire15,wire240,wire4369,wire8738,wire17476,wire63624],
  [wire15,wire240,wire4369,wire8738,wire17476,wire65280]]
private def pool6_50 : List (List (List T)) := [chunk5_25, chunk5_51, chunk5_62, chunk5_63, chunk5_64, chunk5_93, chunk5_95, chunk5_109, chunk5_291, chunk5_378, chunk5_389]
private theorem checked6_50 : ∀ w ∈ chunk6_50, ¬ Need 6 w.toFinset := by
  have h : chunk6_50.all (routes 5 pool6_50.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_50,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_25 _ hm
  · exact checked5_51 _ hm
  · exact checked5_62 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_93 _ hm
  · exact checked5_95 _ hm
  · exact checked5_109 _ hm
  · exact checked5_291 _ hm
  · exact checked5_378 _ hm
  · exact checked5_389 _ hm
private def chunk6_51 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire65295],
  [wire15,wire240,wire4369,wire8738,wire17476,wire65520],
  [wire15,wire240,wire4369,wire8738,wire17476,wire65535],
  [wire15,wire240,wire4369,wire8738,wire17487,wire34952]]
private def pool6_51 : List (List (List T)) := [chunk5_1, chunk5_2, chunk5_7, chunk5_15, chunk5_25, chunk5_48, chunk5_51, chunk5_57, chunk5_95, chunk5_246, chunk5_292, chunk5_375, chunk5_377, chunk5_389, chunk5_419, chunk5_460]
private theorem checked6_51 : ∀ w ∈ chunk6_51, ¬ Need 6 w.toFinset := by
  have h : chunk6_51.all (routes 5 pool6_51.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_51,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_2 _ hm
  · exact checked5_7 _ hm
  · exact checked5_15 _ hm
  · exact checked5_25 _ hm
  · exact checked5_48 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_95 _ hm
  · exact checked5_246 _ hm
  · exact checked5_292 _ hm
  · exact checked5_375 _ hm
  · exact checked5_377 _ hm
  · exact checked5_389 _ hm
  · exact checked5_419 _ hm
  · exact checked5_460 _ hm
private def chunk6_52 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17652,wire34952],
  [wire15,wire240,wire4369,wire8738,wire20292],
  [wire15,wire240,wire4369,wire8738,wire20292,wire34952],
  [wire15,wire240,wire4369,wire8738,wire20292,wire34952,wire61440]]
private def pool6_52 : List (List (List T)) := [chunk5_22, chunk5_54, chunk5_55, chunk5_57, chunk5_61, chunk5_66, chunk5_77, chunk5_101, chunk5_102, chunk5_103, chunk5_138, chunk5_143, chunk5_156, chunk5_208, chunk5_247, chunk5_260, chunk5_292, chunk5_337, chunk5_379, chunk5_380]
private theorem checked6_52 : ∀ w ∈ chunk6_52, ¬ Need 6 w.toFinset := by
  have h : chunk6_52.all (routes 5 pool6_52.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_52,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_22 _ hm
  · exact checked5_54 _ hm
  · exact checked5_55 _ hm
  · exact checked5_57 _ hm
  · exact checked5_61 _ hm
  · exact checked5_66 _ hm
  · exact checked5_77 _ hm
  · exact checked5_101 _ hm
  · exact checked5_102 _ hm
  · exact checked5_103 _ hm
  · exact checked5_138 _ hm
  · exact checked5_143 _ hm
  · exact checked5_156 _ hm
  · exact checked5_208 _ hm
  · exact checked5_247 _ hm
  · exact checked5_260 _ hm
  · exact checked5_292 _ hm
  · exact checked5_337 _ hm
  · exact checked5_379 _ hm
  · exact checked5_380 _ hm
private def chunk6_53 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire20292,wire61440],
  [wire15,wire240,wire4369,wire8738,wire21845],
  [wire15,wire240,wire4369,wire8738,wire21845,wire34952],
  [wire15,wire240,wire4369,wire8738,wire21845,wire61440]]
private def pool6_53 : List (List (List T)) := [chunk5_22, chunk5_54, chunk5_56, chunk5_57, chunk5_60, chunk5_62, chunk5_64, chunk5_66, chunk5_77, chunk5_104, chunk5_105, chunk5_106, chunk5_107, chunk5_133, chunk5_144, chunk5_157, chunk5_158, chunk5_174, chunk5_208, chunk5_247, chunk5_248, chunk5_292, chunk5_337, chunk5_381, chunk5_390]
private theorem checked6_53 : ∀ w ∈ chunk6_53, ¬ Need 6 w.toFinset := by
  have h : chunk6_53.all (routes 5 pool6_53.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_53,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_22 _ hm
  · exact checked5_54 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
  · exact checked5_60 _ hm
  · exact checked5_62 _ hm
  · exact checked5_64 _ hm
  · exact checked5_66 _ hm
  · exact checked5_77 _ hm
  · exact checked5_104 _ hm
  · exact checked5_105 _ hm
  · exact checked5_106 _ hm
  · exact checked5_107 _ hm
  · exact checked5_133 _ hm
  · exact checked5_144 _ hm
  · exact checked5_157 _ hm
  · exact checked5_158 _ hm
  · exact checked5_174 _ hm
  · exact checked5_208 _ hm
  · exact checked5_247 _ hm
  · exact checked5_248 _ hm
  · exact checked5_292 _ hm
  · exact checked5_337 _ hm
  · exact checked5_381 _ hm
  · exact checked5_390 _ hm
private def chunk6_54 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire26214],
  [wire15,wire240,wire4369,wire8738,wire26214,wire34952],
  [wire15,wire240,wire4369,wire8738,wire26214,wire61440],
  [wire15,wire240,wire4369,wire8738,wire30583]]
private def pool6_54 : List (List (List T)) := [chunk5_1, chunk5_30, chunk5_55, chunk5_56, chunk5_57, chunk5_60, chunk5_63, chunk5_69, chunk5_77, chunk5_78, chunk5_108, chunk5_109, chunk5_110, chunk5_133, chunk5_139, chunk5_144, chunk5_158, chunk5_159, chunk5_161, chunk5_175, chunk5_208, chunk5_248, chunk5_250, chunk5_337, chunk5_338, chunk5_381, chunk5_382]
private theorem checked6_54 : ∀ w ∈ chunk6_54, ¬ Need 6 w.toFinset := by
  have h : chunk6_54.all (routes 5 pool6_54.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_54,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_1 _ hm
  · exact checked5_30 _ hm
  · exact checked5_55 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
  · exact checked5_60 _ hm
  · exact checked5_63 _ hm
  · exact checked5_69 _ hm
  · exact checked5_77 _ hm
  · exact checked5_78 _ hm
  · exact checked5_108 _ hm
  · exact checked5_109 _ hm
  · exact checked5_110 _ hm
  · exact checked5_133 _ hm
  · exact checked5_139 _ hm
  · exact checked5_144 _ hm
  · exact checked5_158 _ hm
  · exact checked5_159 _ hm
  · exact checked5_161 _ hm
  · exact checked5_175 _ hm
  · exact checked5_208 _ hm
  · exact checked5_248 _ hm
  · exact checked5_250 _ hm
  · exact checked5_337 _ hm
  · exact checked5_338 _ hm
  · exact checked5_381 _ hm
  · exact checked5_382 _ hm
private def chunk6_55 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire30583,wire34952],
  [wire15,wire240,wire4369,wire8738,wire30583,wire61440],
  [wire15,wire240,wire4369,wire8738,wire32768,wire34952],
  [wire15,wire240,wire4369,wire8738,wire34952]]
private def pool6_55 : List (List (List T)) := [chunk5_2, chunk5_31, chunk5_56, chunk5_57, chunk5_60, chunk5_63, chunk5_69, chunk5_78, chunk5_110, chunk5_111, chunk5_112, chunk5_115, chunk5_133, chunk5_144, chunk5_160, chunk5_161, chunk5_163, chunk5_209, chunk5_249, chunk5_250, chunk5_251, chunk5_338, chunk5_383]
private theorem checked6_55 : ∀ w ∈ chunk6_55, ¬ Need 6 w.toFinset := by
  have h : chunk6_55.all (routes 5 pool6_55.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_55,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_31 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
  · exact checked5_60 _ hm
  · exact checked5_63 _ hm
  · exact checked5_69 _ hm
  · exact checked5_78 _ hm
  · exact checked5_110 _ hm
  · exact checked5_111 _ hm
  · exact checked5_112 _ hm
  · exact checked5_115 _ hm
  · exact checked5_133 _ hm
  · exact checked5_144 _ hm
  · exact checked5_160 _ hm
  · exact checked5_161 _ hm
  · exact checked5_163 _ hm
  · exact checked5_209 _ hm
  · exact checked5_249 _ hm
  · exact checked5_250 _ hm
  · exact checked5_251 _ hm
  · exact checked5_338 _ hm
  · exact checked5_383 _ hm
private def chunk6_56 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire34952,wire34959],
  [wire15,wire240,wire4369,wire8738,wire34952,wire35064],
  [wire15,wire240,wire4369,wire8738,wire34952,wire36744],
  [wire15,wire240,wire4369,wire8738,wire34952,wire39321]]
private def pool6_56 : List (List (List T)) := [chunk5_2, chunk5_16, chunk5_57, chunk5_59, chunk5_60, chunk5_112, chunk5_113, chunk5_121, chunk5_122, chunk5_124, chunk5_161, chunk5_164, chunk5_175, chunk5_250, chunk5_252, chunk5_260, chunk5_419]
private theorem checked6_56 : ∀ w ∈ chunk6_56, ¬ Need 6 w.toFinset := by
  have h : chunk6_56.all (routes 5 pool6_56.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_56,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_16 _ hm
  · exact checked5_57 _ hm
  · exact checked5_59 _ hm
  · exact checked5_60 _ hm
  · exact checked5_112 _ hm
  · exact checked5_113 _ hm
  · exact checked5_121 _ hm
  · exact checked5_122 _ hm
  · exact checked5_124 _ hm
  · exact checked5_161 _ hm
  · exact checked5_164 _ hm
  · exact checked5_175 _ hm
  · exact checked5_250 _ hm
  · exact checked5_252 _ hm
  · exact checked5_260 _ hm
  · exact checked5_419 _ hm
private def chunk6_57 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire34952,wire43690],
  [wire15,wire240,wire4369,wire8738,wire34952,wire48059],
  [wire15,wire240,wire4369,wire8738,wire34952,wire52428],
  [wire15,wire240,wire4369,wire8738,wire34952,wire56797]]
private def pool6_57 : List (List (List T)) := [chunk5_17, chunk5_57, chunk5_60, chunk5_61, chunk5_112, chunk5_113, chunk5_115, chunk5_125, chunk5_126, chunk5_162, chunk5_165, chunk5_176, chunk5_252, chunk5_253]
private theorem checked6_57 : ∀ w ∈ chunk6_57, ¬ Need 6 w.toFinset := by
  have h : chunk6_57.all (routes 5 pool6_57.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_57,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_17 _ hm
  · exact checked5_57 _ hm
  · exact checked5_60 _ hm
  · exact checked5_61 _ hm
  · exact checked5_112 _ hm
  · exact checked5_113 _ hm
  · exact checked5_115 _ hm
  · exact checked5_125 _ hm
  · exact checked5_126 _ hm
  · exact checked5_162 _ hm
  · exact checked5_165 _ hm
  · exact checked5_176 _ hm
  · exact checked5_252 _ hm
  · exact checked5_253 _ hm
private def chunk6_58 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire34952,wire61166],
  [wire15,wire240,wire4369,wire8738,wire34952,wire61440],
  [wire15,wire240,wire4369,wire8738,wire34952,wire61455],
  [wire15,wire240,wire4369,wire8738,wire34952,wire61680]]
private def pool6_58 : List (List (List T)) := [chunk5_50, chunk5_57, chunk5_63, chunk5_117, chunk5_163, chunk5_165, chunk5_176, chunk5_460]
private theorem checked6_58 : ∀ w ∈ chunk6_58, ¬ Need 6 w.toFinset := by
  have h : chunk6_58.all (routes 5 pool6_58.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_58,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_50 _ hm
  · exact checked5_57 _ hm
  · exact checked5_63 _ hm
  · exact checked5_117 _ hm
  · exact checked5_163 _ hm
  · exact checked5_165 _ hm
  · exact checked5_176 _ hm
  · exact checked5_460 _ hm
private def chunk6_59 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire34952,wire61695],
  [wire15,wire240,wire4369,wire8738,wire34952,wire61713],
  [wire15,wire240,wire4369,wire8738,wire34952,wire61986],
  [wire15,wire240,wire4369,wire8738,wire34952,wire62532]]
private def pool6_59 : List (List (List T)) := [chunk5_50, chunk5_56, chunk5_57, chunk5_63, chunk5_64, chunk5_117, chunk5_126]
private theorem checked6_59 : ∀ w ∈ chunk6_59, ¬ Need 6 w.toFinset := by
  have h : chunk6_59.all (routes 5 pool6_59.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_59,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_50 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_117 _ hm
  · exact checked5_126 _ hm
private def chunk6_60 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire34952,wire63624],
  [wire15,wire240,wire4369,wire8738,wire34952,wire65280],
  [wire15,wire240,wire4369,wire8738,wire34952,wire65295],
  [wire15,wire240,wire4369,wire8738,wire34952,wire65520]]
private def pool6_60 : List (List (List T)) := [chunk5_7, chunk5_48, chunk5_51, chunk5_57, chunk5_63, chunk5_64, chunk5_118, chunk5_119, chunk5_120, chunk5_126, chunk5_251, chunk5_253, chunk5_261, chunk5_383, chunk5_420, chunk5_461]
private theorem checked6_60 : ∀ w ∈ chunk6_60, ¬ Need 6 w.toFinset := by
  have h : chunk6_60.all (routes 5 pool6_60.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_60,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_7 _ hm
  · exact checked5_48 _ hm
  · exact checked5_51 _ hm
  · exact checked5_57 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_118 _ hm
  · exact checked5_119 _ hm
  · exact checked5_120 _ hm
  · exact checked5_126 _ hm
  · exact checked5_251 _ hm
  · exact checked5_253 _ hm
  · exact checked5_261 _ hm
  · exact checked5_383 _ hm
  · exact checked5_420 _ hm
  · exact checked5_461 _ hm
private def chunk6_61 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire34952,wire65535],
  [wire15,wire240,wire4369,wire8738,wire36744],
  [wire15,wire240,wire4369,wire8738,wire36744,wire61440],
  [wire15,wire240,wire4369,wire8738,wire39321]]
private def pool6_61 : List (List (List T)) := [chunk5_2, chunk5_55, chunk5_56, chunk5_57, chunk5_59, chunk5_60, chunk5_61, chunk5_64, chunk5_69, chunk5_70, chunk5_78, chunk5_122, chunk5_123, chunk5_124, chunk5_125, chunk5_134, chunk5_139, chunk5_145, chunk5_165, chunk5_176, chunk5_209, chunk5_253, chunk5_254, chunk5_255, chunk5_261, chunk5_338, chunk5_384, chunk5_420]
private theorem checked6_61 : ∀ w ∈ chunk6_61, ¬ Need 6 w.toFinset := by
  have h : chunk6_61.all (routes 5 pool6_61.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_61,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_55 _ hm
  · exact checked5_56 _ hm
  · exact checked5_57 _ hm
  · exact checked5_59 _ hm
  · exact checked5_60 _ hm
  · exact checked5_61 _ hm
  · exact checked5_64 _ hm
  · exact checked5_69 _ hm
  · exact checked5_70 _ hm
  · exact checked5_78 _ hm
  · exact checked5_122 _ hm
  · exact checked5_123 _ hm
  · exact checked5_124 _ hm
  · exact checked5_125 _ hm
  · exact checked5_134 _ hm
  · exact checked5_139 _ hm
  · exact checked5_145 _ hm
  · exact checked5_165 _ hm
  · exact checked5_176 _ hm
  · exact checked5_209 _ hm
  · exact checked5_253 _ hm
  · exact checked5_254 _ hm
  · exact checked5_255 _ hm
  · exact checked5_261 _ hm
  · exact checked5_338 _ hm
  · exact checked5_384 _ hm
  · exact checked5_420 _ hm
private def chunk6_62 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire39321,wire61440],
  [wire15,wire240,wire4369,wire8738,wire43690],
  [wire15,wire240,wire4369,wire8738,wire43690,wire61440],
  [wire15,wire240,wire4369,wire8738,wire48059]]
private def pool6_62 : List (List (List T)) := [chunk5_18, chunk5_22, chunk5_51, chunk5_54, chunk5_60, chunk5_61, chunk5_63, chunk5_64, chunk5_67, chunk5_79, chunk5_125, chunk5_126, chunk5_127, chunk5_134, chunk5_139, chunk5_145, chunk5_166, chunk5_167, chunk5_177, chunk5_209, chunk5_210, chunk5_256, chunk5_339, chunk5_385]
private theorem checked6_62 : ∀ w ∈ chunk6_62, ¬ Need 6 w.toFinset := by
  have h : chunk6_62.all (routes 5 pool6_62.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_62,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_18 _ hm
  · exact checked5_22 _ hm
  · exact checked5_51 _ hm
  · exact checked5_54 _ hm
  · exact checked5_60 _ hm
  · exact checked5_61 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_67 _ hm
  · exact checked5_79 _ hm
  · exact checked5_125 _ hm
  · exact checked5_126 _ hm
  · exact checked5_127 _ hm
  · exact checked5_134 _ hm
  · exact checked5_139 _ hm
  · exact checked5_145 _ hm
  · exact checked5_166 _ hm
  · exact checked5_167 _ hm
  · exact checked5_177 _ hm
  · exact checked5_209 _ hm
  · exact checked5_210 _ hm
  · exact checked5_256 _ hm
  · exact checked5_339 _ hm
  · exact checked5_385 _ hm
private def chunk6_63 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire48059,wire61440],
  [wire15,wire240,wire4369,wire8738,wire61440,wire62532],
  [wire15,wire240,wire4369,wire8738,wire61440,wire63624],
  [wire15,wire240,wire4369,wire8738,wire62532]]
private def pool6_63 : List (List (List T)) := [chunk5_23, chunk5_42, chunk5_62, chunk5_63, chunk5_64, chunk5_67, chunk5_79, chunk5_127, chunk5_128, chunk5_129, chunk5_139, chunk5_146, chunk5_167, chunk5_210, chunk5_257, chunk5_339, chunk5_386, chunk5_387]
private theorem checked6_63 : ∀ w ∈ chunk6_63, ¬ Need 6 w.toFinset := by
  have h : chunk6_63.all (routes 5 pool6_63.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_63,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_23 _ hm
  · exact checked5_42 _ hm
  · exact checked5_62 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_67 _ hm
  · exact checked5_79 _ hm
  · exact checked5_127 _ hm
  · exact checked5_128 _ hm
  · exact checked5_129 _ hm
  · exact checked5_139 _ hm
  · exact checked5_146 _ hm
  · exact checked5_167 _ hm
  · exact checked5_210 _ hm
  · exact checked5_257 _ hm
  · exact checked5_339 _ hm
  · exact checked5_386 _ hm
  · exact checked5_387 _ hm
private def chunk6_64 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire63624],
  [wire15,wire240,wire4369,wire8751,wire17476],
  [wire15,wire240,wire4369,wire8751,wire17476,wire34952],
  [wire15,wire240,wire4369,wire8751,wire17476,wire61440]]
private def pool6_64 : List (List (List T)) := [chunk5_3, chunk5_9, chunk5_21, chunk5_41, chunk5_63, chunk5_64, chunk5_66, chunk5_67, chunk5_70, chunk5_79, chunk5_80, chunk5_82, chunk5_85, chunk5_91, chunk5_93, chunk5_128, chunk5_130, chunk5_134, chunk5_140, chunk5_146, chunk5_168, chunk5_169, chunk5_210, chunk5_258, chunk5_259, chunk5_260, chunk5_339, chunk5_340, chunk5_373, chunk5_388, chunk5_389, chunk5_461, chunk5_462]
private theorem checked6_64 : ∀ w ∈ chunk6_64, ¬ Need 6 w.toFinset := by
  have h : chunk6_64.all (routes 5 pool6_64.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_64,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_9 _ hm
  · exact checked5_21 _ hm
  · exact checked5_41 _ hm
  · exact checked5_63 _ hm
  · exact checked5_64 _ hm
  · exact checked5_66 _ hm
  · exact checked5_67 _ hm
  · exact checked5_70 _ hm
  · exact checked5_79 _ hm
  · exact checked5_80 _ hm
  · exact checked5_82 _ hm
  · exact checked5_85 _ hm
  · exact checked5_91 _ hm
  · exact checked5_93 _ hm
  · exact checked5_128 _ hm
  · exact checked5_130 _ hm
  · exact checked5_134 _ hm
  · exact checked5_140 _ hm
  · exact checked5_146 _ hm
  · exact checked5_168 _ hm
  · exact checked5_169 _ hm
  · exact checked5_210 _ hm
  · exact checked5_258 _ hm
  · exact checked5_259 _ hm
  · exact checked5_260 _ hm
  · exact checked5_339 _ hm
  · exact checked5_340 _ hm
  · exact checked5_373 _ hm
  · exact checked5_388 _ hm
  · exact checked5_389 _ hm
  · exact checked5_461 _ hm
  · exact checked5_462 _ hm
private def chunk6_65 : List (List T) := [[wire15,wire240,wire4369,wire8946,wire17476,wire34952],
  [wire15,wire240,wire4369,wire8946,wire34952],
  [wire15,wire240,wire4369,wire8946,wire34952,wire61440],
  [wire15,wire240,wire4369,wire12066,wire17476]]
private def pool6_65 : List (List (List T)) := [chunk5_2, chunk5_21, chunk5_32, chunk5_69, chunk5_70, chunk5_72, chunk5_73, chunk5_75, chunk5_76, chunk5_80, chunk5_83, chunk5_85, chunk5_91, chunk5_112, chunk5_115, chunk5_117, chunk5_134, chunk5_140, chunk5_170, chunk5_171, chunk5_211, chunk5_243, chunk5_260, chunk5_261, chunk5_262, chunk5_340, chunk5_390, chunk5_391, chunk5_462]
private theorem checked6_65 : ∀ w ∈ chunk6_65, ¬ Need 6 w.toFinset := by
  have h : chunk6_65.all (routes 5 pool6_65.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_65,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_21 _ hm
  · exact checked5_32 _ hm
  · exact checked5_69 _ hm
  · exact checked5_70 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_75 _ hm
  · exact checked5_76 _ hm
  · exact checked5_80 _ hm
  · exact checked5_83 _ hm
  · exact checked5_85 _ hm
  · exact checked5_91 _ hm
  · exact checked5_112 _ hm
  · exact checked5_115 _ hm
  · exact checked5_117 _ hm
  · exact checked5_134 _ hm
  · exact checked5_140 _ hm
  · exact checked5_170 _ hm
  · exact checked5_171 _ hm
  · exact checked5_211 _ hm
  · exact checked5_243 _ hm
  · exact checked5_260 _ hm
  · exact checked5_261 _ hm
  · exact checked5_262 _ hm
  · exact checked5_340 _ hm
  · exact checked5_390 _ hm
  · exact checked5_391 _ hm
  · exact checked5_462 _ hm
private def chunk6_66 : List (List T) := [[wire15,wire240,wire4369,wire12066,wire17476,wire34952],
  [wire15,wire240,wire4369,wire12066,wire17476,wire34952,wire61440],
  [wire15,wire240,wire4369,wire12066,wire17476,wire61440],
  [wire15,wire240,wire4369,wire12066,wire34952]]
private def pool6_66 : List (List (List T)) := [chunk5_2, chunk5_72, chunk5_73, chunk5_74, chunk5_75, chunk5_76, chunk5_80, chunk5_85, chunk5_95, chunk5_112, chunk5_115, chunk5_135, chunk5_172, chunk5_211, chunk5_262, chunk5_263, chunk5_292, chunk5_293, chunk5_340, chunk5_392, chunk5_420]
private theorem checked6_66 : ∀ w ∈ chunk6_66, ¬ Need 6 w.toFinset := by
  have h : chunk6_66.all (routes 5 pool6_66.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_66,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_72 _ hm
  · exact checked5_73 _ hm
  · exact checked5_74 _ hm
  · exact checked5_75 _ hm
  · exact checked5_76 _ hm
  · exact checked5_80 _ hm
  · exact checked5_85 _ hm
  · exact checked5_95 _ hm
  · exact checked5_112 _ hm
  · exact checked5_115 _ hm
  · exact checked5_135 _ hm
  · exact checked5_172 _ hm
  · exact checked5_211 _ hm
  · exact checked5_262 _ hm
  · exact checked5_263 _ hm
  · exact checked5_292 _ hm
  · exact checked5_293 _ hm
  · exact checked5_340 _ hm
  · exact checked5_392 _ hm
  · exact checked5_420 _ hm
private def chunk6_67 : List (List T) := [[wire15,wire240,wire4369,wire12066,wire34952,wire61440],
  [wire15,wire240,wire4369,wire13107,wire17476],
  [wire15,wire240,wire4369,wire13107,wire17476,wire34952],
  [wire15,wire240,wire4369,wire13107,wire17476,wire61440]]
private def pool6_67 : List (List (List T)) := [chunk5_27, chunk5_75, chunk5_77, chunk5_78, chunk5_79, chunk5_80, chunk5_83, chunk5_85, chunk5_90, chunk5_93, chunk5_119, chunk5_172, chunk5_173, chunk5_174, chunk5_211, chunk5_263, chunk5_264, chunk5_341, chunk5_392, chunk5_393, chunk5_421]
private theorem checked6_67 : ∀ w ∈ chunk6_67, ¬ Need 6 w.toFinset := by
  have h : chunk6_67.all (routes 5 pool6_67.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_67,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_27 _ hm
  · exact checked5_75 _ hm
  · exact checked5_77 _ hm
  · exact checked5_78 _ hm
  · exact checked5_79 _ hm
  · exact checked5_80 _ hm
  · exact checked5_83 _ hm
  · exact checked5_85 _ hm
  · exact checked5_90 _ hm
  · exact checked5_93 _ hm
  · exact checked5_119 _ hm
  · exact checked5_172 _ hm
  · exact checked5_173 _ hm
  · exact checked5_174 _ hm
  · exact checked5_211 _ hm
  · exact checked5_263 _ hm
  · exact checked5_264 _ hm
  · exact checked5_341 _ hm
  · exact checked5_392 _ hm
  · exact checked5_393 _ hm
  · exact checked5_421 _ hm
private def chunk6_68 : List (List T) := [[wire15,wire240,wire4369,wire13107,wire34952],
  [wire15,wire240,wire4369,wire13107,wire34952,wire61440],
  [wire15,wire240,wire4369,wire16384,wire17476,wire34952],
  [wire15,wire240,wire4369,wire17476,wire17487,wire34952]]
private def pool6_68 : List (List (List T)) := [chunk5_8, chunk5_78, chunk5_79, chunk5_80, chunk5_85, chunk5_90, chunk5_113, chunk5_114, chunk5_117, chunk5_175, chunk5_176, chunk5_177, chunk5_189, chunk5_212, chunk5_264, chunk5_341, chunk5_394, chunk5_395]
private theorem checked6_68 : ∀ w ∈ chunk6_68, ¬ Need 6 w.toFinset := by
  have h : chunk6_68.all (routes 5 pool6_68.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_68,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_78 _ hm
  · exact checked5_79 _ hm
  · exact checked5_80 _ hm
  · exact checked5_85 _ hm
  · exact checked5_90 _ hm
  · exact checked5_113 _ hm
  · exact checked5_114 _ hm
  · exact checked5_117 _ hm
  · exact checked5_175 _ hm
  · exact checked5_176 _ hm
  · exact checked5_177 _ hm
  · exact checked5_189 _ hm
  · exact checked5_212 _ hm
  · exact checked5_264 _ hm
  · exact checked5_341 _ hm
  · exact checked5_394 _ hm
  · exact checked5_395 _ hm
private def chunk6_69 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire17652,wire34952],
  [wire15,wire240,wire4369,wire17476,wire20292,wire34952],
  [wire15,wire240,wire4369,wire17476,wire21845,wire34952],
  [wire15,wire240,wire4369,wire17476,wire26214]]
private def pool6_69 : List (List (List T)) := [chunk5_9, chunk5_29, chunk5_32, chunk5_82, chunk5_83, chunk5_85, chunk5_89, chunk5_91, chunk5_98, chunk5_99, chunk5_102, chunk5_103, chunk5_105, chunk5_106, chunk5_108, chunk5_140, chunk5_178, chunk5_179, chunk5_180, chunk5_182, chunk5_191, chunk5_212, chunk5_266, chunk5_341, chunk5_394, chunk5_397, chunk5_398, chunk5_404, chunk5_405]
private theorem checked6_69 : ∀ w ∈ chunk6_69, ¬ Need 6 w.toFinset := by
  have h : chunk6_69.all (routes 5 pool6_69.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_69,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_29 _ hm
  · exact checked5_32 _ hm
  · exact checked5_82 _ hm
  · exact checked5_83 _ hm
  · exact checked5_85 _ hm
  · exact checked5_89 _ hm
  · exact checked5_91 _ hm
  · exact checked5_98 _ hm
  · exact checked5_99 _ hm
  · exact checked5_102 _ hm
  · exact checked5_103 _ hm
  · exact checked5_105 _ hm
  · exact checked5_106 _ hm
  · exact checked5_108 _ hm
  · exact checked5_140 _ hm
  · exact checked5_178 _ hm
  · exact checked5_179 _ hm
  · exact checked5_180 _ hm
  · exact checked5_182 _ hm
  · exact checked5_191 _ hm
  · exact checked5_212 _ hm
  · exact checked5_266 _ hm
  · exact checked5_341 _ hm
  · exact checked5_394 _ hm
  · exact checked5_397 _ hm
  · exact checked5_398 _ hm
  · exact checked5_404 _ hm
  · exact checked5_405 _ hm
private def chunk6_70 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire26214,wire34952],
  [wire15,wire240,wire4369,wire17476,wire26214,wire61440],
  [wire15,wire240,wire4369,wire17476,wire30583],
  [wire15,wire240,wire4369,wire17476,wire30583,wire34952]]
private def pool6_70 : List (List (List T)) := [chunk5_9, chunk5_30, chunk5_31, chunk5_83, chunk5_84, chunk5_85, chunk5_93, chunk5_99, chunk5_105, chunk5_109, chunk5_110, chunk5_178, chunk5_182, chunk5_183, chunk5_191, chunk5_192, chunk5_212, chunk5_265, chunk5_266, chunk5_267, chunk5_341, chunk5_395, chunk5_398]
private theorem checked6_70 : ∀ w ∈ chunk6_70, ¬ Need 6 w.toFinset := by
  have h : chunk6_70.all (routes 5 pool6_70.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_70,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_30 _ hm
  · exact checked5_31 _ hm
  · exact checked5_83 _ hm
  · exact checked5_84 _ hm
  · exact checked5_85 _ hm
  · exact checked5_93 _ hm
  · exact checked5_99 _ hm
  · exact checked5_105 _ hm
  · exact checked5_109 _ hm
  · exact checked5_110 _ hm
  · exact checked5_178 _ hm
  · exact checked5_182 _ hm
  · exact checked5_183 _ hm
  · exact checked5_191 _ hm
  · exact checked5_192 _ hm
  · exact checked5_212 _ hm
  · exact checked5_265 _ hm
  · exact checked5_266 _ hm
  · exact checked5_267 _ hm
  · exact checked5_341 _ hm
  · exact checked5_395 _ hm
  · exact checked5_398 _ hm
private def chunk6_71 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire30583,wire61440],
  [wire15,wire240,wire4369,wire17476,wire32768,wire34952],
  [wire15,wire240,wire4369,wire17476,wire34952],
  [wire15,wire240,wire4369,wire17476,wire34952,wire34959]]
private def pool6_71 : List (List (List T)) := [chunk5_9, chunk5_32, chunk5_83, chunk5_85, chunk5_86, chunk5_89, chunk5_90, chunk5_94, chunk5_99, chunk5_105, chunk5_111, chunk5_113, chunk5_114, chunk5_178, chunk5_183, chunk5_184, chunk5_212, chunk5_267, chunk5_268, chunk5_269, chunk5_342, chunk5_395, chunk5_400]
private theorem checked6_71 : ∀ w ∈ chunk6_71, ¬ Need 6 w.toFinset := by
  have h : chunk6_71.all (routes 5 pool6_71.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_71,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_32 _ hm
  · exact checked5_83 _ hm
  · exact checked5_85 _ hm
  · exact checked5_86 _ hm
  · exact checked5_89 _ hm
  · exact checked5_90 _ hm
  · exact checked5_94 _ hm
  · exact checked5_99 _ hm
  · exact checked5_105 _ hm
  · exact checked5_111 _ hm
  · exact checked5_113 _ hm
  · exact checked5_114 _ hm
  · exact checked5_178 _ hm
  · exact checked5_183 _ hm
  · exact checked5_184 _ hm
  · exact checked5_212 _ hm
  · exact checked5_267 _ hm
  · exact checked5_268 _ hm
  · exact checked5_269 _ hm
  · exact checked5_342 _ hm
  · exact checked5_395 _ hm
  · exact checked5_400 _ hm
private def chunk6_72 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire34952,wire35064],
  [wire15,wire240,wire4369,wire17476,wire34952,wire36744],
  [wire15,wire240,wire4369,wire17476,wire34952,wire39321],
  [wire15,wire240,wire4369,wire17476,wire34952,wire43690]]
private def pool6_72 : List (List (List T)) := [chunk5_85, chunk5_88, chunk5_89, chunk5_114, chunk5_115, chunk5_123, chunk5_124, chunk5_125, chunk5_183, chunk5_185, chunk5_186, chunk5_192, chunk5_267, chunk5_270, chunk5_279, chunk5_405]
private theorem checked6_72 : ∀ w ∈ chunk6_72, ¬ Need 6 w.toFinset := by
  have h : chunk6_72.all (routes 5 pool6_72.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_72,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_85 _ hm
  · exact checked5_88 _ hm
  · exact checked5_89 _ hm
  · exact checked5_114 _ hm
  · exact checked5_115 _ hm
  · exact checked5_123 _ hm
  · exact checked5_124 _ hm
  · exact checked5_125 _ hm
  · exact checked5_183 _ hm
  · exact checked5_185 _ hm
  · exact checked5_186 _ hm
  · exact checked5_192 _ hm
  · exact checked5_267 _ hm
  · exact checked5_270 _ hm
  · exact checked5_279 _ hm
  · exact checked5_405 _ hm
private def chunk6_73 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire34952,wire48059],
  [wire15,wire240,wire4369,wire17476,wire34952,wire52428],
  [wire15,wire240,wire4369,wire17476,wire34952,wire56797],
  [wire15,wire240,wire4369,wire17476,wire34952,wire61166]]
private def pool6_73 : List (List (List T)) := [chunk5_18, chunk5_85, chunk5_90, chunk5_91, chunk5_113, chunk5_114, chunk5_115, chunk5_126, chunk5_184, chunk5_186, chunk5_192, chunk5_193, chunk5_270, chunk5_271, chunk5_405, chunk5_406]
private theorem checked6_73 : ∀ w ∈ chunk6_73, ¬ Need 6 w.toFinset := by
  have h : chunk6_73.all (routes 5 pool6_73.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_73,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_18 _ hm
  · exact checked5_85 _ hm
  · exact checked5_90 _ hm
  · exact checked5_91 _ hm
  · exact checked5_113 _ hm
  · exact checked5_114 _ hm
  · exact checked5_115 _ hm
  · exact checked5_126 _ hm
  · exact checked5_184 _ hm
  · exact checked5_186 _ hm
  · exact checked5_192 _ hm
  · exact checked5_193 _ hm
  · exact checked5_270 _ hm
  · exact checked5_271 _ hm
  · exact checked5_405 _ hm
  · exact checked5_406 _ hm
private def chunk6_74 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire34952,wire61440],
  [wire15,wire240,wire4369,wire17476,wire34952,wire61455],
  [wire15,wire240,wire4369,wire17476,wire34952,wire61680],
  [wire15,wire240,wire4369,wire17476,wire34952,wire61695]]
private def pool6_74 : List (List (List T)) := [chunk5_81, chunk5_84, chunk5_85, chunk5_94, chunk5_117, chunk5_118, chunk5_463]
private theorem checked6_74 : ∀ w ∈ chunk6_74, ¬ Need 6 w.toFinset := by
  have h : chunk6_74.all (routes 5 pool6_74.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_74,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_81 _ hm
  · exact checked5_84 _ hm
  · exact checked5_85 _ hm
  · exact checked5_94 _ hm
  · exact checked5_117 _ hm
  · exact checked5_118 _ hm
  · exact checked5_463 _ hm
private def chunk6_75 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire34952,wire61713],
  [wire15,wire240,wire4369,wire17476,wire34952,wire61986],
  [wire15,wire240,wire4369,wire17476,wire34952,wire62532],
  [wire15,wire240,wire4369,wire17476,wire34952,wire63624]]
private def pool6_75 : List (List (List T)) := [chunk5_85, chunk5_94, chunk5_95, chunk5_117, chunk5_118, chunk5_119, chunk5_127, chunk5_128, chunk5_271, chunk5_406]
private theorem checked6_75 : ∀ w ∈ chunk6_75, ¬ Need 6 w.toFinset := by
  have h : chunk6_75.all (routes 5 pool6_75.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_75,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_85 _ hm
  · exact checked5_94 _ hm
  · exact checked5_95 _ hm
  · exact checked5_117 _ hm
  · exact checked5_118 _ hm
  · exact checked5_119 _ hm
  · exact checked5_127 _ hm
  · exact checked5_128 _ hm
  · exact checked5_271 _ hm
  · exact checked5_406 _ hm
private def chunk6_76 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire34952,wire65280],
  [wire15,wire240,wire4369,wire17476,wire34952,wire65295],
  [wire15,wire240,wire4369,wire17476,wire34952,wire65520],
  [wire15,wire240,wire4369,wire17476,wire34952,wire65535]]
private def pool6_76 : List (List (List T)) := [chunk5_14, chunk5_36, chunk5_81, chunk5_85, chunk5_96, chunk5_119, chunk5_120, chunk5_268, chunk5_279, chunk5_400, chunk5_463]
private theorem checked6_76 : ∀ w ∈ chunk6_76, ¬ Need 6 w.toFinset := by
  have h : chunk6_76.all (routes 5 pool6_76.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_76,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_14 _ hm
  · exact checked5_36 _ hm
  · exact checked5_81 _ hm
  · exact checked5_85 _ hm
  · exact checked5_96 _ hm
  · exact checked5_119 _ hm
  · exact checked5_120 _ hm
  · exact checked5_268 _ hm
  · exact checked5_279 _ hm
  · exact checked5_400 _ hm
  · exact checked5_463 _ hm
private def chunk6_77 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire34959],
  [wire15,wire240,wire4369,wire17476,wire34959,wire61440],
  [wire15,wire240,wire4369,wire17476,wire36744],
  [wire15,wire240,wire4369,wire17476,wire36744,wire61440]]
private def pool6_77 : List (List (List T)) := [chunk5_10, chunk5_32, chunk5_83, chunk5_86, chunk5_88, chunk5_89, chunk5_90, chunk5_91, chunk5_94, chunk5_96, chunk5_99, chunk5_105, chunk5_106, chunk5_121, chunk5_122, chunk5_123, chunk5_124, chunk5_178, chunk5_179, chunk5_185, chunk5_186, chunk5_213, chunk5_269, chunk5_270, chunk5_271, chunk5_272, chunk5_279, chunk5_342, chunk5_373, chunk5_395, chunk5_396, chunk5_400, chunk5_401]
private theorem checked6_77 : ∀ w ∈ chunk6_77, ¬ Need 6 w.toFinset := by
  have h : chunk6_77.all (routes 5 pool6_77.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_77,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_10 _ hm
  · exact checked5_32 _ hm
  · exact checked5_83 _ hm
  · exact checked5_86 _ hm
  · exact checked5_88 _ hm
  · exact checked5_89 _ hm
  · exact checked5_90 _ hm
  · exact checked5_91 _ hm
  · exact checked5_94 _ hm
  · exact checked5_96 _ hm
  · exact checked5_99 _ hm
  · exact checked5_105 _ hm
  · exact checked5_106 _ hm
  · exact checked5_121 _ hm
  · exact checked5_122 _ hm
  · exact checked5_123 _ hm
  · exact checked5_124 _ hm
  · exact checked5_178 _ hm
  · exact checked5_179 _ hm
  · exact checked5_185 _ hm
  · exact checked5_186 _ hm
  · exact checked5_213 _ hm
  · exact checked5_269 _ hm
  · exact checked5_270 _ hm
  · exact checked5_271 _ hm
  · exact checked5_272 _ hm
  · exact checked5_279 _ hm
  · exact checked5_342 _ hm
  · exact checked5_373 _ hm
  · exact checked5_395 _ hm
  · exact checked5_396 _ hm
  · exact checked5_400 _ hm
  · exact checked5_401 _ hm
private def chunk6_78 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire39321],
  [wire15,wire240,wire4369,wire17476,wire39321,wire61440],
  [wire15,wire240,wire4369,wire17476,wire52428],
  [wire15,wire240,wire4369,wire17476,wire52428,wire61440]]
private def pool6_78 : List (List (List T)) := [chunk5_10, chunk5_38, chunk5_77, chunk5_82, chunk5_89, chunk5_90, chunk5_91, chunk5_94, chunk5_95, chunk5_100, chunk5_106, chunk5_124, chunk5_125, chunk5_126, chunk5_127, chunk5_140, chunk5_179, chunk5_186, chunk5_188, chunk5_193, chunk5_194, chunk5_213, chunk5_273, chunk5_274, chunk5_342, chunk5_343, chunk5_396, chunk5_401, chunk5_402]
private theorem checked6_78 : ∀ w ∈ chunk6_78, ¬ Need 6 w.toFinset := by
  have h : chunk6_78.all (routes 5 pool6_78.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_78,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_10 _ hm
  · exact checked5_38 _ hm
  · exact checked5_77 _ hm
  · exact checked5_82 _ hm
  · exact checked5_89 _ hm
  · exact checked5_90 _ hm
  · exact checked5_91 _ hm
  · exact checked5_94 _ hm
  · exact checked5_95 _ hm
  · exact checked5_100 _ hm
  · exact checked5_106 _ hm
  · exact checked5_124 _ hm
  · exact checked5_125 _ hm
  · exact checked5_126 _ hm
  · exact checked5_127 _ hm
  · exact checked5_140 _ hm
  · exact checked5_179 _ hm
  · exact checked5_186 _ hm
  · exact checked5_188 _ hm
  · exact checked5_193 _ hm
  · exact checked5_194 _ hm
  · exact checked5_213 _ hm
  · exact checked5_273 _ hm
  · exact checked5_274 _ hm
  · exact checked5_342 _ hm
  · exact checked5_343 _ hm
  · exact checked5_396 _ hm
  · exact checked5_401 _ hm
  · exact checked5_402 _ hm
private def chunk6_79 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire56797],
  [wire15,wire240,wire4369,wire17476,wire56797,wire61440],
  [wire15,wire240,wire4369,wire17476,wire61440,wire61986],
  [wire15,wire240,wire4369,wire17476,wire61440,wire63624]]
private def pool6_79 : List (List (List T)) := [chunk5_38, chunk5_51, chunk5_91, chunk5_92, chunk5_93, chunk5_94, chunk5_95, chunk5_106, chunk5_127, chunk5_128, chunk5_130, chunk5_141, chunk5_179, chunk5_188, chunk5_214, chunk5_274, chunk5_275, chunk5_343, chunk5_397, chunk5_402]
private theorem checked6_79 : ∀ w ∈ chunk6_79, ¬ Need 6 w.toFinset := by
  have h : chunk6_79.all (routes 5 pool6_79.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_79,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_38 _ hm
  · exact checked5_51 _ hm
  · exact checked5_91 _ hm
  · exact checked5_92 _ hm
  · exact checked5_93 _ hm
  · exact checked5_94 _ hm
  · exact checked5_95 _ hm
  · exact checked5_106 _ hm
  · exact checked5_127 _ hm
  · exact checked5_128 _ hm
  · exact checked5_130 _ hm
  · exact checked5_141 _ hm
  · exact checked5_179 _ hm
  · exact checked5_188 _ hm
  · exact checked5_214 _ hm
  · exact checked5_274 _ hm
  · exact checked5_275 _ hm
  · exact checked5_343 _ hm
  · exact checked5_397 _ hm
  · exact checked5_402 _ hm
private def chunk6_80 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire61986],
  [wire15,wire240,wire4369,wire17476,wire63624],
  [wire15,wire240,wire4369,wire17652,wire34952],
  [wire15,wire240,wire4369,wire17652,wire34952,wire61440]]
private def pool6_80 : List (List (List T)) := [chunk5_9, chunk5_10, chunk5_21, chunk5_32, chunk5_33, chunk5_41, chunk5_42, chunk5_93, chunk5_94, chunk5_95, chunk5_99, chunk5_100, chunk5_107, chunk5_113, chunk5_114, chunk5_118, chunk5_127, chunk5_129, chunk5_130, chunk5_141, chunk5_180, chunk5_188, chunk5_189, chunk5_190, chunk5_214, chunk5_244, chunk5_276, chunk5_277, chunk5_279, chunk5_343, chunk5_344, chunk5_397, chunk5_403, chunk5_406, chunk5_407]
private theorem checked6_80 : ∀ w ∈ chunk6_80, ¬ Need 6 w.toFinset := by
  have h : chunk6_80.all (routes 5 pool6_80.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_80,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_10 _ hm
  · exact checked5_21 _ hm
  · exact checked5_32 _ hm
  · exact checked5_33 _ hm
  · exact checked5_41 _ hm
  · exact checked5_42 _ hm
  · exact checked5_93 _ hm
  · exact checked5_94 _ hm
  · exact checked5_95 _ hm
  · exact checked5_99 _ hm
  · exact checked5_100 _ hm
  · exact checked5_107 _ hm
  · exact checked5_113 _ hm
  · exact checked5_114 _ hm
  · exact checked5_118 _ hm
  · exact checked5_127 _ hm
  · exact checked5_129 _ hm
  · exact checked5_130 _ hm
  · exact checked5_141 _ hm
  · exact checked5_180 _ hm
  · exact checked5_188 _ hm
  · exact checked5_189 _ hm
  · exact checked5_190 _ hm
  · exact checked5_214 _ hm
  · exact checked5_244 _ hm
  · exact checked5_276 _ hm
  · exact checked5_277 _ hm
  · exact checked5_279 _ hm
  · exact checked5_343 _ hm
  · exact checked5_344 _ hm
  · exact checked5_397 _ hm
  · exact checked5_403 _ hm
  · exact checked5_406 _ hm
  · exact checked5_407 _ hm
private def chunk6_81 : List (List T) := [[wire15,wire240,wire4369,wire20292,wire34952],
  [wire15,wire240,wire4369,wire20292,wire34952,wire61440],
  [wire15,wire240,wire4369,wire21845,wire34952],
  [wire15,wire240,wire4369,wire21845,wire34952,wire61440]]
private def pool6_81 : List (List (List T)) := [chunk5_9, chunk5_15, chunk5_33, chunk5_101, chunk5_102, chunk5_103, chunk5_104, chunk5_105, chunk5_106, chunk5_107, chunk5_112, chunk5_113, chunk5_115, chunk5_118, chunk5_119, chunk5_135, chunk5_191, chunk5_192, chunk5_193, chunk5_215, chunk5_280, chunk5_281, chunk5_344, chunk5_407, chunk5_409, chunk5_412]
private theorem checked6_81 : ∀ w ∈ chunk6_81, ¬ Need 6 w.toFinset := by
  have h : chunk6_81.all (routes 5 pool6_81.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_81,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_9 _ hm
  · exact checked5_15 _ hm
  · exact checked5_33 _ hm
  · exact checked5_101 _ hm
  · exact checked5_102 _ hm
  · exact checked5_103 _ hm
  · exact checked5_104 _ hm
  · exact checked5_105 _ hm
  · exact checked5_106 _ hm
  · exact checked5_107 _ hm
  · exact checked5_112 _ hm
  · exact checked5_113 _ hm
  · exact checked5_115 _ hm
  · exact checked5_118 _ hm
  · exact checked5_119 _ hm
  · exact checked5_135 _ hm
  · exact checked5_191 _ hm
  · exact checked5_192 _ hm
  · exact checked5_193 _ hm
  · exact checked5_215 _ hm
  · exact checked5_280 _ hm
  · exact checked5_281 _ hm
  · exact checked5_344 _ hm
  · exact checked5_407 _ hm
  · exact checked5_409 _ hm
  · exact checked5_412 _ hm
private def chunk6_82 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire43690],
  [wire15,wire240,wire4369,wire34952,wire43690,wire61440],
  [wire15,wire240,wire4369,wire34952,wire48059],
  [wire15,wire240,wire4369,wire34952,wire48059,wire61440]]
private def pool6_82 : List (List (List T)) := [chunk5_16, chunk5_17, chunk5_18, chunk5_19, chunk5_34, chunk5_85, chunk5_105, chunk5_110, chunk5_112, chunk5_113, chunk5_118, chunk5_121, chunk5_124, chunk5_126, chunk5_127, chunk5_135, chunk5_196, chunk5_197, chunk5_198, chunk5_199, chunk5_200, chunk5_201, chunk5_215, chunk5_282, chunk5_284, chunk5_344, chunk5_345, chunk5_412, chunk5_413]
private theorem checked6_82 : ∀ w ∈ chunk6_82, ¬ Need 6 w.toFinset := by
  have h : chunk6_82.all (routes 5 pool6_82.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_82,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_16 _ hm
  · exact checked5_17 _ hm
  · exact checked5_18 _ hm
  · exact checked5_19 _ hm
  · exact checked5_34 _ hm
  · exact checked5_85 _ hm
  · exact checked5_105 _ hm
  · exact checked5_110 _ hm
  · exact checked5_112 _ hm
  · exact checked5_113 _ hm
  · exact checked5_118 _ hm
  · exact checked5_121 _ hm
  · exact checked5_124 _ hm
  · exact checked5_126 _ hm
  · exact checked5_127 _ hm
  · exact checked5_135 _ hm
  · exact checked5_196 _ hm
  · exact checked5_197 _ hm
  · exact checked5_198 _ hm
  · exact checked5_199 _ hm
  · exact checked5_200 _ hm
  · exact checked5_201 _ hm
  · exact checked5_215 _ hm
  · exact checked5_282 _ hm
  · exact checked5_284 _ hm
  · exact checked5_344 _ hm
  · exact checked5_345 _ hm
  · exact checked5_412 _ hm
  · exact checked5_413 _ hm
private def chunk6_83 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire52428],
  [wire15,wire240,wire4369,wire34952,wire52428,wire61440],
  [wire15,wire240,wire4369,wire34952,wire56797],
  [wire15,wire240,wire4369,wire34952,wire56797,wire61440]]
private def pool6_83 : List (List (List T)) := [chunk5_19, chunk5_20, chunk5_57, chunk5_78, chunk5_110, chunk5_114, chunk5_115, chunk5_116, chunk5_119, chunk5_124, chunk5_125, chunk5_128, chunk5_135, chunk5_197, chunk5_199, chunk5_200, chunk5_201, chunk5_216, chunk5_282, chunk5_283, chunk5_285, chunk5_345, chunk5_414]
private theorem checked6_83 : ∀ w ∈ chunk6_83, ¬ Need 6 w.toFinset := by
  have h : chunk6_83.all (routes 5 pool6_83.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_83,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_19 _ hm
  · exact checked5_20 _ hm
  · exact checked5_57 _ hm
  · exact checked5_78 _ hm
  · exact checked5_110 _ hm
  · exact checked5_114 _ hm
  · exact checked5_115 _ hm
  · exact checked5_116 _ hm
  · exact checked5_119 _ hm
  · exact checked5_124 _ hm
  · exact checked5_125 _ hm
  · exact checked5_128 _ hm
  · exact checked5_135 _ hm
  · exact checked5_197 _ hm
  · exact checked5_199 _ hm
  · exact checked5_200 _ hm
  · exact checked5_201 _ hm
  · exact checked5_216 _ hm
  · exact checked5_282 _ hm
  · exact checked5_283 _ hm
  · exact checked5_285 _ hm
  · exact checked5_345 _ hm
  · exact checked5_414 _ hm
private def chunk6_84 : List (List T) := [[wire15,wire240,wire4369,wire34952,wire61440,wire61986],
  [wire15,wire240,wire4369,wire34952,wire61440,wire62532],
  [wire15,wire240,wire4369,wire34952,wire61986],
  [wire15,wire240,wire4369,wire34952,wire62532]]
private def pool6_84 : List (List (List T)) := [chunk5_2, chunk5_9, chunk5_34, chunk5_42, chunk5_43, chunk5_111, chunk5_117, chunk5_118, chunk5_119, chunk5_122, chunk5_125, chunk5_129, chunk5_130, chunk5_136, chunk5_197, chunk5_198, chunk5_200, chunk5_216, chunk5_283, chunk5_286, chunk5_345, chunk5_346, chunk5_415, chunk5_416, chunk5_417]
private theorem checked6_84 : ∀ w ∈ chunk6_84, ¬ Need 6 w.toFinset := by
  have h : chunk6_84.all (routes 5 pool6_84.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_84,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_2 _ hm
  · exact checked5_9 _ hm
  · exact checked5_34 _ hm
  · exact checked5_42 _ hm
  · exact checked5_43 _ hm
  · exact checked5_111 _ hm
  · exact checked5_117 _ hm
  · exact checked5_118 _ hm
  · exact checked5_119 _ hm
  · exact checked5_122 _ hm
  · exact checked5_125 _ hm
  · exact checked5_129 _ hm
  · exact checked5_130 _ hm
  · exact checked5_136 _ hm
  · exact checked5_197 _ hm
  · exact checked5_198 _ hm
  · exact checked5_200 _ hm
  · exact checked5_216 _ hm
  · exact checked5_283 _ hm
  · exact checked5_286 _ hm
  · exact checked5_345 _ hm
  · exact checked5_346 _ hm
  · exact checked5_415 _ hm
  · exact checked5_416 _ hm
  · exact checked5_417 _ hm
private def chunk6_85 : List (List T) := [[wire15,wire240,wire4383,wire8738,wire17476,wire34952],
  [wire15,wire240,wire4383,wire8738,wire34952],
  [wire15,wire240,wire4383,wire8738,wire34952,wire61440],
  [wire15,wire240,wire4593,wire8738,wire17476]]
private def pool6_85 : List (List (List T)) := [chunk5_3, chunk5_23, chunk5_133, chunk5_134, chunk5_135, chunk5_136, chunk5_138, chunk5_139, chunk5_140, chunk5_141, chunk5_146, chunk5_147, chunk5_149, chunk5_152, chunk5_161, chunk5_163, chunk5_217, chunk5_289, chunk5_290, chunk5_291, chunk5_292, chunk5_346, chunk5_418, chunk5_419, chunk5_420, chunk5_421, chunk5_464]
private theorem checked6_85 : ∀ w ∈ chunk6_85, ¬ Need 6 w.toFinset := by
  have h : chunk6_85.all (routes 5 pool6_85.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_85,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_23 _ hm
  · exact checked5_133 _ hm
  · exact checked5_134 _ hm
  · exact checked5_135 _ hm
  · exact checked5_136 _ hm
  · exact checked5_138 _ hm
  · exact checked5_139 _ hm
  · exact checked5_140 _ hm
  · exact checked5_141 _ hm
  · exact checked5_146 _ hm
  · exact checked5_147 _ hm
  · exact checked5_149 _ hm
  · exact checked5_152 _ hm
  · exact checked5_161 _ hm
  · exact checked5_163 _ hm
  · exact checked5_217 _ hm
  · exact checked5_289 _ hm
  · exact checked5_290 _ hm
  · exact checked5_291 _ hm
  · exact checked5_292 _ hm
  · exact checked5_346 _ hm
  · exact checked5_418 _ hm
  · exact checked5_419 _ hm
  · exact checked5_420 _ hm
  · exact checked5_421 _ hm
  · exact checked5_464 _ hm
private def chunk6_86 : List (List T) := [[wire15,wire240,wire4593,wire8738,wire17476,wire34952],
  [wire15,wire240,wire4593,wire8738,wire17476,wire61440],
  [wire15,wire240,wire7953,wire8738,wire17476,wire34952],
  [wire15,wire240,wire8192,wire8738,wire17476,wire34952]]
private def pool6_86 : List (List (List T)) := [chunk5_139, chunk5_141, chunk5_149, chunk5_151, chunk5_158, chunk5_291, chunk5_293, chunk5_422, chunk5_465]
private theorem checked6_86 : ∀ w ∈ chunk6_86, ¬ Need 6 w.toFinset := by
  have h : chunk6_86.all (routes 5 pool6_86.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_86,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_139 _ hm
  · exact checked5_141 _ hm
  · exact checked5_149 _ hm
  · exact checked5_151 _ hm
  · exact checked5_158 _ hm
  · exact checked5_291 _ hm
  · exact checked5_293 _ hm
  · exact checked5_422 _ hm
  · exact checked5_465 _ hm
private def chunk6_87 : List (List T) := [[wire15,wire240,wire8738,wire8751,wire17476,wire34952],
  [wire15,wire240,wire8738,wire8946,wire17476,wire34952],
  [wire15,wire240,wire8738,wire12066,wire17476,wire34952],
  [wire15,wire240,wire8738,wire13107,wire17476]]
private def pool6_87 : List (List (List T)) := [chunk5_8, chunk5_26, chunk5_143, chunk5_144, chunk5_145, chunk5_146, chunk5_148, chunk5_149, chunk5_151, chunk5_152, chunk5_160, chunk5_169, chunk5_170, chunk5_171, chunk5_172, chunk5_173, chunk5_175, chunk5_217, chunk5_293, chunk5_294, chunk5_295, chunk5_346, chunk5_423, chunk5_424, chunk5_465]
private theorem checked6_87 : ∀ w ∈ chunk6_87, ¬ Need 6 w.toFinset := by
  have h : chunk6_87.all (routes 5 pool6_87.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_87,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_26 _ hm
  · exact checked5_143 _ hm
  · exact checked5_144 _ hm
  · exact checked5_145 _ hm
  · exact checked5_146 _ hm
  · exact checked5_148 _ hm
  · exact checked5_149 _ hm
  · exact checked5_151 _ hm
  · exact checked5_152 _ hm
  · exact checked5_160 _ hm
  · exact checked5_169 _ hm
  · exact checked5_170 _ hm
  · exact checked5_171 _ hm
  · exact checked5_172 _ hm
  · exact checked5_173 _ hm
  · exact checked5_175 _ hm
  · exact checked5_217 _ hm
  · exact checked5_293 _ hm
  · exact checked5_294 _ hm
  · exact checked5_295 _ hm
  · exact checked5_346 _ hm
  · exact checked5_423 _ hm
  · exact checked5_424 _ hm
  · exact checked5_465 _ hm
private def chunk6_88 : List (List T) := [[wire15,wire240,wire8738,wire13107,wire17476,wire34952],
  [wire15,wire240,wire8738,wire13107,wire17476,wire61440],
  [wire15,wire240,wire8738,wire13107,wire34952],
  [wire15,wire240,wire8738,wire13107,wire34952,wire61440]]
private def pool6_88 : List (List (List T)) := [chunk5_144, chunk5_145, chunk5_146, chunk5_149, chunk5_162, chunk5_163, chunk5_173, chunk5_175, chunk5_176, chunk5_177, chunk5_217, chunk5_294, chunk5_295, chunk5_347, chunk5_424, chunk5_425]
private theorem checked6_88 : ∀ w ∈ chunk6_88, ¬ Need 6 w.toFinset := by
  have h : chunk6_88.all (routes 5 pool6_88.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_88,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_144 _ hm
  · exact checked5_145 _ hm
  · exact checked5_146 _ hm
  · exact checked5_149 _ hm
  · exact checked5_162 _ hm
  · exact checked5_163 _ hm
  · exact checked5_173 _ hm
  · exact checked5_175 _ hm
  · exact checked5_176 _ hm
  · exact checked5_177 _ hm
  · exact checked5_217 _ hm
  · exact checked5_294 _ hm
  · exact checked5_295 _ hm
  · exact checked5_347 _ hm
  · exact checked5_424 _ hm
  · exact checked5_425 _ hm
private def chunk6_89 : List (List T) := [[wire15,wire240,wire8738,wire16384,wire17476,wire34952],
  [wire15,wire240,wire8738,wire17476,wire17487,wire34952],
  [wire15,wire240,wire8738,wire17476,wire17652,wire34952],
  [wire15,wire240,wire8738,wire17476,wire20292,wire34952]]
private def pool6_89 : List (List (List T)) := [chunk5_15, chunk5_28, chunk5_149, chunk5_152, chunk5_154, chunk5_156, chunk5_180, chunk5_190, chunk5_296, chunk5_297, chunk5_425, chunk5_426, chunk5_428, chunk5_432, chunk5_433, chunk5_436]
private theorem checked6_89 : ∀ w ∈ chunk6_89, ¬ Need 6 w.toFinset := by
  have h : chunk6_89.all (routes 5 pool6_89.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_89,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_15 _ hm
  · exact checked5_28 _ hm
  · exact checked5_149 _ hm
  · exact checked5_152 _ hm
  · exact checked5_154 _ hm
  · exact checked5_156 _ hm
  · exact checked5_180 _ hm
  · exact checked5_190 _ hm
  · exact checked5_296 _ hm
  · exact checked5_297 _ hm
  · exact checked5_425 _ hm
  · exact checked5_426 _ hm
  · exact checked5_428 _ hm
  · exact checked5_432 _ hm
  · exact checked5_433 _ hm
  · exact checked5_436 _ hm
private def chunk6_90 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire21845],
  [wire15,wire240,wire8738,wire17476,wire21845,wire34952],
  [wire15,wire240,wire8738,wire17476,wire21845,wire61440],
  [wire15,wire240,wire8738,wire17476,wire26214,wire34952]]
private def pool6_90 : List (List (List T)) := [chunk5_23, chunk5_147, chunk5_148, chunk5_149, chunk5_151, chunk5_153, chunk5_154, chunk5_157, chunk5_158, chunk5_159, chunk5_168, chunk5_178, chunk5_179, chunk5_180, chunk5_181, chunk5_191, chunk5_192, chunk5_218, chunk5_297, chunk5_298, chunk5_347, chunk5_426, chunk5_428, chunk5_433, chunk5_434]
private theorem checked6_90 : ∀ w ∈ chunk6_90, ¬ Need 6 w.toFinset := by
  have h : chunk6_90.all (routes 5 pool6_90.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_90,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_23 _ hm
  · exact checked5_147 _ hm
  · exact checked5_148 _ hm
  · exact checked5_149 _ hm
  · exact checked5_151 _ hm
  · exact checked5_153 _ hm
  · exact checked5_154 _ hm
  · exact checked5_157 _ hm
  · exact checked5_158 _ hm
  · exact checked5_159 _ hm
  · exact checked5_168 _ hm
  · exact checked5_178 _ hm
  · exact checked5_179 _ hm
  · exact checked5_180 _ hm
  · exact checked5_181 _ hm
  · exact checked5_191 _ hm
  · exact checked5_192 _ hm
  · exact checked5_218 _ hm
  · exact checked5_297 _ hm
  · exact checked5_298 _ hm
  · exact checked5_347 _ hm
  · exact checked5_426 _ hm
  · exact checked5_428 _ hm
  · exact checked5_433 _ hm
  · exact checked5_434 _ hm
private def chunk6_91 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire30583],
  [wire15,wire240,wire8738,wire17476,wire30583,wire34952],
  [wire15,wire240,wire8738,wire17476,wire30583,wire61440],
  [wire15,wire240,wire8738,wire17476,wire32768,wire34952]]
private def pool6_91 : List (List (List T)) := [chunk5_32, chunk5_148, chunk5_149, chunk5_154, chunk5_158, chunk5_160, chunk5_162, chunk5_180, chunk5_182, chunk5_183, chunk5_218, chunk5_299, chunk5_300, chunk5_347, chunk5_426, chunk5_429, chunk5_435]
private theorem checked6_91 : ∀ w ∈ chunk6_91, ¬ Need 6 w.toFinset := by
  have h : chunk6_91.all (routes 5 pool6_91.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_91,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_32 _ hm
  · exact checked5_148 _ hm
  · exact checked5_149 _ hm
  · exact checked5_154 _ hm
  · exact checked5_158 _ hm
  · exact checked5_160 _ hm
  · exact checked5_162 _ hm
  · exact checked5_180 _ hm
  · exact checked5_182 _ hm
  · exact checked5_183 _ hm
  · exact checked5_218 _ hm
  · exact checked5_299 _ hm
  · exact checked5_300 _ hm
  · exact checked5_347 _ hm
  · exact checked5_426 _ hm
  · exact checked5_429 _ hm
  · exact checked5_435 _ hm
private def chunk6_92 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire34952],
  [wire15,wire240,wire8738,wire17476,wire34952,wire34959],
  [wire15,wire240,wire8738,wire17476,wire34952,wire35064],
  [wire15,wire240,wire8738,wire17476,wire34952,wire36744]]
private def pool6_92 : List (List (List T)) := [chunk5_16, chunk5_36, chunk5_148, chunk5_149, chunk5_150, chunk5_151, chunk5_152, chunk5_154, chunk5_158, chunk5_162, chunk5_163, chunk5_164, chunk5_181, chunk5_184, chunk5_185, chunk5_218, chunk5_300, chunk5_301, chunk5_302, chunk5_303, chunk5_347, chunk5_426, chunk5_430, chunk5_436]
private theorem checked6_92 : ∀ w ∈ chunk6_92, ¬ Need 6 w.toFinset := by
  have h : chunk6_92.all (routes 5 pool6_92.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_92,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_16 _ hm
  · exact checked5_36 _ hm
  · exact checked5_148 _ hm
  · exact checked5_149 _ hm
  · exact checked5_150 _ hm
  · exact checked5_151 _ hm
  · exact checked5_152 _ hm
  · exact checked5_154 _ hm
  · exact checked5_158 _ hm
  · exact checked5_162 _ hm
  · exact checked5_163 _ hm
  · exact checked5_164 _ hm
  · exact checked5_181 _ hm
  · exact checked5_184 _ hm
  · exact checked5_185 _ hm
  · exact checked5_218 _ hm
  · exact checked5_300 _ hm
  · exact checked5_301 _ hm
  · exact checked5_302 _ hm
  · exact checked5_303 _ hm
  · exact checked5_347 _ hm
  · exact checked5_426 _ hm
  · exact checked5_430 _ hm
  · exact checked5_436 _ hm
private def chunk6_93 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire34952,wire39321],
  [wire15,wire240,wire8738,wire17476,wire34952,wire43690],
  [wire15,wire240,wire8738,wire17476,wire34952,wire48059],
  [wire15,wire240,wire8738,wire17476,wire34952,wire52428]]
private def pool6_93 : List (List (List T)) := [chunk5_19, chunk5_149, chunk5_151, chunk5_152, chunk5_162, chunk5_163, chunk5_165, chunk5_166, chunk5_184, chunk5_186, chunk5_187, chunk5_194, chunk5_303, chunk5_304, chunk5_437, chunk5_438]
private theorem checked6_93 : ∀ w ∈ chunk6_93, ¬ Need 6 w.toFinset := by
  have h : chunk6_93.all (routes 5 pool6_93.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_93,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_19 _ hm
  · exact checked5_149 _ hm
  · exact checked5_151 _ hm
  · exact checked5_152 _ hm
  · exact checked5_162 _ hm
  · exact checked5_163 _ hm
  · exact checked5_165 _ hm
  · exact checked5_166 _ hm
  · exact checked5_184 _ hm
  · exact checked5_186 _ hm
  · exact checked5_187 _ hm
  · exact checked5_194 _ hm
  · exact checked5_303 _ hm
  · exact checked5_304 _ hm
  · exact checked5_437 _ hm
  · exact checked5_438 _ hm
private def chunk6_94 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire34952,wire56797],
  [wire15,wire240,wire8738,wire17476,wire34952,wire61166],
  [wire15,wire240,wire8738,wire17476,wire34952,wire61440],
  [wire15,wire240,wire8738,wire17476,wire34952,wire61455]]
private def pool6_94 : List (List (List T)) := [chunk5_149, chunk5_153, chunk5_163, chunk5_184, chunk5_187, chunk5_195, chunk5_305, chunk5_306, chunk5_438, chunk5_439, chunk5_466]
private theorem checked6_94 : ∀ w ∈ chunk6_94, ¬ Need 6 w.toFinset := by
  have h : chunk6_94.all (routes 5 pool6_94.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_94,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_149 _ hm
  · exact checked5_153 _ hm
  · exact checked5_163 _ hm
  · exact checked5_184 _ hm
  · exact checked5_187 _ hm
  · exact checked5_195 _ hm
  · exact checked5_305 _ hm
  · exact checked5_306 _ hm
  · exact checked5_438 _ hm
  · exact checked5_439 _ hm
  · exact checked5_466 _ hm
private def chunk6_95 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire34952,wire61680],
  [wire15,wire240,wire8738,wire17476,wire34952,wire61695],
  [wire15,wire240,wire8738,wire17476,wire34952,wire61713],
  [wire15,wire240,wire8738,wire17476,wire34952,wire61986]]
private def pool6_95 : List (List (List T)) := [chunk5_149, chunk5_187, chunk5_195, chunk5_306, chunk5_307, chunk5_439, chunk5_440, chunk5_466]
private theorem checked6_95 : ∀ w ∈ chunk6_95, ¬ Need 6 w.toFinset := by
  have h : chunk6_95.all (routes 5 pool6_95.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_95,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_149 _ hm
  · exact checked5_187 _ hm
  · exact checked5_195 _ hm
  · exact checked5_306 _ hm
  · exact checked5_307 _ hm
  · exact checked5_439 _ hm
  · exact checked5_440 _ hm
  · exact checked5_466 _ hm
private def chunk6_96 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire34952,wire62532],
  [wire15,wire240,wire8738,wire17476,wire34952,wire63624],
  [wire15,wire240,wire8738,wire17476,wire34952,wire65280],
  [wire15,wire240,wire8738,wire17476,wire34952,wire65295]]
private def pool6_96 : List (List (List T)) := [chunk5_148, chunk5_149, chunk5_167, chunk5_187, chunk5_195, chunk5_301, chunk5_307, chunk5_308, chunk5_440, chunk5_441, chunk5_466]
private theorem checked6_96 : ∀ w ∈ chunk6_96, ¬ Need 6 w.toFinset := by
  have h : chunk6_96.all (routes 5 pool6_96.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_96,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_148 _ hm
  · exact checked5_149 _ hm
  · exact checked5_167 _ hm
  · exact checked5_187 _ hm
  · exact checked5_195 _ hm
  · exact checked5_301 _ hm
  · exact checked5_307 _ hm
  · exact checked5_308 _ hm
  · exact checked5_440 _ hm
  · exact checked5_441 _ hm
  · exact checked5_466 _ hm
private def chunk6_97 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire34952,wire65520],
  [wire15,wire240,wire8738,wire17476,wire34952,wire65535],
  [wire15,wire240,wire8738,wire17476,wire35064],
  [wire15,wire240,wire8738,wire17476,wire35064,wire61440]]
private def pool6_97 : List (List (List T)) := [chunk5_0, chunk5_25, chunk5_28, chunk5_147, chunk5_148, chunk5_149, chunk5_150, chunk5_151, chunk5_152, chunk5_155, chunk5_159, chunk5_164, chunk5_181, chunk5_185, chunk5_218, chunk5_294, chunk5_296, chunk5_302, chunk5_305, chunk5_306, chunk5_308, chunk5_348, chunk5_427, chunk5_430, chunk5_441, chunk5_442, chunk5_466]
private theorem checked6_97 : ∀ w ∈ chunk6_97, ¬ Need 6 w.toFinset := by
  have h : chunk6_97.all (routes 5 pool6_97.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_97,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_25 _ hm
  · exact checked5_28 _ hm
  · exact checked5_147 _ hm
  · exact checked5_148 _ hm
  · exact checked5_149 _ hm
  · exact checked5_150 _ hm
  · exact checked5_151 _ hm
  · exact checked5_152 _ hm
  · exact checked5_155 _ hm
  · exact checked5_159 _ hm
  · exact checked5_164 _ hm
  · exact checked5_181 _ hm
  · exact checked5_185 _ hm
  · exact checked5_218 _ hm
  · exact checked5_294 _ hm
  · exact checked5_296 _ hm
  · exact checked5_302 _ hm
  · exact checked5_305 _ hm
  · exact checked5_306 _ hm
  · exact checked5_308 _ hm
  · exact checked5_348 _ hm
  · exact checked5_427 _ hm
  · exact checked5_430 _ hm
  · exact checked5_441 _ hm
  · exact checked5_442 _ hm
  · exact checked5_466 _ hm
private def chunk6_98 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire43690],
  [wire15,wire240,wire8738,wire17476,wire43690,wire61440],
  [wire15,wire240,wire8738,wire17476,wire52428],
  [wire15,wire240,wire8738,wire17476,wire52428,wire61440]]
private def pool6_98 : List (List (List T)) := [chunk5_24, chunk5_143, chunk5_147, chunk5_151, chunk5_152, chunk5_153, chunk5_155, chunk5_159, chunk5_166, chunk5_167, chunk5_169, chunk5_181, chunk5_187, chunk5_188, chunk5_195, chunk5_196, chunk5_219, chunk5_309, chunk5_310, chunk5_348, chunk5_427, chunk5_431, chunk5_442, chunk5_443]
private theorem checked6_98 : ∀ w ∈ chunk6_98, ¬ Need 6 w.toFinset := by
  have h : chunk6_98.all (routes 5 pool6_98.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_98,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_24 _ hm
  · exact checked5_143 _ hm
  · exact checked5_147 _ hm
  · exact checked5_151 _ hm
  · exact checked5_152 _ hm
  · exact checked5_153 _ hm
  · exact checked5_155 _ hm
  · exact checked5_159 _ hm
  · exact checked5_166 _ hm
  · exact checked5_167 _ hm
  · exact checked5_169 _ hm
  · exact checked5_181 _ hm
  · exact checked5_187 _ hm
  · exact checked5_188 _ hm
  · exact checked5_195 _ hm
  · exact checked5_196 _ hm
  · exact checked5_219 _ hm
  · exact checked5_309 _ hm
  · exact checked5_310 _ hm
  · exact checked5_348 _ hm
  · exact checked5_427 _ hm
  · exact checked5_431 _ hm
  · exact checked5_442 _ hm
  · exact checked5_443 _ hm
private def chunk6_99 : List (List T) := [[wire15,wire240,wire8738,wire17476,wire61166],
  [wire15,wire240,wire8738,wire17476,wire61166,wire61440],
  [wire15,wire240,wire8738,wire17487,wire34952],
  [wire15,wire240,wire8738,wire17487,wire34952,wire61440]]
private def pool6_99 : List (List (List T)) := [chunk5_0, chunk5_7, chunk5_16, chunk5_24, chunk5_51, chunk5_153, chunk5_154, chunk5_155, chunk5_159, chunk5_160, chunk5_162, chunk5_163, chunk5_167, chunk5_169, chunk5_182, chunk5_188, chunk5_189, chunk5_219, chunk5_310, chunk5_311, chunk5_348, chunk5_349, chunk5_423, chunk5_427, chunk5_432, chunk5_436, chunk5_439, chunk5_441]
private theorem checked6_99 : ∀ w ∈ chunk6_99, ¬ Need 6 w.toFinset := by
  have h : chunk6_99.all (routes 5 pool6_99.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_99,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_7 _ hm
  · exact checked5_16 _ hm
  · exact checked5_24 _ hm
  · exact checked5_51 _ hm
  · exact checked5_153 _ hm
  · exact checked5_154 _ hm
  · exact checked5_155 _ hm
  · exact checked5_159 _ hm
  · exact checked5_160 _ hm
  · exact checked5_162 _ hm
  · exact checked5_163 _ hm
  · exact checked5_167 _ hm
  · exact checked5_169 _ hm
  · exact checked5_182 _ hm
  · exact checked5_188 _ hm
  · exact checked5_189 _ hm
  · exact checked5_219 _ hm
  · exact checked5_310 _ hm
  · exact checked5_311 _ hm
  · exact checked5_348 _ hm
  · exact checked5_349 _ hm
  · exact checked5_423 _ hm
  · exact checked5_427 _ hm
  · exact checked5_432 _ hm
  · exact checked5_436 _ hm
  · exact checked5_439 _ hm
  · exact checked5_441 _ hm
private def chunk6_100 : List (List T) := [[wire15,wire240,wire8738,wire26214,wire34952],
  [wire15,wire240,wire8738,wire26214,wire34952,wire61440],
  [wire15,wire240,wire8738,wire34952,wire39321],
  [wire15,wire240,wire8738,wire34952,wire39321,wire61440]]
private def pool6_100 : List (List (List T)) := [chunk5_3, chunk5_4, chunk5_158, chunk5_159, chunk5_160, chunk5_161, chunk5_162, chunk5_163, chunk5_164, chunk5_165, chunk5_170, chunk5_194, chunk5_195, chunk5_196, chunk5_197, chunk5_200, chunk5_201, chunk5_220, chunk5_312, chunk5_313, chunk5_314, chunk5_316, chunk5_349, chunk5_444]
private theorem checked6_100 : ∀ w ∈ chunk6_100, ¬ Need 6 w.toFinset := by
  have h : chunk6_100.all (routes 5 pool6_100.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_100,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_3 _ hm
  · exact checked5_4 _ hm
  · exact checked5_158 _ hm
  · exact checked5_159 _ hm
  · exact checked5_160 _ hm
  · exact checked5_161 _ hm
  · exact checked5_162 _ hm
  · exact checked5_163 _ hm
  · exact checked5_164 _ hm
  · exact checked5_165 _ hm
  · exact checked5_170 _ hm
  · exact checked5_194 _ hm
  · exact checked5_195 _ hm
  · exact checked5_196 _ hm
  · exact checked5_197 _ hm
  · exact checked5_200 _ hm
  · exact checked5_201 _ hm
  · exact checked5_220 _ hm
  · exact checked5_312 _ hm
  · exact checked5_313 _ hm
  · exact checked5_314 _ hm
  · exact checked5_316 _ hm
  · exact checked5_349 _ hm
  · exact checked5_444 _ hm
private def chunk6_101 : List (List T) := [[wire15,wire240,wire8738,wire34952,wire48059],
  [wire15,wire240,wire8738,wire34952,wire48059,wire61440],
  [wire15,wire240,wire8738,wire34952,wire52428],
  [wire15,wire240,wire8738,wire34952,wire52428,wire61440]]
private def pool6_101 : List (List (List T)) := [chunk5_19, chunk5_144, chunk5_149, chunk5_160, chunk5_162, chunk5_163, chunk5_164, chunk5_166, chunk5_167, chunk5_198, chunk5_199, chunk5_201, chunk5_202, chunk5_220, chunk5_313, chunk5_315, chunk5_316, chunk5_317, chunk5_349, chunk5_350, chunk5_445, chunk5_446]
private theorem checked6_101 : ∀ w ∈ chunk6_101, ¬ Need 6 w.toFinset := by
  have h : chunk6_101.all (routes 5 pool6_101.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_101,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_19 _ hm
  · exact checked5_144 _ hm
  · exact checked5_149 _ hm
  · exact checked5_160 _ hm
  · exact checked5_162 _ hm
  · exact checked5_163 _ hm
  · exact checked5_164 _ hm
  · exact checked5_166 _ hm
  · exact checked5_167 _ hm
  · exact checked5_198 _ hm
  · exact checked5_199 _ hm
  · exact checked5_201 _ hm
  · exact checked5_202 _ hm
  · exact checked5_220 _ hm
  · exact checked5_313 _ hm
  · exact checked5_315 _ hm
  · exact checked5_316 _ hm
  · exact checked5_317 _ hm
  · exact checked5_349 _ hm
  · exact checked5_350 _ hm
  · exact checked5_445 _ hm
  · exact checked5_446 _ hm
private def chunk6_102 : List (List T) := [[wire15,wire240,wire8738,wire34952,wire61166],
  [wire15,wire240,wire8738,wire34952,wire61166,wire61440],
  [wire15,wire240,wire17476,wire21845,wire34952],
  [wire15,wire240,wire17476,wire21845,wire34952,wire61440]]
private def pool6_102 : List (List (List T)) := [chunk5_4, chunk5_35, chunk5_57, chunk5_161, chunk5_163, chunk5_164, chunk5_166, chunk5_168, chunk5_170, chunk5_178, chunk5_179, chunk5_180, chunk5_184, chunk5_189, chunk5_192, chunk5_193, chunk5_194, chunk5_198, chunk5_200, chunk5_221, chunk5_314, chunk5_316, chunk5_317, chunk5_318, chunk5_350, chunk5_446, chunk5_447, chunk5_448, chunk5_451]
private theorem checked6_102 : ∀ w ∈ chunk6_102, ¬ Need 6 w.toFinset := by
  have h : chunk6_102.all (routes 5 pool6_102.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_102,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_35 _ hm
  · exact checked5_57 _ hm
  · exact checked5_161 _ hm
  · exact checked5_163 _ hm
  · exact checked5_164 _ hm
  · exact checked5_166 _ hm
  · exact checked5_168 _ hm
  · exact checked5_170 _ hm
  · exact checked5_178 _ hm
  · exact checked5_179 _ hm
  · exact checked5_180 _ hm
  · exact checked5_184 _ hm
  · exact checked5_189 _ hm
  · exact checked5_192 _ hm
  · exact checked5_193 _ hm
  · exact checked5_194 _ hm
  · exact checked5_198 _ hm
  · exact checked5_200 _ hm
  · exact checked5_221 _ hm
  · exact checked5_314 _ hm
  · exact checked5_316 _ hm
  · exact checked5_317 _ hm
  · exact checked5_318 _ hm
  · exact checked5_350 _ hm
  · exact checked5_446 _ hm
  · exact checked5_447 _ hm
  · exact checked5_448 _ hm
  · exact checked5_451 _ hm
private def chunk6_103 : List (List T) := [[wire15,wire240,wire17476,wire26214,wire34952],
  [wire15,wire240,wire17476,wire26214,wire34952,wire61440],
  [wire15,wire240,wire17476,wire34952,wire39321],
  [wire15,wire240,wire17476,wire34952,wire39321,wire61440]]
private def pool6_103 : List (List (List T)) := [chunk5_11, chunk5_180, chunk5_181, chunk5_182, chunk5_183, chunk5_184, chunk5_185, chunk5_186, chunk5_190, chunk5_194, chunk5_195, chunk5_196, chunk5_197, chunk5_198, chunk5_201, chunk5_221, chunk5_318, chunk5_319, chunk5_320, chunk5_321, chunk5_323, chunk5_350, chunk5_351, chunk5_447, chunk5_449]
private theorem checked6_103 : ∀ w ∈ chunk6_103, ¬ Need 6 w.toFinset := by
  have h : chunk6_103.all (routes 5 pool6_103.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_103,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_11 _ hm
  · exact checked5_180 _ hm
  · exact checked5_181 _ hm
  · exact checked5_182 _ hm
  · exact checked5_183 _ hm
  · exact checked5_184 _ hm
  · exact checked5_185 _ hm
  · exact checked5_186 _ hm
  · exact checked5_190 _ hm
  · exact checked5_194 _ hm
  · exact checked5_195 _ hm
  · exact checked5_196 _ hm
  · exact checked5_197 _ hm
  · exact checked5_198 _ hm
  · exact checked5_201 _ hm
  · exact checked5_221 _ hm
  · exact checked5_318 _ hm
  · exact checked5_319 _ hm
  · exact checked5_320 _ hm
  · exact checked5_321 _ hm
  · exact checked5_323 _ hm
  · exact checked5_350 _ hm
  · exact checked5_351 _ hm
  · exact checked5_447 _ hm
  · exact checked5_449 _ hm
private def chunk6_104 : List (List T) := [[wire15,wire240,wire17476,wire34952,wire43690],
  [wire15,wire240,wire17476,wire34952,wire43690,wire61440],
  [wire15,wire240,wire17476,wire34952,wire56797],
  [wire15,wire240,wire17476,wire34952,wire56797,wire61440]]
private def pool6_104 : List (List (List T)) := [chunk5_35, chunk5_149, chunk5_178, chunk5_182, chunk5_184, chunk5_185, chunk5_187, chunk5_188, chunk5_189, chunk5_198, chunk5_199, chunk5_201, chunk5_202, chunk5_222, chunk5_320, chunk5_321, chunk5_322, chunk5_323, chunk5_351, chunk5_447, chunk5_448, chunk5_450, chunk5_452]
private theorem checked6_104 : ∀ w ∈ chunk6_104, ¬ Need 6 w.toFinset := by
  have h : chunk6_104.all (routes 5 pool6_104.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_104,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_35 _ hm
  · exact checked5_149 _ hm
  · exact checked5_178 _ hm
  · exact checked5_182 _ hm
  · exact checked5_184 _ hm
  · exact checked5_185 _ hm
  · exact checked5_187 _ hm
  · exact checked5_188 _ hm
  · exact checked5_189 _ hm
  · exact checked5_198 _ hm
  · exact checked5_199 _ hm
  · exact checked5_201 _ hm
  · exact checked5_202 _ hm
  · exact checked5_222 _ hm
  · exact checked5_320 _ hm
  · exact checked5_321 _ hm
  · exact checked5_322 _ hm
  · exact checked5_323 _ hm
  · exact checked5_351 _ hm
  · exact checked5_447 _ hm
  · exact checked5_448 _ hm
  · exact checked5_450 _ hm
  · exact checked5_452 _ hm
private def chunk6_105 : List (List T) := [[wire15,wire240,wire17476,wire34952,wire61166],
  [wire15,wire240,wire17476,wire34952,wire61166,wire61440],
  [wire15,wire255,wire3840,wire4369,wire8738,wire17476],
  [wire15,wire255,wire3840,wire4369,wire8738,wire34952]]
private def pool6_105 : List (List (List T)) := [chunk5_11, chunk5_35, chunk5_85, chunk5_183, chunk5_184, chunk5_185, chunk5_188, chunk5_189, chunk5_190, chunk5_199, chunk5_200, chunk5_208, chunk5_209, chunk5_211, chunk5_222, chunk5_320, chunk5_322, chunk5_351, chunk5_448, chunk5_451, chunk5_454, chunk5_455]
private theorem checked6_105 : ∀ w ∈ chunk6_105, ¬ Need 6 w.toFinset := by
  have h : chunk6_105.all (routes 5 pool6_105.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_105,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_11 _ hm
  · exact checked5_35 _ hm
  · exact checked5_85 _ hm
  · exact checked5_183 _ hm
  · exact checked5_184 _ hm
  · exact checked5_185 _ hm
  · exact checked5_188 _ hm
  · exact checked5_189 _ hm
  · exact checked5_190 _ hm
  · exact checked5_199 _ hm
  · exact checked5_200 _ hm
  · exact checked5_208 _ hm
  · exact checked5_209 _ hm
  · exact checked5_211 _ hm
  · exact checked5_222 _ hm
  · exact checked5_320 _ hm
  · exact checked5_322 _ hm
  · exact checked5_351 _ hm
  · exact checked5_448 _ hm
  · exact checked5_451 _ hm
  · exact checked5_454 _ hm
  · exact checked5_455 _ hm
private def chunk6_106 : List (List T) := [[wire15,wire255,wire3840,wire4369,wire17476,wire34952],
  [wire15,wire255,wire3840,wire8738,wire17476,wire34952],
  [wire15,wire255,wire4369,wire8738,wire17476],
  [wire15,wire255,wire4369,wire8738,wire17476,wire34952]]
private def pool6_106 : List (List (List T)) := [chunk5_26, chunk5_29, chunk5_207, chunk5_208, chunk5_210, chunk5_211, chunk5_212, chunk5_213, chunk5_214, chunk5_215, chunk5_217, chunk5_218, chunk5_219, chunk5_245, chunk5_455, chunk5_457, chunk5_458, chunk5_460, chunk5_461, chunk5_464]
private theorem checked6_106 : ∀ w ∈ chunk6_106, ¬ Need 6 w.toFinset := by
  have h : chunk6_106.all (routes 5 pool6_106.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_106,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_26 _ hm
  · exact checked5_29 _ hm
  · exact checked5_207 _ hm
  · exact checked5_208 _ hm
  · exact checked5_210 _ hm
  · exact checked5_211 _ hm
  · exact checked5_212 _ hm
  · exact checked5_213 _ hm
  · exact checked5_214 _ hm
  · exact checked5_215 _ hm
  · exact checked5_217 _ hm
  · exact checked5_218 _ hm
  · exact checked5_219 _ hm
  · exact checked5_245 _ hm
  · exact checked5_455 _ hm
  · exact checked5_457 _ hm
  · exact checked5_458 _ hm
  · exact checked5_460 _ hm
  · exact checked5_461 _ hm
  · exact checked5_464 _ hm
private def chunk6_107 : List (List T) := [[wire15,wire255,wire4369,wire8738,wire17476,wire61440],
  [wire15,wire255,wire4369,wire8738,wire34952],
  [wire15,wire255,wire4369,wire8738,wire34952,wire61440],
  [wire15,wire255,wire4369,wire17476,wire34952]]
private def pool6_107 : List (List (List T)) := [chunk5_4, chunk5_12, chunk5_27, chunk5_29, chunk5_37, chunk5_208, chunk5_209, chunk5_210, chunk5_212, chunk5_213, chunk5_214, chunk5_215, chunk5_216, chunk5_217, chunk5_220, chunk5_221, chunk5_222, chunk5_250, chunk5_251, chunk5_268, chunk5_457, chunk5_458, chunk5_459, chunk5_460, chunk5_461, chunk5_462, chunk5_463, chunk5_464]
private theorem checked6_107 : ∀ w ∈ chunk6_107, ¬ Need 6 w.toFinset := by
  have h : chunk6_107.all (routes 5 pool6_107.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_107,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_4 _ hm
  · exact checked5_12 _ hm
  · exact checked5_27 _ hm
  · exact checked5_29 _ hm
  · exact checked5_37 _ hm
  · exact checked5_208 _ hm
  · exact checked5_209 _ hm
  · exact checked5_210 _ hm
  · exact checked5_212 _ hm
  · exact checked5_213 _ hm
  · exact checked5_214 _ hm
  · exact checked5_215 _ hm
  · exact checked5_216 _ hm
  · exact checked5_217 _ hm
  · exact checked5_220 _ hm
  · exact checked5_221 _ hm
  · exact checked5_222 _ hm
  · exact checked5_250 _ hm
  · exact checked5_251 _ hm
  · exact checked5_268 _ hm
  · exact checked5_457 _ hm
  · exact checked5_458 _ hm
  · exact checked5_459 _ hm
  · exact checked5_460 _ hm
  · exact checked5_461 _ hm
  · exact checked5_462 _ hm
  · exact checked5_463 _ hm
  · exact checked5_464 _ hm
private def chunk6_108 : List (List T) := [[wire15,wire255,wire4369,wire17476,wire34952,wire61440],
  [wire15,wire255,wire8738,wire17476,wire34952],
  [wire15,wire255,wire8738,wire17476,wire34952,wire61440],
  [wire15,wire3840,wire4080,wire4369,wire8738,wire17476]]
private def pool6_108 : List (List (List T)) := [chunk5_214, chunk5_216, chunk5_218, chunk5_219, chunk5_220, chunk5_221, chunk5_222, chunk5_301, chunk5_463, chunk5_465, chunk5_466, chunk5_491]
private theorem checked6_108 : ∀ w ∈ chunk6_108, ¬ Need 6 w.toFinset := by
  have h : chunk6_108.all (routes 5 pool6_108.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_108,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_214 _ hm
  · exact checked5_216 _ hm
  · exact checked5_218 _ hm
  · exact checked5_219 _ hm
  · exact checked5_220 _ hm
  · exact checked5_221 _ hm
  · exact checked5_222 _ hm
  · exact checked5_301 _ hm
  · exact checked5_463 _ hm
  · exact checked5_465 _ hm
  · exact checked5_466 _ hm
  · exact checked5_491 _ hm
private def chunk6_109 : List (List T) := [[wire15,wire3840,wire4080,wire4369,wire8738,wire34952],
  [wire15,wire3840,wire4080,wire4369,wire17476,wire34952],
  [wire15,wire3840,wire4080,wire8738,wire17476,wire34952],
  [wire15,wire3840,wire4095,wire4369,wire8738,wire17476]]
private def pool6_109 : List (List (List T)) := [chunk5_241, chunk5_242, chunk5_468, chunk5_492]
private theorem checked6_109 : ∀ w ∈ chunk6_109, ¬ Need 6 w.toFinset := by
  have h : chunk6_109.all (routes 5 pool6_109.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_109,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_241 _ hm
  · exact checked5_242 _ hm
  · exact checked5_468 _ hm
  · exact checked5_492 _ hm
private def chunk6_110 : List (List T) := [[wire15,wire3840,wire4095,wire4369,wire8738,wire34952],
  [wire15,wire3840,wire4095,wire4369,wire17476,wire34952],
  [wire15,wire3840,wire4095,wire8738,wire17476,wire34952],
  [wire15,wire3840,wire4369,wire8738,wire17476,wire35064]]
private def pool6_110 : List (List (List T)) := [chunk5_222, chunk5_242, chunk5_293, chunk5_469, chunk5_471]
private theorem checked6_110 : ∀ w ∈ chunk6_110, ¬ Need 6 w.toFinset := by
  have h : chunk6_110.all (routes 5 pool6_110.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_110,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_222 _ hm
  · exact checked5_242 _ hm
  · exact checked5_293 _ hm
  · exact checked5_469 _ hm
  · exact checked5_471 _ hm
private def chunk6_111 : List (List T) := [[wire15,wire3840,wire4369,wire8738,wire17476,wire35064,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire17476,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire17476,wire61455],
  [wire15,wire3840,wire4369,wire8738,wire17476,wire63624]]
private def pool6_111 : List (List (List T)) := [chunk5_245, chunk5_246, chunk5_471, chunk5_472, chunk5_479, chunk5_492]
private theorem checked6_111 : ∀ w ∈ chunk6_111, ¬ Need 6 w.toFinset := by
  have h : chunk6_111.all (routes 5 pool6_111.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_111,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_245 _ hm
  · exact checked5_246 _ hm
  · exact checked5_471 _ hm
  · exact checked5_472 _ hm
  · exact checked5_479 _ hm
  · exact checked5_492 _ hm
private def chunk6_112 : List (List T) := [[wire15,wire3840,wire4369,wire8738,wire17476,wire65280],
  [wire15,wire3840,wire4369,wire8738,wire17476,wire65295],
  [wire15,wire3840,wire4369,wire8738,wire20292,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire21845,wire61440]]
private def pool6_112 : List (List (List T)) := [chunk5_235, chunk5_245, chunk5_246, chunk5_247, chunk5_261, chunk5_262, chunk5_472, chunk5_473, chunk5_480, chunk5_493]
private theorem checked6_112 : ∀ w ∈ chunk6_112, ¬ Need 6 w.toFinset := by
  have h : chunk6_112.all (routes 5 pool6_112.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_112,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_235 _ hm
  · exact checked5_245 _ hm
  · exact checked5_246 _ hm
  · exact checked5_247 _ hm
  · exact checked5_261 _ hm
  · exact checked5_262 _ hm
  · exact checked5_472 _ hm
  · exact checked5_473 _ hm
  · exact checked5_480 _ hm
  · exact checked5_493 _ hm
private def chunk6_113 : List (List T) := [[wire15,wire3840,wire4369,wire8738,wire26214,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire30583,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire34952,wire35064],
  [wire15,wire3840,wire4369,wire8738,wire34952,wire61440]]
private def pool6_113 : List (List (List T)) := [chunk5_225, chunk5_234, chunk5_236, chunk5_248, chunk5_249, chunk5_251, chunk5_252, chunk5_253, chunk5_262, chunk5_480]
private theorem checked6_113 : ∀ w ∈ chunk6_113, ¬ Need 6 w.toFinset := by
  have h : chunk6_113.all (routes 5 pool6_113.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_113,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_225 _ hm
  · exact checked5_234 _ hm
  · exact checked5_236 _ hm
  · exact checked5_248 _ hm
  · exact checked5_249 _ hm
  · exact checked5_251 _ hm
  · exact checked5_252 _ hm
  · exact checked5_253 _ hm
  · exact checked5_262 _ hm
  · exact checked5_480 _ hm
private def chunk6_114 : List (List T) := [[wire15,wire3840,wire4369,wire8738,wire34952,wire61455],
  [wire15,wire3840,wire4369,wire8738,wire34952,wire63624],
  [wire15,wire3840,wire4369,wire8738,wire34952,wire65280],
  [wire15,wire3840,wire4369,wire8738,wire34952,wire65295]]
private def pool6_114 : List (List (List T)) := [chunk5_225, chunk5_229, chunk5_251, chunk5_254, chunk5_262, chunk5_263, chunk5_480, chunk5_481, chunk5_493]
private theorem checked6_114 : ∀ w ∈ chunk6_114, ¬ Need 6 w.toFinset := by
  have h : chunk6_114.all (routes 5 pool6_114.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_114,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_225 _ hm
  · exact checked5_229 _ hm
  · exact checked5_251 _ hm
  · exact checked5_254 _ hm
  · exact checked5_262 _ hm
  · exact checked5_263 _ hm
  · exact checked5_480 _ hm
  · exact checked5_481 _ hm
  · exact checked5_493 _ hm
private def chunk6_115 : List (List T) := [[wire15,wire3840,wire4369,wire8738,wire36744,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire39321,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire43690,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire48059,wire61440]]
private def pool6_115 : List (List (List T)) := [chunk5_225, chunk5_236, chunk5_253, chunk5_254, chunk5_255, chunk5_256, chunk5_263, chunk5_473, chunk5_481]
private theorem checked6_115 : ∀ w ∈ chunk6_115, ¬ Need 6 w.toFinset := by
  have h : chunk6_115.all (routes 5 pool6_115.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_115,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_225 _ hm
  · exact checked5_236 _ hm
  · exact checked5_253 _ hm
  · exact checked5_254 _ hm
  · exact checked5_255 _ hm
  · exact checked5_256 _ hm
  · exact checked5_263 _ hm
  · exact checked5_473 _ hm
  · exact checked5_481 _ hm
private def chunk6_116 : List (List T) := [[wire15,wire3840,wire4369,wire8738,wire61440,wire62532],
  [wire15,wire3840,wire4369,wire8738,wire61440,wire63624],
  [wire15,wire3840,wire4369,wire8738,wire63624],
  [wire15,wire3840,wire4369,wire8751,wire17476,wire61440]]
private def pool6_116 : List (List (List T)) := [chunk5_5, chunk5_223, chunk5_225, chunk5_226, chunk5_230, chunk5_231, chunk5_232, chunk5_233, chunk5_235, chunk5_240, chunk5_256, chunk5_257, chunk5_258, chunk5_259, chunk5_260, chunk5_467, chunk5_469, chunk5_470, chunk5_471, chunk5_472, chunk5_474, chunk5_481, chunk5_482]
private theorem checked6_116 : ∀ w ∈ chunk6_116, ¬ Need 6 w.toFinset := by
  have h : chunk6_116.all (routes 5 pool6_116.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_116,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_223 _ hm
  · exact checked5_225 _ hm
  · exact checked5_226 _ hm
  · exact checked5_230 _ hm
  · exact checked5_231 _ hm
  · exact checked5_232 _ hm
  · exact checked5_233 _ hm
  · exact checked5_235 _ hm
  · exact checked5_240 _ hm
  · exact checked5_256 _ hm
  · exact checked5_257 _ hm
  · exact checked5_258 _ hm
  · exact checked5_259 _ hm
  · exact checked5_260 _ hm
  · exact checked5_467 _ hm
  · exact checked5_469 _ hm
  · exact checked5_470 _ hm
  · exact checked5_471 _ hm
  · exact checked5_472 _ hm
  · exact checked5_474 _ hm
  · exact checked5_481 _ hm
  · exact checked5_482 _ hm
private def chunk6_117 : List (List T) := [[wire15,wire3840,wire4369,wire8946,wire34952,wire61440],
  [wire15,wire3840,wire4369,wire12066,wire17476,wire61440],
  [wire15,wire3840,wire4369,wire12066,wire34952,wire61440],
  [wire15,wire3840,wire4369,wire13107,wire17476,wire61440]]
private def pool6_117 : List (List (List T)) := [chunk5_225, chunk5_226, chunk5_235, chunk5_261, chunk5_262, chunk5_263, chunk5_476, chunk5_482]
private theorem checked6_117 : ∀ w ∈ chunk6_117, ¬ Need 6 w.toFinset := by
  have h : chunk6_117.all (routes 5 pool6_117.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_117,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_225 _ hm
  · exact checked5_226 _ hm
  · exact checked5_235 _ hm
  · exact checked5_261 _ hm
  · exact checked5_262 _ hm
  · exact checked5_263 _ hm
  · exact checked5_476 _ hm
  · exact checked5_482 _ hm
private def chunk6_118 : List (List T) := [[wire15,wire3840,wire4369,wire13107,wire34952,wire61440],
  [wire15,wire3840,wire4369,wire17476,wire26214,wire61440],
  [wire15,wire3840,wire4369,wire17476,wire30583,wire61440],
  [wire15,wire3840,wire4369,wire17476,wire34952,wire35064]]
private def pool6_118 : List (List (List T)) := [chunk5_226, chunk5_236, chunk5_237, chunk5_238, chunk5_264, chunk5_265, chunk5_267, chunk5_270, chunk5_280]
private theorem checked6_118 : ∀ w ∈ chunk6_118, ¬ Need 6 w.toFinset := by
  have h : chunk6_118.all (routes 5 pool6_118.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_118,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_226 _ hm
  · exact checked5_236 _ hm
  · exact checked5_237 _ hm
  · exact checked5_238 _ hm
  · exact checked5_264 _ hm
  · exact checked5_265 _ hm
  · exact checked5_267 _ hm
  · exact checked5_270 _ hm
  · exact checked5_280 _ hm
private def chunk6_119 : List (List T) := [[wire15,wire3840,wire4369,wire17476,wire34952,wire61440],
  [wire15,wire3840,wire4369,wire17476,wire34952,wire61455],
  [wire15,wire3840,wire4369,wire17476,wire34952,wire63624],
  [wire15,wire3840,wire4369,wire17476,wire34952,wire65280]]
private def pool6_119 : List (List (List T)) := [chunk5_226, chunk5_227, chunk5_230, chunk5_268, chunk5_271, chunk5_272, chunk5_280, chunk5_494]
private theorem checked6_119 : ∀ w ∈ chunk6_119, ¬ Need 6 w.toFinset := by
  have h : chunk6_119.all (routes 5 pool6_119.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_119,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_226 _ hm
  · exact checked5_227 _ hm
  · exact checked5_230 _ hm
  · exact checked5_268 _ hm
  · exact checked5_271 _ hm
  · exact checked5_272 _ hm
  · exact checked5_280 _ hm
  · exact checked5_494 _ hm
private def chunk6_120 : List (List T) := [[wire15,wire3840,wire4369,wire17476,wire34952,wire65295],
  [wire15,wire3840,wire4369,wire17476,wire34959,wire61440],
  [wire15,wire3840,wire4369,wire17476,wire36744,wire61440],
  [wire15,wire3840,wire4369,wire17476,wire39321,wire61440]]
private def pool6_120 : List (List (List T)) := [chunk5_227, chunk5_238, chunk5_268, chunk5_269, chunk5_271, chunk5_272, chunk5_273, chunk5_280]
private theorem checked6_120 : ∀ w ∈ chunk6_120, ¬ Need 6 w.toFinset := by
  have h : chunk6_120.all (routes 5 pool6_120.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_120,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_227 _ hm
  · exact checked5_238 _ hm
  · exact checked5_268 _ hm
  · exact checked5_269 _ hm
  · exact checked5_271 _ hm
  · exact checked5_272 _ hm
  · exact checked5_273 _ hm
  · exact checked5_280 _ hm
private def chunk6_121 : List (List T) := [[wire15,wire3840,wire4369,wire17476,wire52428,wire61440],
  [wire15,wire3840,wire4369,wire17476,wire56797,wire61440],
  [wire15,wire3840,wire4369,wire17476,wire61440,wire61986],
  [wire15,wire3840,wire4369,wire17476,wire61440,wire63624]]
private def pool6_121 : List (List (List T)) := [chunk5_226, chunk5_230, chunk5_231, chunk5_238, chunk5_274, chunk5_275, chunk5_276, chunk5_477]
private theorem checked6_121 : ∀ w ∈ chunk6_121, ¬ Need 6 w.toFinset := by
  have h : chunk6_121.all (routes 5 pool6_121.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_121,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_226 _ hm
  · exact checked5_230 _ hm
  · exact checked5_231 _ hm
  · exact checked5_238 _ hm
  · exact checked5_274 _ hm
  · exact checked5_275 _ hm
  · exact checked5_276 _ hm
  · exact checked5_477 _ hm
private def chunk6_122 : List (List T) := [[wire15,wire3840,wire4369,wire17476,wire63624],
  [wire15,wire3840,wire4369,wire17652,wire34952,wire61440],
  [wire15,wire3840,wire4369,wire20292,wire34952,wire61440],
  [wire15,wire3840,wire4369,wire21845,wire34952,wire61440]]
private def pool6_122 : List (List (List T)) := [chunk5_12, chunk5_223, chunk5_226, chunk5_227, chunk5_228, chunk5_229, chunk5_231, chunk5_236, chunk5_238, chunk5_241, chunk5_275, chunk5_277, chunk5_278, chunk5_279, chunk5_280, chunk5_281, chunk5_467, chunk5_469, chunk5_478, chunk5_482, chunk5_494]
private theorem checked6_122 : ∀ w ∈ chunk6_122, ¬ Need 6 w.toFinset := by
  have h : chunk6_122.all (routes 5 pool6_122.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_122,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_12 _ hm
  · exact checked5_223 _ hm
  · exact checked5_226 _ hm
  · exact checked5_227 _ hm
  · exact checked5_228 _ hm
  · exact checked5_229 _ hm
  · exact checked5_231 _ hm
  · exact checked5_236 _ hm
  · exact checked5_238 _ hm
  · exact checked5_241 _ hm
  · exact checked5_275 _ hm
  · exact checked5_277 _ hm
  · exact checked5_278 _ hm
  · exact checked5_279 _ hm
  · exact checked5_280 _ hm
  · exact checked5_281 _ hm
  · exact checked5_467 _ hm
  · exact checked5_469 _ hm
  · exact checked5_478 _ hm
  · exact checked5_482 _ hm
  · exact checked5_494 _ hm
private def chunk6_123 : List (List T) := [[wire15,wire3840,wire4369,wire34952,wire43690,wire61440],
  [wire15,wire3840,wire4369,wire34952,wire48059,wire61440],
  [wire15,wire3840,wire4369,wire34952,wire52428,wire61440],
  [wire15,wire3840,wire4369,wire34952,wire56797,wire61440]]
private def pool6_123 : List (List (List T)) := [chunk5_20, chunk5_229, chunk5_230, chunk5_239, chunk5_284, chunk5_285, chunk5_287, chunk5_288, chunk5_482, chunk5_483]
private theorem checked6_123 : ∀ w ∈ chunk6_123, ¬ Need 6 w.toFinset := by
  have h : chunk6_123.all (routes 5 pool6_123.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_123,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_20 _ hm
  · exact checked5_229 _ hm
  · exact checked5_230 _ hm
  · exact checked5_239 _ hm
  · exact checked5_284 _ hm
  · exact checked5_285 _ hm
  · exact checked5_287 _ hm
  · exact checked5_288 _ hm
  · exact checked5_482 _ hm
  · exact checked5_483 _ hm
private def chunk6_124 : List (List T) := [[wire15,wire3840,wire4369,wire34952,wire61440,wire61986],
  [wire15,wire3840,wire4369,wire34952,wire61440,wire62532],
  [wire15,wire3840,wire4383,wire8738,wire34952,wire61440],
  [wire15,wire3840,wire4593,wire8738,wire17476,wire34952,wire61440]]
private def pool6_124 : List (List (List T)) := [chunk5_8, chunk5_230, chunk5_231, chunk5_232, chunk5_233, chunk5_286, chunk5_289, chunk5_290, chunk5_291, chunk5_292, chunk5_479, chunk5_480, chunk5_483]
private theorem checked6_124 : ∀ w ∈ chunk6_124, ¬ Need 6 w.toFinset := by
  have h : chunk6_124.all (routes 5 pool6_124.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_124,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_230 _ hm
  · exact checked5_231 _ hm
  · exact checked5_232 _ hm
  · exact checked5_233 _ hm
  · exact checked5_286 _ hm
  · exact checked5_289 _ hm
  · exact checked5_290 _ hm
  · exact checked5_291 _ hm
  · exact checked5_292 _ hm
  · exact checked5_479 _ hm
  · exact checked5_480 _ hm
  · exact checked5_483 _ hm
private def chunk6_125 : List (List T) := [[wire15,wire3840,wire4593,wire8738,wire17476,wire61440],
  [wire15,wire3840,wire8738,wire13107,wire17476,wire61440],
  [wire15,wire3840,wire8738,wire13107,wire34952,wire61440],
  [wire15,wire3840,wire8738,wire17476,wire21845,wire61440]]
private def pool6_125 : List (List (List T)) := [chunk5_232, chunk5_233, chunk5_236, chunk5_238, chunk5_291, chunk5_292, chunk5_293, chunk5_294, chunk5_295, chunk5_296, chunk5_297, chunk5_487, chunk5_490]
private theorem checked6_125 : ∀ w ∈ chunk6_125, ¬ Need 6 w.toFinset := by
  have h : chunk6_125.all (routes 5 pool6_125.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_125,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_232 _ hm
  · exact checked5_233 _ hm
  · exact checked5_236 _ hm
  · exact checked5_238 _ hm
  · exact checked5_291 _ hm
  · exact checked5_292 _ hm
  · exact checked5_293 _ hm
  · exact checked5_294 _ hm
  · exact checked5_295 _ hm
  · exact checked5_296 _ hm
  · exact checked5_297 _ hm
  · exact checked5_487 _ hm
  · exact checked5_490 _ hm
private def chunk6_126 : List (List T) := [[wire15,wire3840,wire8738,wire17476,wire30583,wire61440],
  [wire15,wire3840,wire8738,wire17476,wire34952,wire35064],
  [wire15,wire3840,wire8738,wire17476,wire34952,wire61440],
  [wire15,wire3840,wire8738,wire17476,wire34952,wire61455]]
private def pool6_126 : List (List (List T)) := [chunk5_224, chunk5_234, chunk5_299, chunk5_301, chunk5_303, chunk5_488, chunk5_489, chunk5_494]
private theorem checked6_126 : ∀ w ∈ chunk6_126, ¬ Need 6 w.toFinset := by
  have h : chunk6_126.all (routes 5 pool6_126.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_126,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_224 _ hm
  · exact checked5_234 _ hm
  · exact checked5_299 _ hm
  · exact checked5_301 _ hm
  · exact checked5_303 _ hm
  · exact checked5_488 _ hm
  · exact checked5_489 _ hm
  · exact checked5_494 _ hm
private def chunk6_127 : List (List T) := [[wire15,wire3840,wire8738,wire17476,wire34952,wire63624],
  [wire15,wire3840,wire8738,wire17476,wire34952,wire65280],
  [wire15,wire3840,wire8738,wire17476,wire34952,wire65295],
  [wire15,wire3840,wire8738,wire17476,wire35064]]
private def pool6_127 : List (List (List T)) := [chunk5_0, chunk5_223, chunk5_224, chunk5_233, chunk5_234, chunk5_235, chunk5_237, chunk5_241, chunk5_294, chunk5_297, chunk5_301, chunk5_303, chunk5_306, chunk5_309, chunk5_467, chunk5_487, chunk5_488, chunk5_489, chunk5_495]
private theorem checked6_127 : ∀ w ∈ chunk6_127, ¬ Need 6 w.toFinset := by
  have h : chunk6_127.all (routes 5 pool6_127.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_127,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_223 _ hm
  · exact checked5_224 _ hm
  · exact checked5_233 _ hm
  · exact checked5_234 _ hm
  · exact checked5_235 _ hm
  · exact checked5_237 _ hm
  · exact checked5_241 _ hm
  · exact checked5_294 _ hm
  · exact checked5_297 _ hm
  · exact checked5_301 _ hm
  · exact checked5_303 _ hm
  · exact checked5_306 _ hm
  · exact checked5_309 _ hm
  · exact checked5_467 _ hm
  · exact checked5_487 _ hm
  · exact checked5_488 _ hm
  · exact checked5_489 _ hm
  · exact checked5_495 _ hm
private def chunk6_128 : List (List T) := [[wire15,wire3840,wire8738,wire17476,wire35064,wire61440],
  [wire15,wire3840,wire8738,wire17476,wire43690,wire61440],
  [wire15,wire3840,wire8738,wire17476,wire52428,wire61440],
  [wire15,wire3840,wire8738,wire17476,wire61166,wire61440]]
private def pool6_128 : List (List (List T)) := [chunk5_0, chunk5_239, chunk5_308, chunk5_309, chunk5_310, chunk5_489, chunk5_490]
private theorem checked6_128 : ∀ w ∈ chunk6_128, ¬ Need 6 w.toFinset := by
  have h : chunk6_128.all (routes 5 pool6_128.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_128,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_239 _ hm
  · exact checked5_308 _ hm
  · exact checked5_309 _ hm
  · exact checked5_310 _ hm
  · exact checked5_489 _ hm
  · exact checked5_490 _ hm
private def chunk6_129 : List (List T) := [[wire15,wire3840,wire8738,wire17487,wire34952,wire61440],
  [wire15,wire3840,wire8738,wire26214,wire34952,wire61440],
  [wire15,wire3840,wire8738,wire34952,wire39321,wire61440],
  [wire15,wire3840,wire8738,wire34952,wire48059,wire61440]]
private def pool6_129 : List (List (List T)) := [chunk5_239, chunk5_311, chunk5_312, chunk5_314, chunk5_489, chunk5_495]
private theorem checked6_129 : ∀ w ∈ chunk6_129, ¬ Need 6 w.toFinset := by
  have h : chunk6_129.all (routes 5 pool6_129.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_129,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_239 _ hm
  · exact checked5_311 _ hm
  · exact checked5_312 _ hm
  · exact checked5_314 _ hm
  · exact checked5_489 _ hm
  · exact checked5_495 _ hm
private def chunk6_130 : List (List T) := [[wire15,wire3840,wire8738,wire34952,wire52428,wire61440],
  [wire15,wire3840,wire8738,wire34952,wire61166,wire61440],
  [wire15,wire3840,wire17476,wire21845,wire34952,wire61440],
  [wire15,wire3840,wire17476,wire26214,wire34952,wire61440]]
private def pool6_130 : List (List (List T)) := [chunk5_235, chunk5_236, chunk5_238, chunk5_239, chunk5_240, chunk5_315, chunk5_317, chunk5_318, chunk5_319]
private theorem checked6_130 : ∀ w ∈ chunk6_130, ¬ Need 6 w.toFinset := by
  have h : chunk6_130.all (routes 5 pool6_130.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_130,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_235 _ hm
  · exact checked5_236 _ hm
  · exact checked5_238 _ hm
  · exact checked5_239 _ hm
  · exact checked5_240 _ hm
  · exact checked5_315 _ hm
  · exact checked5_317 _ hm
  · exact checked5_318 _ hm
  · exact checked5_319 _ hm
private def chunk6_131 : List (List T) := [[wire15,wire3840,wire17476,wire34952,wire39321,wire61440],
  [wire15,wire3840,wire17476,wire34952,wire43690,wire61440],
  [wire15,wire3840,wire17476,wire34952,wire56797,wire61440],
  [wire15,wire3840,wire17476,wire34952,wire61166,wire61440]]
private def pool6_131 : List (List (List T)) := [chunk5_237, chunk5_238, chunk5_239, chunk5_240, chunk5_321, chunk5_322, chunk5_324]
private theorem checked6_131 : ∀ w ∈ chunk6_131, ¬ Need 6 w.toFinset := by
  have h : chunk6_131.all (routes 5 pool6_131.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_131,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_237 _ hm
  · exact checked5_238 _ hm
  · exact checked5_239 _ hm
  · exact checked5_240 _ hm
  · exact checked5_321 _ hm
  · exact checked5_322 _ hm
  · exact checked5_324 _ hm
private def chunk6_132 : List (List T) := [[wire15,wire3855,wire4369,wire8738,wire17476,wire61440],
  [wire15,wire3855,wire4369,wire8738,wire34952,wire61440],
  [wire15,wire3855,wire4369,wire17476,wire34952,wire61440],
  [wire15,wire3855,wire8738,wire17476,wire34952,wire61440]]
private def pool6_132 : List (List (List T)) := [chunk5_240, chunk5_241, chunk5_246, chunk5_251, chunk5_268, chunk5_273, chunk5_301, chunk5_492, chunk5_493, chunk5_494, chunk5_495]
private theorem checked6_132 : ∀ w ∈ chunk6_132, ¬ Need 6 w.toFinset := by
  have h : chunk6_132.all (routes 5 pool6_132.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_132,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_240 _ hm
  · exact checked5_241 _ hm
  · exact checked5_246 _ hm
  · exact checked5_251 _ hm
  · exact checked5_268 _ hm
  · exact checked5_273 _ hm
  · exact checked5_301 _ hm
  · exact checked5_492 _ hm
  · exact checked5_493 _ hm
  · exact checked5_494 _ hm
  · exact checked5_495 _ hm
private def chunk6_133 : List (List T) := [[wire15,wire4369,wire8738,wire17476,wire34952,wire35064],
  [wire15,wire4369,wire8738,wire17476,wire34952,wire65280],
  [wire15,wire4369,wire8738,wire17476,wire34952,wire65295],
  [wire15,wire4369,wire8738,wire17476,wire35064]]
private def pool6_133 : List (List (List T)) := [chunk5_0, chunk5_21, chunk5_25, chunk5_28, chunk5_244, chunk5_245, chunk5_246, chunk5_247, chunk5_248, chunk5_253, chunk5_259, chunk5_263, chunk5_265, chunk5_271, chunk5_289, chunk5_294, chunk5_297, chunk5_303, chunk5_305, chunk5_502, chunk5_504, chunk5_505, chunk5_508, chunk5_513]
private theorem checked6_133 : ∀ w ∈ chunk6_133, ¬ Need 6 w.toFinset := by
  have h : chunk6_133.all (routes 5 pool6_133.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_133,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_21 _ hm
  · exact checked5_25 _ hm
  · exact checked5_28 _ hm
  · exact checked5_244 _ hm
  · exact checked5_245 _ hm
  · exact checked5_246 _ hm
  · exact checked5_247 _ hm
  · exact checked5_248 _ hm
  · exact checked5_253 _ hm
  · exact checked5_259 _ hm
  · exact checked5_263 _ hm
  · exact checked5_265 _ hm
  · exact checked5_271 _ hm
  · exact checked5_289 _ hm
  · exact checked5_294 _ hm
  · exact checked5_297 _ hm
  · exact checked5_303 _ hm
  · exact checked5_305 _ hm
  · exact checked5_502 _ hm
  · exact checked5_504 _ hm
  · exact checked5_505 _ hm
  · exact checked5_508 _ hm
  · exact checked5_513 _ hm
private def chunk6_134 : List (List T) := [[wire15,wire4369,wire8738,wire17476,wire35064,wire61440],
  [wire15,wire4369,wire8738,wire17476,wire36744,wire61440],
  [wire15,wire4369,wire8738,wire17476,wire61440,wire61680],
  [wire15,wire4369,wire8738,wire17476,wire61440,wire61695]]
private def pool6_134 : List (List (List T)) := [chunk5_243, chunk5_246, chunk5_306, chunk5_503, chunk5_505, chunk5_508, chunk5_513]
private theorem checked6_134 : ∀ w ∈ chunk6_134, ¬ Need 6 w.toFinset := by
  have h : chunk6_134.all (routes 5 pool6_134.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_134,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_243 _ hm
  · exact checked5_246 _ hm
  · exact checked5_306 _ hm
  · exact checked5_503 _ hm
  · exact checked5_505 _ hm
  · exact checked5_508 _ hm
  · exact checked5_513 _ hm
private def chunk6_135 : List (List T) := [[wire15,wire4369,wire8738,wire17476,wire61440,wire65280],
  [wire15,wire4369,wire8738,wire17476,wire61440,wire65295],
  [wire15,wire4369,wire8738,wire17476,wire65280],
  [wire15,wire4369,wire8738,wire17476,wire65295]]
private def pool6_135 : List (List (List T)) := [chunk5_51, chunk5_207, chunk5_243, chunk5_245, chunk5_246, chunk5_247, chunk5_248, chunk5_256, chunk5_257, chunk5_259, chunk5_260, chunk5_263, chunk5_264, chunk5_265, chunk5_266, chunk5_274, chunk5_276, chunk5_277, chunk5_278, chunk5_294, chunk5_295, chunk5_297, chunk5_310, chunk5_498, chunk5_500, chunk5_502, chunk5_503, chunk5_504, chunk5_508, chunk5_509]
private theorem checked6_135 : ∀ w ∈ chunk6_135, ¬ Need 6 w.toFinset := by
  have h : chunk6_135.all (routes 5 pool6_135.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_135,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_51 _ hm
  · exact checked5_207 _ hm
  · exact checked5_243 _ hm
  · exact checked5_245 _ hm
  · exact checked5_246 _ hm
  · exact checked5_247 _ hm
  · exact checked5_248 _ hm
  · exact checked5_256 _ hm
  · exact checked5_257 _ hm
  · exact checked5_259 _ hm
  · exact checked5_260 _ hm
  · exact checked5_263 _ hm
  · exact checked5_264 _ hm
  · exact checked5_265 _ hm
  · exact checked5_266 _ hm
  · exact checked5_274 _ hm
  · exact checked5_276 _ hm
  · exact checked5_277 _ hm
  · exact checked5_278 _ hm
  · exact checked5_294 _ hm
  · exact checked5_295 _ hm
  · exact checked5_297 _ hm
  · exact checked5_310 _ hm
  · exact checked5_498 _ hm
  · exact checked5_500 _ hm
  · exact checked5_502 _ hm
  · exact checked5_503 _ hm
  · exact checked5_504 _ hm
  · exact checked5_508 _ hm
  · exact checked5_509 _ hm
private def chunk6_136 : List (List T) := [[wire15,wire4369,wire8738,wire34952,wire35064],
  [wire15,wire4369,wire8738,wire34952,wire35064,wire61440],
  [wire15,wire4369,wire8738,wire34952,wire36744,wire61440],
  [wire15,wire4369,wire8738,wire34952,wire61440,wire61680]]
private def pool6_136 : List (List (List T)) := [chunk5_5, chunk5_249, chunk5_250, chunk5_251, chunk5_252, chunk5_253, chunk5_254, chunk5_257, chunk5_264, chunk5_282, chunk5_283, chunk5_287, chunk5_289, chunk5_295, chunk5_313, chunk5_314, chunk5_316, chunk5_506, chunk5_514]
private theorem checked6_136 : ∀ w ∈ chunk6_136, ¬ Need 6 w.toFinset := by
  have h : chunk6_136.all (routes 5 pool6_136.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_136,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_249 _ hm
  · exact checked5_250 _ hm
  · exact checked5_251 _ hm
  · exact checked5_252 _ hm
  · exact checked5_253 _ hm
  · exact checked5_254 _ hm
  · exact checked5_257 _ hm
  · exact checked5_264 _ hm
  · exact checked5_282 _ hm
  · exact checked5_283 _ hm
  · exact checked5_287 _ hm
  · exact checked5_289 _ hm
  · exact checked5_295 _ hm
  · exact checked5_313 _ hm
  · exact checked5_314 _ hm
  · exact checked5_316 _ hm
  · exact checked5_506 _ hm
  · exact checked5_514 _ hm
private def chunk6_137 : List (List T) := [[wire15,wire4369,wire8738,wire34952,wire61440,wire61695],
  [wire15,wire4369,wire8738,wire34952,wire61440,wire65280],
  [wire15,wire4369,wire8738,wire34952,wire61440,wire65295],
  [wire15,wire4369,wire8738,wire34952,wire65280]]
private def pool6_137 : List (List (List T)) := [chunk5_5, chunk5_209, chunk5_249, chunk5_251, chunk5_255, chunk5_256, chunk5_257, chunk5_258, chunk5_259, chunk5_264, chunk5_284, chunk5_285, chunk5_286, chunk5_287, chunk5_290, chunk5_295, chunk5_314, chunk5_315, chunk5_498, chunk5_501, chunk5_506, chunk5_507, chunk5_514]
private theorem checked6_137 : ∀ w ∈ chunk6_137, ¬ Need 6 w.toFinset := by
  have h : chunk6_137.all (routes 5 pool6_137.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_137,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_209 _ hm
  · exact checked5_249 _ hm
  · exact checked5_251 _ hm
  · exact checked5_255 _ hm
  · exact checked5_256 _ hm
  · exact checked5_257 _ hm
  · exact checked5_258 _ hm
  · exact checked5_259 _ hm
  · exact checked5_264 _ hm
  · exact checked5_284 _ hm
  · exact checked5_285 _ hm
  · exact checked5_286 _ hm
  · exact checked5_287 _ hm
  · exact checked5_290 _ hm
  · exact checked5_295 _ hm
  · exact checked5_314 _ hm
  · exact checked5_315 _ hm
  · exact checked5_498 _ hm
  · exact checked5_501 _ hm
  · exact checked5_506 _ hm
  · exact checked5_507 _ hm
  · exact checked5_514 _ hm
private def chunk6_138 : List (List T) := [[wire15,wire4369,wire8738,wire34952,wire65295],
  [wire15,wire4369,wire8738,wire36744,wire61440],
  [wire15,wire4369,wire17476,wire34952,wire35064],
  [wire15,wire4369,wire17476,wire34952,wire35064,wire61440]]
private def pool6_138 : List (List (List T)) := [chunk5_5, chunk5_6, chunk5_12, chunk5_57, chunk5_242, chunk5_244, chunk5_249, chunk5_250, chunk5_251, chunk5_253, chunk5_254, chunk5_255, chunk5_256, chunk5_259, chunk5_264, chunk5_265, chunk5_266, chunk5_267, chunk5_268, chunk5_269, chunk5_270, chunk5_271, chunk5_281, chunk5_282, chunk5_283, chunk5_284, chunk5_285, chunk5_287, chunk5_288, chunk5_289, chunk5_290, chunk5_295, chunk5_296, chunk5_314, chunk5_316, chunk5_317, chunk5_320, chunk5_323, chunk5_498, chunk5_501, chunk5_507, chunk5_508, chunk5_510, chunk5_515]
private theorem checked6_138 : ∀ w ∈ chunk6_138, ¬ Need 6 w.toFinset := by
  have h : chunk6_138.all (routes 5 pool6_138.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_138,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_5 _ hm
  · exact checked5_6 _ hm
  · exact checked5_12 _ hm
  · exact checked5_57 _ hm
  · exact checked5_242 _ hm
  · exact checked5_244 _ hm
  · exact checked5_249 _ hm
  · exact checked5_250 _ hm
  · exact checked5_251 _ hm
  · exact checked5_253 _ hm
  · exact checked5_254 _ hm
  · exact checked5_255 _ hm
  · exact checked5_256 _ hm
  · exact checked5_259 _ hm
  · exact checked5_264 _ hm
  · exact checked5_265 _ hm
  · exact checked5_266 _ hm
  · exact checked5_267 _ hm
  · exact checked5_268 _ hm
  · exact checked5_269 _ hm
  · exact checked5_270 _ hm
  · exact checked5_271 _ hm
  · exact checked5_281 _ hm
  · exact checked5_282 _ hm
  · exact checked5_283 _ hm
  · exact checked5_284 _ hm
  · exact checked5_285 _ hm
  · exact checked5_287 _ hm
  · exact checked5_288 _ hm
  · exact checked5_289 _ hm
  · exact checked5_290 _ hm
  · exact checked5_295 _ hm
  · exact checked5_296 _ hm
  · exact checked5_314 _ hm
  · exact checked5_316 _ hm
  · exact checked5_317 _ hm
  · exact checked5_320 _ hm
  · exact checked5_323 _ hm
  · exact checked5_498 _ hm
  · exact checked5_501 _ hm
  · exact checked5_507 _ hm
  · exact checked5_508 _ hm
  · exact checked5_510 _ hm
  · exact checked5_515 _ hm
private def chunk6_139 : List (List T) := [[wire15,wire4369,wire17476,wire34952,wire36744,wire61440],
  [wire15,wire4369,wire17476,wire34952,wire61440,wire61680],
  [wire15,wire4369,wire17476,wire34952,wire61440,wire61695],
  [wire15,wire4369,wire17476,wire34952,wire61440,wire65280]]
private def pool6_139 : List (List (List T)) := [chunk5_268, chunk5_271, chunk5_272, chunk5_275, chunk5_276, chunk5_286, chunk5_288, chunk5_511]
private theorem checked6_139 : ∀ w ∈ chunk6_139, ¬ Need 6 w.toFinset := by
  have h : chunk6_139.all (routes 5 pool6_139.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_139,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_268 _ hm
  · exact checked5_271 _ hm
  · exact checked5_272 _ hm
  · exact checked5_275 _ hm
  · exact checked5_276 _ hm
  · exact checked5_286 _ hm
  · exact checked5_288 _ hm
  · exact checked5_511 _ hm
private def chunk6_140 : List (List T) := [[wire15,wire4369,wire17476,wire34952,wire61440,wire65295],
  [wire15,wire4369,wire17476,wire34952,wire65280],
  [wire15,wire4369,wire17476,wire34952,wire65295],
  [wire15,wire4369,wire17476,wire36744,wire61440]]
private def pool6_140 : List (List (List T)) := [chunk5_13, chunk5_85, chunk5_212, chunk5_242, chunk5_265, chunk5_266, chunk5_267, chunk5_268, chunk5_269, chunk5_270, chunk5_271, chunk5_272, chunk5_273, chunk5_274, chunk5_275, chunk5_277, chunk5_278, chunk5_281, chunk5_284, chunk5_285, chunk5_286, chunk5_287, chunk5_288, chunk5_289, chunk5_318, chunk5_321, chunk5_322, chunk5_324, chunk5_499, chunk5_510, chunk5_511, chunk5_512]
private theorem checked6_140 : ∀ w ∈ chunk6_140, ¬ Need 6 w.toFinset := by
  have h : chunk6_140.all (routes 5 pool6_140.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_140,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_13 _ hm
  · exact checked5_85 _ hm
  · exact checked5_212 _ hm
  · exact checked5_242 _ hm
  · exact checked5_265 _ hm
  · exact checked5_266 _ hm
  · exact checked5_267 _ hm
  · exact checked5_268 _ hm
  · exact checked5_269 _ hm
  · exact checked5_270 _ hm
  · exact checked5_271 _ hm
  · exact checked5_272 _ hm
  · exact checked5_273 _ hm
  · exact checked5_274 _ hm
  · exact checked5_275 _ hm
  · exact checked5_277 _ hm
  · exact checked5_278 _ hm
  · exact checked5_281 _ hm
  · exact checked5_284 _ hm
  · exact checked5_285 _ hm
  · exact checked5_286 _ hm
  · exact checked5_287 _ hm
  · exact checked5_288 _ hm
  · exact checked5_289 _ hm
  · exact checked5_318 _ hm
  · exact checked5_321 _ hm
  · exact checked5_322 _ hm
  · exact checked5_324 _ hm
  · exact checked5_499 _ hm
  · exact checked5_510 _ hm
  · exact checked5_511 _ hm
  · exact checked5_512 _ hm
private def chunk6_141 : List (List T) := [[wire15,wire8738,wire17476,wire34952,wire35064],
  [wire15,wire8738,wire17476,wire34952,wire35064,wire61440],
  [wire15,wire8738,wire17476,wire34952,wire36744,wire61440],
  [wire15,wire8738,wire17476,wire34952,wire61440,wire61680]]
private def pool6_141 : List (List (List T)) := [chunk5_0, chunk5_15, chunk5_298, chunk5_299, chunk5_300, chunk5_301, chunk5_302, chunk5_304, chunk5_305, chunk5_307, chunk5_309, chunk5_310, chunk5_312, chunk5_313, chunk5_317, chunk5_318, chunk5_320, chunk5_324, chunk5_517, chunk5_518, chunk5_521]
private theorem checked6_141 : ∀ w ∈ chunk6_141, ¬ Need 6 w.toFinset := by
  have h : chunk6_141.all (routes 5 pool6_141.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_141,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_15 _ hm
  · exact checked5_298 _ hm
  · exact checked5_299 _ hm
  · exact checked5_300 _ hm
  · exact checked5_301 _ hm
  · exact checked5_302 _ hm
  · exact checked5_304 _ hm
  · exact checked5_305 _ hm
  · exact checked5_307 _ hm
  · exact checked5_309 _ hm
  · exact checked5_310 _ hm
  · exact checked5_312 _ hm
  · exact checked5_313 _ hm
  · exact checked5_317 _ hm
  · exact checked5_318 _ hm
  · exact checked5_320 _ hm
  · exact checked5_324 _ hm
  · exact checked5_517 _ hm
  · exact checked5_518 _ hm
  · exact checked5_521 _ hm
private def chunk6_142 : List (List T) := [[wire15,wire8738,wire17476,wire34952,wire61440,wire61695],
  [wire15,wire8738,wire17476,wire34952,wire61440,wire65280],
  [wire15,wire8738,wire17476,wire34952,wire61440,wire65295],
  [wire15,wire8738,wire17476,wire34952,wire65280]]
private def pool6_142 : List (List (List T)) := [chunk5_218, chunk5_299, chunk5_301, chunk5_309, chunk5_311, chunk5_312, chunk5_314, chunk5_315, chunk5_319, chunk5_321, chunk5_322, chunk5_517, chunk5_519, chunk5_521]
private theorem checked6_142 : ∀ w ∈ chunk6_142, ¬ Need 6 w.toFinset := by
  have h : chunk6_142.all (routes 5 pool6_142.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_142,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_218 _ hm
  · exact checked5_299 _ hm
  · exact checked5_301 _ hm
  · exact checked5_309 _ hm
  · exact checked5_311 _ hm
  · exact checked5_312 _ hm
  · exact checked5_314 _ hm
  · exact checked5_315 _ hm
  · exact checked5_319 _ hm
  · exact checked5_321 _ hm
  · exact checked5_322 _ hm
  · exact checked5_517 _ hm
  · exact checked5_519 _ hm
  · exact checked5_521 _ hm
private def chunk6_143 : List (List T) := [[wire15,wire8738,wire17476,wire34952,wire65295],
  [wire15,wire8738,wire17476,wire35064],
  [wire15,wire8738,wire17476,wire35064,wire61440],
  [wire32,wire240,wire3840,wire4369,wire17476,wire61440]]
private def pool6_143 : List (List (List T)) := [chunk5_0, chunk5_6, chunk5_13, chunk5_15, chunk5_25, chunk5_28, chunk5_149, chunk5_243, chunk5_293, chunk5_296, chunk5_298, chunk5_299, chunk5_300, chunk5_301, chunk5_302, chunk5_304, chunk5_305, chunk5_306, chunk5_307, chunk5_308, chunk5_309, chunk5_310, chunk5_311, chunk5_312, chunk5_313, chunk5_315, chunk5_316, chunk5_317, chunk5_319, chunk5_321, chunk5_322, chunk5_323, chunk5_326, chunk5_327, chunk5_355, chunk5_356, chunk5_370, chunk5_517, chunk5_518, chunk5_520, chunk5_522]
private theorem checked6_143 : ∀ w ∈ chunk6_143, ¬ Need 6 w.toFinset := by
  have h : chunk6_143.all (routes 5 pool6_143.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_143,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_6 _ hm
  · exact checked5_13 _ hm
  · exact checked5_15 _ hm
  · exact checked5_25 _ hm
  · exact checked5_28 _ hm
  · exact checked5_149 _ hm
  · exact checked5_243 _ hm
  · exact checked5_293 _ hm
  · exact checked5_296 _ hm
  · exact checked5_298 _ hm
  · exact checked5_299 _ hm
  · exact checked5_300 _ hm
  · exact checked5_301 _ hm
  · exact checked5_302 _ hm
  · exact checked5_304 _ hm
  · exact checked5_305 _ hm
  · exact checked5_306 _ hm
  · exact checked5_307 _ hm
  · exact checked5_308 _ hm
  · exact checked5_309 _ hm
  · exact checked5_310 _ hm
  · exact checked5_311 _ hm
  · exact checked5_312 _ hm
  · exact checked5_313 _ hm
  · exact checked5_315 _ hm
  · exact checked5_316 _ hm
  · exact checked5_317 _ hm
  · exact checked5_319 _ hm
  · exact checked5_321 _ hm
  · exact checked5_322 _ hm
  · exact checked5_323 _ hm
  · exact checked5_326 _ hm
  · exact checked5_327 _ hm
  · exact checked5_355 _ hm
  · exact checked5_356 _ hm
  · exact checked5_370 _ hm
  · exact checked5_517 _ hm
  · exact checked5_518 _ hm
  · exact checked5_520 _ hm
  · exact checked5_522 _ hm
private def chunk6_144 : List (List T) := [[wire128,wire240,wire3840,wire4369,wire17476,wire61440],
  [wire240,wire255,wire3840,wire4369,wire8738,wire17476],
  [wire240,wire255,wire3840,wire4369,wire8738,wire34952],
  [wire240,wire255,wire3840,wire4369,wire17476,wire34952]]
private def pool6_144 : List (List (List T)) := [chunk5_332, chunk5_333, chunk5_337, chunk5_338, chunk5_340, chunk5_342, chunk5_344, chunk5_356, chunk5_362, chunk5_370, chunk5_454, chunk5_456]
private theorem checked6_144 : ∀ w ∈ chunk6_144, ¬ Need 6 w.toFinset := by
  have h : chunk6_144.all (routes 5 pool6_144.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_144,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_332 _ hm
  · exact checked5_333 _ hm
  · exact checked5_337 _ hm
  · exact checked5_338 _ hm
  · exact checked5_340 _ hm
  · exact checked5_342 _ hm
  · exact checked5_344 _ hm
  · exact checked5_356 _ hm
  · exact checked5_362 _ hm
  · exact checked5_370 _ hm
  · exact checked5_454 _ hm
  · exact checked5_456 _ hm
private def chunk6_145 : List (List T) := [[wire240,wire255,wire3840,wire8738,wire17476,wire34952],
  [wire240,wire255,wire4369,wire8738,wire17476],
  [wire240,wire255,wire4369,wire8738,wire17476,wire34952],
  [wire240,wire255,wire4369,wire8738,wire17476,wire61440]]
private def pool6_145 : List (List (List T)) := [chunk5_326, chunk5_328, chunk5_330, chunk5_337, chunk5_339, chunk5_341, chunk5_343, chunk5_346, chunk5_347, chunk5_348, chunk5_374, chunk5_375, chunk5_379, chunk5_456, chunk5_457, chunk5_459, chunk5_460, chunk5_462, chunk5_464, chunk5_465]
private theorem checked6_145 : ∀ w ∈ chunk6_145, ¬ Need 6 w.toFinset := by
  have h : chunk6_145.all (routes 5 pool6_145.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_145,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_326 _ hm
  · exact checked5_328 _ hm
  · exact checked5_330 _ hm
  · exact checked5_337 _ hm
  · exact checked5_339 _ hm
  · exact checked5_341 _ hm
  · exact checked5_343 _ hm
  · exact checked5_346 _ hm
  · exact checked5_347 _ hm
  · exact checked5_348 _ hm
  · exact checked5_374 _ hm
  · exact checked5_375 _ hm
  · exact checked5_379 _ hm
  · exact checked5_456 _ hm
  · exact checked5_457 _ hm
  · exact checked5_459 _ hm
  · exact checked5_460 _ hm
  · exact checked5_462 _ hm
  · exact checked5_464 _ hm
  · exact checked5_465 _ hm
private def chunk6_146 : List (List T) := [[wire240,wire255,wire4369,wire8738,wire34952],
  [wire240,wire255,wire4369,wire8738,wire34952,wire61440],
  [wire240,wire255,wire4369,wire17476,wire34952],
  [wire240,wire255,wire4369,wire17476,wire34952,wire61440]]
private def pool6_146 : List (List (List T)) := [chunk5_328, chunk5_331, chunk5_332, chunk5_334, chunk5_338, chunk5_339, chunk5_340, chunk5_341, chunk5_342, chunk5_343, chunk5_344, chunk5_345, chunk5_346, chunk5_347, chunk5_349, chunk5_350, chunk5_351, chunk5_382, chunk5_397, chunk5_399, chunk5_458, chunk5_459, chunk5_460, chunk5_461, chunk5_462, chunk5_463]
private theorem checked6_146 : ∀ w ∈ chunk6_146, ¬ Need 6 w.toFinset := by
  have h : chunk6_146.all (routes 5 pool6_146.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_146,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_328 _ hm
  · exact checked5_331 _ hm
  · exact checked5_332 _ hm
  · exact checked5_334 _ hm
  · exact checked5_338 _ hm
  · exact checked5_339 _ hm
  · exact checked5_340 _ hm
  · exact checked5_341 _ hm
  · exact checked5_342 _ hm
  · exact checked5_343 _ hm
  · exact checked5_344 _ hm
  · exact checked5_345 _ hm
  · exact checked5_346 _ hm
  · exact checked5_347 _ hm
  · exact checked5_349 _ hm
  · exact checked5_350 _ hm
  · exact checked5_351 _ hm
  · exact checked5_382 _ hm
  · exact checked5_397 _ hm
  · exact checked5_399 _ hm
  · exact checked5_458 _ hm
  · exact checked5_459 _ hm
  · exact checked5_460 _ hm
  · exact checked5_461 _ hm
  · exact checked5_462 _ hm
  · exact checked5_463 _ hm
private def chunk6_147 : List (List T) := [[wire240,wire255,wire8738,wire17476,wire34952],
  [wire240,wire255,wire8738,wire17476,wire34952,wire61440],
  [wire240,wire3840,wire3855,wire4369,wire8738,wire17476],
  [wire240,wire3840,wire3855,wire4369,wire8738,wire34952]]
private def pool6_147 : List (List (List T)) := [chunk5_347, chunk5_348, chunk5_349, chunk5_350, chunk5_351, chunk5_369, chunk5_428, chunk5_429, chunk5_465, chunk5_466, chunk5_491, chunk5_492]
private theorem checked6_147 : ∀ w ∈ chunk6_147, ¬ Need 6 w.toFinset := by
  have h : chunk6_147.all (routes 5 pool6_147.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_147,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_347 _ hm
  · exact checked5_348 _ hm
  · exact checked5_349 _ hm
  · exact checked5_350 _ hm
  · exact checked5_351 _ hm
  · exact checked5_369 _ hm
  · exact checked5_428 _ hm
  · exact checked5_429 _ hm
  · exact checked5_465 _ hm
  · exact checked5_466 _ hm
  · exact checked5_491 _ hm
  · exact checked5_492 _ hm
private def chunk6_148 : List (List T) := [[wire240,wire3840,wire3855,wire4369,wire17476,wire34952],
  [wire240,wire3840,wire3855,wire8738,wire17476,wire34952],
  [wire240,wire3840,wire4095,wire4369,wire8738,wire17476],
  [wire240,wire3840,wire4095,wire4369,wire8738,wire34952]]
private def pool6_148 : List (List (List T)) := [chunk5_370, chunk5_371, chunk5_467, chunk5_468, chunk5_469, chunk5_492]
private theorem checked6_148 : ∀ w ∈ chunk6_148, ¬ Need 6 w.toFinset := by
  have h : chunk6_148.all (routes 5 pool6_148.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_148,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_370 _ hm
  · exact checked5_371 _ hm
  · exact checked5_467 _ hm
  · exact checked5_468 _ hm
  · exact checked5_469 _ hm
  · exact checked5_492 _ hm
private def chunk6_149 : List (List T) := [[wire240,wire3840,wire4095,wire4369,wire17476,wire34952],
  [wire240,wire3840,wire4095,wire8738,wire17476,wire34952],
  [wire240,wire3840,wire4369,wire8738,wire17476,wire17487],
  [wire240,wire3840,wire4369,wire8738,wire17476,wire61440]]
private def pool6_149 : List (List (List T)) := [chunk5_354, chunk5_363, chunk5_372, chunk5_375, chunk5_376, chunk5_379, chunk5_391, chunk5_483]
private theorem checked6_149 : ∀ w ∈ chunk6_149, ¬ Need 6 w.toFinset := by
  have h : chunk6_149.all (routes 5 pool6_149.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_149,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_354 _ hm
  · exact checked5_363 _ hm
  · exact checked5_372 _ hm
  · exact checked5_375 _ hm
  · exact checked5_376 _ hm
  · exact checked5_379 _ hm
  · exact checked5_391 _ hm
  · exact checked5_483 _ hm
private def chunk6_150 : List (List T) := [[wire240,wire3840,wire4369,wire8738,wire17476,wire61680],
  [wire240,wire3840,wire4369,wire8738,wire17476,wire62532],
  [wire240,wire3840,wire4369,wire8738,wire17476,wire65280],
  [wire240,wire3840,wire4369,wire8738,wire17476,wire65520]]
private def pool6_150 : List (List (List T)) := [chunk5_354, chunk5_356, chunk5_375, chunk5_379, chunk5_380, chunk5_391, chunk5_483, chunk5_484, chunk5_495]
private theorem checked6_150 : ∀ w ∈ chunk6_150, ¬ Need 6 w.toFinset := by
  have h : chunk6_150.all (routes 5 pool6_150.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_150,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_354 _ hm
  · exact checked5_356 _ hm
  · exact checked5_375 _ hm
  · exact checked5_379 _ hm
  · exact checked5_380 _ hm
  · exact checked5_391 _ hm
  · exact checked5_483 _ hm
  · exact checked5_484 _ hm
  · exact checked5_495 _ hm
private def chunk6_151 : List (List T) := [[wire240,wire3840,wire4369,wire8738,wire17487,wire34952],
  [wire240,wire3840,wire4369,wire8738,wire17487,wire34952,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire20292,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire21845,wire61440]]
private def pool6_151 : List (List (List T)) := [chunk5_352, chunk5_354, chunk5_365, chunk5_377, chunk5_379, chunk5_380, chunk5_381, chunk5_391, chunk5_422, chunk5_471, chunk5_484]
private theorem checked6_151 : ∀ w ∈ chunk6_151, ¬ Need 6 w.toFinset := by
  have h : chunk6_151.all (routes 5 pool6_151.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_151,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_352 _ hm
  · exact checked5_354 _ hm
  · exact checked5_365 _ hm
  · exact checked5_377 _ hm
  · exact checked5_379 _ hm
  · exact checked5_380 _ hm
  · exact checked5_381 _ hm
  · exact checked5_391 _ hm
  · exact checked5_422 _ hm
  · exact checked5_471 _ hm
  · exact checked5_484 _ hm
private def chunk6_152 : List (List T) := [[wire240,wire3840,wire4369,wire8738,wire26214,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire30583,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire34952,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire34952,wire61680]]
private def pool6_152 : List (List (List T)) := [chunk5_365, chunk5_381, chunk5_382, chunk5_383, chunk5_474, chunk5_484, chunk5_496]
private theorem checked6_152 : ∀ w ∈ chunk6_152, ¬ Need 6 w.toFinset := by
  have h : chunk6_152.all (routes 5 pool6_152.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_152,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_365 _ hm
  · exact checked5_381 _ hm
  · exact checked5_382 _ hm
  · exact checked5_383 _ hm
  · exact checked5_474 _ hm
  · exact checked5_484 _ hm
  · exact checked5_496 _ hm
private def chunk6_153 : List (List T) := [[wire240,wire3840,wire4369,wire8738,wire34952,wire62532],
  [wire240,wire3840,wire4369,wire8738,wire34952,wire65280],
  [wire240,wire3840,wire4369,wire8738,wire34952,wire65520],
  [wire240,wire3840,wire4369,wire8738,wire36744,wire61440]]
private def pool6_153 : List (List (List T)) := [chunk5_382, chunk5_383, chunk5_384, chunk5_392, chunk5_475, chunk5_484, chunk5_496]
private theorem checked6_153 : ∀ w ∈ chunk6_153, ¬ Need 6 w.toFinset := by
  have h : chunk6_153.all (routes 5 pool6_153.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_153,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_382 _ hm
  · exact checked5_383 _ hm
  · exact checked5_384 _ hm
  · exact checked5_392 _ hm
  · exact checked5_475 _ hm
  · exact checked5_484 _ hm
  · exact checked5_496 _ hm
private def chunk6_154 : List (List T) := [[wire240,wire3840,wire4369,wire8738,wire39321,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire43690,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire48059,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire61440,wire62532]]
private def pool6_154 : List (List (List T)) := [chunk5_354, chunk5_359, chunk5_365, chunk5_384, chunk5_385, chunk5_386, chunk5_387, chunk5_475, chunk5_485]
private theorem checked6_154 : ∀ w ∈ chunk6_154, ¬ Need 6 w.toFinset := by
  have h : chunk6_154.all (routes 5 pool6_154.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_154,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_354 _ hm
  · exact checked5_359 _ hm
  · exact checked5_365 _ hm
  · exact checked5_384 _ hm
  · exact checked5_385 _ hm
  · exact checked5_386 _ hm
  · exact checked5_387 _ hm
  · exact checked5_475 _ hm
  · exact checked5_485 _ hm
private def chunk6_155 : List (List T) := [[wire240,wire3840,wire4369,wire8738,wire61440,wire63624],
  [wire240,wire3840,wire4369,wire8738,wire62532],
  [wire240,wire3840,wire4369,wire8751,wire17476,wire61440],
  [wire240,wire3840,wire4369,wire8946,wire34952,wire61440]]
private def pool6_155 : List (List (List T)) := [chunk5_326, chunk5_354, chunk5_355, chunk5_359, chunk5_360, chunk5_362, chunk5_364, chunk5_371, chunk5_386, chunk5_387, chunk5_388, chunk5_389, chunk5_390, chunk5_467, chunk5_470, chunk5_471, chunk5_472, chunk5_474, chunk5_475, chunk5_485]
private theorem checked6_155 : ∀ w ∈ chunk6_155, ¬ Need 6 w.toFinset := by
  have h : chunk6_155.all (routes 5 pool6_155.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_155,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_326 _ hm
  · exact checked5_354 _ hm
  · exact checked5_355 _ hm
  · exact checked5_359 _ hm
  · exact checked5_360 _ hm
  · exact checked5_362 _ hm
  · exact checked5_364 _ hm
  · exact checked5_371 _ hm
  · exact checked5_386 _ hm
  · exact checked5_387 _ hm
  · exact checked5_388 _ hm
  · exact checked5_389 _ hm
  · exact checked5_390 _ hm
  · exact checked5_467 _ hm
  · exact checked5_470 _ hm
  · exact checked5_471 _ hm
  · exact checked5_472 _ hm
  · exact checked5_474 _ hm
  · exact checked5_475 _ hm
  · exact checked5_485 _ hm
private def chunk6_156 : List (List T) := [[wire240,wire3840,wire4369,wire12066,wire17476,wire61440],
  [wire240,wire3840,wire4369,wire12066,wire34952,wire61440],
  [wire240,wire3840,wire4369,wire13107,wire17476,wire61440],
  [wire240,wire3840,wire4369,wire13107,wire34952,wire61440]]
private def pool6_156 : List (List (List T)) := [chunk5_355, chunk5_365, chunk5_391, chunk5_392, chunk5_393, chunk5_394, chunk5_476, chunk5_486]
private theorem checked6_156 : ∀ w ∈ chunk6_156, ¬ Need 6 w.toFinset := by
  have h : chunk6_156.all (routes 5 pool6_156.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_156,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_355 _ hm
  · exact checked5_365 _ hm
  · exact checked5_391 _ hm
  · exact checked5_392 _ hm
  · exact checked5_393 _ hm
  · exact checked5_394 _ hm
  · exact checked5_476 _ hm
  · exact checked5_486 _ hm
private def chunk6_157 : List (List T) := [[wire240,wire3840,wire4369,wire17476,wire17487,wire34952],
  [wire240,wire3840,wire4369,wire17476,wire26214,wire61440],
  [wire240,wire3840,wire4369,wire17476,wire30583,wire61440],
  [wire240,wire3840,wire4369,wire17476,wire34952,wire61440]]
private def pool6_157 : List (List (List T)) := [chunk5_356, chunk5_357, chunk5_366, chunk5_396, chunk5_398, chunk5_399, chunk5_404, chunk5_407, chunk5_408, chunk5_486]
private theorem checked6_157 : ∀ w ∈ chunk6_157, ¬ Need 6 w.toFinset := by
  have h : chunk6_157.all (routes 5 pool6_157.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_157,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_356 _ hm
  · exact checked5_357 _ hm
  · exact checked5_366 _ hm
  · exact checked5_396 _ hm
  · exact checked5_398 _ hm
  · exact checked5_399 _ hm
  · exact checked5_404 _ hm
  · exact checked5_407 _ hm
  · exact checked5_408 _ hm
  · exact checked5_486 _ hm
private def chunk6_158 : List (List T) := [[wire240,wire3840,wire4369,wire17476,wire34952,wire61680],
  [wire240,wire3840,wire4369,wire17476,wire34952,wire62532],
  [wire240,wire3840,wire4369,wire17476,wire34952,wire65280],
  [wire240,wire3840,wire4369,wire17476,wire34952,wire65520]]
private def pool6_158 : List (List (List T)) := [chunk5_357, chunk5_358, chunk5_359, chunk5_399, chunk5_400, chunk5_401, chunk5_408, chunk5_409, chunk5_496, chunk5_497]
private theorem checked6_158 : ∀ w ∈ chunk6_158, ¬ Need 6 w.toFinset := by
  have h : chunk6_158.all (routes 5 pool6_158.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_158,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_357 _ hm
  · exact checked5_358 _ hm
  · exact checked5_359 _ hm
  · exact checked5_399 _ hm
  · exact checked5_400 _ hm
  · exact checked5_401 _ hm
  · exact checked5_408 _ hm
  · exact checked5_409 _ hm
  · exact checked5_496 _ hm
  · exact checked5_497 _ hm
private def chunk6_159 : List (List T) := [[wire240,wire3840,wire4369,wire17476,wire34959,wire61440],
  [wire240,wire3840,wire4369,wire17476,wire36744,wire61440],
  [wire240,wire3840,wire4369,wire17476,wire39321,wire61440],
  [wire240,wire3840,wire4369,wire17476,wire52428,wire61440]]
private def pool6_159 : List (List (List T)) := [chunk5_336, chunk5_358, chunk5_359, chunk5_367, chunk5_400, chunk5_401, chunk5_402, chunk5_409, chunk5_410, chunk5_478, chunk5_486, chunk5_497]
private theorem checked6_159 : ∀ w ∈ chunk6_159, ¬ Need 6 w.toFinset := by
  have h : chunk6_159.all (routes 5 pool6_159.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_159,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_336 _ hm
  · exact checked5_358 _ hm
  · exact checked5_359 _ hm
  · exact checked5_367 _ hm
  · exact checked5_400 _ hm
  · exact checked5_401 _ hm
  · exact checked5_402 _ hm
  · exact checked5_409 _ hm
  · exact checked5_410 _ hm
  · exact checked5_478 _ hm
  · exact checked5_486 _ hm
  · exact checked5_497 _ hm
private def chunk6_160 : List (List T) := [[wire240,wire3840,wire4369,wire17476,wire56797,wire61440],
  [wire240,wire3840,wire4369,wire17476,wire61440,wire61986],
  [wire240,wire3840,wire4369,wire17476,wire61440,wire63624],
  [wire240,wire3840,wire4369,wire17652,wire34952,wire61440]]
private def pool6_160 : List (List (List T)) := [chunk5_336, chunk5_357, chunk5_359, chunk5_360, chunk5_402, chunk5_403, chunk5_406, chunk5_411, chunk5_477, chunk5_486, chunk5_487]
private theorem checked6_160 : ∀ w ∈ chunk6_160, ¬ Need 6 w.toFinset := by
  have h : chunk6_160.all (routes 5 pool6_160.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_160,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_336 _ hm
  · exact checked5_357 _ hm
  · exact checked5_359 _ hm
  · exact checked5_360 _ hm
  · exact checked5_402 _ hm
  · exact checked5_403 _ hm
  · exact checked5_406 _ hm
  · exact checked5_411 _ hm
  · exact checked5_477 _ hm
  · exact checked5_486 _ hm
  · exact checked5_487 _ hm
private def chunk6_161 : List (List T) := [[wire240,wire3840,wire4369,wire20292,wire34952,wire61440],
  [wire240,wire3840,wire4369,wire21845,wire34952,wire61440],
  [wire240,wire3840,wire4369,wire34952,wire43690,wire61440],
  [wire240,wire3840,wire4369,wire34952,wire48059,wire61440]]
private def pool6_161 : List (List (List T)) := [chunk5_357, chunk5_367, chunk5_368, chunk5_408, chunk5_409, chunk5_410, chunk5_412, chunk5_413]
private theorem checked6_161 : ∀ w ∈ chunk6_161, ¬ Need 6 w.toFinset := by
  have h : chunk6_161.all (routes 5 pool6_161.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_161,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_357 _ hm
  · exact checked5_367 _ hm
  · exact checked5_368 _ hm
  · exact checked5_408 _ hm
  · exact checked5_409 _ hm
  · exact checked5_410 _ hm
  · exact checked5_412 _ hm
  · exact checked5_413 _ hm
private def chunk6_162 : List (List T) := [[wire240,wire3840,wire4369,wire34952,wire52428,wire61440],
  [wire240,wire3840,wire4369,wire34952,wire56797,wire61440],
  [wire240,wire3840,wire4369,wire34952,wire61440,wire61986],
  [wire240,wire3840,wire4369,wire34952,wire61440,wire62532]]
private def pool6_162 : List (List (List T)) := [chunk5_357, chunk5_360, chunk5_369, chunk5_413, chunk5_414, chunk5_415, chunk5_416, chunk5_478]
private theorem checked6_162 : ∀ w ∈ chunk6_162, ¬ Need 6 w.toFinset := by
  have h : chunk6_162.all (routes 5 pool6_162.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_162,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_357 _ hm
  · exact checked5_360 _ hm
  · exact checked5_369 _ hm
  · exact checked5_413 _ hm
  · exact checked5_414 _ hm
  · exact checked5_415 _ hm
  · exact checked5_416 _ hm
  · exact checked5_478 _ hm
private def chunk6_163 : List (List T) := [[wire240,wire3840,wire4369,wire34952,wire62532],
  [wire240,wire3840,wire4383,wire8738,wire17476,wire34952,wire61440],
  [wire240,wire3840,wire4383,wire8738,wire34952,wire61440],
  [wire240,wire3840,wire4593,wire8738,wire17476,wire61440]]
private def pool6_163 : List (List (List T)) := [chunk5_327, chunk5_332, chunk5_354, chunk5_356, chunk5_357, chunk5_358, chunk5_359, chunk5_360, chunk5_361, chunk5_362, chunk5_368, chunk5_371, chunk5_415, chunk5_416, chunk5_417, chunk5_419, chunk5_420, chunk5_421, chunk5_422, chunk5_468, chunk5_470, chunk5_479, chunk5_483]
private theorem checked6_163 : ∀ w ∈ chunk6_163, ¬ Need 6 w.toFinset := by
  have h : chunk6_163.all (routes 5 pool6_163.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_163,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_327 _ hm
  · exact checked5_332 _ hm
  · exact checked5_354 _ hm
  · exact checked5_356 _ hm
  · exact checked5_357 _ hm
  · exact checked5_358 _ hm
  · exact checked5_359 _ hm
  · exact checked5_360 _ hm
  · exact checked5_361 _ hm
  · exact checked5_362 _ hm
  · exact checked5_368 _ hm
  · exact checked5_371 _ hm
  · exact checked5_415 _ hm
  · exact checked5_416 _ hm
  · exact checked5_417 _ hm
  · exact checked5_419 _ hm
  · exact checked5_420 _ hm
  · exact checked5_421 _ hm
  · exact checked5_422 _ hm
  · exact checked5_468 _ hm
  · exact checked5_470 _ hm
  · exact checked5_479 _ hm
  · exact checked5_483 _ hm
private def chunk6_164 : List (List T) := [[wire240,wire3840,wire8738,wire13107,wire17476,wire61440],
  [wire240,wire3840,wire8738,wire13107,wire34952,wire61440],
  [wire240,wire3840,wire8738,wire17476,wire17487,wire34952],
  [wire240,wire3840,wire8738,wire17476,wire21845,wire61440]]
private def pool6_164 : List (List (List T)) := [chunk5_352, chunk5_362, chunk5_363, chunk5_365, chunk5_366, chunk5_424, chunk5_425, chunk5_428, chunk5_433, chunk5_487]
private theorem checked6_164 : ∀ w ∈ chunk6_164, ¬ Need 6 w.toFinset := by
  have h : chunk6_164.all (routes 5 pool6_164.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_164,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_352 _ hm
  · exact checked5_362 _ hm
  · exact checked5_363 _ hm
  · exact checked5_365 _ hm
  · exact checked5_366 _ hm
  · exact checked5_424 _ hm
  · exact checked5_425 _ hm
  · exact checked5_428 _ hm
  · exact checked5_433 _ hm
  · exact checked5_487 _ hm
private def chunk6_165 : List (List T) := [[wire240,wire3840,wire8738,wire17476,wire30583,wire61440],
  [wire240,wire3840,wire8738,wire17476,wire34952,wire61440],
  [wire240,wire3840,wire8738,wire17476,wire34952,wire61680],
  [wire240,wire3840,wire8738,wire17476,wire34952,wire62532]]
private def pool6_165 : List (List (List T)) := [chunk5_364, chunk5_367, chunk5_428, chunk5_429, chunk5_430, chunk5_443, chunk5_488, chunk5_497]
private theorem checked6_165 : ∀ w ∈ chunk6_165, ¬ Need 6 w.toFinset := by
  have h : chunk6_165.all (routes 5 pool6_165.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_165,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_364 _ hm
  · exact checked5_367 _ hm
  · exact checked5_428 _ hm
  · exact checked5_429 _ hm
  · exact checked5_430 _ hm
  · exact checked5_443 _ hm
  · exact checked5_488 _ hm
  · exact checked5_497 _ hm
private def chunk6_166 : List (List T) := [[wire240,wire3840,wire8738,wire17476,wire34952,wire65280],
  [wire240,wire3840,wire8738,wire17476,wire34952,wire65520],
  [wire240,wire3840,wire8738,wire17476,wire35064,wire61440],
  [wire240,wire3840,wire8738,wire17476,wire43690,wire61440]]
private def pool6_166 : List (List (List T)) := [chunk5_367, chunk5_429, chunk5_430, chunk5_431, chunk5_488, chunk5_497, chunk5_498]
private theorem checked6_166 : ∀ w ∈ chunk6_166, ¬ Need 6 w.toFinset := by
  have h : chunk6_166.all (routes 5 pool6_166.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_166,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_367 _ hm
  · exact checked5_429 _ hm
  · exact checked5_430 _ hm
  · exact checked5_431 _ hm
  · exact checked5_488 _ hm
  · exact checked5_497 _ hm
  · exact checked5_498 _ hm
private def chunk6_167 : List (List T) := [[wire240,wire3840,wire8738,wire17476,wire52428,wire61440],
  [wire240,wire3840,wire8738,wire17476,wire61166,wire61440],
  [wire240,wire3840,wire8738,wire17487,wire34952],
  [wire240,wire3840,wire8738,wire17487,wire34952,wire61440]]
private def pool6_167 : List (List (List T)) := [chunk5_0, chunk5_352, chunk5_353, chunk5_363, chunk5_364, chunk5_366, chunk5_368, chunk5_371, chunk5_423, chunk5_431, chunk5_432, chunk5_433, chunk5_436, chunk5_439, chunk5_441, chunk5_443, chunk5_468, chunk5_488, chunk5_489]
private theorem checked6_167 : ∀ w ∈ chunk6_167, ¬ Need 6 w.toFinset := by
  have h : chunk6_167.all (routes 5 pool6_167.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_167,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_352 _ hm
  · exact checked5_353 _ hm
  · exact checked5_363 _ hm
  · exact checked5_364 _ hm
  · exact checked5_366 _ hm
  · exact checked5_368 _ hm
  · exact checked5_371 _ hm
  · exact checked5_423 _ hm
  · exact checked5_431 _ hm
  · exact checked5_432 _ hm
  · exact checked5_433 _ hm
  · exact checked5_436 _ hm
  · exact checked5_439 _ hm
  · exact checked5_441 _ hm
  · exact checked5_443 _ hm
  · exact checked5_468 _ hm
  · exact checked5_488 _ hm
  · exact checked5_489 _ hm
private def chunk6_168 : List (List T) := [[wire240,wire3840,wire8738,wire26214,wire34952,wire61440],
  [wire240,wire3840,wire8738,wire34952,wire39321,wire61440],
  [wire240,wire3840,wire8738,wire34952,wire48059,wire61440],
  [wire240,wire3840,wire8738,wire34952,wire52428,wire61440]]
private def pool6_168 : List (List (List T)) := [chunk5_367, chunk5_368, chunk5_369, chunk5_444, chunk5_445, chunk5_446, chunk5_491]
private theorem checked6_168 : ∀ w ∈ chunk6_168, ¬ Need 6 w.toFinset := by
  have h : chunk6_168.all (routes 5 pool6_168.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_168,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_367 _ hm
  · exact checked5_368 _ hm
  · exact checked5_369 _ hm
  · exact checked5_444 _ hm
  · exact checked5_445 _ hm
  · exact checked5_446 _ hm
  · exact checked5_491 _ hm
private def chunk6_169 : List (List T) := [[wire240,wire3840,wire8738,wire34952,wire61166,wire61440],
  [wire240,wire3840,wire17476,wire21845,wire34952,wire61440],
  [wire240,wire3840,wire17476,wire26214,wire34952,wire61440],
  [wire240,wire3840,wire17476,wire34952,wire39321,wire61440]]
private def pool6_169 : List (List (List T)) := [chunk5_367, chunk5_368, chunk5_369, chunk5_446, chunk5_448, chunk5_449, chunk5_453, chunk5_491]
private theorem checked6_169 : ∀ w ∈ chunk6_169, ¬ Need 6 w.toFinset := by
  have h : chunk6_169.all (routes 5 pool6_169.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_169,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_367 _ hm
  · exact checked5_368 _ hm
  · exact checked5_369 _ hm
  · exact checked5_446 _ hm
  · exact checked5_448 _ hm
  · exact checked5_449 _ hm
  · exact checked5_453 _ hm
  · exact checked5_491 _ hm
private def chunk6_170 : List (List T) := [[wire240,wire3840,wire17476,wire34952,wire43690,wire61440],
  [wire240,wire3840,wire17476,wire34952,wire56797,wire61440],
  [wire240,wire3840,wire17476,wire34952,wire61166,wire61440],
  [wire240,wire4080,wire4369,wire8738,wire17476,wire61440]]
private def pool6_170 : List (List (List T)) := [chunk5_368, chunk5_369, chunk5_371, chunk5_375, chunk5_450, chunk5_451, chunk5_453, chunk5_495]
private theorem checked6_170 : ∀ w ∈ chunk6_170, ¬ Need 6 w.toFinset := by
  have h : chunk6_170.all (routes 5 pool6_170.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_170,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_368 _ hm
  · exact checked5_369 _ hm
  · exact checked5_371 _ hm
  · exact checked5_375 _ hm
  · exact checked5_450 _ hm
  · exact checked5_451 _ hm
  · exact checked5_453 _ hm
  · exact checked5_495 _ hm
private def chunk6_171 : List (List T) := [[wire240,wire4080,wire4369,wire8738,wire34952,wire61440],
  [wire240,wire4080,wire4369,wire17476,wire34952,wire61440],
  [wire240,wire4080,wire8738,wire17476,wire34952,wire61440],
  [wire240,wire4369,wire8738,wire17476,wire17487]]
private def pool6_171 : List (List (List T)) := [chunk5_326, chunk5_371, chunk5_374, chunk5_376, chunk5_378, chunk5_383, chunk5_392, chunk5_394, chunk5_395, chunk5_397, chunk5_400, chunk5_411, chunk5_421, chunk5_423, chunk5_426, chunk5_427, chunk5_430, chunk5_433, chunk5_496, chunk5_497, chunk5_498, chunk5_502]
private theorem checked6_171 : ∀ w ∈ chunk6_171, ¬ Need 6 w.toFinset := by
  have h : chunk6_171.all (routes 5 pool6_171.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_171,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_326 _ hm
  · exact checked5_371 _ hm
  · exact checked5_374 _ hm
  · exact checked5_376 _ hm
  · exact checked5_378 _ hm
  · exact checked5_383 _ hm
  · exact checked5_392 _ hm
  · exact checked5_394 _ hm
  · exact checked5_395 _ hm
  · exact checked5_397 _ hm
  · exact checked5_400 _ hm
  · exact checked5_411 _ hm
  · exact checked5_421 _ hm
  · exact checked5_423 _ hm
  · exact checked5_426 _ hm
  · exact checked5_427 _ hm
  · exact checked5_430 _ hm
  · exact checked5_433 _ hm
  · exact checked5_496 _ hm
  · exact checked5_497 _ hm
  · exact checked5_498 _ hm
  · exact checked5_502 _ hm
private def chunk6_172 : List (List T) := [[wire240,wire4369,wire8738,wire17476,wire17487,wire34952],
  [wire240,wire4369,wire8738,wire17476,wire17487,wire61440],
  [wire240,wire4369,wire8738,wire17476,wire20292,wire61440],
  [wire240,wire4369,wire8738,wire17476,wire34952,wire65280]]
private def pool6_172 : List (List (List T)) := [chunk5_0, chunk5_375, chunk5_377, chunk5_378, chunk5_379, chunk5_380, chunk5_383, chunk5_397, chunk5_407, chunk5_433, chunk5_434, chunk5_502, chunk5_509, chunk5_515]
private theorem checked6_172 : ∀ w ∈ chunk6_172, ¬ Need 6 w.toFinset := by
  have h : chunk6_172.all (routes 5 pool6_172.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_172,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_375 _ hm
  · exact checked5_377 _ hm
  · exact checked5_378 _ hm
  · exact checked5_379 _ hm
  · exact checked5_380 _ hm
  · exact checked5_383 _ hm
  · exact checked5_397 _ hm
  · exact checked5_407 _ hm
  · exact checked5_433 _ hm
  · exact checked5_434 _ hm
  · exact checked5_502 _ hm
  · exact checked5_509 _ hm
  · exact checked5_515 _ hm
private def chunk6_173 : List (List T) := [[wire240,wire4369,wire8738,wire17476,wire34952,wire65520],
  [wire240,wire4369,wire8738,wire17476,wire61440,wire61455],
  [wire240,wire4369,wire8738,wire17476,wire61440,wire61695],
  [wire240,wire4369,wire8738,wire17476,wire61440,wire65280]]
private def pool6_173 : List (List (List T)) := [chunk5_375, chunk5_383, chunk5_386, chunk5_387, chunk5_403, chunk5_502, chunk5_503, chunk5_515, chunk5_516]
private theorem checked6_173 : ∀ w ∈ chunk6_173, ¬ Need 6 w.toFinset := by
  have h : chunk6_173.all (routes 5 pool6_173.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_173,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_375 _ hm
  · exact checked5_383 _ hm
  · exact checked5_386 _ hm
  · exact checked5_387 _ hm
  · exact checked5_403 _ hm
  · exact checked5_502 _ hm
  · exact checked5_503 _ hm
  · exact checked5_515 _ hm
  · exact checked5_516 _ hm
private def chunk6_174 : List (List T) := [[wire240,wire4369,wire8738,wire17476,wire61440,wire65520],
  [wire240,wire4369,wire8738,wire17476,wire65280],
  [wire240,wire4369,wire8738,wire17476,wire65520],
  [wire240,wire4369,wire8738,wire17487,wire34952]]
private def pool6_174 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_7, chunk5_15, chunk5_51, chunk5_324, chunk5_326, chunk5_327, chunk5_337, chunk5_373, chunk5_375, chunk5_377, chunk5_378, chunk5_379, chunk5_381, chunk5_382, chunk5_385, chunk5_387, chunk5_388, chunk5_390, chunk5_393, chunk5_398, chunk5_402, chunk5_403, chunk5_404, chunk5_405, chunk5_406, chunk5_421, chunk5_422, chunk5_424, chunk5_428, chunk5_432, chunk5_434, chunk5_437, chunk5_438, chunk5_499, chunk5_501, chunk5_503, chunk5_504, chunk5_505, chunk5_516]
private theorem checked6_174 : ∀ w ∈ chunk6_174, ¬ Need 6 w.toFinset := by
  have h : chunk6_174.all (routes 5 pool6_174.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_174,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_1 _ hm
  · exact checked5_7 _ hm
  · exact checked5_15 _ hm
  · exact checked5_51 _ hm
  · exact checked5_324 _ hm
  · exact checked5_326 _ hm
  · exact checked5_327 _ hm
  · exact checked5_337 _ hm
  · exact checked5_373 _ hm
  · exact checked5_375 _ hm
  · exact checked5_377 _ hm
  · exact checked5_378 _ hm
  · exact checked5_379 _ hm
  · exact checked5_381 _ hm
  · exact checked5_382 _ hm
  · exact checked5_385 _ hm
  · exact checked5_387 _ hm
  · exact checked5_388 _ hm
  · exact checked5_390 _ hm
  · exact checked5_393 _ hm
  · exact checked5_398 _ hm
  · exact checked5_402 _ hm
  · exact checked5_403 _ hm
  · exact checked5_404 _ hm
  · exact checked5_405 _ hm
  · exact checked5_406 _ hm
  · exact checked5_421 _ hm
  · exact checked5_422 _ hm
  · exact checked5_424 _ hm
  · exact checked5_428 _ hm
  · exact checked5_432 _ hm
  · exact checked5_434 _ hm
  · exact checked5_437 _ hm
  · exact checked5_438 _ hm
  · exact checked5_499 _ hm
  · exact checked5_501 _ hm
  · exact checked5_503 _ hm
  · exact checked5_504 _ hm
  · exact checked5_505 _ hm
  · exact checked5_516 _ hm
private def chunk6_175 : List (List T) := [[wire240,wire4369,wire8738,wire17487,wire34952,wire61440],
  [wire240,wire4369,wire8738,wire20292,wire34952,wire61440],
  [wire240,wire4369,wire8738,wire20292,wire61440],
  [wire240,wire4369,wire8738,wire34952,wire61440,wire61455]]
private def pool6_175 : List (List (List T)) := [chunk5_327, chunk5_371, chunk5_372, chunk5_379, chunk5_380, chunk5_383, chunk5_385, chunk5_386, chunk5_388, chunk5_393, chunk5_407, chunk5_411, chunk5_422, chunk5_424, chunk5_440, chunk5_443, chunk5_499, chunk5_501, chunk5_505, chunk5_506, chunk5_516]
private theorem checked6_175 : ∀ w ∈ chunk6_175, ¬ Need 6 w.toFinset := by
  have h : chunk6_175.all (routes 5 pool6_175.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_175,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_327 _ hm
  · exact checked5_371 _ hm
  · exact checked5_372 _ hm
  · exact checked5_379 _ hm
  · exact checked5_380 _ hm
  · exact checked5_383 _ hm
  · exact checked5_385 _ hm
  · exact checked5_386 _ hm
  · exact checked5_388 _ hm
  · exact checked5_393 _ hm
  · exact checked5_407 _ hm
  · exact checked5_411 _ hm
  · exact checked5_422 _ hm
  · exact checked5_424 _ hm
  · exact checked5_440 _ hm
  · exact checked5_443 _ hm
  · exact checked5_499 _ hm
  · exact checked5_501 _ hm
  · exact checked5_505 _ hm
  · exact checked5_506 _ hm
  · exact checked5_516 _ hm
private def chunk6_176 : List (List T) := [[wire240,wire4369,wire8738,wire34952,wire61440,wire61695],
  [wire240,wire4369,wire8738,wire34952,wire61440,wire65280],
  [wire240,wire4369,wire8738,wire34952,wire61440,wire65520],
  [wire240,wire4369,wire8738,wire34952,wire65280]]
private def pool6_176 : List (List (List T)) := [chunk5_338, chunk5_382, chunk5_383, chunk5_384, chunk5_387, chunk5_388, chunk5_390, chunk5_394, chunk5_412, chunk5_414, chunk5_415, chunk5_416, chunk5_417, chunk5_425, chunk5_444, chunk5_446, chunk5_500, chunk5_502, chunk5_506, chunk5_507, chunk5_509, chunk5_510]
private theorem checked6_176 : ∀ w ∈ chunk6_176, ¬ Need 6 w.toFinset := by
  have h : chunk6_176.all (routes 5 pool6_176.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_176,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_338 _ hm
  · exact checked5_382 _ hm
  · exact checked5_383 _ hm
  · exact checked5_384 _ hm
  · exact checked5_387 _ hm
  · exact checked5_388 _ hm
  · exact checked5_390 _ hm
  · exact checked5_394 _ hm
  · exact checked5_412 _ hm
  · exact checked5_414 _ hm
  · exact checked5_415 _ hm
  · exact checked5_416 _ hm
  · exact checked5_417 _ hm
  · exact checked5_425 _ hm
  · exact checked5_444 _ hm
  · exact checked5_446 _ hm
  · exact checked5_500 _ hm
  · exact checked5_502 _ hm
  · exact checked5_506 _ hm
  · exact checked5_507 _ hm
  · exact checked5_509 _ hm
  · exact checked5_510 _ hm
private def chunk6_177 : List (List T) := [[wire240,wire4369,wire8738,wire34952,wire65520],
  [wire240,wire4369,wire17476,wire17487,wire34952],
  [wire240,wire4369,wire17476,wire17487,wire34952,wire61440],
  [wire240,wire4369,wire17476,wire20292,wire34952,wire61440]]
private def pool6_177 : List (List (List T)) := [chunk5_57, chunk5_333, chunk5_372, chunk5_382, chunk5_383, chunk5_384, chunk5_385, chunk5_390, chunk5_394, chunk5_395, chunk5_396, chunk5_397, chunk5_399, chunk5_404, chunk5_405, chunk5_406, chunk5_408, chunk5_410, chunk5_412, chunk5_414, chunk5_418, chunk5_425, chunk5_444, chunk5_446, chunk5_447, chunk5_448, chunk5_451, chunk5_506, chunk5_507, chunk5_510]
private theorem checked6_177 : ∀ w ∈ chunk6_177, ¬ Need 6 w.toFinset := by
  have h : chunk6_177.all (routes 5 pool6_177.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_177,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_57 _ hm
  · exact checked5_333 _ hm
  · exact checked5_372 _ hm
  · exact checked5_382 _ hm
  · exact checked5_383 _ hm
  · exact checked5_384 _ hm
  · exact checked5_385 _ hm
  · exact checked5_390 _ hm
  · exact checked5_394 _ hm
  · exact checked5_395 _ hm
  · exact checked5_396 _ hm
  · exact checked5_397 _ hm
  · exact checked5_399 _ hm
  · exact checked5_404 _ hm
  · exact checked5_405 _ hm
  · exact checked5_406 _ hm
  · exact checked5_408 _ hm
  · exact checked5_410 _ hm
  · exact checked5_412 _ hm
  · exact checked5_414 _ hm
  · exact checked5_418 _ hm
  · exact checked5_425 _ hm
  · exact checked5_444 _ hm
  · exact checked5_446 _ hm
  · exact checked5_447 _ hm
  · exact checked5_448 _ hm
  · exact checked5_451 _ hm
  · exact checked5_506 _ hm
  · exact checked5_507 _ hm
  · exact checked5_510 _ hm
private def chunk6_178 : List (List T) := [[wire240,wire4369,wire17476,wire34952,wire61440,wire61455],
  [wire240,wire4369,wire17476,wire34952,wire61440,wire61695],
  [wire240,wire4369,wire17476,wire34952,wire61440,wire65280],
  [wire240,wire4369,wire17476,wire34952,wire61440,wire65520]]
private def pool6_178 : List (List (List T)) := [chunk5_399, chunk5_400, chunk5_403, chunk5_414, chunk5_415, chunk5_416, chunk5_417, chunk5_511]
private theorem checked6_178 : ∀ w ∈ chunk6_178, ¬ Need 6 w.toFinset := by
  have h : chunk6_178.all (routes 5 pool6_178.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_178,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_399 _ hm
  · exact checked5_400 _ hm
  · exact checked5_403 _ hm
  · exact checked5_414 _ hm
  · exact checked5_415 _ hm
  · exact checked5_416 _ hm
  · exact checked5_417 _ hm
  · exact checked5_511 _ hm
private def chunk6_179 : List (List T) := [[wire240,wire4369,wire17476,wire34952,wire65280],
  [wire240,wire4369,wire17476,wire34952,wire65520],
  [wire240,wire4369,wire20292,wire34952,wire61440],
  [wire240,wire8738,wire17476,wire17487,wire34952]]
private def pool6_179 : List (List (List T)) := [chunk5_0, chunk5_85, chunk5_330, chunk5_333, chunk5_342, chunk5_372, chunk5_398, chunk5_399, chunk5_400, chunk5_401, chunk5_402, chunk5_404, chunk5_406, chunk5_407, chunk5_408, chunk5_409, chunk5_410, chunk5_411, chunk5_412, chunk5_413, chunk5_414, chunk5_417, chunk5_418, chunk5_426, chunk5_427, chunk5_428, chunk5_429, chunk5_432, chunk5_434, chunk5_436, chunk5_437, chunk5_438, chunk5_447, chunk5_448, chunk5_449, chunk5_451, chunk5_453, chunk5_500, chunk5_510, chunk5_511, chunk5_512, chunk5_513, chunk5_517, chunk5_518]
private theorem checked6_179 : ∀ w ∈ chunk6_179, ¬ Need 6 w.toFinset := by
  have h : chunk6_179.all (routes 5 pool6_179.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_179,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_85 _ hm
  · exact checked5_330 _ hm
  · exact checked5_333 _ hm
  · exact checked5_342 _ hm
  · exact checked5_372 _ hm
  · exact checked5_398 _ hm
  · exact checked5_399 _ hm
  · exact checked5_400 _ hm
  · exact checked5_401 _ hm
  · exact checked5_402 _ hm
  · exact checked5_404 _ hm
  · exact checked5_406 _ hm
  · exact checked5_407 _ hm
  · exact checked5_408 _ hm
  · exact checked5_409 _ hm
  · exact checked5_410 _ hm
  · exact checked5_411 _ hm
  · exact checked5_412 _ hm
  · exact checked5_413 _ hm
  · exact checked5_414 _ hm
  · exact checked5_417 _ hm
  · exact checked5_418 _ hm
  · exact checked5_426 _ hm
  · exact checked5_427 _ hm
  · exact checked5_428 _ hm
  · exact checked5_429 _ hm
  · exact checked5_432 _ hm
  · exact checked5_434 _ hm
  · exact checked5_436 _ hm
  · exact checked5_437 _ hm
  · exact checked5_438 _ hm
  · exact checked5_447 _ hm
  · exact checked5_448 _ hm
  · exact checked5_449 _ hm
  · exact checked5_451 _ hm
  · exact checked5_453 _ hm
  · exact checked5_500 _ hm
  · exact checked5_510 _ hm
  · exact checked5_511 _ hm
  · exact checked5_512 _ hm
  · exact checked5_513 _ hm
  · exact checked5_517 _ hm
  · exact checked5_518 _ hm
private def chunk6_180 : List (List T) := [[wire240,wire8738,wire17476,wire17487,wire34952,wire61440],
  [wire240,wire8738,wire17476,wire20292,wire34952,wire61440],
  [wire240,wire8738,wire17476,wire34952,wire61440,wire61455],
  [wire240,wire8738,wire17476,wire34952,wire61440,wire61695]]
private def pool6_180 : List (List (List T)) := [chunk5_425, chunk5_429, chunk5_439, chunk5_440, chunk5_443, chunk5_453, chunk5_518, chunk5_520]
private theorem checked6_180 : ∀ w ∈ chunk6_180, ¬ Need 6 w.toFinset := by
  have h : chunk6_180.all (routes 5 pool6_180.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_180,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_425 _ hm
  · exact checked5_429 _ hm
  · exact checked5_439 _ hm
  · exact checked5_440 _ hm
  · exact checked5_443 _ hm
  · exact checked5_453 _ hm
  · exact checked5_518 _ hm
  · exact checked5_520 _ hm
private def chunk6_181 : List (List T) := [[wire240,wire8738,wire17476,wire34952,wire61440,wire65280],
  [wire240,wire8738,wire17476,wire34952,wire61440,wire65520],
  [wire240,wire8738,wire17476,wire34952,wire65280],
  [wire240,wire8738,wire17476,wire34952,wire65520]]
private def pool6_181 : List (List (List T)) := [chunk5_149, chunk5_347, chunk5_426, chunk5_428, chunk5_429, chunk5_430, chunk5_431, chunk5_444, chunk5_445, chunk5_446, chunk5_449, chunk5_450, chunk5_517, chunk5_518, chunk5_519, chunk5_520]
private theorem checked6_181 : ∀ w ∈ chunk6_181, ¬ Need 6 w.toFinset := by
  have h : chunk6_181.all (routes 5 pool6_181.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_181,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_149 _ hm
  · exact checked5_347 _ hm
  · exact checked5_426 _ hm
  · exact checked5_428 _ hm
  · exact checked5_429 _ hm
  · exact checked5_430 _ hm
  · exact checked5_431 _ hm
  · exact checked5_444 _ hm
  · exact checked5_445 _ hm
  · exact checked5_446 _ hm
  · exact checked5_449 _ hm
  · exact checked5_450 _ hm
  · exact checked5_517 _ hm
  · exact checked5_518 _ hm
  · exact checked5_519 _ hm
  · exact checked5_520 _ hm
private def chunk6_182 : List (List T) := [[wire240,wire8738,wire17487,wire34952],
  [wire240,wire8738,wire17487,wire34952,wire61440],
  [wire3840,wire3855,wire4369,wire8738,wire17476,wire61440],
  [wire3840,wire3855,wire4369,wire8738,wire34952,wire61440]]
private def pool6_182 : List (List (List T)) := [chunk5_0, chunk5_7, chunk5_16, chunk5_327, chunk5_330, chunk5_334, chunk5_372, chunk5_422, chunk5_423, chunk5_425, chunk5_432, chunk5_434, chunk5_435, chunk5_436, chunk5_437, chunk5_438, chunk5_439, chunk5_440, chunk5_441, chunk5_442, chunk5_443, chunk5_445, chunk5_452, chunk5_467, chunk5_476, chunk5_493, chunk5_521, chunk5_522]
private theorem checked6_182 : ∀ w ∈ chunk6_182, ¬ Need 6 w.toFinset := by
  have h : chunk6_182.all (routes 5 pool6_182.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_182,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_0 _ hm
  · exact checked5_7 _ hm
  · exact checked5_16 _ hm
  · exact checked5_327 _ hm
  · exact checked5_330 _ hm
  · exact checked5_334 _ hm
  · exact checked5_372 _ hm
  · exact checked5_422 _ hm
  · exact checked5_423 _ hm
  · exact checked5_425 _ hm
  · exact checked5_432 _ hm
  · exact checked5_434 _ hm
  · exact checked5_435 _ hm
  · exact checked5_436 _ hm
  · exact checked5_437 _ hm
  · exact checked5_438 _ hm
  · exact checked5_439 _ hm
  · exact checked5_440 _ hm
  · exact checked5_441 _ hm
  · exact checked5_442 _ hm
  · exact checked5_443 _ hm
  · exact checked5_445 _ hm
  · exact checked5_452 _ hm
  · exact checked5_467 _ hm
  · exact checked5_476 _ hm
  · exact checked5_493 _ hm
  · exact checked5_521 _ hm
  · exact checked5_522 _ hm
private def chunk6_183 : List (List T) := [[wire3840,wire3855,wire4369,wire17476,wire34952,wire61440],
  [wire3840,wire3855,wire8738,wire17476,wire34952,wire61440],
  [wire3840,wire4080,wire4369,wire8738,wire17476,wire61440],
  [wire3840,wire4080,wire4369,wire8738,wire34952,wire61440]]
private def pool6_183 : List (List (List T)) := [chunk5_467, chunk5_476, chunk5_494, chunk5_495, chunk5_496]
private theorem checked6_183 : ∀ w ∈ chunk6_183, ¬ Need 6 w.toFinset := by
  have h : chunk6_183.all (routes 5 pool6_183.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_183,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact checked5_467 _ hm
  · exact checked5_476 _ hm
  · exact checked5_494 _ hm
  · exact checked5_495 _ hm
  · exact checked5_496 _ hm
private def chunk6_184 : List (List T) := [[wire3840,wire4080,wire4369,wire17476,wire34952,wire61440],
  [wire3840,wire4080,wire8738,wire17476,wire34952,wire61440],
  [wire3840,wire4369,wire4383,wire8738,wire17476,wire61440],
  [wire3840,wire4369,wire4383,wire8738,wire34952,wire61440]]
private def pool6_184 : List (List (List T)) := [chunk5_468, chunk5_469, chunk5_476, chunk5_480, chunk5_497, chunk5_498]
private theorem checked6_184 : ∀ w ∈ chunk6_184, ¬ Need 6 w.toFinset := by
  have h : chunk6_184.all (routes 5 pool6_184.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_184,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_468 _ hm
  · exact checked5_469 _ hm
  · exact checked5_476 _ hm
  · exact checked5_480 _ hm
  · exact checked5_497 _ hm
  · exact checked5_498 _ hm
private def chunk6_185 : List (List T) := [[wire3840,wire4369,wire4383,wire17476,wire34952,wire61440],
  [wire3840,wire4369,wire4593,wire8738,wire17476,wire61440],
  [wire3840,wire4369,wire4593,wire8738,wire34952,wire61440],
  [wire3840,wire4369,wire4593,wire17476,wire34952,wire61440]]
private def pool6_185 : List (List (List T)) := [chunk5_469, chunk5_470, chunk5_476, chunk5_482, chunk5_483, chunk5_485, chunk5_486, chunk5_499, chunk5_500]
private theorem checked6_185 : ∀ w ∈ chunk6_185, ¬ Need 6 w.toFinset := by
  have h : chunk6_185.all (routes 5 pool6_185.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_185,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_469 _ hm
  · exact checked5_470 _ hm
  · exact checked5_476 _ hm
  · exact checked5_482 _ hm
  · exact checked5_483 _ hm
  · exact checked5_485 _ hm
  · exact checked5_486 _ hm
  · exact checked5_499 _ hm
  · exact checked5_500 _ hm
private def chunk6_186 : List (List T) := [[wire3840,wire4369,wire8738,wire8751,wire17476,wire61440],
  [wire3840,wire4369,wire8738,wire8751,wire34952,wire61440],
  [wire3840,wire4369,wire8738,wire8946,wire17476,wire61440],
  [wire3840,wire4369,wire8738,wire8946,wire34952,wire61440]]
private def pool6_186 : List (List (List T)) := [chunk5_470, chunk5_472, chunk5_473, chunk5_474, chunk5_487, chunk5_500, chunk5_501, chunk5_502]
private theorem checked6_186 : ∀ w ∈ chunk6_186, ¬ Need 6 w.toFinset := by
  have h : chunk6_186.all (routes 5 pool6_186.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_186,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_470 _ hm
  · exact checked5_472 _ hm
  · exact checked5_473 _ hm
  · exact checked5_474 _ hm
  · exact checked5_487 _ hm
  · exact checked5_500 _ hm
  · exact checked5_501 _ hm
  · exact checked5_502 _ hm
private def chunk6_187 : List (List T) := [[wire3840,wire4369,wire8738,wire17476,wire61440,wire61455],
  [wire3840,wire4369,wire8738,wire17476,wire61440,wire61680],
  [wire3840,wire4369,wire8738,wire17476,wire61440,wire65295],
  [wire3840,wire4369,wire8738,wire17476,wire61440,wire65520]]
private def pool6_187 : List (List (List T)) := [chunk5_471, chunk5_472, chunk5_477, chunk5_503, chunk5_504, chunk5_505]
private theorem checked6_187 : ∀ w ∈ chunk6_187, ¬ Need 6 w.toFinset := by
  have h : chunk6_187.all (routes 5 pool6_187.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_187,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_471 _ hm
  · exact checked5_472 _ hm
  · exact checked5_477 _ hm
  · exact checked5_503 _ hm
  · exact checked5_504 _ hm
  · exact checked5_505 _ hm
private def chunk6_188 : List (List T) := [[wire3840,wire4369,wire8738,wire34952,wire61440,wire61455],
  [wire3840,wire4369,wire8738,wire34952,wire61440,wire61680],
  [wire3840,wire4369,wire8738,wire34952,wire61440,wire65295],
  [wire3840,wire4369,wire8738,wire34952,wire61440,wire65520]]
private def pool6_188 : List (List (List T)) := [chunk5_471, chunk5_472, chunk5_478, chunk5_479, chunk5_506, chunk5_507, chunk5_508]
private theorem checked6_188 : ∀ w ∈ chunk6_188, ¬ Need 6 w.toFinset := by
  have h : chunk6_188.all (routes 5 pool6_188.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_188,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_471 _ hm
  · exact checked5_472 _ hm
  · exact checked5_478 _ hm
  · exact checked5_479 _ hm
  · exact checked5_506 _ hm
  · exact checked5_507 _ hm
  · exact checked5_508 _ hm
private def chunk6_189 : List (List T) := [[wire3840,wire4369,wire8751,wire17476,wire34952,wire61440],
  [wire3840,wire4369,wire8751,wire17476,wire61440],
  [wire3840,wire4369,wire8946,wire17476,wire34952,wire61440],
  [wire3840,wire4369,wire8946,wire34952,wire61440]]
private def pool6_189 : List (List (List T)) := [chunk5_468, chunk5_472, chunk5_473, chunk5_474, chunk5_475, chunk5_476, chunk5_477, chunk5_478, chunk5_490, chunk5_491, chunk5_508, chunk5_509, chunk5_510]
private theorem checked6_189 : ∀ w ∈ chunk6_189, ¬ Need 6 w.toFinset := by
  have h : chunk6_189.all (routes 5 pool6_189.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_189,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_468 _ hm
  · exact checked5_472 _ hm
  · exact checked5_473 _ hm
  · exact checked5_474 _ hm
  · exact checked5_475 _ hm
  · exact checked5_476 _ hm
  · exact checked5_477 _ hm
  · exact checked5_478 _ hm
  · exact checked5_490 _ hm
  · exact checked5_491 _ hm
  · exact checked5_508 _ hm
  · exact checked5_509 _ hm
  · exact checked5_510 _ hm
private def chunk6_190 : List (List T) := [[wire3840,wire4369,wire17476,wire34952,wire61440,wire61455],
  [wire3840,wire4369,wire17476,wire34952,wire61440,wire61680],
  [wire3840,wire4369,wire17476,wire34952,wire61440,wire65295],
  [wire3840,wire4369,wire17476,wire34952,wire61440,wire65520]]
private def pool6_190 : List (List (List T)) := [chunk5_477, chunk5_478, chunk5_479, chunk5_511, chunk5_512, chunk5_513]
private theorem checked6_190 : ∀ w ∈ chunk6_190, ¬ Need 6 w.toFinset := by
  have h : chunk6_190.all (routes 5 pool6_190.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_190,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_477 _ hm
  · exact checked5_478 _ hm
  · exact checked5_479 _ hm
  · exact checked5_511 _ hm
  · exact checked5_512 _ hm
  · exact checked5_513 _ hm
private def chunk6_191 : List (List T) := [[wire3840,wire4383,wire8738,wire17476,wire34952,wire61440],
  [wire3840,wire4383,wire8738,wire34952,wire61440],
  [wire3840,wire4593,wire8738,wire17476,wire34952,wire61440],
  [wire3840,wire4593,wire8738,wire17476,wire61440]]
private def pool6_191 : List (List (List T)) := [chunk5_8, chunk5_327, chunk5_469, chunk5_479, chunk5_480, chunk5_481, chunk5_482, chunk5_483, chunk5_484, chunk5_485, chunk5_486, chunk5_487, chunk5_488, chunk5_490, chunk5_513, chunk5_514, chunk5_515, chunk5_516]
private theorem checked6_191 : ∀ w ∈ chunk6_191, ¬ Need 6 w.toFinset := by
  have h : chunk6_191.all (routes 5 pool6_191.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_191,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked5_8 _ hm
  · exact checked5_327 _ hm
  · exact checked5_469 _ hm
  · exact checked5_479 _ hm
  · exact checked5_480 _ hm
  · exact checked5_481 _ hm
  · exact checked5_482 _ hm
  · exact checked5_483 _ hm
  · exact checked5_484 _ hm
  · exact checked5_485 _ hm
  · exact checked5_486 _ hm
  · exact checked5_487 _ hm
  · exact checked5_488 _ hm
  · exact checked5_490 _ hm
  · exact checked5_513 _ hm
  · exact checked5_514 _ hm
  · exact checked5_515 _ hm
  · exact checked5_516 _ hm
private def chunk6_192 : List (List T) := [[wire3840,wire8738,wire8751,wire17476,wire34952,wire61440],
  [wire3840,wire8738,wire8946,wire17476,wire34952,wire61440],
  [wire3840,wire8738,wire17476,wire34952,wire61440,wire61455],
  [wire3840,wire8738,wire17476,wire34952,wire61440,wire61680]]
private def pool6_192 : List (List (List T)) := [chunk5_490, chunk5_491, chunk5_517, chunk5_519]
private theorem checked6_192 : ∀ w ∈ chunk6_192, ¬ Need 6 w.toFinset := by
  have h : chunk6_192.all (routes 5 pool6_192.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_192,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact checked5_490 _ hm
  · exact checked5_491 _ hm
  · exact checked5_517 _ hm
  · exact checked5_519 _ hm
private def chunk6_193 : List (List T) := [[wire3840,wire8738,wire17476,wire34952,wire61440,wire65295],
  [wire3840,wire8738,wire17476,wire34952,wire61440,wire65520]]
private def pool6_193 : List (List (List T)) := [chunk5_519]
private theorem checked6_193 : ∀ w ∈ chunk6_193, ¬ Need 6 w.toFinset := by
  have h : chunk6_193.all (routes 5 pool6_193.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_193,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_519 _ hm
#print axioms checked6_193
private def chunk7_0 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire8738,wire17476],
  [wire15,wire240,wire3840,wire4369,wire8738,wire17476,wire34952],
  [wire15,wire240,wire3840,wire4369,wire8738,wire17476,wire34952,wire61440],
  [wire15,wire240,wire3840,wire4369,wire8738,wire17476,wire61440]]
private def pool7_0 : List (List (List T)) := [chunk6_0, chunk6_8, chunk6_10, chunk6_14, chunk6_15, chunk6_16, chunk6_17, chunk6_18, chunk6_19, chunk6_20, chunk6_21, chunk6_22, chunk6_23, chunk6_24, chunk6_25, chunk6_28, chunk6_29, chunk6_31, chunk6_34, chunk6_35, chunk6_39, chunk6_42, chunk6_44, chunk6_46, chunk6_47, chunk6_49, chunk6_50, chunk6_52, chunk6_53, chunk6_65, chunk6_66, chunk6_86, chunk6_105, chunk6_108, chunk6_110, chunk6_111, chunk6_112, chunk6_124, chunk6_125, chunk6_144, chunk6_147, chunk6_149, chunk6_150, chunk6_151, chunk6_155, chunk6_163]
private theorem checked7_0 : ∀ w ∈ chunk7_0, ¬ Need 7 w.toFinset := by
  have h : chunk7_0.all (routes 6 pool7_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_8 _ hm
  · exact checked6_10 _ hm
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
  · exact checked6_24 _ hm
  · exact checked6_25 _ hm
  · exact checked6_28 _ hm
  · exact checked6_29 _ hm
  · exact checked6_31 _ hm
  · exact checked6_34 _ hm
  · exact checked6_35 _ hm
  · exact checked6_39 _ hm
  · exact checked6_42 _ hm
  · exact checked6_44 _ hm
  · exact checked6_46 _ hm
  · exact checked6_47 _ hm
  · exact checked6_49 _ hm
  · exact checked6_50 _ hm
  · exact checked6_52 _ hm
  · exact checked6_53 _ hm
  · exact checked6_65 _ hm
  · exact checked6_66 _ hm
  · exact checked6_86 _ hm
  · exact checked6_105 _ hm
  · exact checked6_108 _ hm
  · exact checked6_110 _ hm
  · exact checked6_111 _ hm
  · exact checked6_112 _ hm
  · exact checked6_124 _ hm
  · exact checked6_125 _ hm
  · exact checked6_144 _ hm
  · exact checked6_147 _ hm
  · exact checked6_149 _ hm
  · exact checked6_150 _ hm
  · exact checked6_151 _ hm
  · exact checked6_155 _ hm
  · exact checked6_163 _ hm
private def chunk7_1 : List (List T) := [[wire15,wire240,wire3840,wire4369,wire8738,wire34952],
  [wire15,wire240,wire3840,wire4369,wire8738,wire34952,wire61440],
  [wire15,wire240,wire3840,wire4369,wire17476,wire34952],
  [wire15,wire240,wire3840,wire4369,wire17476,wire34952,wire61440]]
private def pool7_1 : List (List (List T)) := [chunk6_0, chunk6_2, chunk6_4, chunk6_6, chunk6_11, chunk6_13, chunk6_14, chunk6_15, chunk6_17, chunk6_18, chunk6_19, chunk6_20, chunk6_21, chunk6_22, chunk6_23, chunk6_24, chunk6_25, chunk6_26, chunk6_27, chunk6_28, chunk6_29, chunk6_31, chunk6_32, chunk6_33, chunk6_34, chunk6_35, chunk6_40, chunk6_42, chunk6_56, chunk6_59, chunk6_60, chunk6_61, chunk6_66, chunk6_67, chunk6_69, chunk6_72, chunk6_74, chunk6_76, chunk6_77, chunk6_81, chunk6_105, chunk6_106, chunk6_109, chunk6_113, chunk6_114, chunk6_117, chunk6_118, chunk6_120, chunk6_122, chunk6_144, chunk6_147, chunk6_148, chunk6_153, chunk6_157, chunk6_158, chunk6_159, chunk6_163]
private theorem checked7_1 : ∀ w ∈ chunk7_1, ¬ Need 7 w.toFinset := by
  have h : chunk7_1.all (routes 6 pool7_1.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_1,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_2 _ hm
  · exact checked6_4 _ hm
  · exact checked6_6 _ hm
  · exact checked6_11 _ hm
  · exact checked6_13 _ hm
  · exact checked6_14 _ hm
  · exact checked6_15 _ hm
  · exact checked6_17 _ hm
  · exact checked6_18 _ hm
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
  · exact checked6_31 _ hm
  · exact checked6_32 _ hm
  · exact checked6_33 _ hm
  · exact checked6_34 _ hm
  · exact checked6_35 _ hm
  · exact checked6_40 _ hm
  · exact checked6_42 _ hm
  · exact checked6_56 _ hm
  · exact checked6_59 _ hm
  · exact checked6_60 _ hm
  · exact checked6_61 _ hm
  · exact checked6_66 _ hm
  · exact checked6_67 _ hm
  · exact checked6_69 _ hm
  · exact checked6_72 _ hm
  · exact checked6_74 _ hm
  · exact checked6_76 _ hm
  · exact checked6_77 _ hm
  · exact checked6_81 _ hm
  · exact checked6_105 _ hm
  · exact checked6_106 _ hm
  · exact checked6_109 _ hm
  · exact checked6_113 _ hm
  · exact checked6_114 _ hm
  · exact checked6_117 _ hm
  · exact checked6_118 _ hm
  · exact checked6_120 _ hm
  · exact checked6_122 _ hm
  · exact checked6_144 _ hm
  · exact checked6_147 _ hm
  · exact checked6_148 _ hm
  · exact checked6_153 _ hm
  · exact checked6_157 _ hm
  · exact checked6_158 _ hm
  · exact checked6_159 _ hm
  · exact checked6_163 _ hm
private def chunk7_2 : List (List T) := [[wire15,wire240,wire3840,wire8738,wire17476,wire34952],
  [wire15,wire240,wire3840,wire8738,wire17476,wire34952,wire61440],
  [wire15,wire240,wire4369,wire8738,wire17476],
  [wire15,wire240,wire4369,wire8738,wire17476,wire34952]]
private def pool7_2 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_4, chunk6_6, chunk6_7, chunk6_8, chunk6_9, chunk6_10, chunk6_11, chunk6_13, chunk6_16, chunk6_17, chunk6_18, chunk6_29, chunk6_30, chunk6_31, chunk6_32, chunk6_33, chunk6_35, chunk6_36, chunk6_38, chunk6_39, chunk6_41, chunk6_42, chunk6_43, chunk6_44, chunk6_45, chunk6_46, chunk6_47, chunk6_48, chunk6_51, chunk6_52, chunk6_53, chunk6_54, chunk6_57, chunk6_62, chunk6_64, chunk6_65, chunk6_67, chunk6_69, chunk6_70, chunk6_72, chunk6_73, chunk6_79, chunk6_85, chunk6_86, chunk6_87, chunk6_88, chunk6_89, chunk6_90, chunk6_92, chunk6_93, chunk6_94, chunk6_95, chunk6_96, chunk6_99, chunk6_106, chunk6_109, chunk6_126, chunk6_127, chunk6_128, chunk6_133, chunk6_135, chunk6_145, chunk6_148, chunk6_164, chunk6_166, chunk6_167, chunk6_171, chunk6_172, chunk6_173, chunk6_174]
private theorem checked7_2 : ∀ w ∈ chunk7_2, ¬ Need 7 w.toFinset := by
  have h : chunk7_2.all (routes 6 pool7_2.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_2,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_4 _ hm
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_9 _ hm
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_13 _ hm
  · exact checked6_16 _ hm
  · exact checked6_17 _ hm
  · exact checked6_18 _ hm
  · exact checked6_29 _ hm
  · exact checked6_30 _ hm
  · exact checked6_31 _ hm
  · exact checked6_32 _ hm
  · exact checked6_33 _ hm
  · exact checked6_35 _ hm
  · exact checked6_36 _ hm
  · exact checked6_38 _ hm
  · exact checked6_39 _ hm
  · exact checked6_41 _ hm
  · exact checked6_42 _ hm
  · exact checked6_43 _ hm
  · exact checked6_44 _ hm
  · exact checked6_45 _ hm
  · exact checked6_46 _ hm
  · exact checked6_47 _ hm
  · exact checked6_48 _ hm
  · exact checked6_51 _ hm
  · exact checked6_52 _ hm
  · exact checked6_53 _ hm
  · exact checked6_54 _ hm
  · exact checked6_57 _ hm
  · exact checked6_62 _ hm
  · exact checked6_64 _ hm
  · exact checked6_65 _ hm
  · exact checked6_67 _ hm
  · exact checked6_69 _ hm
  · exact checked6_70 _ hm
  · exact checked6_72 _ hm
  · exact checked6_73 _ hm
  · exact checked6_79 _ hm
  · exact checked6_85 _ hm
  · exact checked6_86 _ hm
  · exact checked6_87 _ hm
  · exact checked6_88 _ hm
  · exact checked6_89 _ hm
  · exact checked6_90 _ hm
  · exact checked6_92 _ hm
  · exact checked6_93 _ hm
  · exact checked6_94 _ hm
  · exact checked6_95 _ hm
  · exact checked6_96 _ hm
  · exact checked6_99 _ hm
  · exact checked6_106 _ hm
  · exact checked6_109 _ hm
  · exact checked6_126 _ hm
  · exact checked6_127 _ hm
  · exact checked6_128 _ hm
  · exact checked6_133 _ hm
  · exact checked6_135 _ hm
  · exact checked6_145 _ hm
  · exact checked6_148 _ hm
  · exact checked6_164 _ hm
  · exact checked6_166 _ hm
  · exact checked6_167 _ hm
  · exact checked6_171 _ hm
  · exact checked6_172 _ hm
  · exact checked6_173 _ hm
  · exact checked6_174 _ hm
private def chunk7_3 : List (List T) := [[wire15,wire240,wire4369,wire8738,wire17476,wire34952,wire61440],
  [wire15,wire240,wire4369,wire8738,wire17476,wire61440],
  [wire15,wire240,wire4369,wire8738,wire34952],
  [wire15,wire240,wire4369,wire8738,wire34952,wire61440]]
private def pool7_3 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_3, chunk6_6, chunk6_7, chunk6_9, chunk6_12, chunk6_13, chunk6_36, chunk6_37, chunk6_38, chunk6_39, chunk6_40, chunk6_41, chunk6_42, chunk6_43, chunk6_45, chunk6_48, chunk6_49, chunk6_50, chunk6_53, chunk6_54, chunk6_55, chunk6_56, chunk6_57, chunk6_58, chunk6_59, chunk6_60, chunk6_61, chunk6_62, chunk6_63, chunk6_64, chunk6_65, chunk6_67, chunk6_68, chunk6_70, chunk6_75, chunk6_79, chunk6_80, chunk6_82, chunk6_83, chunk6_84, chunk6_85, chunk6_86, chunk6_88, chunk6_90, chunk6_95, chunk6_99, chunk6_100, chunk6_102, chunk6_107, chunk6_134, chunk6_135, chunk6_136, chunk6_137, chunk6_138, chunk6_145, chunk6_146, chunk6_172, chunk6_173, chunk6_174, chunk6_175, chunk6_176, chunk6_177]
private theorem checked7_3 : ∀ w ∈ chunk7_3, ¬ Need 7 w.toFinset := by
  have h : chunk7_3.all (routes 6 pool7_3.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_3,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_2 _ hm
  · exact checked6_3 _ hm
  · exact checked6_6 _ hm
  · exact checked6_7 _ hm
  · exact checked6_9 _ hm
  · exact checked6_12 _ hm
  · exact checked6_13 _ hm
  · exact checked6_36 _ hm
  · exact checked6_37 _ hm
  · exact checked6_38 _ hm
  · exact checked6_39 _ hm
  · exact checked6_40 _ hm
  · exact checked6_41 _ hm
  · exact checked6_42 _ hm
  · exact checked6_43 _ hm
  · exact checked6_45 _ hm
  · exact checked6_48 _ hm
  · exact checked6_49 _ hm
  · exact checked6_50 _ hm
  · exact checked6_53 _ hm
  · exact checked6_54 _ hm
  · exact checked6_55 _ hm
  · exact checked6_56 _ hm
  · exact checked6_57 _ hm
  · exact checked6_58 _ hm
  · exact checked6_59 _ hm
  · exact checked6_60 _ hm
  · exact checked6_61 _ hm
  · exact checked6_62 _ hm
  · exact checked6_63 _ hm
  · exact checked6_64 _ hm
  · exact checked6_65 _ hm
  · exact checked6_67 _ hm
  · exact checked6_68 _ hm
  · exact checked6_70 _ hm
  · exact checked6_75 _ hm
  · exact checked6_79 _ hm
  · exact checked6_80 _ hm
  · exact checked6_82 _ hm
  · exact checked6_83 _ hm
  · exact checked6_84 _ hm
  · exact checked6_85 _ hm
  · exact checked6_86 _ hm
  · exact checked6_88 _ hm
  · exact checked6_90 _ hm
  · exact checked6_95 _ hm
  · exact checked6_99 _ hm
  · exact checked6_100 _ hm
  · exact checked6_102 _ hm
  · exact checked6_107 _ hm
  · exact checked6_134 _ hm
  · exact checked6_135 _ hm
  · exact checked6_136 _ hm
  · exact checked6_137 _ hm
  · exact checked6_138 _ hm
  · exact checked6_145 _ hm
  · exact checked6_146 _ hm
  · exact checked6_172 _ hm
  · exact checked6_173 _ hm
  · exact checked6_174 _ hm
  · exact checked6_175 _ hm
  · exact checked6_176 _ hm
  · exact checked6_177 _ hm
private def chunk7_4 : List (List T) := [[wire15,wire240,wire4369,wire17476,wire34952],
  [wire15,wire240,wire4369,wire17476,wire34952,wire61440],
  [wire15,wire240,wire8738,wire17476,wire34952],
  [wire15,wire240,wire8738,wire17476,wire34952,wire61440]]
private def pool7_4 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_3, chunk6_5, chunk6_7, chunk6_8, chunk6_10, chunk6_11, chunk6_12, chunk6_13, chunk6_14, chunk6_36, chunk6_37, chunk6_38, chunk6_39, chunk6_68, chunk6_69, chunk6_70, chunk6_71, chunk6_72, chunk6_73, chunk6_74, chunk6_75, chunk6_76, chunk6_77, chunk6_78, chunk6_79, chunk6_80, chunk6_81, chunk6_82, chunk6_83, chunk6_84, chunk6_86, chunk6_87, chunk6_89, chunk6_90, chunk6_91, chunk6_92, chunk6_93, chunk6_94, chunk6_95, chunk6_96, chunk6_97, chunk6_98, chunk6_99, chunk6_100, chunk6_101, chunk6_102, chunk6_103, chunk6_104, chunk6_105, chunk6_107, chunk6_108, chunk6_138, chunk6_139, chunk6_140, chunk6_141, chunk6_142, chunk6_143, chunk6_146, chunk6_147, chunk6_177, chunk6_178, chunk6_179, chunk6_180, chunk6_181, chunk6_182]
private theorem checked7_4 : ∀ w ∈ chunk7_4, ¬ Need 7 w.toFinset := by
  have h : chunk7_4.all (routes 6 pool7_4.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hm
  · exact checked6_1 _ hm
  · exact checked6_3 _ hm
  · exact checked6_5 _ hm
  · exact checked6_7 _ hm
  · exact checked6_8 _ hm
  · exact checked6_10 _ hm
  · exact checked6_11 _ hm
  · exact checked6_12 _ hm
  · exact checked6_13 _ hm
  · exact checked6_14 _ hm
  · exact checked6_36 _ hm
  · exact checked6_37 _ hm
  · exact checked6_38 _ hm
  · exact checked6_39 _ hm
  · exact checked6_68 _ hm
  · exact checked6_69 _ hm
  · exact checked6_70 _ hm
  · exact checked6_71 _ hm
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
  · exact checked6_86 _ hm
  · exact checked6_87 _ hm
  · exact checked6_89 _ hm
  · exact checked6_90 _ hm
  · exact checked6_91 _ hm
  · exact checked6_92 _ hm
  · exact checked6_93 _ hm
  · exact checked6_94 _ hm
  · exact checked6_95 _ hm
  · exact checked6_96 _ hm
  · exact checked6_97 _ hm
  · exact checked6_98 _ hm
  · exact checked6_99 _ hm
  · exact checked6_100 _ hm
  · exact checked6_101 _ hm
  · exact checked6_102 _ hm
  · exact checked6_103 _ hm
  · exact checked6_104 _ hm
  · exact checked6_105 _ hm
  · exact checked6_107 _ hm
  · exact checked6_108 _ hm
  · exact checked6_138 _ hm
  · exact checked6_139 _ hm
  · exact checked6_140 _ hm
  · exact checked6_141 _ hm
  · exact checked6_142 _ hm
  · exact checked6_143 _ hm
  · exact checked6_146 _ hm
  · exact checked6_147 _ hm
  · exact checked6_177 _ hm
  · exact checked6_178 _ hm
  · exact checked6_179 _ hm
  · exact checked6_180 _ hm
  · exact checked6_181 _ hm
  · exact checked6_182 _ hm
private def chunk7_5 : List (List T) := [[wire15,wire3840,wire4369,wire8738,wire17476,wire34952,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire17476,wire61440],
  [wire15,wire3840,wire4369,wire8738,wire34952,wire61440],
  [wire15,wire3840,wire4369,wire17476,wire34952,wire61440]]
private def pool7_5 : List (List (List T)) := [chunk6_3, chunk6_6, chunk6_109, chunk6_110, chunk6_111, chunk6_112, chunk6_113, chunk6_114, chunk6_115, chunk6_116, chunk6_117, chunk6_118, chunk6_119, chunk6_120, chunk6_121, chunk6_122, chunk6_123, chunk6_124, chunk6_125, chunk6_128, chunk6_129, chunk6_130, chunk6_131, chunk6_132, chunk6_133, chunk6_134, chunk6_135, chunk6_136, chunk6_137, chunk6_138, chunk6_139, chunk6_140, chunk6_182, chunk6_183, chunk6_184, chunk6_185, chunk6_186, chunk6_187, chunk6_188, chunk6_189, chunk6_190, chunk6_191]
private theorem checked7_5 : ∀ w ∈ chunk7_5, ¬ Need 7 w.toFinset := by
  have h : chunk7_5.all (routes 6 pool7_5.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_5,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_3 _ hm
  · exact checked6_6 _ hm
  · exact checked6_109 _ hm
  · exact checked6_110 _ hm
  · exact checked6_111 _ hm
  · exact checked6_112 _ hm
  · exact checked6_113 _ hm
  · exact checked6_114 _ hm
  · exact checked6_115 _ hm
  · exact checked6_116 _ hm
  · exact checked6_117 _ hm
  · exact checked6_118 _ hm
  · exact checked6_119 _ hm
  · exact checked6_120 _ hm
  · exact checked6_121 _ hm
  · exact checked6_122 _ hm
  · exact checked6_123 _ hm
  · exact checked6_124 _ hm
  · exact checked6_125 _ hm
  · exact checked6_128 _ hm
  · exact checked6_129 _ hm
  · exact checked6_130 _ hm
  · exact checked6_131 _ hm
  · exact checked6_132 _ hm
  · exact checked6_133 _ hm
  · exact checked6_134 _ hm
  · exact checked6_135 _ hm
  · exact checked6_136 _ hm
  · exact checked6_137 _ hm
  · exact checked6_138 _ hm
  · exact checked6_139 _ hm
  · exact checked6_140 _ hm
  · exact checked6_182 _ hm
  · exact checked6_183 _ hm
  · exact checked6_184 _ hm
  · exact checked6_185 _ hm
  · exact checked6_186 _ hm
  · exact checked6_187 _ hm
  · exact checked6_188 _ hm
  · exact checked6_189 _ hm
  · exact checked6_190 _ hm
  · exact checked6_191 _ hm
private def chunk7_6 : List (List T) := [[wire15,wire3840,wire8738,wire17476,wire34952,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire17476,wire34952,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire17476,wire61440],
  [wire240,wire3840,wire4369,wire8738,wire34952,wire61440]]
private def pool7_6 : List (List (List T)) := [chunk6_110, chunk6_126, chunk6_127, chunk6_128, chunk6_129, chunk6_130, chunk6_131, chunk6_132, chunk6_141, chunk6_142, chunk6_143, chunk6_148, chunk6_149, chunk6_150, chunk6_151, chunk6_152, chunk6_153, chunk6_154, chunk6_155, chunk6_156, chunk6_157, chunk6_160, chunk6_161, chunk6_162, chunk6_163, chunk6_164, chunk6_167, chunk6_168, chunk6_169, chunk6_170, chunk6_171, chunk6_172, chunk6_173, chunk6_174, chunk6_175, chunk6_176, chunk6_183, chunk6_185, chunk6_186, chunk6_187, chunk6_188, chunk6_189, chunk6_191, chunk6_192, chunk6_193]
private theorem checked7_6 : ∀ w ∈ chunk7_6, ¬ Need 7 w.toFinset := by
  have h : chunk7_6.all (routes 6 pool7_6.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_6,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_110 _ hm
  · exact checked6_126 _ hm
  · exact checked6_127 _ hm
  · exact checked6_128 _ hm
  · exact checked6_129 _ hm
  · exact checked6_130 _ hm
  · exact checked6_131 _ hm
  · exact checked6_132 _ hm
  · exact checked6_141 _ hm
  · exact checked6_142 _ hm
  · exact checked6_143 _ hm
  · exact checked6_148 _ hm
  · exact checked6_149 _ hm
  · exact checked6_150 _ hm
  · exact checked6_151 _ hm
  · exact checked6_152 _ hm
  · exact checked6_153 _ hm
  · exact checked6_154 _ hm
  · exact checked6_155 _ hm
  · exact checked6_156 _ hm
  · exact checked6_157 _ hm
  · exact checked6_160 _ hm
  · exact checked6_161 _ hm
  · exact checked6_162 _ hm
  · exact checked6_163 _ hm
  · exact checked6_164 _ hm
  · exact checked6_167 _ hm
  · exact checked6_168 _ hm
  · exact checked6_169 _ hm
  · exact checked6_170 _ hm
  · exact checked6_171 _ hm
  · exact checked6_172 _ hm
  · exact checked6_173 _ hm
  · exact checked6_174 _ hm
  · exact checked6_175 _ hm
  · exact checked6_176 _ hm
  · exact checked6_183 _ hm
  · exact checked6_185 _ hm
  · exact checked6_186 _ hm
  · exact checked6_187 _ hm
  · exact checked6_188 _ hm
  · exact checked6_189 _ hm
  · exact checked6_191 _ hm
  · exact checked6_192 _ hm
  · exact checked6_193 _ hm
private def chunk7_7 : List (List T) := [[wire240,wire3840,wire4369,wire17476,wire34952,wire61440],
  [wire240,wire3840,wire8738,wire17476,wire34952,wire61440]]
private def pool7_7 : List (List (List T)) := [chunk6_144, chunk6_149, chunk6_157, chunk6_158, chunk6_159, chunk6_160, chunk6_161, chunk6_162, chunk6_163, chunk6_165, chunk6_166, chunk6_167, chunk6_168, chunk6_169, chunk6_170, chunk6_171, chunk6_177, chunk6_178, chunk6_179, chunk6_180, chunk6_181, chunk6_184, chunk6_185, chunk6_190, chunk6_192, chunk6_193]
private theorem checked7_7 : ∀ w ∈ chunk7_7, ¬ Need 7 w.toFinset := by
  have h : chunk7_7.all (routes 6 pool7_7.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool7_7,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_144 _ hm
  · exact checked6_149 _ hm
  · exact checked6_157 _ hm
  · exact checked6_158 _ hm
  · exact checked6_159 _ hm
  · exact checked6_160 _ hm
  · exact checked6_161 _ hm
  · exact checked6_162 _ hm
  · exact checked6_163 _ hm
  · exact checked6_165 _ hm
  · exact checked6_166 _ hm
  · exact checked6_167 _ hm
  · exact checked6_168 _ hm
  · exact checked6_169 _ hm
  · exact checked6_170 _ hm
  · exact checked6_171 _ hm
  · exact checked6_177 _ hm
  · exact checked6_178 _ hm
  · exact checked6_179 _ hm
  · exact checked6_180 _ hm
  · exact checked6_181 _ hm
  · exact checked6_184 _ hm
  · exact checked6_185 _ hm
  · exact checked6_190 _ hm
  · exact checked6_192 _ hm
  · exact checked6_193 _ hm
#print axioms checked7_7
private def roots : List (List (List T)) := [chunk7_0, chunk7_1, chunk7_2, chunk7_3, chunk7_4, chunk7_5, chunk7_6, chunk7_7]
private theorem root : safe 7 ins := by
  apply initial (next := roots.flatten)
  · intro w hw
    obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hw
    simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact checked7_0 _ hm
    · exact checked7_1 _ hm
    · exact checked7_2 _ hm
    · exact checked7_3 _ hm
    · exact checked7_4 _ hm
    · exact checked7_5 _ hm
    · exact checked7_6 _ hm
    · exact checked7_7 _ hm
  · decide +kernel
private def samples : Fin (2*K) → Fin 4 × Fin 4 := ![(0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (0, 0), (0, 2), (1, 0), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (0, 0), (0, 2), (1, 0), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (0, 0), (0, 2), (1, 0), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (0, 0), (0, 2), (1, 0), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (0, 0), (0, 2), (1, 0), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (0, 0), (0, 2), (1, 0), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)]

private def inputs (i : Fin (2*K)) :=
  PEqualNP.Represents.oneEach (samples i).1 (samples i).2

def graph (u v : Fin 4) := (4458 : ℕ).testBit (4 * u.val + v.val)

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧
    PEqualNP.Represents.Represents (fun u v : Fin 4 => (4458 : ℕ).testBit (4 * u.val + v.val)) C) := by
  rintro ⟨C,hg,hs,he⟩
  apply exclude C.gates C.output (fun g hm => hg g hm) ins ins (fun ⦃_⦄ h => h) 7 hs root
  intro k
  have hi : ∀ i : Fin (2*K), inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin (2*K), graph (samples i).1 (samples i).2 = bit i target := by decide +kernel
  have heval : C.eval (inputs k) = graph (samples k).1 (samples k).2 := he (samples k).1 (samples k).2
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using heval

def circuit : Circuit :=
  { gates := [⟨.or,[5,7]⟩, ⟨.and,[0,8]⟩, ⟨.or,[5,6]⟩, ⟨.and,[1,10]⟩,
              ⟨.or,[2,3]⟩, ⟨.and,[4,12]⟩, ⟨.or,[9,11]⟩, ⟨.or,[13,14]⟩], output := 15 }

theorem upper : PEqualNP.Represents.RepSizeAtMost graph 8 := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

theorem catalogue5555 : PEqualNP.Represents.RepSizeAtMost graph 8 ∧
    ¬ PEqualNP.Represents.RepSizeAtMost graph 7 := by
  refine ⟨upper,?_⟩
  rintro ⟨C,hm,hs,he⟩
  apply generalLower
  refine ⟨C,?_,hs,he⟩
  intro g hg
  obtain ⟨ho,ha⟩ := hm g hg
  change g.op = .and ∨ g.op = .or at ho
  exact ⟨ho.imp_right Or.inl,ha⟩

#print axioms generalLower
#print axioms upper
#print axioms catalogue5555
end Matrix4458
