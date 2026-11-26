import PEqualNP.Defs.Represents

-- The gate semantics and safety induction adapt the Apache-2.0 proof credited in Mask53Exact.lean.
-- Lewis Watson and Nico Habets developed the earlier gate enumeration.
-- Here the twenty-one table entries are all singleton and pair inputs on six pins.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace Graph781

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev K := 80
private abbrev T := BitVec (2*K)
private def ins : List T := [(((((((((0x70007 : T) <<< 32) ||| 0x70007) <<< 32) ||| 0x70000) <<< 32) ||| 0xffff) <<< 32) ||| 0xffffffff), (((((((((0x390039 : T) <<< 32) ||| 0x390039) <<< 32) ||| 0x39ffff) <<< 32) ||| 0xffff0000) <<< 32) ||| 0x0), (((((((((0x3c003c0 : T) <<< 32) ||| 0x3c003c0) <<< 32) ||| 0x3c00000) <<< 32) ||| 0xffff0000) <<< 32) ||| 0xffff0000), (((((((((0x1c801c80 : T) <<< 32) ||| 0x1c801c80) <<< 32) ||| 0x1c80ffff) <<< 32) ||| 0xffff) <<< 32) ||| 0x0), (((((((((0x69126912 : T) <<< 32) ||| 0x69126912) <<< 32) ||| 0x69120000) <<< 32) ||| 0x0) <<< 32) ||| 0x0), (((((((((0xd224d224 : T) <<< 32) ||| 0xd224d224) <<< 32) ||| 0xd2240000) <<< 32) ||| 0x0) <<< 32) ||| 0x0)]
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
private def wire63 : T := (((((((((0x70007 : T) <<< 32) ||| 0x70007) <<< 32) ||| 0x70000) <<< 32) ||| 0xffff) <<< 32) ||| 0xffffffff)
private def wire1986 : T := (((((((((0x390039 : T) <<< 32) ||| 0x390039) <<< 32) ||| 0x39ffff) <<< 32) ||| 0xffff0000) <<< 32) ||| 0x0)
private def wire30852 : T := (((((((((0x3c003c0 : T) <<< 32) ||| 0x3c003c0) <<< 32) ||| 0x3c00000) <<< 32) ||| 0xffff0000) <<< 32) ||| 0xffff0000)
private def wire233736 : T := (((((((((0x1c801c80 : T) <<< 32) ||| 0x1c801c80) <<< 32) ||| 0x1c80ffff) <<< 32) ||| 0xffff) <<< 32) ||| 0x0)
private def wire260492 : T := (((((((((0x1fc01fc0 : T) <<< 32) ||| 0x1fc01fc0) <<< 32) ||| 0x1fc0ffff) <<< 32) ||| 0xffffffff) <<< 32) ||| 0xffff0000)
private def wire860688 : T := (((((((((0x69126912 : T) <<< 32) ||| 0x69126912) <<< 32) ||| 0x69120000) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire1721376 : T := (((((((((0xd224d224 : T) <<< 32) ||| 0xd224d224) <<< 32) ||| 0xd2240000) <<< 32) ||| 0x0) <<< 32) ||| 0x0)
private def wire2057776 : T := (((((((((0xfb36fb36 : T) <<< 32) ||| 0xfb36fb36) <<< 32) ||| 0xfb360000) <<< 32) ||| 0x0) <<< 32) ||| 0x0)

-- Every listed set is checked against every possible next output and every reuse of its inputs.
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private def layer3 : List (List T) := []
private theorem good3 (w : List T) (h : w ∈ layer3) : ¬ Need 3 w.toFinset := by simp [layer3] at h
private def chunk4_0 : List (List T) := [[wire63,wire1986,wire260492,wire2057776]]
private def pool4_0 : List (List (List T)) := []
private theorem checked4_0 : ∀ w ∈ chunk4_0, ¬ Need 4 w.toFinset := by
  have h : chunk4_0.all (routes 3 pool4_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  simp [pool4_0] at hv
#print axioms checked4_0
private def chunk5_0 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire2057776],
  [wire63,wire1986,wire260492,wire860688,wire1721376]]
private def pool5_0 : List (List (List T)) := [chunk4_0]
private theorem checked5_0 : ∀ w ∈ chunk5_0, ¬ Need 5 w.toFinset := by
  have h : chunk5_0.all (routes 4 pool5_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool5_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked4_0 _ hm
#print axioms checked5_0
private def chunk6_0 : List (List T) := [[wire63,wire1986,wire30852,wire233736,wire860688,wire1721376]]
private def pool6_0 : List (List (List T)) := [chunk5_0]
private theorem checked6_0 : ∀ w ∈ chunk6_0, ¬ Need 6 w.toFinset := by
  have h : chunk6_0.all (routes 5 pool6_0.flatten) = true := by decide +kernel
  intro w hw
  apply route_sound _ ((List.all_eq_true.mp h) w hw)
  intro v hv
  obtain ⟨g,hg,hm⟩ := List.mem_flatten.mp hv
  simp only [pool6_0,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl
  · exact checked5_0 _ hm
#print axioms checked6_0
private theorem root : safe 6 ins := initial checked6_0 (by decide +kernel)
private def samples : Fin (2*K) → Fin 6 × Fin 6 := ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (0, 1), (0, 4), (0, 5), (1, 1), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (0, 1), (0, 4), (0, 5), (1, 1), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (0, 1), (0, 4), (0, 5), (1, 1), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (0, 1), (0, 4), (0, 5), (1, 1), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5), (0, 1), (0, 4), (0, 5), (1, 1), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
private def inputs (i : Fin (2*K)) :=
  List.ofFn fun k : Fin 6 => decide (k = (samples i).1 ∨ k = (samples i).2)

private theorem tables (C : Circuit)
    (he : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (781 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :
    ∀ k, (C.gates.foldl step (ins.map (bit k))).getD C.output false = bit k target := by
  intro k
  have hi : ∀ i : Fin (2*K), inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin (2*K), (781 : Nat).testBit
      (6 * min (samples i).1.val (samples i).2.val + max (samples i).1.val (samples i).2.val) = bit i target := by decide +kernel
  have h := he (samples k).1 (samples k).2
  change C.eval (inputs k) = _ at h
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using h

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (781 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hg,hs,he⟩
  exact exclude C.gates C.output (fun g hm => hg g hm) ins ins
    (fun ⦃_⦄ hx => hx) 6 hs root (tables C he)

#print axioms generalLower

-- Seven gates suffice on all 36 ordered input pairs.
def circuit : Circuit :=
  { gates := [⟨.or,[1,0]⟩, ⟨.or,[3,2]⟩, ⟨.or,[4,1]⟩, ⟨.or,[5,8]⟩,
              ⟨.not,[9]⟩, ⟨.or,[7,10]⟩, ⟨.and,[11,6]⟩], output := 12 }

theorem seven : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (781 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms seven
end Graph781
