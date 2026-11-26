import PEqualNP.Defs.Represents

-- The gate semantics and safety induction adapt the Apache-2.0 proof credited in Mask53Exact.lean.
-- Lewis Watson and Nico Habets developed the earlier gate enumeration.
-- On the fifteen singleton and pair inputs of pins 0 through 4, pin 5 is zero.
namespace Graph34087

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 15
private def ins : List T := [31, 482, 3652, 13448, 26896, 0]
private def target : T := 1351
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

private def absSep (x : T) (p q : Fin 15) : Prop := bit p x ≠ bit q x
private def down (x : T) (p q : Fin 15) : Prop := bit p x = true ∧ bit q x = false
private def covers (r : T → Fin 15 → Fin 15 → Prop) (s : Finset T) :=
  ∀ p q, down target p q → ∃ x ∈ s, r x p q

private theorem absFactors (g : Op) (p q) (h : absSep g.out p q) :
    ∃ x ∈ g.args, absSep x p q := by
  cases g
  case ones =>
    have ho : ∀ i : Fin 15, bit i (-1) = true := by decide +kernel
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
private def permit (directed : Bool) (x : T) (p : Fin 15) : T :=
  if bit p x then x else if directed then -1 else ~~~x

private def residue (d : Bool) (p : Fin 15) : List T → T
  | [] => ~~~target
  | x::xs => permit d x p &&& residue d p xs

private def rel : Bool → T → Fin 15 → Fin 15 → Prop
  | true => down
  | false => absSep

private theorem permit_bit (d x p q) : bit q (permit d x p) = true ↔ ¬ rel d x p q := by
  have ho : ∀ i : Fin 15, bit i (-1) = true := by decide +kernel
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
    decide (∀ p : Fin 15, bit p target = true →
      residue (decide (n < w.toFinset.card)) p w = 0)

private theorem fits {n w} (h : Need n w.toFinset) : viable n w = true := by
  obtain ⟨hc,ha,hd⟩ := bound h
  simp only [viable,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨hc,?_⟩
  intro p hp
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let q : Fin 15 := ⟨i,hi⟩
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
private def layer3 : List (List T) := []
private theorem good3 (w : List T) (h : w ∈ layer3) : ¬ Need 3 w.toFinset := by simp [layer3] at h
private def chunk4_0 : List (List T) := [[7,482,3652,13448,26896],
  [31,340,3652,13448],
  [31,482,1098,26896],
  [31,4070,13802,28500],
  [31,9536,13448,26896]]
private theorem checked4_0 : ∀ w ∈ chunk4_0, ¬ Need 4 w.toFinset := by
  have h : chunk4_0.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_1 : List (List T) := [[272,511,3679,13448],
  [480,3648,13448,26896],
  [482,615,3652,13448,26911],
  [482,615,3652,13471],
  [482,615,3652,13471,26896]]
private theorem checked4_1 : ∀ w ∈ chunk4_1, ¬ Need 4 w.toFinset := by
  have h : chunk4_1.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_2 : List (List T) := [[482,615,3652,26911],
  [482,3652,5856,32152],
  [482,3652,13471,32152],
  [482,3652,13471,32732],
  [482,3652,19296,32152]]
private theorem checked4_2 : ∀ w ∈ chunk4_2, ¬ Need 4 w.toFinset := by
  have h : chunk4_2.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_3 : List (List T) := [[482,3652,26911,32152],
  [482,3652,26911,32250],
  [482,3679,26911,32152],
  [482,13471,29115,32152],
  [482,26911,28500,32152]]
private theorem checked4_3 : ∀ w ∈ chunk4_3, ¬ Need 4 w.toFinset := by
  have h : chunk4_3.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_4 : List (List T) := [[482,26911,28511,32152],
  [482,26911,29115,32152],
  [511,1032,3679,26896],
  [511,3652,13471,32152],
  [511,3679,5871,13448]]
private theorem checked4_4 : ∀ w ∈ chunk4_4, ¬ Need 4 w.toFinset := by
  have h : chunk4_4.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_5 : List (List T) := [[511,3679,13448,26896],
  [511,3679,13448,32152],
  [511,3679,19319,26896],
  [511,3679,26896,32152],
  [511,13448,26896,29088]]
private theorem checked4_5 : ∀ w ∈ chunk4_5, ¬ Need 4 w.toFinset := by
  have h : chunk4_5.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunk4_6 : List (List T) := [[3652,13471,13802,32152],
  [3652,13471,13823,32152],
  [3652,13471,32152,32285],
  [3652,26911,32152,32285],
  [3679,13448,26896,32256]]
private theorem checked4_6 : ∀ w ∈ chunk4_6, ¬ Need 4 w.toFinset := by
  have h : chunk4_6.all (routes 3 layer3) = true := by decide +kernel
  intro w hw
  exact route_sound good3 ((List.all_eq_true.mp h) w hw)
private def chunks4 : List (List (List T)) := [chunk4_0, chunk4_1, chunk4_2, chunk4_3, chunk4_4, chunk4_5, chunk4_6]
private def layer4 := chunks4.flatten
private theorem good4 (w : List T) (hw : w ∈ layer4) : ¬ Need 4 w.toFinset := by
  obtain ⟨c,h,hc⟩ := List.mem_flatten.mp hw
  simp only [chunks4,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked4_0 _ hc
  · exact checked4_1 _ hc
  · exact checked4_2 _ hc
  · exact checked4_3 _ hc
  · exact checked4_4 _ hc
  · exact checked4_5 _ hc
  · exact checked4_6 _ hc
private def chunk5_0 : List (List T) := [[0,482,3652,13471,32152],
  [0,482,3652,26911,32152],
  [0,511,3679,13448,26896],
  [6,482,3652,13448,26896],
  [15,482,3652,5871,13448]]
private theorem checked5_0 : ∀ w ∈ chunk5_0, ¬ Need 5 w.toFinset := by
  have h : chunk5_0.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_1 : List (List T) := [[15,482,3652,13448,26896],
  [23,482,3652,13448,26896],
  [23,482,3652,19319,26896],
  [31,272,482,3652,13448],
  [31,272,511,3652,13448]]
private theorem checked5_1 : ∀ w ∈ chunk5_1, ¬ Need 5 w.toFinset := by
  have h : chunk5_1.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_2 : List (List T) := [[31,320,3652,13448,26896],
  [31,320,3652,13448,28500],
  [31,320,13448,26896,28500],
  [31,354,3652,13448,26896],
  [31,354,3652,19319,26896]]
private theorem checked5_2 : ∀ w ∈ chunk5_2, ¬ Need 5 w.toFinset := by
  have h : chunk5_2.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_3 : List (List T) := [[31,480,3652,13448,26896],
  [31,482,615,3652,13448],
  [31,482,615,3652,13448,26896],
  [31,482,615,3652,26896],
  [31,482,1032,3652,26896]]
private theorem checked5_3 : ∀ w ∈ chunk5_3, ¬ Need 5 w.toFinset := by
  have h : chunk5_3.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_4 : List (List T) := [[31,482,1032,3679,26896],
  [31,482,1088,13448,26896],
  [31,482,1088,13802,26896],
  [31,482,1604,5871,13448],
  [31,482,1604,13448,26896]]
private theorem checked5_4 : ∀ w ∈ chunk5_4, ¬ Need 5 w.toFinset := by
  have h : chunk5_4.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_5 : List (List T) := [[31,482,3648,13448,26896],
  [31,482,3652,4267,13448],
  [31,482,3652,5256,5871],
  [31,482,3652,5256,26896],
  [31,482,3652,5871,13448]]
private theorem checked5_5 : ∀ w ∈ chunk5_5, ¬ Need 5 w.toFinset := by
  have h : chunk5_5.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_6 : List (List T) := [[31,482,3652,5871,13802],
  [31,482,3652,5871,19319],
  [31,482,3652,5871,32152],
  [31,482,3652,7919,13448],
  [31,482,3652,13320,26896]]
private theorem checked5_6 : ∀ w ∈ chunk5_6, ¬ Need 5 w.toFinset := by
  have h : chunk5_6.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_7 : List (List T) := [[31,482,3652,13448,14063],
  [31,482,3652,13448,18704],
  [31,482,3652,13448,24848],
  [31,482,3652,13448,26896],
  [31,482,3652,13448,26898]]
private theorem checked5_7 : ∀ w ∈ chunk5_7, ¬ Need 5 w.toFinset := by
  have h : chunk5_7.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_8 : List (List T) := [[31,482,3652,13448,26900],
  [31,482,3652,13448,26904],
  [31,482,3652,13448,26960],
  [31,482,3652,13448,27024],
  [31,482,3652,13448,27920]]
private theorem checked5_8 : ∀ w ∈ chunk5_8, ¬ Need 5 w.toFinset := by
  have h : chunk5_8.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_9 : List (List T) := [[31,482,3652,13448,28500],
  [31,482,3652,13448,32152],
  [31,482,3652,13448,32732],
  [31,482,3652,13450,26896],
  [31,482,3652,13452,26896]]
private theorem checked5_9 : ∀ w ∈ chunk5_9, ¬ Need 5 w.toFinset := by
  have h : chunk5_9.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_10 : List (List T) := [[31,482,3652,13464,26896],
  [31,482,3652,13471,32152],
  [31,482,3652,13512,26896],
  [31,482,3652,13704,26896],
  [31,482,3652,13802,26896]]
private theorem checked5_10 : ∀ w ∈ chunk5_10, ¬ Need 5 w.toFinset := by
  have h : chunk5_10.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_11 : List (List T) := [[31,482,3652,13802,28500],
  [31,482,3652,15496,26896],
  [31,482,3652,18704,19319],
  [31,482,3652,18965,26896],
  [31,482,3652,19319,26896]]
private theorem checked5_11 : ∀ w ∈ chunk5_11, ¬ Need 5 w.toFinset := by
  have h : chunk5_11.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_12 : List (List T) := [[31,482,3652,19319,28500],
  [31,482,3652,19319,32152],
  [31,482,3652,19447,26896],
  [31,482,3652,26896,27511],
  [31,482,3652,26896,32152]]
private theorem checked5_12 : ∀ w ∈ chunk5_12, ¬ Need 5 w.toFinset := by
  have h : chunk5_12.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_13 : List (List T) := [[31,482,3652,26896,32250],
  [31,482,3652,26911,32152],
  [31,482,3654,13448,26896],
  [31,482,3660,13448,26896],
  [31,482,3668,13448,26896]]
private theorem checked5_13 : ∀ w ∈ chunk5_13, ¬ Need 5 w.toFinset := by
  have h : chunk5_13.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_14 : List (List T) := [[31,482,3679,5871,13448],
  [31,482,3679,13448,26896],
  [31,482,3679,13448,32152],
  [31,482,3679,13802,26896],
  [31,482,3679,19319,26896]]
private theorem checked5_14 : ∀ w ∈ chunk5_14, ¬ Need 5 w.toFinset := by
  have h : chunk5_14.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_15 : List (List T) := [[31,482,3679,26896,32152],
  [31,482,3780,13448,26896],
  [31,482,3908,13448,26896],
  [31,482,4070,13448,28500],
  [31,482,4267,13448,26896]]
private theorem checked5_15 : ∀ w ∈ chunk5_15, ¬ Need 5 w.toFinset := by
  have h : chunk5_15.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_16 : List (List T) := [[31,482,5871,13448,28500],
  [31,482,5871,13448,29115],
  [31,482,11844,13448,26896],
  [31,482,13448,24848,29115],
  [31,482,13448,26896,28500]]
private theorem checked5_16 : ∀ w ∈ chunk5_16, ¬ Need 5 w.toFinset := by
  have h : chunk5_16.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_17 : List (List T) := [[31,482,13448,26896,28511],
  [31,482,13448,26896,29088],
  [31,482,13448,26896,29115],
  [31,482,13448,26896,29119],
  [31,482,13448,26896,31163]]
private theorem checked5_17 : ∀ w ∈ chunk5_17, ¬ Need 5 w.toFinset := by
  have h : chunk5_17.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_18 : List (List T) := [[31,482,13448,27122,28500],
  [31,482,13448,28500,29115],
  [31,482,13448,29115,32152],
  [31,482,13802,26896,28500],
  [31,482,13802,26896,29115]]
private theorem checked5_18 : ∀ w ∈ chunk5_18, ¬ Need 5 w.toFinset := by
  have h : chunk5_18.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_19 : List (List T) := [[31,482,19319,26896,28500],
  [31,482,19319,26896,29115],
  [31,482,26896,28500,32152],
  [31,482,26896,29115,32152],
  [31,486,3652,13448,26896]]
private theorem checked5_19 : ∀ w ∈ chunk5_19, ¬ Need 5 w.toFinset := by
  have h : chunk5_19.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_20 : List (List T) := [[31,490,3652,13448,26896],
  [31,498,3652,13448,26896],
  [31,511,3652,5871,13448],
  [31,511,3652,13448,26896],
  [31,511,3652,13448,28500]]
private theorem checked5_20 : ∀ w ∈ chunk5_20, ¬ Need 5 w.toFinset := by
  have h : chunk5_20.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_21 : List (List T) := [[31,511,3652,13448,32152],
  [31,511,3652,19319,26896],
  [31,511,3652,26896,32152],
  [31,511,3679,13448,26896],
  [31,511,13448,26896,28500]]
private theorem checked5_21 : ∀ w ∈ chunk5_21, ¬ Need 5 w.toFinset := by
  have h : chunk5_21.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_22 : List (List T) := [[31,511,13448,26896,29115],
  [31,1088,13448,13802,26896],
  [31,1506,3652,13448,26896],
  [31,2530,3652,13448,26896],
  [31,3652,4070,13802,26896]]
private theorem checked5_22 : ∀ w ∈ chunk5_22, ¬ Need 5 w.toFinset := by
  have h : chunk5_22.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_23 : List (List T) := [[31,3652,5871,13448,13802],
  [31,3652,5871,13448,32285],
  [31,3652,8674,13448,26896],
  [31,3652,13320,26896,32285],
  [31,3652,13448,13802,26896]]
private theorem checked5_23 : ∀ w ∈ chunk5_23, ¬ Need 5 w.toFinset := by
  have h : chunk5_23.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_24 : List (List T) := [[31,3652,13448,13802,28500],
  [31,3652,13448,13802,32152],
  [31,3652,13448,13823,26896],
  [31,3652,13448,18965,26896],
  [31,3652,13448,26896,32256]]
private theorem checked5_24 : ∀ w ∈ chunk5_24, ¬ Need 5 w.toFinset := by
  have h : chunk5_24.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_25 : List (List T) := [[31,3652,13448,26896,32285],
  [31,3652,13448,26896,32287],
  [31,3652,13448,26896,32413],
  [31,3652,13448,28500,32285],
  [31,3652,13448,32152,32285]]
private theorem checked5_25 : ∀ w ∈ chunk5_25, ¬ Need 5 w.toFinset := by
  have h : chunk5_25.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_26 : List (List T) := [[31,3652,13802,16076,26896],
  [31,3652,13802,19319,26896],
  [31,3652,13802,26896,32285],
  [31,3652,19319,26896,32285],
  [31,3652,26896,32152,32285]]
private theorem checked5_26 : ∀ w ∈ chunk5_26, ¬ Need 5 w.toFinset := by
  have h : chunk5_26.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_27 : List (List T) := [[31,3679,13448,13802,26896],
  [31,3679,13448,26896,32285],
  [31,13448,13802,26896,28500],
  [31,13448,13802,26896,29115],
  [31,13448,26896,28500,32285]]
private theorem checked5_27 : ∀ w ∈ chunk5_27, ¬ Need 5 w.toFinset := by
  have h : chunk5_27.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_28 : List (List T) := [[31,13448,26896,29115,32285],
  [95,482,3652,13448,26896],
  [159,482,3652,13448,26896],
  [287,482,3652,13448,26896],
  [480,3652,13448,26896,32736]]
private theorem checked5_28 : ∀ w ∈ chunk5_28, ¬ Need 5 w.toFinset := by
  have h : chunk5_28.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_29 : List (List T) := [[482,511,3679,13448,26896],
  [482,1055,3652,13448,26896],
  [482,2079,3652,13448,26896],
  [482,3648,13448,26896,32736],
  [482,3652,5856,13448,26896]]
private theorem checked5_29 : ∀ w ∈ chunk5_29, ¬ Need 5 w.toFinset := by
  have h : chunk5_29.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_30 : List (List T) := [[482,3652,5871,13448,13471],
  [482,3652,5871,13448,26911],
  [482,3652,5871,13448,32736],
  [482,3652,8223,13448,26896],
  [482,3652,13448,13471,26896]]
private theorem checked5_30 : ∀ w ∈ chunk5_30, ¬ Need 5 w.toFinset := by
  have h : chunk5_30.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_31 : List (List T) := [[482,3652,13448,13471,28500],
  [482,3652,13448,13471,32152],
  [482,3652,13448,19296,26896],
  [482,3652,13448,26896,26911],
  [482,3652,13448,26896,32159]]
private theorem checked5_31 : ∀ w ∈ chunk5_31, ¬ Need 5 w.toFinset := by
  have h : chunk5_31.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_32 : List (List T) := [[482,3652,13448,26896,32736],
  [482,3652,13448,26896,32744],
  [482,3652,13448,26896,32752],
  [482,3652,13448,26911,27122],
  [482,3652,13448,26911,32152]]
private theorem checked5_32 : ∀ w ∈ chunk5_32, ¬ Need 5 w.toFinset := by
  have h : chunk5_32.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_33 : List (List T) := [[482,3652,13448,28500,32736],
  [482,3652,13448,32152,32159],
  [482,3652,13448,32152,32736],
  [482,3652,13471,16076,26896],
  [482,3652,13471,19319,26896]]
private theorem checked5_33 : ∀ w ∈ chunk5_33, ¬ Need 5 w.toFinset := by
  have h : chunk5_33.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_34 : List (List T) := [[482,3652,13471,26896,32152],
  [482,3652,13471,32152],
  [482,3652,13802,26896,26911],
  [482,3652,13802,26896,32736],
  [482,3652,19319,26896,26911]]
private theorem checked5_34 : ∀ w ∈ chunk5_34, ¬ Need 5 w.toFinset := by
  have h : chunk5_34.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_35 : List (List T) := [[482,3652,19319,26896,32736],
  [482,3652,26896,26911,32152],
  [482,3652,26896,32152,32159],
  [482,3652,26896,32152,32736],
  [482,3652,26911,32152]]
private theorem checked5_35 : ∀ w ∈ chunk5_35, ¬ Need 5 w.toFinset := by
  have h : chunk5_35.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_36 : List (List T) := [[482,3679,13448,26896,26911],
  [482,3679,13448,26896,32736],
  [482,13448,13471,26896,28500],
  [482,13448,13471,26896,29115],
  [482,13448,26896,26911,28500]]
private theorem checked5_36 : ∀ w ∈ chunk5_36, ¬ Need 5 w.toFinset := by
  have h : chunk5_36.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_37 : List (List T) := [[482,13448,26896,26911,28511],
  [482,13448,26896,26911,29115],
  [482,13448,26896,28500,32736],
  [482,13448,26896,29115,32736],
  [511,3652,3679,13448,26896]]
private theorem checked5_37 : ∀ w ∈ chunk5_37, ¬ Need 5 w.toFinset := by
  have h : chunk5_37.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_38 : List (List T) := [[511,3652,13448,13471,26896],
  [511,3652,13448,26896,32736],
  [511,3679,13448,26896],
  [3652,13448,13471,13802,26896],
  [3652,13448,13471,13823,26896]]
private theorem checked5_38 : ∀ w ∈ chunk5_38, ¬ Need 5 w.toFinset := by
  have h : chunk5_38.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunk5_39 : List (List T) := [[3652,13448,13471,26896,32285],
  [3652,13448,13802,26896,26911],
  [3652,13448,13802,26896,32736],
  [3652,13448,26896,26911,32285],
  [3652,13448,26896,32285,32736]]
private theorem checked5_39 : ∀ w ∈ chunk5_39, ¬ Need 5 w.toFinset := by
  have h : chunk5_39.all (routes 4 layer4) = true := by decide +kernel
  intro w hw
  exact route_sound good4 ((List.all_eq_true.mp h) w hw)
private def chunks5 : List (List (List T)) := [chunk5_0, chunk5_1, chunk5_2, chunk5_3, chunk5_4, chunk5_5, chunk5_6, chunk5_7, chunk5_8, chunk5_9, chunk5_10, chunk5_11, chunk5_12, chunk5_13, chunk5_14, chunk5_15, chunk5_16, chunk5_17, chunk5_18, chunk5_19, chunk5_20, chunk5_21, chunk5_22, chunk5_23, chunk5_24, chunk5_25, chunk5_26, chunk5_27, chunk5_28, chunk5_29, chunk5_30, chunk5_31, chunk5_32, chunk5_33, chunk5_34, chunk5_35, chunk5_36, chunk5_37, chunk5_38, chunk5_39]
private def layer5 := chunks5.flatten
private theorem good5 (w : List T) (hw : w ∈ layer5) : ¬ Need 5 w.toFinset := by
  obtain ⟨c,h,hc⟩ := List.mem_flatten.mp hw
  simp only [chunks5,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact checked5_16 _ hc
  · exact checked5_17 _ hc
  · exact checked5_18 _ hc
  · exact checked5_19 _ hc
  · exact checked5_20 _ hc
  · exact checked5_21 _ hc
  · exact checked5_22 _ hc
  · exact checked5_23 _ hc
  · exact checked5_24 _ hc
  · exact checked5_25 _ hc
  · exact checked5_26 _ hc
  · exact checked5_27 _ hc
  · exact checked5_28 _ hc
  · exact checked5_29 _ hc
  · exact checked5_30 _ hc
  · exact checked5_31 _ hc
  · exact checked5_32 _ hc
  · exact checked5_33 _ hc
  · exact checked5_34 _ hc
  · exact checked5_35 _ hc
  · exact checked5_36 _ hc
  · exact checked5_37 _ hc
  · exact checked5_38 _ hc
  · exact checked5_39 _ hc
private def chunk6_0 : List (List T) := [[0,31,482,3652,5871,13448],
  [0,31,482,3652,13448,26896],
  [0,31,482,3652,13448,28500],
  [0,31,482,3652,13448,32152],
  [0,31,482,3652,13802,26896]]
private theorem checked6_0 : ∀ w ∈ chunk6_0, ¬ Need 6 w.toFinset := by
  have h : chunk6_0.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_1 : List (List T) := [[0,31,482,3652,19319,26896],
  [0,31,482,3652,26896,32152],
  [0,31,482,3679,13448,26896],
  [0,31,482,13448,26896,28500],
  [0,31,482,13448,26896,29115]]
private theorem checked6_1 : ∀ w ∈ chunk6_1, ¬ Need 6 w.toFinset := by
  have h : chunk6_1.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_2 : List (List T) := [[0,31,511,3652,13448,26896],
  [0,31,3652,13448,13802,26896],
  [0,31,3652,13448,26896,32285],
  [0,482,3652,13448,13471,26896],
  [0,482,3652,13448,26896,26911]]
private theorem checked6_2 : ∀ w ∈ chunk6_2, ¬ Need 6 w.toFinset := by
  have h : chunk6_2.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_3 : List (List T) := [[0,482,3652,13448,26896,32736],
  [2,31,482,3652,13448,26896],
  [4,31,482,3652,13448,26896],
  [8,31,482,3652,13448,26896],
  [16,31,482,3652,13448,26896]]
private theorem checked6_3 : ∀ w ∈ chunk6_3, ¬ Need 6 w.toFinset := by
  have h : chunk6_3.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_4 : List (List T) := [[31,64,482,3652,13448,26896],
  [31,128,482,3652,13448,26896],
  [31,256,482,3652,13448,26896],
  [31,482,511,3652,13448,26896],
  [31,482,1024,3652,13448,26896]]
private theorem checked6_4 : ∀ w ∈ chunk6_4, ¬ Need 6 w.toFinset := by
  have h : chunk6_4.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_5 : List (List T) := [[31,482,2048,3652,13448,26896],
  [31,482,3652,3679,13448,26896],
  [31,482,3652,4070,13448,26896],
  [31,482,3652,5871,13448],
  [31,482,3652,5871,13448,26896]]
private theorem checked6_5 : ∀ w ∈ chunk6_5, ¬ Need 6 w.toFinset := by
  have h : chunk6_5.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_6 : List (List T) := [[31,482,3652,8192,13448,26896],
  [31,482,3652,13448,13471,26896],
  [31,482,3652,13448,13802,26896],
  [31,482,3652,13448,16076,26896],
  [31,482,3652,13448,19319,26896]]
private theorem checked6_6 : ∀ w ∈ chunk6_6, ¬ Need 6 w.toFinset := by
  have h : chunk6_6.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_7 : List (List T) := [[31,482,3652,13448,26896],
  [31,482,3652,13448,26896,26911],
  [31,482,3652,13448,26896,27122],
  [31,482,3652,13448,26896,28500],
  [31,482,3652,13448,26896,29115]]
private theorem checked6_7 : ∀ w ∈ chunk6_7, ¬ Need 6 w.toFinset := by
  have h : chunk6_7.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_8 : List (List T) := [[31,482,3652,13448,26896,32152],
  [31,482,3652,13448,26896,32285],
  [31,482,3652,13448,26896,32736],
  [31,482,3652,13448,26896,32767],
  [31,482,3652,13448,28500]]
private theorem checked6_8 : ∀ w ∈ chunk6_8, ¬ Need 6 w.toFinset := by
  have h : chunk6_8.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_9 : List (List T) := [[31,482,3652,13448,32152],
  [31,482,3652,13802,26896],
  [31,482,3652,19319,26896],
  [31,482,3652,26896,32152],
  [31,482,3679,13448,26896]]
private theorem checked6_9 : ∀ w ∈ chunk6_9, ¬ Need 6 w.toFinset := by
  have h : chunk6_9.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_10 : List (List T) := [[31,482,13448,26896,28500],
  [31,482,13448,26896,29115],
  [31,511,3652,13448,26896],
  [31,3652,13448,13802,26896],
  [31,3652,13448,26896,32285]]
private theorem checked6_10 : ∀ w ∈ chunk6_10, ¬ Need 6 w.toFinset := by
  have h : chunk6_10.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunk6_11 : List (List T) := [[482,3652,13448,13471,26896],
  [482,3652,13448,26896,26911],
  [482,3652,13448,26896,32736]]
private theorem checked6_11 : ∀ w ∈ chunk6_11, ¬ Need 6 w.toFinset := by
  have h : chunk6_11.all (routes 5 layer5) = true := by decide +kernel
  intro w hw
  exact route_sound good5 ((List.all_eq_true.mp h) w hw)
private def chunks6 : List (List (List T)) := [chunk6_0, chunk6_1, chunk6_2, chunk6_3, chunk6_4, chunk6_5, chunk6_6, chunk6_7, chunk6_8, chunk6_9, chunk6_10, chunk6_11]
private def layer6 := chunks6.flatten
private theorem good6 (w : List T) (hw : w ∈ layer6) : ¬ Need 6 w.toFinset := by
  obtain ⟨c,h,hc⟩ := List.mem_flatten.mp hw
  simp only [chunks6,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked6_0 _ hc
  · exact checked6_1 _ hc
  · exact checked6_2 _ hc
  · exact checked6_3 _ hc
  · exact checked6_4 _ hc
  · exact checked6_5 _ hc
  · exact checked6_6 _ hc
  · exact checked6_7 _ hc
  · exact checked6_8 _ hc
  · exact checked6_9 _ hc
  · exact checked6_10 _ hc
  · exact checked6_11 _ hc
private def chunk7_0 : List (List T) := [[0,31,482,3652,13448,26896],
  [31,482,3652,13448,26896]]
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
private def samples : Fin 15 → Fin 6 × Fin 6 := ![(0,0), (0,1), (0,2), (0,3), (0,4), (1,1), (1,2), (1,3), (1,4), (2,2), (2,3), (2,4), (3,3), (3,4), (4,4)]
private def inputs (i : Fin 15) :=
  List.ofFn fun k : Fin 6 => decide (k = (samples i).1 ∨ k = (samples i).2)

private theorem tables (C : Circuit)
    (he : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (34087 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :
    ∀ k, (C.gates.foldl step (ins.map (bit k))).getD C.output false = bit k target := by
  intro k
  have hi : ∀ i : Fin 15, inputs i = ins.map (bit i) := by decide +kernel
  have ht : ∀ i : Fin 15, (34087 : Nat).testBit
      (6 * min (samples i).1.val (samples i).2.val + max (samples i).1.val (samples i).2.val) = bit i target := by decide +kernel
  have h := he (samples k).1 (samples k).2
  change C.eval (inputs k) = _ at h
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using h

theorem generalLower : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34087 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C,hg,hs,he⟩
  exact exclude C.gates C.output (fun g hm => hg g hm) ins ins
    (fun ⦃_⦄ hx => hx) 7 hs root (tables C he)

#print axioms generalLower

-- An eight-gate circuit directly solves catalogue claim L-meta-22573.
def circuit : Circuit :=
  { gates := [⟨.or,[0,3]⟩, ⟨.or,[2,4]⟩, ⟨.and,[1,7]⟩, ⟨.or,[3,7]⟩,
              ⟨.not,[9]⟩, ⟨.or,[2,10]⟩, ⟨.and,[6,11]⟩, ⟨.or,[8,12]⟩], output := 13 }

theorem catalogue22573 : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (34087 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit,?_,?_,?_⟩
  · intro g hg
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel

#print axioms catalogue22573
end Graph34087
