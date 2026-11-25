import OneShorePairRank

namespace OneShoreSetRank
open FlagCrossRank
open OneShorePairRank (Label physical rawRank splitLeaves)
open scoped BigOperators

variable {P L H : Type} (I : P → L → Prop) (S : H → Finset P) (f : H → P → P)

-- At each occurrence of a point in a helper's support, select one other
-- point. The selection can depend on the matching we want to charge.
def mates (p q : P) : Prop := ∃ h, p ∈ S h ∧ f h p = q

def kept (p : P) (l : L) : Prop := I p l ∧ ∀ q, mates S f p q → ¬ I q l

def posPart (p : P) (l : L) (q : P) : Prop :=
  (q ≠ p ∧ kept I S f q l) ∨ mates S f p q
def linePart (p : P) (l k : L) : Prop := k ≠ l ∧ kept I S f p k

-- The negative cross uses the other retained neighbors on both shores,
-- together with every partner of the selected point.
theorem crossIndependent
    (free : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k)
    {p q : P} {l k : L} (e : kept I S f p l)
    (hq : posPart I S f p l q) (hk : linePart I S f p l k) : ¬ I q k := by
  rcases hq with ⟨ne,edge⟩ | mate
  · exact free p q l k ne.symm hk.1.symm e.1 edge.1 hk.2.1
  · exact hk.2.2 q mate

def values (X : P → Prop) (Y : L → Prop) : Label P L H → Prop :=
  Sum.elim X (Sum.elim Y (fun h => ∃ q ∈ S h, X q))

theorem sharedCovered (D : H → Finset P)
    (hitMate : ∀ h p, p ∈ S h → ∃ q ∈ S h, mates D f p q)
    {a p : P} {b l : L} (row : kept I D f a b) (touch : a = p ∨ b = l)
    (h : H) (hit : ∃ q ∈ S h, q = a) : ∃ q ∈ S h, posPart I D f p l q := by
  obtain ⟨q,ha,eq₀⟩ := hit
  subst q
  by_cases eq : a = p
  · subst a
    obtain ⟨q,hq,mate⟩ := hitMate h p ha
    exact ⟨q,hq,Or.inr mate⟩
  · obtain rfl := touch.resolve_left eq
    exact ⟨a, ha, Or.inl ⟨eq,row⟩⟩

noncomputable def bits (X : P → Prop) (Y : L → Prop) : Label P L H → Bool := by
  classical
  exact fun w => decide (values S X Y w)

theorem bitsOn {X : P → Prop} {Y : L → Prop} {w : Label P L H} :
    bits S X Y w = true ↔ values S X Y w := by classical simp [bits]

theorem bitsOff {X : P → Prop} {Y : L → Prop} {w : Label P L H} :
    bits S X Y w = false ↔ ¬ values S X Y w := by classical simp [bits]

abbrev retained := FlagCrossRank.Flag (kept I S f)
def left (e : retained I S f) : Label P L H := .inl e.val.1
def right (e : retained I S f) : Label P L H := .inr (.inl e.val.2)


theorem rawRetained (D : H → Finset P) [Fintype P] [Fintype L] [Fintype H] [DecidableEq P] [DecidableEq L]
    [DecidableEq H] [DecidableRel (kept I D f)]
    (hitMate : ∀ h p, p ∈ S h → ∃ q ∈ S h, mates D f p q)
    (free : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k)
    (T : FlagCrossRank.Tree (Label P L H))
    (correct : ∀ X Y, T.val (bits S X Y) = true ↔ ∃ p l, I p l ∧ X p ∧ Y l)
    (n : Nat) (cover : ∀ K : Finset (Label P L H),
      (∀ e : retained I D f, left I D f e ∈ K ∨ right I D f e ∈ K) → n ≤ K.card) :
    Fintype.card (retained I D f) + n ≤ T.cost (fun w => if physical w then 1 else 0) := by
  classical
  let N := {t : (P → Prop) × (L → Prop) // ∀ q k, t.1 q → t.2 k → ¬ I q k}
  let cx (e : retained I D f) : N := ⟨(posPart I D f e.val.1 e.val.2,
    linePart I D f e.val.1 e.val.2), fun _ _ x y => crossIndependent I D f free e.property x y⟩
  let pos (e : retained I D f) := bits S (fun q => q = e.val.1) (fun k => k = e.val.2)
  let neg (c : N) := bits S c.val.1 c.val.2
  have rawOnly (a b : retained I D f) (touch : a.val.1 = b.val.1 ∨ a.val.2 = b.val.2)
      (w : Label P L H) (on : pos a w = true) (off : neg (cx b) w = false) :
      w = left I D f a ∨ w = right I D f a := by
    have yes := (bitsOn S).mp on
    have no := (bitsOff S).mp off
    rcases w with q | (k | h)
    · exact Or.inl (congrArg Sum.inl yes)
    · exact Or.inr (congrArg (fun k : L => (Sum.inr (Sum.inl k) : Label P L H)) yes)
    · exact False.elim (no (sharedCovered I S f D hitMate a.property touch h yes))
  apply rawRank T physical (left I D f) (right I D f) pos neg cx ?_ ?_
    (fun _ => ⟨rfl,rfl⟩) (fun _ => Sum.inl_ne_inr) ?_ ?_ ?_ n cover
  · intro e
    exact (correct _ _).2 ⟨e.val.1, e.val.2, e.property.1, rfl, rfl⟩
  · intro c
    cases hh : T.val (neg c) with
    | false => rfl
    | true =>
      obtain ⟨q,k,edge,hq,hk⟩ := (correct _ _).1 hh
      exact (c.property q k hq hk edge).elim
  · intro e w
    exact rawOnly e e (Or.inl rfl) w
  · rintro a b z w ne (rfl | rfl) (same | same) on off
    · have eq : a.val.1 = b.val.1 := Sum.inl.inj same
      have dif : a.val.2 ≠ b.val.2 := fun h => ne (Subtype.ext (Prod.ext eq h))
      rcases rawOnly a b (Or.inl eq) w on off with done | replace
      · exact done
      · subst w
        exact False.elim ((bitsOff S).mp off ⟨dif, eq ▸ a.property⟩)
    · exact (Sum.inl_ne_inr same).elim
    · exact (Sum.inr_ne_inl same).elim
    · have eq : a.val.2 = b.val.2 := Sum.inl.inj (Sum.inr.inj same)
      have dif : a.val.1 ≠ b.val.1 := fun h => ne (Subtype.ext (Prod.ext h eq))
      rcases rawOnly a b (Or.inr eq) w on off with replace | done
      · subst w
        exact False.elim ((bitsOff S).mp off (Or.inl ⟨dif, eq ▸ a.property⟩))
      · exact done
  · rintro e z (rfl | rfl)
    · let c : N := ⟨(mates D f e.val.1, fun k => k = e.val.2), by
        intro q k hq hk
        subst k
        exact e.property.2 q hq⟩
      refine ⟨c, ?_⟩
      intro w on off
      have yes := (bitsOn S).mp on
      have no := (bitsOff S).mp off
      rcases w with q | (k | h)
      · exact congrArg Sum.inl yes
      · exact False.elim (no yes)
      · obtain ⟨a,ha,eq⟩ := yes
        subst a
        obtain ⟨q,hq,mate⟩ := hitMate h _ ha
        exact False.elim (no ⟨q,hq,mate⟩)
    · let c : N := ⟨(fun q => q = e.val.1, fun _ => False), by simp⟩
      refine ⟨c, ?_⟩
      intro w on off
      have yes := (bitsOn S).mp on
      have no := (bitsOff S).mp off
      rcases w with q | (k | h)
      · exact False.elim (no yes)
      · exact congrArg (fun k : L => (Sum.inr (Sum.inl k) : Label P L H)) yes
      · exact False.elim (no yes)




abbrev Free := ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k

-- A safe partner avoids every matched line of the selected point. When a
-- safe partner exists we always take one, independently at each occurrence.
theorem selectPartners (M : Finset (P × L)) (large : ∀ h, 2 ≤ (S h).card) :
    ∃ f : H → P → P, ∀ h p, p ∈ S h →
      f h p ∈ S h ∧ f h p ≠ p ∧
      ((∃ q ∈ S h, q ≠ p ∧ ∀ l, (p,l) ∈ M → ¬ I q l) →
       ∀ l, (p,l) ∈ M → ¬ I (f h p) l) := by
  classical
  have supply (h : H) (p : P) : ∃ q ∈ S h, q ≠ p := by
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (large h)
    by_cases eq : a = p
    · exact ⟨b,hb,eq ▸ ne.symm⟩
    · exact ⟨a,ha,eq⟩
  let safe h p q := q ∈ S h ∧ q ≠ p ∧ ∀ l, (p,l) ∈ M → ¬ I q l
  let f h p := if ex : ∃ q, safe h p q then ex.choose else (supply h p).choose
  refine ⟨f,fun h p _ => ?_⟩
  by_cases ex : ∃ q, safe h p q
  · have eq : f h p = ex.choose := by simp only [f, dite_eq_left ex]
    rw [eq]
    exact ⟨ex.choose_spec.1,ex.choose_spec.2.1,fun _ => ex.choose_spec.2.2⟩
  · exact ⟨by simpa [f,ex] using (supply h p).choose_spec.1,
      by simpa [f,ex] using (supply h p).choose_spec.2,fun good => (ex good).elim⟩

-- A general counting step. Every discarded member has at least one owner.
private theorem lossBound {A J : Type} [Fintype J] [DecidableEq A]
    (all keep : Finset A) (lost : J → Finset A)
    (classify : ∀ a ∈ all, a ∉ keep → ∃ j, a ∈ lost j) :
    all.card ≤ keep.card + ∑ j, (lost j).card := by
  classical
  let B := Finset.univ.biUnion lost
  have subset : all ⊆ keep ∪ B := by
    intro a ha
    by_cases ok : a ∈ keep
    · exact Finset.mem_union_left _ ok
    · obtain ⟨j,hj⟩ := classify a ha ok
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hj⟩)
  exact ((Finset.card_le_card subset).trans (Finset.card_union_le keep B)).trans
    (Nat.add_le_add_left Finset.card_biUnion_le _)

def discarded (h : H) (a : P × L) : Prop := a.1 ∈ S h ∧ I (f h a.1) a.2

theorem lostOwner {p : P} {l : L} (edge : I p l) (gone : ¬kept I S f p l) :
    ∃ h, discarded I S f h (p,l) := by
  classical
  by_contra! no
  apply gone
  refine ⟨edge,?_⟩
  rintro q ⟨h,mem,rfl⟩ inc
  exact no h ⟨mem,inc⟩

section Finite
variable [Fintype P] [Fintype L] [Fintype H]
variable [DecidableEq P] [DecidableEq L] [DecidableEq H]

omit [DecidableEq H] in
theorem countFlags [DecidableRel I] [DecidableRel (kept I S f)]
    (free : Free I) (diff : ∀ h p, p ∈ S h → f h p ≠ p) :
    Fintype.card (FlagCrossRank.Flag I) ≤ Fintype.card (retained I S f) + ∑ h, (S h).card := by
  classical
  let E := Finset.univ.filter (fun a : P × L => I a.1 a.2)
  let D := Finset.univ.filter (fun a : P × L => kept I S f a.1 a.2)
  let lost (h : H) := E.filter (discarded I S f h)
  have charge (h : H) : (lost h).card ≤ (S h).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    · rintro ⟨p,l⟩ ha ⟨q,k⟩ hb eq
      change p = q at eq
      subst q
      obtain ⟨am,am'⟩ := Finset.mem_filter.mp ha
      obtain ⟨bm,bm'⟩ := Finset.mem_filter.mp hb
      refine Prod.ext (x := (p,l)) (y := (p,k)) rfl ?_
      by_contra ne
      exact free p (f h p) l k (diff h p am'.1).symm ne
        (Finset.mem_filter.mp am).2 am'.2 (Finset.mem_filter.mp bm).2 bm'.2
  have bound := lossBound E D lost (by
    rintro ⟨p,l⟩ inc gone
    obtain ⟨h,hv⟩ := lostOwner I S f (Finset.mem_filter.mp inc).2
      (fun good => gone (Finset.mem_filter.mpr ⟨Finset.mem_univ _,good⟩))
    exact ⟨h,Finset.mem_filter.mpr ⟨inc,hv⟩⟩)
  have net : (∑ h, (lost h).card) ≤ ∑ h, (S h).card :=
    Finset.sum_le_sum (fun h _ => charge h)
  have ec : Fintype.card (FlagCrossRank.Flag I) = E.card := by simp [E,FlagCrossRank.Flag,Fintype.card_subtype]
  have dc : Fintype.card (retained I S f) = D.card := by simp [D,retained,FlagCrossRank.Flag,Fintype.card_subtype]
  omega

def collinear (h : H) : Prop := ∃ l, ∀ p ∈ S h, I p l

omit [Fintype P] [Fintype L] [DecidableEq H] in
theorem countMatching (D : H → Finset P) (M : Finset (P × L)) (sub : ∀ a ∈ M, I a.1 a.2)
    (pointUnique : ∀ p l k, (p,l) ∈ M → (p,k) ∈ M → l = k)
    (lineUnique : ∀ p q l, (p,l) ∈ M → (q,l) ∈ M → p = q)
    (large : ∀ h, 2 ≤ (S h).card) (free : Free I)
    (prefer : ∀ h p, p ∈ D h →
      (∃ q ∈ S h, q ≠ p ∧ ∀ l, (p,l) ∈ M → ¬ I q l) →
       ∀ l, (p,l) ∈ M → ¬ I (f h p) l)
    [DecidableRel (kept I D f)] [DecidablePred (collinear I S)] :
    M.card ≤ (M.filter (fun a => kept I D f a.1 a.2)).card +
        (Finset.univ.filter (collinear I S)).card := by
  classical
  let R := M.filter (fun a => kept I D f a.1 a.2)
  let lost (h : H) := M.filter (discarded I D f h)
  have allOn (h : H) {p : P} {l : L} (mem : (p,l) ∈ lost h) : ∀ q ∈ S h, I q l := by
    obtain ⟨inM,del⟩ := Finset.mem_filter.mp mem
    intro q hq
    by_contra bad
    have diff : q ≠ p := by rintro rfl; exact bad (sub _ inM)
    have safe : ∀ k, (p,k) ∈ M → ¬ I q k := by
      intro k hk
      obtain rfl := pointUnique p l k inM hk
      exact bad
    exact prefer h p del.1 ⟨q,hq,diff,safe⟩ l inM del.2
  have charge (h : H) : (lost h).card ≤ if collinear I S h then 1 else 0 := by
    split
    · apply Finset.card_le_one.mpr
      rintro ⟨p,l⟩ ha ⟨q,k⟩ hb
      have onA := allOn h ha
      have onB := allOn h hb
      obtain ⟨u,hu,v,hv,diff⟩ := Finset.one_lt_card.mp (large h)
      have eq : l = k := by
        by_contra ne
        exact free u v l k diff ne (onA u hu) (onA v hv) (onB u hu) (onB v hv)
      subst k
      exact Prod.ext (lineUnique p q l (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1) rfl
    · rename_i no
      have empty : lost h = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        rintro ⟨p,l⟩ mem
        exact no ⟨l,allOn h mem⟩
      simp [empty]
  have bound := lossBound M R lost (by
    rintro ⟨p,l⟩ inc gone
    obtain ⟨h,hv⟩ := lostOwner I D f (sub _ inc)
      (fun ok => gone (Finset.mem_filter.mpr ⟨inc,ok⟩))
    exact ⟨h,Finset.mem_filter.mpr ⟨inc,hv⟩⟩)
  have net : (∑ h, (lost h).card) ≤ (Finset.univ.filter (collinear I S)).card := by
    simpa [Finset.sum_boole] using (Finset.sum_le_sum (s := Finset.univ) (fun h _ => charge h))
  exact bound.trans (Nat.add_le_add_left net _)


-- A cover of the retained edges needs a different endpoint for each edge
-- in the retained matching, even if it contains virtual labels as well.
omit [Fintype P] [Fintype L] [Fintype H] in
theorem matchingCover (M : Finset (P × L))
    (pointUnique : ∀ p l k, (p,l) ∈ M → (p,k) ∈ M → l = k)
    (lineUnique : ∀ p q l, (p,l) ∈ M → (q,l) ∈ M → p = q)
    [DecidableRel (kept I S f)] (K : Finset (Label P L H))
    (covers : ∀ e : retained I S f, left I S f e ∈ K ∨ right I S f e ∈ K) :
    (M.filter (fun a => kept I S f a.1 a.2)).card ≤ K.card := by
  classical
  let pick (a : P × L) : Label P L H :=
    if Sum.inl a.1 ∈ K then Sum.inl a.1 else Sum.inr (Sum.inl a.2)
  apply Finset.card_le_card_of_injOn pick
  · rintro ⟨p,l⟩ ha
    obtain ⟨_,ret⟩ := Finset.mem_filter.mp ha
    rcases covers ⟨(p,l),ret⟩ with hp | hl
    · change Sum.inl p ∈ K at hp
      simp [pick,hp]
    · change Sum.inr (Sum.inl l) ∈ K at hl
      by_cases hp : Sum.inl p ∈ K <;> simp [pick,hp,hl]
  · rintro ⟨p,l⟩ ha ⟨q,k⟩ hb eq
    have am := (Finset.mem_filter.mp ha).1
    have bm := (Finset.mem_filter.mp hb).1
    by_cases hp : Sum.inl p ∈ K <;> by_cases hq : Sum.inl q ∈ K <;>
      simp [pick,hp,hq] at eq
    · subst q
      exact Prod.ext rfl (pointUnique p l k am bm)
    · subst k
      exact Prod.ext (lineUnique p q l am bm) rfl

-- A helper region can read raw points or earlier helper outputs. Each
-- raw occurrence inherits a witness from a region below it, possibly itself.
theorem circuitBound (D : H → Finset P) [DecidableRel I] [DecidablePred (collinear I S)]
    (M : Finset (P × L)) (sub : ∀ a ∈ M, I a.1 a.2)
    (pointUnique : ∀ p l k, (p,l) ∈ M → (p,k) ∈ M → l = k)
    (lineUnique : ∀ p q l, (p,l) ∈ M → (q,l) ∈ M → p = q)
    (direct : ∀ h, D h ⊆ S h)
    (source : ∀ h p, p ∈ S h → ∃ j, p ∈ D j ∧ S j ⊆ S h)
    (large : ∀ h, 2 ≤ (S h).card) (free : Free I)
    (T : FlagCrossRank.Tree (Label P L H))
    (correct : ∀ X Y, T.val (bits S X Y) = true ↔ ∃ p l, I p l ∧ X p ∧ Y l)
    (innerRefs : Nat)
    (shared : 2 * Fintype.card H ≤ T.cost (fun w => if physical w then 0 else 1) + innerRefs)
    (gates : Nat) (size : T.leaves + (∑ h, (D h).card) + innerRefs ≤
      gates + 1 + Fintype.card H) :
    Fintype.card (FlagCrossRank.Flag I) + M.card + Fintype.card H ≤
      gates + 1 + (Finset.univ.filter (collinear I S)).card := by
  classical
  obtain ⟨part,spec⟩ := selectPartners I S M large
  have hitMate (h : H) (p : P) (hp : p ∈ S h) : ∃ q ∈ S h, mates D part p q := by
    obtain ⟨j,hj,subtree⟩ := source h p hp
    exact ⟨part j p,subtree (spec j p (direct j hj)).1,j,hj,rfl⟩
  have rank := rawRetained I S part D hitMate free T correct _
    (matchingCover I D part M pointUnique lineUnique)
  have e := countFlags I D part free (fun h p hp => (spec h p (direct h hp)).2.1)
  have m := countMatching I S part D M sub pointUnique lineUnique large free
    (fun h p hp => (spec h p (direct h hp)).2.2)
  have split := splitLeaves T
  omega


-- A region is a binary OR tree whose leaves are points or earlier helper
-- outputs. Costs and supports follow from this syntax, including repeated
-- leaves and repeated references to the same earlier helper.
end Finite

inductive OrRegion (P H : Type) where
  | point (p : P)
  | helper (h : H)
  | join (a b : OrRegion P H)

namespace OrRegion

def support [DecidableEq P] (S : H → Finset P) : OrRegion P H → Finset P
  | .point p => {p}
  | .helper h => S h
  | .join a b => support S a ∪ support S b

def direct [DecidableEq P] : OrRegion P H → Finset P
  | .point p => {p}
  | .helper _ => ∅
  | .join a b => direct a ∪ direct b

def refs : OrRegion P H → Nat
  | .point _ => 0
  | .helper _ => 1
  | .join a b => refs a + refs b

def gates : OrRegion P H → Nat
  | .point _ | .helper _ => 0
  | .join a b => gates a + gates b + 1

def reads (j : H) : OrRegion P H → Prop
  | .point _ => False
  | .helper h => j = h
  | .join a b => reads j a ∨ reads j b

theorem price [DecidableEq P] (v : OrRegion P H) : v.direct.card + v.refs ≤ v.gates + 1 := by
  induction v with
  | point p => simp [direct,refs,gates]
  | helper h => simp [direct,refs,gates]
  | join a b ia ib =>
    have bound := Finset.card_union_le a.direct b.direct
    simp only [direct,refs,gates]
    omega

theorem directSubset [DecidableEq P] (v : OrRegion P H) : v.direct ⊆ v.support S := by
  induction v with
  | point p => exact fun _ h => h
  | helper h => exact Finset.empty_subset _
  | join a b ia ib => exact Finset.union_subset_union ia ib

theorem trace [DecidableEq P] (v : OrRegion P H) (p : P) (hp : p ∈ v.support S) :
    p ∈ v.direct ∨ ∃ j, v.reads j ∧ p ∈ S j ∧ S j ⊆ v.support S := by
  induction v with
  | point q => exact Or.inl hp
  | helper j => exact Or.inr ⟨j,rfl,hp,fun _ mem => mem⟩
  | join a b ia ib =>
    rcases Finset.mem_union.mp hp with ha | hb
    · rcases ia ha with raw | ⟨j,read,mem,sub⟩
      · exact Or.inl (Finset.mem_union_left _ raw)
      · exact Or.inr ⟨j,Or.inl read,mem,fun _ ok => Finset.mem_union_left _ (sub ok)⟩
    · rcases ib hb with raw | ⟨j,read,mem,sub⟩
      · exact Or.inl (Finset.mem_union_right _ raw)
      · exact Or.inr ⟨j,Or.inr read,mem,fun _ ok => Finset.mem_union_right _ (sub ok)⟩

end OrRegion

-- Cutting all shared OR outputs gives these acyclic regions and an
-- arbitrary residual AND/OR formula. The only remaining count hypothesis
-- says that the shared outputs have at least two uses on average.
section Network
variable [Fintype P] [Fintype L] [Fintype H] [DecidableEq P] [DecidableEq L] [DecidableEq H]

theorem networkBound [DecidableRel I] [DecidablePred (collinear I S)]
    (M : Finset (P × L)) (sub : ∀ a ∈ M, I a.1 a.2)
    (pointUnique : ∀ p l k, (p,l) ∈ M → (p,k) ∈ M → l = k)
    (lineUnique : ∀ p q l, (p,l) ∈ M → (q,l) ∈ M → p = q)
    (regions : H → OrRegion P H) (height : H → Nat)
    (earlier : ∀ h j, (regions h).reads j → height j < height h)
    (supports : ∀ h, (regions h).support S = S h)
    (large : ∀ h, 2 ≤ (S h).card) (free : Free I)
    (T : FlagCrossRank.Tree (Label P L H))
    (correct : ∀ X Y, T.val (bits S X Y) = true ↔ ∃ p l, I p l ∧ X p ∧ Y l)
    (shared : 2 * Fintype.card H ≤
      T.cost (fun w => if physical w then 0 else 1) + ∑ h, (regions h).refs) :
    Fintype.card (FlagCrossRank.Flag I) + M.card + Fintype.card H ≤
      T.leaves + (∑ h, (regions h).gates) + (Finset.univ.filter (collinear I S)).card := by
  classical
  let D (h : H) := (regions h).direct
  have direct (h : H) : D h ⊆ S h := supports h ▸ (regions h).directSubset S
  have source (h : H) (p : P) : p ∈ S h → ∃ j, p ∈ D j ∧ S j ⊆ S h := by
    generalize eq : height h = n
    induction n using Nat.strong_induction_on generalizing h with
    | ind n ih =>
      intro mem
      rcases (regions h).trace S p ((supports h).symm ▸ mem) with raw | ⟨j,read,hp,subtree⟩
      · exact ⟨h,raw,fun _ ok => ok⟩
      · obtain ⟨k,hk,small⟩ := ih (height j) (eq ▸ earlier h j read) j rfl hp
        exact ⟨k,hk,fun _ ok => supports h ▸ subtree (small ok)⟩
  have cost : (∑ h, (D h).card) + ∑ h, (regions h).refs ≤
      (∑ h, (regions h).gates) + Fintype.card H := by
    simpa [D,Finset.sum_add_distrib] using
      (Finset.sum_le_sum (s := Finset.univ) (fun h _ => (regions h).price))
  have positive (tree : FlagCrossRank.Tree (Label P L H)) : 0 < tree.leaves := by
    induction tree with
    | raw _ => simp [FlagCrossRank.Tree.leaves]
    | gate op a b ia ib => simp only [FlagCrossRank.Tree.leaves]; omega
  have live := positive T
  have result := circuitBound I S D M sub pointUnique lineUnique direct source large free T correct _
    shared (T.leaves - 1 + ∑ h, (regions h).gates) (by omega)
  omega

end Network
end OneShoreSetRank
