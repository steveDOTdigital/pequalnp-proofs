import FlagCrossRank

namespace OneShorePairRank
open FlagCrossRank
open scoped BigOperators

-- We only charge leaves whose labels are physical inputs. A virtual input
-- may distinguish nonlocal cells without contributing to any charged rank.
theorem rawRank {E V Y : Type} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (T : FlagCrossRank.Tree V) (raw : V → Bool) (left right : E → V)
    (positive : E → V → Bool) (negative : Y → V → Bool) (cross : E → Y)
    (yes : ∀ e, T.val (positive e) = true) (no : ∀ e, T.val (negative e) = false)
    (endsRaw : ∀ e, raw (left e) = true ∧ raw (right e) = true)
    (different : ∀ e, left e ≠ right e)
    (diag : ∀ e w, positive e w = true → negative (cross e) w = false → w = left e ∨ w = right e)
    (off : ∀ a b v w, a ≠ b → (v = left a ∨ v = right a) →
      (v = left b ∨ v = right b) → positive a w = true → negative (cross b) w = false → w = v)
    (base : ∀ a v, (v = left a ∨ v = right a) → ∃ y, ∀ w,
      positive a w = true → negative y w = false → w = v)
    (n : ℕ) (cover : ∀ K : Finset V, (∀ e, left e ∈ K ∨ right e ∈ K) → n ≤ K.card) :
    Fintype.card E + n ≤ T.cost (fun v => if raw v then 1 else 0) := by
  classical
  let weight (v : V) : ℕ := if raw v then 1 else 0
  obtain ⟨P,_,total,truth⟩ := tree_protocol_cost T weight positive negative
  let report (e : E) := P.label (P.start e (cross e))
  let miss (e : E) := if report e = left e then right e else left e
  have pair (e : E) : (report e = left e ∧ miss e = right e) ∨
      (report e = right e ∧ miss e = left e) := by
    obtain ⟨on,zero⟩ := truth e (cross e) (yes e) (no (cross e))
    rcases diag e _ on zero with h | h
    · change report e = left e at h; left; simp [miss,h]
    · change report e = right e at h; right; simp [miss,h,(different e).symm]
  have atEnd (e : E) (v : V) (mem : miss e = v ∨ report e = v) :
      v = left e ∨ v = right e := by rcases pair e with h | h <;> grind
  have charge (e : E) : raw (miss e) = true ∧ raw (report e) = true := by
    have h := endsRaw e; rcases pair e with h' | h' <;> grind
  have force (a b : E) (v : V) (ne : a ≠ b) (av : miss a = v ∨ report a = v)
      (bv : miss b = v ∨ report b = v) : P.label (P.start a (cross b)) = v := by
    obtain ⟨on,zero⟩ := truth a (cross b) (yes a) (no (cross b))
    exact off a b v _ ne (atEnd a v av) (atEnd b v bv) on zero
  have localBound := partitionLocal P.label P.start P.row P.col P.block cross miss report
    (fun _ => rfl) (fun e => by rcases pair e with h | h <;> have := different e <;> grind)
    force (by
      intro e v ev
      obtain ⟨y,hy⟩ := base e v (atEnd e v ev)
      obtain ⟨on,zero⟩ := truth e y (yes e) (no y)
      exact ⟨y,hy _ on zero⟩)
  let price (v : V) := if raw v then Fintype.card {b // P.label b = v} else 0
  have counted := aggregate miss report price (by
    intro v
    cases h : raw v with
    | true => simpa [price,h] using localBound v
    | false =>
      have : IsEmpty {e // miss e = v} := ⟨fun ⟨e,he⟩ => by
        have := (charge e).1; rw [he,h] at this; contradiction⟩
      have absent : v ∉ Finset.univ.image report := by
        rintro hv; obtain ⟨e,_,he⟩ := Finset.mem_image.mp hv
        have := (charge e).2; rw [he,h] at this; contradiction
      simp [absent,price,h])
  have fiber (v : V) : price v = ∑ b, if P.label b = v then weight v else 0 := by
    cases h : raw v <;> simp [price,weight,h,Fintype.card_subtype,Finset.sum_boole]
  have sum : (∑ v, price v) = ∑ b, weight (P.label b) := by
    simp_rw [fiber]; rw [Finset.sum_comm]; simp
  have minimum := cover (Finset.univ.image report) (fun e => by
    have mem := Finset.mem_image_of_mem report (Finset.mem_univ e)
    rcases pair e with h | h
    · exact Or.inl (h.1 ▸ mem)
    · exact Or.inr (h.1 ▸ mem))
  change Fintype.card E + n ≤ T.cost weight
  rw [←total,←sum]; omega

section Geometry
variable {P L H : Type} (I : P → L → Prop) (u v : H → P)

def mates (p q : P) : Prop := ∃ h, (u h = p ∧ v h = q) ∨ (v h = p ∧ u h = q)
def kept (p : P) (l : L) : Prop := I p l ∧ ∀ q, mates u v p q → ¬ I q l

def posPart (p : P) (l : L) (q : P) : Prop :=
  (q ≠ p ∧ kept I u v q l) ∨ mates u v p q
def linePart (p : P) (l k : L) : Prop := k ≠ l ∧ kept I u v p k

-- The negative cross uses the other retained neighbors on both shores,
-- together with every partner of the selected point.
theorem crossIndependent
    (free : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k)
    {p q : P} {l k : L} (e : kept I u v p l)
    (hq : posPart I u v p l q) (hk : linePart I u v p l k) : ¬ I q k := by
  rcases hq with ⟨ne,edge⟩ | mate
  · exact free p q l k ne.symm hk.1.symm e.1 edge.1 hk.2.1
  · exact hk.2.2 q mate

def values (X : P → Prop) (Y : L → Prop) : P ⊕ (L ⊕ H) → Prop :=
  Sum.elim X (Sum.elim Y (fun h => X (u h) ∨ X (v h)))

-- Whenever two retained flags meet, their positive-to-negative comparison
-- cannot report a virtual input. The diagonal is included.
theorem sharedCovered {a p : P} {b l : L} (row : kept I u v a b)
    (touch : a = p ∨ b = l) (h : H) (hit : u h = a ∨ v h = a) :
    posPart I u v p l (u h) ∨ posPart I u v p l (v h) := by
  by_cases eq : a = p
  · subst a
    rcases hit with hu | hv
    · exact Or.inr (Or.inr ⟨h, Or.inl ⟨hu,rfl⟩⟩)
    · exact Or.inl (Or.inr ⟨h, Or.inr ⟨hv,rfl⟩⟩)
  · have bl := touch.resolve_left eq
    subst b
    rcases hit with hu | hv
    · exact Or.inl (Or.inl ⟨hu.trans_ne eq, hu.symm ▸ row⟩)
    · exact Or.inr (Or.inl ⟨hv.trans_ne eq, hv.symm ▸ row⟩)

-- To force the physical point on a row, turn on its line and its partners.
-- To force the physical line, turn on the point by itself.
theorem pointWitness {p q : P} {l : L} (edge : kept I u v p l)
    (partner : mates u v p q) : ¬ I q l := edge.2 q partner


abbrev Label (P L H : Type) := P ⊕ (L ⊕ H)

noncomputable def bits (X : P → Prop) (Y : L → Prop) : Label P L H → Bool := by
  classical
  exact fun w => decide (values u v X Y w)

theorem bitsOn {X : P → Prop} {Y : L → Prop} {w : Label P L H} :
    bits u v X Y w = true ↔ values u v X Y w := by classical simp [bits]

theorem bitsOff {X : P → Prop} {Y : L → Prop} {w : Label P L H} :
    bits u v X Y w = false ↔ ¬ values u v X Y w := by classical simp [bits]

abbrev retained := FlagCrossRank.Flag (kept I u v)
def left (e : retained I u v) : Label P L H := .inl e.val.1
def right (e : retained I u v) : Label P L H := .inr (.inl e.val.2)
def physical : Label P L H → Bool := Sum.elim (fun _ => true) (Sum.elim (fun _ => true) (fun _ => false))

theorem rawRetained [Fintype P] [Fintype L] [Fintype H] [DecidableEq P] [DecidableEq L]
    [DecidableEq H] [DecidableRel (kept I u v)]
    (free : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k)
    (T : FlagCrossRank.Tree (Label P L H))
    (correct : ∀ X Y, T.val (bits u v X Y) = true ↔ ∃ p l, I p l ∧ X p ∧ Y l)
    (n : Nat) (cover : ∀ K : Finset (Label P L H),
      (∀ e : retained I u v, left I u v e ∈ K ∨ right I u v e ∈ K) → n ≤ K.card) :
    Fintype.card (retained I u v) + n ≤ T.cost (fun w => if physical w then 1 else 0) := by
  classical
  let N := {t : (P → Prop) × (L → Prop) // ∀ q k, t.1 q → t.2 k → ¬ I q k}
  let cx (e : retained I u v) : N := ⟨(posPart I u v e.val.1 e.val.2,
    linePart I u v e.val.1 e.val.2), fun _ _ x y => crossIndependent I u v free e.property x y⟩
  let pos (e : retained I u v) := bits u v (fun q => q = e.val.1) (fun k => k = e.val.2)
  let neg (c : N) := bits u v c.val.1 c.val.2
  have rawOnly (a b : retained I u v) (touch : a.val.1 = b.val.1 ∨ a.val.2 = b.val.2)
      (w : Label P L H) (on : pos a w = true) (off : neg (cx b) w = false) :
      w = left I u v a ∨ w = right I u v a := by
    have yes := (bitsOn u v).mp on
    have no := (bitsOff u v).mp off
    rcases w with q | (k | h)
    · exact Or.inl (congrArg Sum.inl yes)
    · exact Or.inr (congrArg (fun k : L => (Sum.inr (Sum.inl k) : Label P L H)) yes)
    · exact False.elim (no (sharedCovered I u v a.property touch h yes))
  apply rawRank T physical (left I u v) (right I u v) pos neg cx ?_ ?_
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
        exact False.elim ((bitsOff u v).mp off ⟨dif, eq ▸ a.property⟩)
    · exact (Sum.inl_ne_inr same).elim
    · exact (Sum.inr_ne_inl same).elim
    · have eq : a.val.2 = b.val.2 := Sum.inl.inj (Sum.inr.inj same)
      have dif : a.val.1 ≠ b.val.1 := fun h => ne (Subtype.ext (Prod.ext h eq))
      rcases rawOnly a b (Or.inr eq) w on off with replace | done
      · subst w
        exact False.elim ((bitsOff u v).mp off (Or.inl ⟨dif, eq ▸ a.property⟩))
      · exact done
  · rintro e z (rfl | rfl)
    · let c : N := ⟨(mates u v e.val.1, fun k => k = e.val.2), by
        intro q k hq hk
        subst k
        exact e.property.2 q hq⟩
      refine ⟨c, ?_⟩
      intro w on off
      have yes := (bitsOn u v).mp on
      have no := (bitsOff u v).mp off
      rcases w with q | (k | h)
      · exact congrArg Sum.inl yes
      · exact False.elim (no yes)
      · rcases yes with hh | hh
        · exact False.elim (no (Or.inr ⟨h, Or.inl ⟨hh,rfl⟩⟩))
        · exact False.elim (no (Or.inl ⟨h, Or.inr ⟨hh,rfl⟩⟩))
    · let c : N := ⟨(fun q => q = e.val.1, fun _ => False), by simp⟩
      refine ⟨c, ?_⟩
      intro w on off
      have yes := (bitsOn u v).mp on
      have no := (bitsOff u v).mp off
      rcases w with q | (k | h)
      · exact False.elim (no yes)
      · exact congrArg (fun k : L => (Sum.inr (Sum.inl k) : Label P L H)) yes
      · exact False.elim (no yes)


section Accounting
variable [Fintype P] [Fintype L] [Fintype H] [DecidableEq P] [DecidableEq L] [DecidableEq H]

-- All lost flags from one pair are on its single common line, if it has one.
noncomputable def joint (h : H) : Option L := by
  classical
  exact if ex : ∃ l, I (u h) l ∧ I (v h) l then some (Classical.choose ex) else none

theorem jointEq (free : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k)
    (proper : ∀ h, u h ≠ v h) {h : H} {l : L} (a : I (u h) l) (b : I (v h) l) :
    joint I u v h = some l := by
  classical
  have ex : ∃ k, I (u h) k ∧ I (v h) k := ⟨l,a,b⟩
  rw [joint, dif_pos ex]
  congr 1
  by_contra ne
  exact free _ _ _ _ (proper h) ne (Classical.choose_spec ex).1 (Classical.choose_spec ex).2 a b

theorem lostOwner (free : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k)
    (proper : ∀ h, u h ≠ v h) {p : P} {l : L} (e : I p l) (gone : ¬ kept I u v p l) :
    ∃ h, joint I u v h = some l ∧ (u h = p ∨ v h = p) := by
  classical
  have bad : ¬ ∀ q, mates u v p q → ¬ I q l := fun good => gone ⟨e,good⟩
  push Not at bad
  obtain ⟨q,⟨h,⟨ha,hb⟩ | ⟨ha,hb⟩⟩,hq⟩ := bad
  · exact ⟨h,jointEq I u v free proper (ha ▸ e) (hb ▸ hq),Or.inl ha⟩
  · exact ⟨h,jointEq I u v free proper (hb ▸ hq) (ha ▸ e),Or.inr ha⟩

noncomputable def pairFlags (h : H) : Finset (P × L) := by
  classical
  exact match joint I u v h with
    | none => ∅
    | some k => {(u h,k), (v h,k)}

noncomputable def extraLine (h : H) : Finset (Label P L H) := by
  classical
  exact match joint I u v h with
    | none => ∅
    | some k => {Sum.inr (Sum.inl k)}

theorem eraseCount [DecidableRel I] [DecidableRel (kept I u v)]
    (free : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k)
    (proper : ∀ h, u h ≠ v h) :
    Fintype.card (FlagCrossRank.Flag I) ≤ Fintype.card (retained I u v) + 2 * Fintype.card H := by
  classical
  let E := Finset.univ.filter (fun a : P × L => I a.1 a.2)
  let D := Finset.univ.filter (fun a : P × L => kept I u v a.1 a.2)
  let B := Finset.univ.biUnion (pairFlags I u v)
  have subset : E ⊆ D ∪ B := by
    rintro ⟨p,l⟩ mem
    have inc : I p l := (Finset.mem_filter.mp mem).2
    by_cases ok : kept I u v p l
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ok⟩)
    · obtain ⟨h,hj,ha | hb⟩ := lostOwner I u v free proper inc ok
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨h,Finset.mem_univ _,by simp [pairFlags,hj,ha]⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨h,Finset.mem_univ _,by simp [pairFlags,hj,hb]⟩)
  have small (h : H) : (pairFlags I u v h).card ≤ 2 := by
    cases hj : joint I u v h with
    | none => simp [pairFlags,hj]
    | some k =>
      simp only [pairFlags,hj]
      exact le_trans (Finset.card_insert_le _ _) (by simp)
  have bound : B.card ≤ 2 * Fintype.card H := calc
    B.card ≤ ∑ h : H, (pairFlags I u v h).card := Finset.card_biUnion_le
    _ ≤ ∑ _h : H, (2 : Nat) := Finset.sum_le_sum (fun h _ => small h)
    _ = _ := by simp [Nat.mul_comm]
  have count := (Finset.card_le_card subset).trans (Finset.card_union_le D B)
  have ec : Fintype.card (FlagCrossRank.Flag I) = E.card := by simp [E,FlagCrossRank.Flag,Fintype.card_subtype]
  have dc : Fintype.card (retained I u v) = D.card := by simp [D,retained,FlagCrossRank.Flag,Fintype.card_subtype]
  omega

theorem extendCover (free : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k)
    (proper : ∀ h, u h ≠ v h) (K : Finset (Label P L H))
    (covers : ∀ e : retained I u v, left I u v e ∈ K ∨ right I u v e ∈ K) :
    ∃ K' : Finset (Label P L H), K'.card ≤ K.card + Fintype.card H ∧
      ∀ p l, I p l → Sum.inl p ∈ K' ∨ Sum.inr (Sum.inl l) ∈ K' := by
  classical
  let B := Finset.univ.biUnion (extraLine I u v)
  have small (h : H) : (extraLine I u v h).card ≤ 1 := by
    cases hj : joint I u v h <;> simp [extraLine,hj]
  have bound : B.card ≤ Fintype.card H := calc
    B.card ≤ ∑ h : H, (extraLine I u v h).card := Finset.card_biUnion_le
    _ ≤ ∑ _h : H, (1 : Nat) := Finset.sum_le_sum (fun h _ => small h)
    _ = _ := by simp
  refine ⟨K ∪ B,(Finset.card_union_le _ _).trans (Nat.add_le_add_left bound _),?_⟩
  intro p l inc
  by_cases ok : kept I u v p l
  · rcases covers ⟨(p,l),ok⟩ with hp | hl
    · exact Or.inl (Finset.mem_union_left _ hp)
    · exact Or.inr (Finset.mem_union_left _ hl)
  · obtain ⟨h,hj,_⟩ := lostOwner I u v free proper inc ok
    exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨h,Finset.mem_univ _,by simp [extraLine,hj]⟩))


theorem splitLeaves (T : FlagCrossRank.Tree (Label P L H)) :
    T.cost (fun w => if physical w then 1 else 0) +
      T.cost (fun w => if physical w then 0 else 1) = T.leaves := by
  induction T with
  | raw w => cases h : physical w <;> simp [FlagCrossRank.Tree.cost,FlagCrossRank.Tree.leaves,h]
  | gate op a b ia ib =>
    simp only [FlagCrossRank.Tree.cost,FlagCrossRank.Tree.leaves]
    omega

-- Cutting each shared raw pair yields a formula. Each such paid pair occurs
-- at least twice among the virtual leaves, with no restriction on its fanout.
theorem circuitBound [DecidableRel I] [DecidableRel (kept I u v)]
    (free : ∀ p q l k, p ≠ q → l ≠ k → I p l → I q l → I p k → ¬ I q k)
    (proper : ∀ h, u h ≠ v h)
    (T : FlagCrossRank.Tree (Label P L H))
    (correct : ∀ X Y, T.val (bits u v X Y) = true ↔ ∃ p l, I p l ∧ X p ∧ Y l)
    (tau : Nat) (minCover : ∀ K : Finset (Label P L H),
      (∀ p l, I p l → Sum.inl p ∈ K ∨ Sum.inr (Sum.inl l) ∈ K) → tau ≤ K.card)
    (shared : 2 * Fintype.card H ≤ T.cost (fun w => if physical w then 0 else 1))
    (gates : Nat) (size : T.leaves + Fintype.card H ≤ gates + 1) :
    Fintype.card (FlagCrossRank.Flag I) + tau ≤ gates + 1 := by
  have rank := rawRetained I u v free T correct (tau - Fintype.card H) (by
    intro K covers
    obtain ⟨K',small,ok⟩ := extendCover I u v free proper K covers
    have bound := minCover K' ok
    omega)
  have loss := eraseCount I u v free proper
  have both := splitLeaves T
  omega

end Accounting

theorem pairPrice {edges raw cover helpers references gates : ℕ}
    (erased : 100 ≤ edges + 2 * helpers) (capacity : edges ≤ 5 * cover)
    (rank : edges + cover ≤ raw) (shared : 2 * helpers ≤ references)
    (cost : raw + references + helpers ≤ gates + 1) :
    595 + 3 * helpers ≤ 5 * gates := by omega

end Geometry
end OneShorePairRank
