import PEqualNP.Defs

namespace QuadrangleTerms

abbrev V := Fin 13
def near (p w : V) := p-w ∈ ([0,1,3,9] : List V)
instance (p w : V) : Decidable (near p w) := by unfold near; infer_instance

def quad (S : Finset V) := S.card=4 ∧ ∀ w : V, (S.filter fun p => near p w).card ≤ 2
instance (S : Finset V) : Decidable (quad S) := by unfold quad; infer_instance

def clear (S : Finset V) (w : V) := ∀ p ∈ S, ¬near p w
instance (S : Finset V) (w : V) : Decidable (clear S w) := by unfold clear; infer_instance

-- The 26 tests are two cyclic orbits of quadrangles. Bits 0..12 are points.
def tests : List ℕ := [162112,316033,623875,1247750,1325076,2143424,2495500,2641961,4278657,4982809,5275731,8557314,9965618,10551462,12591508,17106437,17311024,19923045,21102924,25183016,33631392,34212874,34622048,39846090,42205848,50366032]
def points (r : ℕ) : Finset V := Finset.univ.filter fun p => r.testBit p.val
def lineBit (r : ℕ) (w : V) := r.testBit (13+w.val)

theorem valid_tests : ∀ r ∈ tests, quad (points r) ∧ ∀ w : V, lineBit r w = true ↔ clear (points r) w := by
  decide +kernel

theorem cover_tests :
    (∀ p q : V, ∃ r ∈ tests, r.testBit p.val = true ∧ r.testBit q.val = true) ∧
    (∀ w v : V, ∃ r ∈ tests, lineBit r w = true ∧ lineBit r v = true) ∧
    (∀ p w : V, ¬near p w → ∃ r ∈ tests, r.testBit p.val = true ∧ lineBit r w = true) := by
  decide +kernel

theorem square_free : ∀ p q w v : V, p≠q → w≠v →
    near p w → near p v → near q w → ¬near q v := by decide +kernel

-- A label records the raw disjunctions containing this input. On a pair of
-- active inputs, a product is true iff the two labels cover all its clauses.
abbrev Label (k : ℕ) := Fin (2^k)
def hit {k : ℕ} (a b : Label k) := a.val ||| b.val = 2^k-1
instance {k : ℕ} (a b : Label k) : Decidable (hit a b) := by unfold hit; infer_instance

def safe {k : ℕ} (P L : V → Label k) := ∀ S, quad S → ∃ j : Fin k,
  (∀ p ∈ S, (P p).val.testBit j.val = false) ∧
  (∀ w : V, clear S w → (L w).val.testBit j.val = false)

theorem pair_constraints {k : ℕ} (P L : V → Label k) (hs : safe P L)
    (bit : ∀ a b : Label k, hit a b → ∀ i : Fin k,
      a.val.testBit i.val = true ∨ b.val.testBit i.val = true) :
    (∀ p q, ¬hit (P p) (P q)) ∧ (∀ w v, ¬hit (L w) (L v)) ∧
    (∀ p w, hit (P p) (L w) → near p w) := by
  have reject (r) (hr : r ∈ tests) := hs (points r) (valid_tests r hr).1
  refine ⟨?_,?_,?_⟩
  · intro p q h
    obtain ⟨r,hr,hp,hq⟩ := cover_tests.1 p q
    obtain ⟨i,off,_⟩ := reject r hr
    have a := off p (by simpa [points] using hp)
    have b := off q (by simpa [points] using hq)
    rcases bit _ _ h i with hh|hh <;> simp_all
  · intro w v h
    obtain ⟨r,hr,hw,hv⟩ := cover_tests.2.1 w v
    obtain ⟨i,_,off⟩ := reject r hr
    have a := off w (((valid_tests r hr).2 w).mp hw)
    have b := off v (((valid_tests r hr).2 v).mp hv)
    rcases bit _ _ h i with hh|hh <;> simp_all
  · intro p w h
    by_contra hn
    obtain ⟨r,hr,hp,hw⟩ := cover_tests.2.2 p w hn
    obtain ⟨i,ap,al⟩ := reject r hr
    have a := ap p (by simpa [points] using hp)
    have b := al w (((valid_tests r hr).2 w).mp hw)
    rcases bit _ _ h i with hh|hh <;> simp_all

theorem nested_rows (P L : V → Label 3) (hs : safe P L) :
    ∀ p q : V, (∀ w, hit (P p) (L w) → hit (P q) (L w)) ∨
      (∀ w, hit (P q) (L w) → hit (P p) (L w)) := by
  obtain ⟨pp,ll,_⟩ := pair_constraints P L hs (by decide +kernel)
  have cross : ∀ a b c d : Label 3, hit a b → hit c d → ¬hit a c → ¬hit b d →
      hit a d ∨ hit c b := by decide +kernel
  intro p q
  by_cases h : ∀ w, hit (P p) (L w) → hit (P q) (L w)
  · exact Or.inl h
  · push Not at h
    obtain ⟨w,hpw,hqw⟩ := h
    exact Or.inr (fun v hqv => (cross _ _ _ _ hpw hqv (pp p q) (ll w v)).resolve_right hqw)

theorem ternary_centers (P L : V → Label 3) (hs : safe P L) :
    ∃ p w : V, near p w ∧ ∀ q v : V, hit (P q) (L v) → q=p ∨ v=w := by
  classical
  have edges := (pair_constraints P L hs (by decide +kernel)).2.2
  let E (p w : V) := hit (P p) (L w)
  have cmp := nested_rows P L hs
  by_cases strong : ∃ p a b : V, a≠b ∧ E p a ∧ E p b
  · obtain ⟨p,a,b,hab,ha,hb⟩ := strong
    have isolated (q : V) (hq : q≠p) :
        (∀ v, E q v → E p v) ∧ (∀ w v, E q w → E q v → w=v) := by
      rcases cmp p q with h|h
      · exact False.elim (square_free p q a b (Ne.symm hq) hab
          (edges _ _ ha) (edges _ _ hb) (edges _ _ (h _ ha)) (edges _ _ (h _ hb)))
      · refine ⟨h,?_⟩
        intro w v hw hv
        by_contra ne
        exact square_free p q w v (Ne.symm hq) ne (edges _ _ (h _ hw)) (edges _ _ (h _ hv))
          (edges _ _ hw) (edges _ _ hv)
    by_cases other : ∃ q w : V, q≠p ∧ E q w
    · obtain ⟨q,w,hq,hw⟩ := other
      refine ⟨p,w,edges _ _ ((isolated q hq).1 _ hw),?_⟩
      intro s v hsv
      by_cases he : s=p
      · exact Or.inl he
      · right
        rcases cmp q s with h|h
        · exact (isolated s he).2 _ _ hsv (h _ hw)
        · exact (isolated q hq).2 _ _ (h _ hsv) hw
    · exact ⟨p,a,edges _ _ ha,fun s v h => Or.inl (by
        by_contra hne
        exact other ⟨s,v,hne,h⟩)⟩
  · have uniq (p w v : V) (hw : E p w) (hv : E p v) : w=v := by
      by_contra ne
      exact strong ⟨p,w,v,ne,hw,hv⟩
    by_cases any : ∃ p w : V, E p w
    · obtain ⟨p,w,hw⟩ := any
      refine ⟨p,w,edges _ _ hw,?_⟩
      intro q v hv
      right
      rcases cmp p q with h|h
      · exact uniq q v w hv (h _ hw)
      · exact uniq p v w (h _ hv) hw
    · exact ⟨0,0,by decide,fun p w h => False.elim (any ⟨p,w,h⟩)⟩

theorem ternary_at_most_seven (P L : V → Label 3) (hs : safe P L) :
    (Finset.univ.filter (fun z : V×V => hit (P z.1) (L z.2))).card ≤ 7 := by
  obtain ⟨p,w,hn,h⟩ := ternary_centers P L hs
  have edges := (pair_constraints P L hs (by decide +kernel)).2.2
  have cap : ∀ p w : V, near p w →
      (Finset.univ.filter (fun z : V×V => near z.1 z.2 ∧ (z.1=p ∨ z.2=w))).card = 7 := by decide +kernel
  rw [← cap p w hn]
  apply Finset.card_le_card
  intro z hz
  have he := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,edges _ _ he,h _ _ he⟩

def edgeSet {k : ℕ} (P L : V → Label k) : Finset (V×V) :=
  Finset.univ.filter (fun z => hit (P z.1) (L z.2))

theorem binary_at_most_four (P L : V → Label 2) (hs : safe P L) : (edgeSet P L).card ≤ 4 := by
  obtain ⟨pp,ll,edges⟩ := pair_constraints P L hs (by decide +kernel)
  let E (p w : V) := hit (P p) (L w)
  have cross : ∀ a b c d : Label 2, hit a b → hit c d → ¬hit a c → ¬hit b d →
      hit a d ∧ hit c b := by decide +kernel
  have joined (p q w v : V) (h : E p w) (k : E q v) : p=q ∨ w=v := by
    by_contra! ne
    obtain ⟨hv,hw⟩ := cross _ _ _ _ h k (pp p q) (ll w v)
    exact square_free p q w v ne.1 ne.2 (edges _ _ h) (edges _ _ hv) (edges _ _ hw) (edges _ _ k)
  have shape : (∃ p, ∀ q v, E q v → q=p) ∨ (∃ w, ∀ q v, E q v → v=w) := by
    by_cases strong : ∃ p a b : V, a≠b ∧ E p a ∧ E p b
    · obtain ⟨p,a,b,hab,ha,hb⟩ := strong
      exact Or.inl ⟨p,fun q v h => by
        by_contra ne
        exact hab (((joined q p v a h ha).resolve_left ne).symm.trans
          ((joined q p v b h hb).resolve_left ne))⟩
    · by_cases any : ∃ p w, E p w
      · obtain ⟨p,w,h⟩ := any
        refine Or.inr ⟨w,fun q v hv => ?_⟩
        rcases joined q p v w hv h with eq|eq
        · subst q
          by_contra ne
          exact strong ⟨p,v,w,ne,hv,h⟩
        · exact eq
      · exact Or.inl ⟨0,fun p w h => False.elim (any ⟨p,w,h⟩)⟩
  rcases shape with ⟨p,h⟩|⟨w,h⟩
  · have cap : ∀ p : V, (Finset.univ.filter (fun z : V×V => z.1=p ∧ near z.1 z.2)).card = 4 := by decide +kernel
    rw [← cap p]
    exact Finset.card_le_card (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      h _ _ (Finset.mem_filter.mp hz).2,edges _ _ (Finset.mem_filter.mp hz).2⟩)
  · have cap : ∀ w : V, (Finset.univ.filter (fun z : V×V => z.2=w ∧ near z.1 z.2)).card = 4 := by decide +kernel
    rw [← cap w]
    exact Finset.card_le_card (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      h _ _ (Finset.mem_filter.mp hz).2,edges _ _ (Finset.mem_filter.mp hz).2⟩)

theorem twelve_binary_terms {n : ℕ} (P L : V → Label 3) (h : safe P L)
    (A B : Fin n → V → Label 2) (ok : ∀ i, safe (A i) (B i))
    (covers : ∀ p w : V, near p w → hit (P p) (L w) ∨ ∃ i, hit (A i p) (B i w)) : 12 ≤ n := by
  let G := Finset.univ.filter (fun z : V×V => near z.1 z.2)
  let pieces (i : Fin n) := edgeSet (A i) (B i)
  have all : G ⊆ edgeSet P L ∪ Finset.univ.biUnion pieces := by
    intro z hz
    rcases covers _ _ (Finset.mem_filter.mp hz).2 with ht|⟨i,hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)
  have count : G.card=52 := by
    change (Finset.univ.filter (fun z : V×V => near z.1 z.2)).card=52
    decide +kernel
  have bound : (Finset.univ.biUnion pieces).card ≤ n*4 := calc
    _ ≤ ∑ i ∈ Finset.univ, (pieces i).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin n, 4 := Finset.sum_le_sum (fun i _ => binary_at_most_four _ _ (ok i))
    _ = n*4 := by simp
  have total := (Finset.card_le_card all).trans (Finset.card_union_le _ _)
  have cap : (edgeSet P L).card ≤ 7 := ternary_at_most_seven _ _ h
  omega

-- A path with three edges singles out the two pure OR clauses and the
-- remaining mixed OR clause. The proof checks only the four three-bit labels.
theorem pure_arms (P L : V → Label 3) (hs : safe P L) (u b v a : V)
    (hua : hit (P u) (L a)) (hbv : hit (P b) (L v)) (huv : hit (P u) (L v))
    (hba : ¬hit (P b) (L a)) :
    ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      (∀ q, (P q).val.testBit i.val = false) ∧
      (∀ l, (L l).val.testBit j.val = false) ∧
      (∀ l, hit (P u) (L l) ↔ (L l).val.testBit i.val = true) ∧
      (∀ q, hit (P q) (L v) ↔ (P q).val.testBit j.val = true) ∧
      (P u).val.testBit k.val = true ∧ (L v).val.testBit k.val = true := by
  obtain ⟨pp,ll,_⟩ := pair_constraints P L hs (by decide +kernel)
  have pattern : ∀ U A B V' : Label 3, hit U A → hit B V' → hit U V' →
      ¬hit U B → ¬hit A V' → ¬hit B A →
      ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
        (∀ t : Label 3, hit U t ↔ t.val.testBit i.val = true) ∧
        (∀ t : Label 3, hit t V' ↔ t.val.testBit j.val = true) ∧
        U.val.testBit k.val = true ∧ V'.val.testBit k.val = true := by decide +kernel
  obtain ⟨i,j,k,hij,hjk,hik,ui,vj,uk,vk⟩ := pattern _ _ _ _ hua hbv huv (pp u b) (ll a v) hba
  exact ⟨i,j,k,hij,hjk,hik,fun q => Bool.eq_false_iff.mpr (fun h => pp u q ((ui _).mpr h)),
    fun l => Bool.eq_false_iff.mpr (fun h => ll l v ((vj _).mpr h)),
    fun l => ui (L l),fun q => vj (P q),uk,vk⟩

-- These quadrangles supply a witness for triples consisting of one center
-- and two vertices outside its neighborhood on the opposite side.
def extensionTests : List ℕ := [3211303,4751635,25428508,37767368,2143424,924680,8471456,34736706,50340976,208132,316033,9965618,23068749,17318185,4466836,12714254,33654402,1079392,16942912,44040362,8434064,2425989,17859153,4786435,3280966,34343960,1378821,8540936,2659331,10498212,601376,37781714,20980052,18940965,2379913,4278657,50348648,5507093,35783754,42992178,17171980,1102401,13107482,1325076,33631392,162112,693506,25232164,33851024,17564697,2641961,5376070,8487810,6357127,19923045,1595425,12845212,801808,115585,346753,8585990,42467386,9703956,2126048,5275731]

theorem extension_rows : ∀ r ∈ extensionTests, quad (points r) ∧ ∀ w : V, lineBit r w = true ↔ clear (points r) w := by
  decide +kernel

theorem point_extension (p a b : V) (ha : ¬near p a) (hb : ¬near p b) :
    ∃ S, quad S ∧ p ∈ S ∧ clear S a ∧ clear S b := by
  have cert : ∀ p a b : V, ¬near p a → ¬near p b → ∃ r ∈ extensionTests,
      r.testBit p.val = true ∧ lineBit r a = true ∧ lineBit r b = true := by decide +kernel
  obtain ⟨r,hr,hp,hx,hy⟩ := cert p a b ha hb
  exact ⟨points r,(extension_rows _ hr).1,by simpa [points] using hp,
    ((extension_rows _ hr).2 a).mp hx,((extension_rows _ hr).2 b).mp hy⟩

theorem line_extension (w a b : V) (ha : ¬near a w) (hb : ¬near b w) :
    ∃ S, quad S ∧ clear S w ∧ a ∈ S ∧ b ∈ S := by
  have cert : ∀ w a b : V, ¬near a w → ¬near b w → ∃ r ∈ extensionTests,
      lineBit r w = true ∧ r.testBit a.val = true ∧ r.testBit b.val = true := by decide +kernel
  obtain ⟨r,hr,hw,hx,hy⟩ := cert w a b ha hb
  exact ⟨points r,(extension_rows _ hr).1,((extension_rows _ hr).2 w).mp hw,
    by simpa [points] using hx,by simpa [points] using hy⟩

-- For a center that accepts a neighbor, one missed clause contains no
-- opposite-side off-neighbor. This allows many same-side centers to share ORs.
theorem clean_bit (u n : Label 3) (f : V → Label 3) (bad : V → Prop)
    (edge : hit u n) (hu : ¬hit u u) (hn : ¬hit n n)
    (off : ∀ x y, bad x → bad y → ∃ k : Fin 3, u.val.testBit k.val = false ∧
      (f x).val.testBit k.val = false ∧ (f y).val.testBit k.val = false) :
    ∃ k : Fin 3, u.val.testBit k.val = false ∧ ∀ z, bad z → (f z).val.testBit k.val = false := by
  classical
  have sparse : ∀ u n : Label 3, hit u n → ¬hit u u → ¬hit n n →
      ∃ i j : Fin 3, u.val.testBit i.val = false ∧ u.val.testBit j.val = false ∧
        ∀ k : Fin 3, u.val.testBit k.val = false → k=i ∨ k=j := by decide +kernel
  obtain ⟨i,j,hi,hj,cov⟩ := sparse u n edge hu hn
  by_contra nh
  have witness (k : Fin 3) (hk : u.val.testBit k.val = false) :
      ∃ z, bad z ∧ (f z).val.testBit k.val ≠ false := by
    by_contra! hh
    exact nh ⟨k,hk,hh⟩
  obtain ⟨x,hx,xi⟩ := witness i hi
  obtain ⟨y,hy,yj⟩ := witness j hj
  obtain ⟨k,hk,xk,yk⟩ := off x y hx hy
  rcases cov k hk with h|h
  · exact xi (h ▸ xk)
  · exact yj (h ▸ yk)

theorem clean_point_clause (P L : V → Label 3) (hs : safe P L) (p w : V)
    (edge : hit (P p) (L w)) : ∃ k : Fin 3, (P p).val.testBit k.val = false ∧
      ∀ v, ¬near p v → (L v).val.testBit k.val = false := by
  obtain ⟨pp,ll,_⟩ := pair_constraints P L hs (by decide +kernel)
  apply clean_bit (P p) (L w) L _ edge (pp p p) (ll w w)
  intro x y hx hy
  obtain ⟨S,hq,hp,ax,ay⟩ := point_extension p x y hx hy
  obtain ⟨k,ps,ls⟩ := hs S hq
  exact ⟨k,ps _ hp,ls _ ax,ls _ ay⟩

theorem clean_line_clause (P L : V → Label 3) (hs : safe P L) (p w : V)
    (edge : hit (P p) (L w)) : ∃ k : Fin 3, (L w).val.testBit k.val = false ∧
      ∀ q, ¬near q w → (P q).val.testBit k.val = false := by
  obtain ⟨pp,ll,_⟩ := pair_constraints P L hs (by decide +kernel)
  have flip : ∀ a b : Label 3, hit a b → hit b a := by decide +kernel
  apply clean_bit (L w) (P p) P _ (flip _ _ edge) (ll w w) (pp p p)
  intro x y hx hy
  obtain ⟨S,hq,hw,ax,ay⟩ := line_extension w x y hx hy
  obtain ⟨k,ps,ls⟩ := hs S hq
  exact ⟨k,ls _ hw,ps _ ax,ps _ ay⟩

-- In a minimum vertex cover all thirteen centers lie on one side.
-- The two incidence matchings at offsets zero and one suffice.
theorem mixed_cover (A B : Finset V) (pa : A.Nonempty) (lb : B.Nonempty)
    (cov : ∀ p w : V, near p w → p ∈ A ∨ w ∈ B) : 14 ≤ A.card + B.card := by
  classical
  have same : ∀ p : V, near p p := by decide +kernel
  have prev : ∀ p : V, near p (p-1) := by decide +kernel
  let R := Finset.univ \ A
  have inc : R ⊆ B := by
    intro p hp
    exact (cov p p (same p)).resolve_left (Finset.mem_sdiff.mp hp).2
  have sum : R.card + A.card = 13 := by
    simpa [R] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  by_contra! low
  have eq : R = B := Finset.eq_of_subset_of_card_le inc (by omega)
  have down (p : V) (hp : p ∈ B) : p-1 ∈ B := by
    rw [← eq] at hp
    exact (cov p (p-1) (prev p)).resolve_left (Finset.mem_sdiff.mp hp).2
  obtain ⟨w,hw⟩ := lb
  have orbit (n : ℕ) : (fun x : V => x-1)^[n] w ∈ B := by
    induction n with
    | zero => exact hw
    | succ n ih => simpa only [Function.iterate_succ_apply'] using down _ ih
  obtain ⟨p,hp⟩ := pa
  have reach : ∀ p w : V, ∃ n : Fin 13, (fun x : V => x-1)^[n.val] w = p := by decide +kernel
  obtain ⟨n,hn⟩ := reach p w
  have h := orbit n.val
  rw [hn, ← eq] at h
  exact (Finset.mem_sdiff.mp h).2 hp

def pointLabel (p : V) : Label 3 := if p=0 then 3 else if near p 0 then 2 else 0
def lineLabel (w : V) : Label 3 := if w=0 then 5 else if near 0 w then 4 else 0

theorem sharp : safe pointLabel lineLabel ∧ (edgeSet pointLabel lineLabel).card=7 := by
  refine ⟨?_,by decide +kernel⟩
  intro S _
  have tab :
      (∀ p : V, (pointLabel p).val.testBit 2 = false) ∧
      (∀ w : V, ¬near 0 w → (lineLabel w).val.testBit 2 = false) ∧
      (∀ w : V, (lineLabel w).val.testBit 1 = false) ∧
      (∀ p : V, ¬near p 0 → (pointLabel p).val.testBit 1 = false) ∧
      (∀ p : V, p≠0 → (pointLabel p).val.testBit 0 = false) ∧
      (∀ w : V, w≠0 → (lineLabel w).val.testBit 0 = false) := by decide +kernel
  obtain ⟨pt2,ln2,ln1,pt1,pt0,ln0⟩ := tab
  by_cases h : (0 : V) ∈ S
  · exact ⟨2,fun p _ => pt2 p,fun w hw => ln2 w (hw 0 h)⟩
  · by_cases k : clear S 0
    · exact ⟨1,fun p hp => pt1 p (k p hp),fun w _ => ln1 w⟩
    · exact ⟨0,fun p hp => pt0 p (by rintro rfl; exact h hp),
        fun w hw => ln0 w (by rintro rfl; exact k hw)⟩

end QuadrangleTerms
