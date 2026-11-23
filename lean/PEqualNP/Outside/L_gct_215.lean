import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_215

abbrev Mat := Fin 4 × Fin 5 → ℂ

def first (t : Mat) : ℂ := ∑ i, ∑ j, t (i, j)

def second (t : Mat) : ℂ :=
  ∑ j, ∑ l, if j = l then 0 else
    ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0

def third (t : Mat) : ℂ :=
  ∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
    ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0

def fourth (t : Mat) : ℂ :=
  ∑ j, ∑ l, ∑ m, ∑ n,
    if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0
    else t (0, j) * t (1, l) * t (2, m) * t (3, n)

-- Each entry of the polar map sums the entries outside its row and column.
private def polarMap : Mat →ₗ[ℂ] Mat where
  toFun x p := x p - (∑ j, x (p.1, j)) - (∑ i, x (i, p.2)) + first x
  map_add' x y := by
    funext p
    simp [first, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    funext p
    simp [first, Finset.mul_sum, mul_sub, mul_add]

private noncomputable def reconstruct (z : Mat) (p : Fin 4 × Fin 5) : ℂ :=
  z p - (∑ j, z (p.1, j)) / 4 - (∑ i, z (i, p.2)) / 3 + first z / 12

set_option maxRecDepth 10000 in
private lemma reconstruct_polar (x : Mat) (p : Fin 4 × Fin 5) :
    reconstruct (polarMap x) p = x p := by
  simp [reconstruct, polarMap, first, Fin.sum_univ_four, Fin.sum_univ_five]
  ring

private lemma polar_injective : Function.Injective polarMap := by
  intro x y h
  funext p
  simpa only [reconstruct_polar] using congrArg (fun z => reconstruct z p) h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma polar_pair (x y : Mat) :
    dotProduct (polarMap x) y = second (x + y) - second x - second y := by
  norm_num [dotProduct, Fintype.sum_prod_type, polarMap, first, second,
    Fin.sum_univ_four, Fin.sum_univ_five]
  ring

private lemma polar_one (x : Mat) : dotProduct (polarMap x) (1 : Mat) = 12 * first x := by
  simp [dotProduct, Fintype.sum_prod_type, polarMap, first, Fin.sum_univ_four,
    Fin.sum_univ_five]
  ring

-- The linear and quadratic equations alone leave only dimensions eight and nine
-- to exclude before the desired upper bound follows.
lemma quadratic_bound (L : Submodule ℂ Mat)
    (h : ∀ x ∈ L, first x = 0 ∧ second x = 0) : Module.finrank ℂ L ≤ 9 := by
  let extend := L ⊔ Submodule.span ℂ {(1 : Mat)}
  let dual := (dotProductEquiv ℂ (Fin 4 × Fin 5)).toLinearMap.comp polarMap
  have hinj : Function.Injective dual :=
    (dotProductEquiv ℂ (Fin 4 × Fin 5)).injective.comp polar_injective
  have hle : L.map dual ≤ extend.dualAnnihilator := by
    rintro f ⟨x, hx, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    have hker : extend ≤ LinearMap.ker (dual x) := by
      apply sup_le
      · intro z hz
        change dotProduct (polarMap x) z = 0
        rw [polar_pair, (h _ (L.add_mem hx hz)).2, (h x hx).2, (h z hz).2]
        ring
      · apply Submodule.span_le.mpr
        rintro z (rfl : z = 1)
        change dotProduct (polarMap x) 1 = 0
        rw [polar_one, (h x hx).1, mul_zero]
    exact hker hy
  have hone : (1 : Mat) ∉ L := by
    intro h1
    have hz := (h 1 h1).1
    norm_num [first] at hz
  have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq extend
  have hsub := Submodule.finrank_mono hle
  have hmap := (Submodule.equivMapOfInjective dual hinj L).finrank_eq
  have hext : Module.finrank ℂ extend = Module.finrank ℂ L + 1 :=
    Submodule.finrank_sup_span_singleton hone
  have hamb : Module.finrank ℂ Mat = 20 := by simp [Mat, Module.finrank_fintype_fun_eq_card]
  rw [hext, hamb] at hdim
  rw [← hmap] at hsub
  have bound : Module.finrank ℂ L + 1 + Module.finrank ℂ L ≤ 20 :=
    (Nat.add_le_add_left hsub (Module.finrank ℂ L + 1)).trans_eq hdim
  clear hdim hext hsub hmap
  omega

-- The total sum is zero, so three row sums and four column sums determine
-- both remaining sums. This gives seven linear measurements on the space.
private def margins : Mat →ₗ[ℂ] ((Fin 3 → ℂ) × (Fin 4 → ℂ)) where
  toFun x := (fun i => ∑ j, x (i.castSucc, j), fun j => ∑ i, x (i, j.castSucc))
  map_add' _ _ := by ext <;> simp [Finset.sum_add_distrib]
  map_smul' _ _ := by ext <;> simp [Finset.mul_sum]

private lemma centered_of_zero_margins (x : Mat) (hx : first x = 0) (hm : margins x = 0) :
    (∀ i, ∑ j, x (i, j) = 0) ∧ (∀ j, ∑ i, x (i, j) = 0) := by
  have rows (i : Fin 3) : ∑ j, x (i.castSucc, j) = 0 := congrFun (congrArg Prod.fst hm) i
  have cols (j : Fin 4) : ∑ i, x (i, j.castSucc) = 0 := congrFun (congrArg Prod.snd hm) j
  constructor
  · refine Fin.lastCases ?_ rows
    simpa only [first, Fin.sum_univ_castSucc (fun i : Fin 4 => ∑ j, x (i, j)),
      rows, Finset.sum_const_zero, zero_add] using hx
  · refine Fin.lastCases ?_ cols
    unfold first at hx
    rw [Finset.sum_comm] at hx
    simpa only [Fin.sum_univ_castSucc (fun j : Fin 5 => ∑ i, x (i, j)),
      cols, Finset.sum_const_zero, zero_add] using hx

-- A centered matrix in the space is orthogonal to every other member.
-- Its complex conjugate can belong to the space only when the matrix is zero.
open scoped ComplexOrder in
private lemma centered_vanishes (L : Submodule ℂ Mat)
    (h : ∀ x ∈ L, first x = 0 ∧ second x = 0)
    (x : Mat) (hx : x ∈ L) (hm : margins x = 0) (hc : star x ∈ L) : x = 0 := by
  obtain ⟨hr, hj⟩ := centered_of_zero_margins x (h x hx).1 hm
  have fixed : polarMap x = x := by
    funext p
    change x p - (∑ j, x (p.1,j)) - (∑ i, x (i,p.2)) + first x = x p
    rw [hr, hj, (h x hx).1]
    ring
  have pair := polar_pair x (star x)
  rw [fixed, (h _ (L.add_mem hx hc)).2, (h x hx).2, (h _ hc).2] at pair
  exact dotProduct_self_star_eq_zero.mp (by simpa using pair)

lemma conjugation_stable_bound (L : Submodule ℂ Mat)
    (h : ∀ x ∈ L, first x = 0 ∧ second x = 0)
    (stable : ∀ x ∈ L, star x ∈ L) : Module.finrank ℂ L ≤ 7 := by
  have inj : Function.Injective (margins.domRestrict L) := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro v hv
    exact Subtype.ext (centered_vanishes L h v v.property hv (stable v v.property))
  have bound := LinearMap.finrank_le_finrank_of_injective inj
  simpa [Module.finrank_prod, Module.finrank_fin_fun] using bound

-- This sum counts weighted matchings of all four rows to distinct columns.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private lemma shifted_fourth (t : Mat) :
    fourth (1 - t) = 120 - 24 * first t + 6 * second t - 2 * third t + fourth t := by
  norm_num [first, second, third, fourth, Fin.sum_univ_four, Fin.sum_univ_five]
  ring

-- More selected rows than available columns force a matching into the rectangle.
private lemma hits_rectangle (rows : Finset (Fin 4)) (cols : Finset (Fin 5))
    (large : 5 < rows.card + cols.card) (f : Fin 4 → Fin 5) (hf : Function.Injective f) :
    ∃ i ∈ rows, f i ∈ cols := by
  by_contra! avoid
  have sub : rows.image f ⊆ colsᶜ := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_compl.mpr (avoid i hi)
  have count := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ hf, Finset.card_compl, Fintype.card_fin] at count
  have bound := Finset.card_le_univ cols
  rw [Fintype.card_fin] at bound
  omega

lemma no_ones_rectangle (t : Mat)
    (h : first t = 0 ∧ second t = 0 ∧ third t = 0 ∧ fourth t = 0)
    (rows : Finset (Fin 4)) (cols : Finset (Fin 5)) (large : 5 < rows.card + cols.card) :
    ¬ ∀ i ∈ rows, ∀ j ∈ cols, t (i,j) = 1 := by
  intro ones
  have vanishes : fourth (1 - t) = 0 := by
    unfold fourth
    apply Finset.sum_eq_zero; intro j _
    apply Finset.sum_eq_zero; intro l _
    apply Finset.sum_eq_zero; intro m _
    apply Finset.sum_eq_zero; intro n _
    split_ifs with repeated
    · rfl
    · let f : Fin 4 → Fin 5 := ![j,l,m,n]
      have inj : Function.Injective f := by
        simp only [not_or] at repeated
        intro a b he
        fin_cases a <;> fin_cases b <;> simp_all [f, eq_comm]
      obtain ⟨i, hi, hc⟩ := hits_rectangle rows cols large f inj
      have entry := ones i hi (f i) hc
      fin_cases i <;> simp [f] at entry <;> simp [entry]
  rw [shifted_fourth, h.1, h.2.1, h.2.2.1, h.2.2.2] at vanishes
  norm_num at vanishes

lemma no_ones_row (t : Mat)
    (h : first t = 0 ∧ second t = 0 ∧ third t = 0 ∧ fourth t = 0)
    (r : Fin 4) : ¬ ∀ j, t (r, j) = 1 := by
  intro ones
  apply no_ones_rectangle t h {r} Finset.univ (by simp)
  simpa using ones

def rectangleMap (rows : Finset (Fin 4)) (cols : Finset (Fin 5)) :
    Mat →ₗ[ℂ] (rows × cols → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun p => (p.1.val, p.2.val))

-- This also bounds each projection to a pair of columns or a two-by-four block.
lemma rectangle_rank (L : Submodule ℂ Mat)
    (h : ∀ t ∈ L, first t = 0 ∧ second t = 0 ∧ third t = 0 ∧ fourth t = 0)
    (rows : Finset (Fin 4)) (cols : Finset (Fin 5)) (large : 5 < rows.card + cols.card) :
    Module.finrank ℂ (L.map (rectangleMap rows cols)) < rows.card * cols.card := by
  have proper : L.map (rectangleMap rows cols) ≠ ⊤ := by
    intro full
    have mem : (1 : rows × cols → ℂ) ∈ L.map (rectangleMap rows cols) := by simp [full]
    obtain ⟨t, ht, he⟩ := mem
    exact no_ones_rectangle t (h t ht) rows cols large
      (fun i hi j hj => congrFun he (⟨i,hi⟩, ⟨j,hj⟩))
  simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_lt proper

lemma rectangle_kernel (L : Submodule ℂ Mat)
    (h : ∀ t ∈ L, first t = 0 ∧ second t = 0 ∧ third t = 0 ∧ fourth t = 0)
    (rows : Finset (Fin 4)) (cols : Finset (Fin 5)) (large : 5 < rows.card + cols.card) :
    Module.finrank ℂ L + 1 ≤ rows.card * cols.card +
      Module.finrank ℂ (LinearMap.ker ((rectangleMap rows cols).domRestrict L)) := by
  have rank := rectangle_rank L h rows cols large
  have dim := LinearMap.finrank_range_add_finrank_ker ((rectangleMap rows cols).domRestrict L)
  rw [LinearMap.range_domRestrict] at dim
  omega

-- A space of independent test directions disjoint from L consumes dimension
-- in the annihilator of the polar image of L.
private lemma normal_budget (L K : Submodule ℂ Mat)
    (h : ∀ x ∈ L, second x = 0) (disj : Disjoint L K)
    (orth : ∀ x ∈ L, ∀ y ∈ K, dotProduct (polarMap x) y = 0) :
    Module.finrank ℂ L + Module.finrank ℂ L + Module.finrank ℂ K ≤ 20 := by
  let dual := (dotProductEquiv ℂ (Fin 4 × Fin 5)).toLinearMap.comp polarMap
  have inj : Function.Injective dual :=
    (dotProductEquiv ℂ (Fin 4 × Fin 5)).injective.comp polar_injective
  have le : L.map dual ≤ (L ⊔ K).dualAnnihilator := by
    rintro f ⟨x, hx, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    have hk : L ⊔ K ≤ LinearMap.ker (dual x) := by
      apply sup_le
      · intro z hz
        change dotProduct (polarMap x) z = 0
        simp [polar_pair, h _ (L.add_mem hx hz), h x hx, h z hz]
      · exact fun z hz => orth x hx z hz
    exact hk hy
  have sub := Submodule.finrank_mono le
  rw [← (Submodule.equivMapOfInjective dual inj L).finrank_eq] at sub
  have dim := Subspace.finrank_add_finrank_dualAnnihilator_eq (L ⊔ K)
  have add := Submodule.finrank_sup_add_finrank_inf_eq L K
  rw [disj.eq_bot, finrank_bot, add_zero] at add
  rw [add] at dim
  have amb : Module.finrank ℂ Mat = 20 := by simp [Mat, Module.finrank_fintype_fun_eq_card]
  rw [amb] at dim
  calc
    _ = (Module.finrank ℂ L + Module.finrank ℂ K) + Module.finrank ℂ L := by ac_rfl
    _ ≤ _ := Nat.add_le_add_left sub (Module.finrank ℂ L + Module.finrank ℂ K)
    _ = 20 := dim

private def rowTests (r : Fin 4) : (Fin 5 → ℂ) →ₗ[ℂ] Mat where
  toFun z p := (if p.1 = r then -2 else 1) * z p.2
  map_add' x y := by funext p; simp [mul_add]
  map_smul' c x := by funext p; simp [mul_left_comm]

private lemma rowTests_injective (r : Fin 4) : Function.Injective (rowTests r) := by
  intro x y he
  funext j
  have eq := congrFun he (r,j)
  simpa [rowTests] using eq

set_option maxRecDepth 10000 in
private lemma rowTests_pair (r : Fin 4) (x : Mat) (z : Fin 5 → ℂ) :
    dotProduct (polarMap x) (rowTests r z) =
      3 * ∑ j, x (r,j) * ((∑ k, z k) - z j) := by
  fin_cases r <;> norm_num [polarMap, first, rowTests, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_four, Fin.sum_univ_five] <;> ring

lemma zero_row_bound (L : Submodule ℂ Mat) (h : ∀ x ∈ L, second x = 0)
    (r : Fin 4) (zero_row : ∀ x ∈ L, ∀ j, x (r,j) = 0) : Module.finrank ℂ L ≤ 7 := by
  let K := LinearMap.range (rowTests r)
  have disj : Disjoint L K := by
    rw [Submodule.disjoint_def]
    rintro _ hx ⟨z, rfl⟩
    have hz : z = 0 := by
      funext j
      simpa [rowTests] using zero_row _ hx j
    rw [hz, map_zero]
  have normal : ∀ x ∈ L, ∀ y ∈ K, dotProduct (polarMap x) y = 0 := by
    rintro x hx _ ⟨z, rfl⟩
    simp [rowTests_pair, zero_row x hx]
  have dim : Module.finrank ℂ K = 5 := by
    rw [show K = LinearMap.range (rowTests r) from rfl,
      LinearMap.finrank_range_of_inj (rowTests_injective r)]
    simp
  have bound := normal_budget L K h disj normal
  rw [dim] at bound
  omega

private def colTests (c : Fin 5) : ((Fin 4 → ℂ) × ℂ) →ₗ[ℂ] Mat where
  toFun za p := if p.2 = c then -3 * za.1 p.1 else za.1 p.1 + za.2
  map_add' x y := by
    funext p
    by_cases hp : p.2 = c <;> simp [hp, mul_add]
    ring
  map_smul' a x := by
    funext p
    by_cases hp : p.2 = c <;> simp [hp, mul_add]
    ring

private lemma colTests_total (c : Fin 5) (z : Fin 4 → ℂ) (a : ℂ) :
    first (colTests c (z,a)) = (∑ i, z i) + 16 * a := by
  fin_cases c <;> norm_num [first, colTests, Fin.sum_univ_five, Fin.sum_univ_four] <;> ring

private lemma colTests_parameters (c : Fin 5) (v : (Fin 4 → ℂ) × ℂ)
    (hc : ∀ i, colTests c v (i,c) = 0) (hs : first (colTests c v) = 0) : v = 0 := by
  obtain ⟨z,a⟩ := v
  have hz : z = 0 := by funext i; simpa [colTests] using hc i
  subst z
  simpa [colTests_total] using hs

private lemma colTests_injective (c : Fin 5) : Function.Injective (colTests c) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  have zero : colTests c v = 0 := hv
  exact colTests_parameters c v (fun i => congrFun zero (i,c)) (by simp [zero, first])

set_option maxRecDepth 10000 in
private lemma colTests_pair (c : Fin 5) (x : Mat) (z : Fin 4 → ℂ) (a : ℂ) :
    dotProduct (polarMap x) (colTests c (z,a)) =
      4 * (∑ i, x (i,c) * ((∑ k, z k) - z i)) + a * (9 * first x + 3 * ∑ i, x (i,c)) := by
  fin_cases c <;> norm_num [polarMap, first, colTests, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_four, Fin.sum_univ_five] <;> ring

lemma zero_column_bound (L : Submodule ℂ Mat) (h : ∀ x ∈ L, first x = 0 ∧ second x = 0)
    (c : Fin 5) (zero_col : ∀ x ∈ L, ∀ i, x (i,c) = 0) : Module.finrank ℂ L ≤ 7 := by
  let K := LinearMap.range (colTests c)
  have disj : Disjoint L K := by
    rw [Submodule.disjoint_def]
    rintro _ hx ⟨v, rfl⟩
    rw [colTests_parameters c v (zero_col _ hx) (h _ hx).1, map_zero]
  have normal : ∀ x ∈ L, ∀ y ∈ K, dotProduct (polarMap x) y = 0 := by
    rintro x hx _ ⟨⟨z,a⟩, rfl⟩
    simp [colTests_pair, zero_col x hx, (h x hx).1]
  have dim : Module.finrank ℂ K = 5 := by
    rw [show K = LinearMap.range (colTests c) from rfl,
      LinearMap.finrank_range_of_inj (colTests_injective c)]
    simp
  have bound := normal_budget L K (fun x hx => (h x hx).2) disj normal
  rw [dim] at bound
  omega

private def matchingTriple (a b c : Fin 5 → ℂ) : ℂ :=
  ∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else a j * b l * c m

set_option maxRecDepth 10000 in
private lemma centered_triple (a b c : Fin 5 → ℂ)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) :
    matchingTriple a b c = 2 * ∑ j, a j * b j * c j := by
  have incl : matchingTriple a b c =
      (∑ j, a j) * (∑ j, b j) * (∑ j, c j) -
      (∑ j, a j * b j) * (∑ j, c j) - (∑ j, a j * c j) * (∑ j, b j) -
      (∑ j, b j * c j) * (∑ j, a j) + 2 * ∑ j, a j * b j * c j := by
    norm_num [matchingTriple, Fin.sum_univ_five]
    ring
  simpa [ha, hb, hc] using incl

private def row (t : Mat) (i : Fin 4) (j : Fin 5) := t (i,j)

set_option maxRecDepth 10000 in
private lemma third_by_rows (t : Mat) :
    third t = matchingTriple (row t 0) (row t 1) (row t 2) +
      matchingTriple (row t 0) (row t 1) (row t 3) +
      matchingTriple (row t 0) (row t 2) (row t 3) +
      matchingTriple (row t 1) (row t 2) (row t 3) := by
  norm_num [row, third, matchingTriple, Fin.sum_univ_five, Fin.sum_univ_four]
  ring

-- With every margin zero, the cubic matching equation becomes a power sum.
private lemma centered_cubic (t : Mat) (hr : ∀ i, ∑ j, row t i j = 0)
    (hc : ∀ j, ∑ i, t (i,j) = 0) : 3 * third t = 2 * ∑ j, ∑ i, t (i,j)^3 := by
  have column (j : Fin 5) :
      3 * (t (0,j) * t (1,j) * t (2,j) + t (0,j) * t (1,j) * t (3,j) +
        t (0,j) * t (2,j) * t (3,j) + t (1,j) * t (2,j) * t (3,j)) = ∑ i, t (i,j)^3 := by
    have total := hc j
    simp only [Fin.sum_univ_four] at total ⊢
    have last : t (3,j) = -(t (0,j) + t (1,j) + t (2,j)) := by linear_combination total
    rw [last]
    ring
  rw [third_by_rows]
  simp only [centered_triple _ _ _ (hr _) (hr _) (hr _), ← column, row,
    Fin.sum_univ_five]
  ring

-- An exceptional space would have a nonzero centered member with both
-- power sums zero, and its complex conjugate would lie outside the space.
lemma centered_witness (L : Submodule ℂ Mat)
    (h : ∀ x ∈ L, first x = 0 ∧ second x = 0 ∧ third x = 0 ∧ fourth x = 0)
    (large : 8 ≤ Module.finrank ℂ L) :
    ∃ x ∈ L, x ≠ 0 ∧ (∀ i, ∑ j, x (i,j) = 0) ∧ (∀ j, ∑ i, x (i,j) = 0) ∧
      dotProduct x x = 0 ∧ (∑ j, ∑ i, x (i,j)^3) = 0 ∧ star x ∉ L := by
  let f := margins.domRestrict L
  have dim : Module.finrank ℂ ((Fin 3 → ℂ) × (Fin 4 → ℂ)) = 7 := by simp
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by rw [dim]; omega))
  have mem := v.property
  have nz : (v : Mat) ≠ 0 := fun z => hn (Subtype.ext z)
  have hm : margins v = 0 := hv
  obtain ⟨hr, hc⟩ := centered_of_zero_margins v (h v mem).1 hm
  have fixed : polarMap v = v := by
    funext p
    change v.val p - (∑ j, v.val (p.1,j)) - (∑ i, v.val (i,p.2)) + first v = v.val p
    simp [hr, hc, (h v mem).1]
  have pair := polar_pair v v
  rw [fixed, (h _ (L.add_mem mem mem)).2.1, (h _ mem).2.1] at pair
  have cubic := centered_cubic v hr hc
  rw [(h _ mem).2.2.1] at cubic
  refine ⟨v, mem, nz, hr, hc, by simpa using pair, ?_, ?_⟩
  · linear_combination -cubic / 2
  · exact fun conjugate => nz (centered_vanishes L (fun x hx => ⟨(h x hx).1, (h x hx).2.1⟩)
      v mem hm conjugate)

end PEqualNP.Outside.L_gct_215
