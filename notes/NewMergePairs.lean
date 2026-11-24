import PEqualNP.Defs.NewLowMerge
import PEqualNP.MetaComplexity.Helpers.LowMergeFacts
import PEqualNP.MetaComplexity.Helpers.Support
import Mathlib.Data.Finset.Powerset

/-! Point-pair witnesses for new merges, localized to any selected wires. -/
namespace NewMergePairs

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.LowMergeProof

variable {P L : ℕ} (inc : Fin P → Fin L → Bool) (C : Circuit)

private theorem next_label (g : ℕ) (w : Fin L) :
    classLabel P L inc C (g+1) w = classStep P L inc C w (classLabel P L inc C g w) g := by
  simp [classLabel,List.range_succ,List.foldl_append]

private theorem persist (g t : ℕ) (w : Fin L) (le : g ≤ t) (p q : Fin P)
    (eq : SameClass P L inc C g w p q) : SameClass P L inc C t w p q := by
  induction t, le using Nat.le_induction with
  | base => exact eq
  | succ n _ ih =>
    unfold SameClass at ih ⊢
    rw [next_label]
    simp only [classStep,ih]

-- A witness is an unordered pair of alive points in distinct earlier classes.
def Witness (g : ℕ) (w : Fin L) (s : Finset (Fin P)) : Prop :=
  ∃ p q, p < q ∧ s={p,q} ∧ p ∈ aliveSet P L C g w ∧ q ∈ aliveSet P L C g w ∧
    ¬ SameClass P L inc C g w p q

theorem has_witness (g : ℕ) (w : Fin L) (h : IsNewLowMerge P L inc C g w) :
    ∃ s, Witness inc C g w s := by
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp h.2
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hb
  rcases lt_trichotomy p q with order|equal|order
  · exact ⟨_,p,q,order,rfl,hp,hq,ne⟩
  · exact False.elim (ne (equal ▸ rfl))
  · exact ⟨_,q,p,order,rfl,hq,hp,Ne.symm ne⟩

private theorem joined_after (g : ℕ) (w : Fin L) (p q : Fin P) (low : IsLow P L inc C g w)
    (hp : p ∈ aliveSet P L C g w) (hq : q ∈ aliveSet P L C g w) :
    SameClass P L inc C (g+1) w p q := by
  unfold SameClass
  rw [next_label]
  simp only [classStep]
  rw [ite_eq_left ⟨low,Finset.mem_image_of_mem _ hp⟩,
    ite_eq_left ⟨low,Finset.mem_image_of_mem _ hq⟩]

-- Once the points are joined at a line, they never witness a later merge.
theorem unique_event
    (sq : ∀ p q u v, p ≠ q → u ≠ v → inc p u = true → inc p v = true →
      inc q u = true → inc q v = true → False)
    {g t : ℕ} {u v : Fin L} {s : Finset (Fin P)}
    (hu : IsLow P L inc C g u) (hv : IsLow P L inc C t v)
    (a : Witness inc C g u s) (b : Witness inc C t v s) : (g,u)=(t,v) := by
  obtain ⟨p,q,ord,rfl,hp,hq,sep⟩ := a
  obtain ⟨x,y,ord',sets,hx,hy,sep'⟩ := b
  have px : p=x ∧ q=y := by
    have first : p ∈ ({p,q} : Finset (Fin P)) := by simp
    have second : q ∈ ({p,q} : Finset (Fin P)) := by simp
    rw [sets] at first second
    have h1 := Finset.mem_insert.mp first
    have h2 := Finset.mem_insert.mp second
    simp only [Finset.mem_singleton] at h1 h2
    rcases h1 with h|h <;> rcases h2 with k|k <;> omega
  obtain ⟨rfl,rfl⟩ := px
  have same : u=v := by
    by_contra neq
    have U := alive_sub_line inc C g u hu
    have V := alive_sub_line inc C t v hv
    exact sq p q u v ord.ne neq (Finset.mem_filter.mp (U hp)).2 (Finset.mem_filter.mp (V hx)).2
      (Finset.mem_filter.mp (U hq)).2 (Finset.mem_filter.mp (V hy)).2
  subst v
  rcases lt_trichotomy g t with early|equal|late
  · exact False.elim (sep' (persist inc C _ _ _ early _ _ (joined_after inc C g u p q hu hp hq)))
  · simp [equal]
  · exact False.elim (sep (persist inc C _ _ _ late _ _ (joined_after inc C t u p q hv hx hy)))

-- This count applies to arbitrary wire sets, including noncontiguous ones.
theorem localized_pairs
    (sq : ∀ p q u v, p ≠ q → u ≠ v → inc p u = true → inc p v = true →
      inc q u = true → inc q v = true → False)
    (W : Finset ℕ) (S : Finset (Fin P))
    (covered : ∀ g ∈ W, ∀ w, IsNewLowMerge P L inc C g w → aliveSet P L C g w ⊆ S) :
    ((W ×ˢ (Finset.univ : Finset (Fin L))).filter
      (fun z => IsNewLowMerge P L inc C z.1 z.2)).card ≤ S.card.choose 2 := by
  classical
  let E := (W ×ˢ (Finset.univ : Finset (Fin L))).filter
      (fun z => IsNewLowMerge P L inc C z.1 z.2)
  let F (z : E) := Classical.choose (has_witness inc C z.val.1 z.val.2 (Finset.mem_filter.mp z.prop).2)
  have spec (z : E) : Witness inc C z.val.1 z.val.2 (F z) :=
    Classical.choose_spec (has_witness inc C z.val.1 z.val.2 (Finset.mem_filter.mp z.prop).2)
  have inj : Function.Injective F := by
    intro x y e
    apply Subtype.ext
    exact unique_event inc C sq (Finset.mem_filter.mp x.prop).2.1 (Finset.mem_filter.mp y.prop).2.1
      (spec x) (e ▸ spec y)
  have inS (z : E) : F z ∈ S.powersetCard 2 := by
    obtain ⟨p,q,ord,eq,hp,hq,_⟩ := spec z
    obtain ⟨inProd,newMerge⟩ := Finset.mem_filter.mp z.prop
    have sub := covered _ (Finset.mem_product.mp inProd).1 _ newMerge
    rw [eq,Finset.mem_powersetCard]
    refine ⟨?_,by simp [ord.ne]⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl
    · exact sub hp
    · exact sub hq
  have count := Fintype.card_le_of_injective
    (fun z : E => (⟨F z,inS z⟩ : S.powersetCard 2)) (fun _ _ h => inj (congrArg Subtype.val h))
  simp only [Fintype.card_coe,Finset.card_powersetCard] at count
  exact count

def wireInputs (P L : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin (P+L)) :=
  (suppsFrom C.gates (inputSupps (P+L))).getD g ∅

-- Low wires reject the all-zero point assignment. Consequently every alive
-- point is a genuine input dependency and lies in the syntactic support.
theorem alive_in_support {g : ℕ} {w : Fin L} (low : IsLow P L inc C g w) {p : Fin P}
    (alive : p ∈ aliveSet P L C g w) : Fin.castAdd L p ∈ wireInputs P L C g := by
  by_contra missing
  let X := Fin.append (ind p) (fun v : Fin L => decide (v=w))
  let Y := Fin.append (fun _ : Fin P => false) (fun v : Fin L => decide (v=w))
  have agree : ∀ i ∈ wireInputs P L C g, X i = Y i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro x hx
      have ne : x ≠ p := fun eq => missing (eq ▸ hx)
      simp [X,Y,ind,ne]
    · intro v _
      simp [X,Y]
  have vals := (agree_wiresFrom X Y C.gates _ _ _ (agree_inputs X Y)).2.2 g agree
  change (C.wires (List.ofFn X)).getD g false = (C.wires (List.ofFn Y)).getD g false at vals
  dsimp only [X,Y] at vals
  rw [List.ofFn_fin_append,List.ofFn_fin_append] at vals
  have yes := (alive_mem C w g p).mp alive
  have zero : V C w g (fun _ : Fin P => false) = true := vals.symm.trans yes
  have bad := low _ zero
  rw [lineSum_false] at bad
  exact Bool.false_ne_true bad

theorem localized_support
    (sq : ∀ p q u v, p ≠ q → u ≠ v → inc p u = true → inc p v = true →
      inc q u = true → inc q v = true → False)
    (W : Finset ℕ) :
    ((W ×ˢ (Finset.univ : Finset (Fin L))).filter
      (fun z => IsNewLowMerge P L inc C z.1 z.2)).card ≤
      (Finset.univ.filter (fun p : Fin P =>
        Fin.castAdd L p ∈ W.biUnion (wireInputs P L C))).card.choose 2 := by
  apply localized_pairs inc C sq
  intro g hg w hm p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr
    ⟨g,hg,alive_in_support inc C hm.1 hp⟩⟩

-- A second bound retains the incidence structure inside the chosen point set.
-- Selected new merges consume distinct drops in its number of current classes.
theorem line_prefix (w : Fin L) (W : Finset ℕ) (S : Finset (Fin P))
    (covered : ∀ g ∈ W, IsNewLowMerge P L inc C g w → aliveSet P L C g w ⊆ S) (n : ℕ) :
    ((Finset.range n).filter (fun g => g ∈ W ∧ IsNewLowMerge P L inc C g w)).card +
      (S.image (classLabel P L inc C n w)).card ≤ S.card := by
  induction n with
  | zero =>
    change _ + (S.image Fin.val).card ≤ S.card
    simp [Finset.card_image_of_injective _ Fin.val_injective]
  | succ t ih =>
    let lab := classLabel P L inc C t w
    let T := (aliveSet P L C t w).image lab
    let f (x : ℕ) := if IsLow P L inc C t w ∧ x ∈ T then T.sup id else x
    let X := S.image lab
    have next : S.image (classLabel P L inc C (t+1) w) = X.image f := by
      rw [next_label,Finset.image_image]
      rfl
    rw [next, Finset.range_add_one, Finset.filter_insert]
    split_ifs with selected
    · rw [Finset.card_insert_of_notMem (by simp)]
      obtain ⟨s,p,q,_,_,hp,hq,ne⟩ := has_witness inc C t w selected.2
      have l1 : lab p ∈ X := Finset.mem_image_of_mem _ (covered t selected.1 selected.2 hp)
      have l2 : lab q ∈ X := Finset.mem_image_of_mem _ (covered t selected.1 selected.2 hq)
      have eq : f (lab p) = f (lab q) := by
        dsimp only [f]
        rw [ite_eq_left ⟨selected.2.1,Finset.mem_image_of_mem _ hp⟩,
          ite_eq_left ⟨selected.2.1,Finset.mem_image_of_mem _ hq⟩]
      have strict : (X.image f).card < X.card := lt_of_le_of_ne Finset.card_image_le
        (fun same => ne ((Finset.card_image_iff.mp same) l1 l2 eq))
      change _ + X.card ≤ _ at ih
      omega
    · change _ + X.card ≤ _ at ih
      exact (Nat.add_le_add_left Finset.card_image_le _).trans ih

theorem line_window (w : Fin L) (W : Finset ℕ) (S : Finset (Fin P))
    (covered : ∀ g ∈ W, IsNewLowMerge P L inc C g w → aliveSet P L C g w ⊆ S) :
    (W.filter (fun g => IsNewLowMerge P L inc C g w)).card ≤ S.card-1 := by
  let n := W.sup id + 1
  have count := line_prefix inc C w W S covered n
  have eq : (Finset.range n).filter (fun g => g ∈ W ∧ IsNewLowMerge P L inc C g w) =
      W.filter (fun g => IsNewLowMerge P L inc C g w) := by
    ext g
    simp only [Finset.mem_filter,Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      have le : g ≤ W.sup id := Finset.le_sup (f:=id) h.1
      exact ⟨Nat.lt_succ_of_le le,h⟩
  rw [eq] at count
  rcases S.eq_empty_or_nonempty with z|hn
  · rw [z] at count ⊢
    simpa using count
  · have pos := Finset.card_pos.mpr (hn.image (classLabel P L inc C n w))
    omega

theorem incidence_window (W : Finset ℕ) (S : Finset (Fin P))
    (covered : ∀ g ∈ W, ∀ w, IsNewLowMerge P L inc C g w → aliveSet P L C g w ⊆ S) :
    (∑ w : Fin L, (W.filter (fun g => IsNewLowMerge P L inc C g w)).card) ≤
      ∑ w : Fin L, ((S.filter (fun p => inc p w = true)).card-1) := by
  apply Finset.sum_le_sum
  intro w _
  apply line_window inc C w W
  intro g hg hm p hp
  exact Finset.mem_filter.mpr ⟨covered g hg w hm hp,
    (Finset.mem_filter.mp (alive_sub_line inc C g w hm.1 hp)).2⟩

-- Useful for realizing the bound: if every earlier low wire sees at most
-- one live point, no class has changed before g.
theorem first_merge {g : ℕ} {w : Fin L} (low : IsLow P L inc C g w)
    (two : 2 ≤ (aliveSet P L C g w).card)
    (early : ∀ t < g, IsLow P L inc C t w → (aliveSet P L C t w).card ≤ 1) :
    IsNewLowMerge P L inc C g w := by
  have untouched (t : ℕ) (ht : t ≤ g) : classLabel P L inc C t w = Fin.val := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [next_label,ih (by omega)]
      funext p
      unfold classStep
      split_ifs with h
      · let A := (aliveSet P L C t w).image Fin.val
        have card : A.card ≤ 1 := Finset.card_image_le.trans (early t (by omega) h.1)
        obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup A ⟨_,h.2⟩ id
        exact he.trans (Finset.card_le_one.mp card a ha p.val h.2)
      · rfl
  refine ⟨low,?_⟩
  unfold classesMet
  rw [untouched g le_rfl, Finset.card_image_of_injective _ Fin.val_injective]
  exact two

-- Three points, one line for each pair. The last OR attains choose(3,2).
-- Orient each pair toward the larger point index. The two sides of the final
-- OR recognize precisely the smaller and larger active endpoints respectively.
def triangleInc (p w : Fin 3) := decide (p ≠ w)
def triangleEdges : Circuit :=
  ⟨[⟨.or,[4,5]⟩,⟨.and,[0,6]⟩,⟨.and,[1,3]⟩,⟨.or,[7,8]⟩,
    ⟨.and,[1,5]⟩,⟨.or,[3,4]⟩,⟨.and,[2,11]⟩,⟨.or,[10,12]⟩,⟨.or,[9,13]⟩],14⟩

theorem triangle_computes : ∀ x y : Fin 3 → Bool,
    triangleEdges.eval (List.ofFn x ++ List.ofFn y) =
      decide (∃ p w, triangleInc p w = true ∧ x p = true ∧ y w = true) := by
  decide +kernel

theorem triangle_sharp (w : Fin 3) : IsNewLowMerge 3 3 triangleInc triangleEdges 14 w := by
  have ready : ∀ v : Fin 3, IsLow 3 3 triangleInc triangleEdges 14 v ∧
      2 ≤ (aliveSet 3 3 triangleEdges 14 v).card := by decide +kernel
  have cert : ∀ v : Fin 3, ∀ j : Fin 14, (aliveSet 3 3 triangleEdges j.val v).card ≤ 1 ∨
      V triangleEdges v j.val (fun _ : Fin 3 => false) = true := by decide +kernel
  apply first_merge triangleInc triangleEdges (ready w).1 (ready w).2
  intro t ht h
  rcases cert w ⟨t,ht⟩ with one|onEmpty
  · exact one
  · have bad := h _ onEmpty
    rw [lineSum_false] at bad
    exact False.elim (Bool.false_ne_true bad)

end NewMergePairs
