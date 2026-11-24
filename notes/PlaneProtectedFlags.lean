import PEqualNP.Defs

namespace PlaneProtectedFlags

-- A protected entry of A × B has a full row and a full column within the rectangle.
def protectedEntry {α β : Type} (R : α → β → Prop) (A : Set α) (B : Set β)
    (p : α) (l : β) : Prop :=
  p ∈ A ∧ l ∈ B ∧ (∀ j ∈ B, R p j) ∧ (∀ i ∈ A, R i l)

-- A rectangle of a four-cycle-free incidence relation with two different
-- protected entries has no false entry anywhere.
theorem full_of_two {α β : Type} (R : α → β → Prop)
    (noSquare : ∀ p r l k, R p l → R p k → R r l → R r k → p = r ∨ l = k)
    (A : Set α) (B : Set β) {p r : α} {l k : β}
    (first : protectedEntry R A B p l) (second : protectedEntry R A B r k)
    (different : (p,l) ≠ (r,k)) : ∀ a ∈ A, ∀ b ∈ B, R a b := by
  obtain ⟨hp,hl,rowP,colL⟩ := first
  obtain ⟨hr,hk,rowR,colK⟩ := second
  intro a ha b hb
  by_cases same : p = r
  · have diff : l ≠ k := fun eq => different (Prod.ext same eq)
    have rows := (noSquare p a l k (rowP _ hl) (rowP _ hk)
      (colL _ ha) (colK _ ha)).resolve_right diff
    exact rows ▸ rowP b hb
  · have cols := (noSquare p r l b (rowP _ hl) (rowP _ hb)
      (rowR _ hl) (rowR _ hb)).resolve_left same
    exact cols ▸ colL a ha

-- This is the quantitative version used in the circuit count.
theorem atMostOne {α β : Type} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (A : Set α) (B : Set β)
    (noSquare : ∀ p r l k, R p l → R p k → R r l → R r k → p = r ∨ l = k)
    (bad : ∃ a ∈ A, ∃ b ∈ B, ¬ R a b) (S : Finset (α × β))
    (guarded : ∀ z ∈ S, protectedEntry R A B z.1 z.2) : S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra distinct
  obtain ⟨a,ha,b,hb,failed⟩ := bad
  exact failed (full_of_two R noSquare A B (guarded u hu) (guarded v hv) distinct a ha b hb)

-- Count the distinct OR operations needed to realize several sets of leaves.
-- Each register starts with at most one leaf or takes a union of two earlier sets.
theorem leafCount {α : Type} [DecidableEq α]
    (n m : ℕ) (S : ℕ → Finset α) (ball : Finset α)
    (raw : ∀ i < n, (S i).card ≤ 1)
    (step : ∀ j < m, (S (n+j)).card ≤ 1 ∨
      ∃ a < n+j, ∃ b < n+j, S (n+j) = S a ∪ S b)
    (W : Finset ℕ) (inRange : W ⊆ Finset.range (n+m))
    (inside : ∀ w ∈ W, S w ⊆ ball) :
    (W.biUnion S).card ≤ W.card +
      ((Finset.range m).filter (fun j => 2 ≤ (S (n+j)).card ∧ S (n+j) ⊆ ball)).card := by
  classical
  let price := fun j => 2 ≤ (S (n+j)).card ∧ S (n+j) ⊆ ball
  induction m generalizing W with
  | zero =>
    have h := Finset.card_biUnion_le (s := W) (t := S)
    have small : ∑ w ∈ W, (S w).card ≤ ∑ _w ∈ W, 1 :=
      Finset.sum_le_sum (fun w hw => raw w (by simpa using inRange hw))
    simpa using h.trans small
  | succ k ih =>
    let r := n+k
    have prior (w : ℕ) (hw : w ∈ W) (hne : w ≠ r) : w < r := by
      have h := Finset.mem_range.mp (inRange hw)
      dsimp [r] at *
      omega
    have before := fun w (hw : w ∈ W.erase r) =>
      prior w (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1
    have localStep := fun j (h : j < k) => step j (Nat.lt_succ_of_lt h)
    by_cases used : r ∈ W
    · have restore : insert r (W.erase r) = W := Finset.insert_erase used
      have oldCard := Finset.card_erase_of_mem used
      have liveCard := Finset.card_pos.mpr ⟨r,used⟩
      by_cases tiny : (S r).card ≤ 1
      · have bound := ih localStep (W.erase r)
          (fun w hw => Finset.mem_range.mpr (before w hw))
          (fun w hw => inside w (Finset.mem_erase.mp hw).2)
        have area : (W.biUnion S).card ≤ (S r).card + ((W.erase r).biUnion S).card := by
          conv_lhs => rw [← restore, Finset.biUnion_insert]
          exact Finset.card_union_le (S r) ((W.erase r).biUnion S)
        have grow : (Finset.filter price (Finset.range k)).card ≤
            (Finset.filter price (Finset.range (k+1))).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
        change _ ≤ (W.erase r).card + (Finset.filter price _).card at bound
        change _ ≤ W.card + (Finset.filter price _).card
        omega
      · obtain ⟨a,ha,b,hb,eq⟩ := (step k (by omega)).resolve_left tiny
        have priceK : price k := ⟨by change 2 ≤ (S r).card; omega, inside r used⟩
        let V := insert a (insert b (W.erase r))
        have old : (W.erase r).biUnion S ⊆ V.biUnion S := by
          intro x hx
          obtain ⟨w,hw,hit⟩ := Finset.mem_biUnion.mp hx
          exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw),hit⟩
        have area : W.biUnion S ⊆ V.biUnion S := by
          intro x hx
          obtain ⟨w,hw,hx⟩ := Finset.mem_biUnion.mp hx
          by_cases same : w = r
          · rw [same] at hx
            rw [show S r = S a ∪ S b from eq] at hx
            rcases Finset.mem_union.mp hx with h | h
            · exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_insert_self _ _,h⟩
            · exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
          · exact old (Finset.mem_biUnion.mpr ⟨w,Finset.mem_erase.mpr ⟨same,hw⟩,hx⟩)
        have subA : S a ⊆ ball := fun x hx => inside r used (eq ▸ Finset.mem_union_left _ hx)
        have subB : S b ⊆ ball := fun x hx => inside r used (eq ▸ Finset.mem_union_right _ hx)
        have bound := ih localStep V (by
          intro w hw
          rcases Finset.mem_insert.mp hw with h | h
          · exact Finset.mem_range.mpr (h ▸ ha)
          rcases Finset.mem_insert.mp h with e | e
          · exact Finset.mem_range.mpr (e ▸ hb)
          · exact Finset.mem_range.mpr (before w e)) (by
          intro w hw
          rcases Finset.mem_insert.mp hw with h | h
          · exact h ▸ subA
          rcases Finset.mem_insert.mp h with e | e
          · exact e ▸ subB
          · exact inside w (Finset.mem_erase.mp e).2)
        have first := Finset.card_insert_le a (insert b (W.erase r))
        have second := Finset.card_insert_le b (W.erase r)
        have cards := Finset.card_le_card area
        change _ ≤ V.card + (Finset.filter price _).card at bound
        change _ ≤ W.card + (Finset.filter price _).card
        dsimp only [V] at bound cards
        rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left priceK,
          Finset.card_insert_of_notMem (by simp)]
        omega
    · have bound := ih localStep W
          (fun w hw => Finset.mem_range.mpr (prior w hw (fun eq => used (eq ▸ hw)))) inside
      have grow : (Finset.filter price (Finset.range k)).card ≤
          (Finset.filter price (Finset.range (k+1))).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
      exact bound.trans (Nat.add_le_add_left grow _)

-- On a row where the first factor already accepts, the second factor alone
-- must reject every compatible false extension. Union gives the exact budget.
theorem anchor {P L : Type} [DecidableEq P] [DecidableEq L]
    (I : P → L → Prop) (F G : Finset P → Finset L → Prop) (q : ℕ)
    (monoF : ∀ {a b : Finset P} {c d : Finset L}, a ⊆ b → c ⊆ d → F a c → F b d)
    (monoG : ∀ {a b : Finset P} {c d : Finset L}, a ⊆ b → c ⊆ d → G a c → G b d)
    (sound : ∀ p l, l.card ≤ q → (∀ x ∈ p, ∀ y ∈ l, ¬ I x y) → ¬ (F p l ∧ G p l))
    (a : Finset P) (b : Finset L) (first : F a b) (base : ∀ x ∈ a, ∀ y ∈ b, ¬ I x y)
    (p : Finset P) (l : Finset L) (budget : b.card + l.card ≤ q)
    (offPoints : ∀ x ∈ p, ∀ y ∈ b, ¬ I x y)
    (offLines : ∀ x ∈ a, ∀ y ∈ l, ¬ I x y) (free : ∀ x ∈ p, ∀ y ∈ l, ¬ I x y) :
    ¬ G p l := by
  intro second
  apply sound (a ∪ p) (b ∪ l) ((Finset.card_union_le _ _).trans budget) ?_
    ⟨monoF Finset.subset_union_left Finset.subset_union_left first,
      monoG Finset.subset_union_right Finset.subset_union_right second⟩
  intro x hx y hy
  rcases Finset.mem_union.mp hx with h | h <;> rcases Finset.mem_union.mp hy with k | k
  · exact base _ h _ k
  · exact offLines _ h _ k
  · exact offPoints _ h _ k
  · exact free _ h _ k

-- At an anchor maximizing the number of active predicates, none of the other
-- predicates can turn on after adding a compatible short row.
theorem stabilize (n k : ℕ) (G : Finset (Fin n) → Prop)
    (H : Fin k → Finset (Fin n) → Prop)
    (mono : ∀ i a b, a ⊆ b → H i a → H i b) (empty : G ∅) :
    ∃ a : Finset (Fin n), G a ∧
      (∃ t : Finset (Fin k), (∀ i, i ∈ t ↔ H i a) ∧ a.card ≤ 2*t.card) ∧
      ∀ i, ¬ H i a → ∀ b : Finset (Fin n), b.card ≤ 2 → G (a ∪ b) → ¬ H i (a ∪ b) := by
  classical
  let hit := fun a : Finset (Fin n) => Finset.univ.filter (fun i => H i a)
  let candidates := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun a => G a ∧ a.card ≤ 2*(hit a).card)
  have start : ∅ ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, empty, by simp⟩
  obtain ⟨a, ha, best⟩ := Finset.exists_max_image candidates (fun a => (hit a).card) ⟨∅,start⟩
  obtain ⟨ind, cheap⟩ := (Finset.mem_filter.mp ha).2
  refine ⟨a,ind,⟨hit a, fun i => by simp [hit], cheap⟩,?_⟩
  intro j missing b small combined fired
  have jm : j ∉ hit a := by simpa [hit] using missing
  have sub : insert j (hit a) ⊆ hit (a ∪ b) := by
    intro t ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_insert.mp ht with rfl | old
    · exact fired
    · exact mono _ _ _ Finset.subset_union_left (Finset.mem_filter.mp old).2
  have more := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem jm] at more
  have affordable := Finset.card_union_le a b
  have member : a ∪ b ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, combined, by omega⟩
  have upper := best (a ∪ b) member
  omega

theorem cleanFactor (n k : ℕ) (G : Finset (Fin n) → Prop)
    (H : Fin k → Finset (Fin n) → Prop)
    (mono : ∀ i a b, a ⊆ b → H i a → H i b) (empty : G ∅)
    (sound : ∀ a, G a → a.card ≤ 2*k → ¬ ∀ i, H i a) :
    ∃ a : Finset (Fin n), G a ∧ a.card ≤ 2*(k-1) ∧
      (∃ i, ¬ H i a) ∧ ∀ i, ¬ H i a →
        ∀ b : Finset (Fin n), b.card ≤ 2 → G (a ∪ b) → ¬ H i b := by
  classical
  obtain ⟨a,ind,⟨t,spec,cheap⟩,stable⟩ := stabilize n k G H mono empty
  have total : t.card ≤ k := by simpa using Finset.card_le_univ t
  obtain ⟨i,miss⟩ := Classical.not_forall.mp (sound a ind (by omega))
  have outside : i ∉ t := fun h => miss ((spec i).mp h)
  have extra := Finset.card_le_univ (insert i t)
  rw [Finset.card_insert_of_notMem outside] at extra
  simp only [Fintype.card_fin] at extra
  exact ⟨a,ind,by omega,⟨i,miss⟩,fun j hj b hb hfree h =>
    stable j hj b hb hfree (mono _ _ _ Finset.subset_union_right h)⟩

-- Removing at most two pencils per selected gate preserves enough flags.
theorem remainingSize (q n t s : ℕ) (hn : n = q^2+q+1)
    (few : 100*t ≤ 49*q) (count : n*(q+1) ≤ s + 2*t*(q+1)^2) :
    n*q ≤ 100*s := by
  have budget := Nat.mul_le_mul_right ((q+1)^2) few
  subst n
  nlinarith

end PlaneProtectedFlags
