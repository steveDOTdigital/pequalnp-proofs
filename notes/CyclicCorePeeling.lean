import PEqualNP.MetaComplexity.Helpers.ForestBound

/-!
# Removing trees while retaining an arbitrary cyclic core

The local elimination and cover lemmas are from the project's ForestBound.
The descent below adapts its claimQ induction. Its terminal case can now contain
cycles, and the isolated-input lemma makes its finite obligations graph-only.
-/

namespace Independent.CyclicCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Helpers.PermInputs
open SimpleGraph

def CanPeel {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ l p, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
    ((∃ q, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
     (∃ z, z ≠ l ∧ G.Adj p z ∧ ∀ w, G.Adj z w → w = p))

theorem zeroAlarm {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (a : Fin n) (ha : a ∈ A) (isolated : ∀ i j, G.Adj i j → i ∉ A)
    (x : Fin n → Bool) : F G A (Function.update x a false) = F G (A.erase a) x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨v, hv, hit⟩
      have ne : v ≠ a := by rintro rfl; simp at hit
      exact ⟨v, Finset.mem_erase.mpr ⟨ne,hv⟩, by rwa [Function.update_of_ne ne] at hit⟩
    · rintro ⟨v, hv, hit⟩
      obtain ⟨ne,hv⟩ := Finset.mem_erase.mp hv
      exact ⟨v, hv, by rwa [Function.update_of_ne ne]⟩
  · have outside (i j) (h : G.Adj i j) : i ≠ a := by
      rintro rfl
      exact isolated _ _ h ha
    constructor <;> rintro ⟨i,j,h,hi,hj⟩ <;>
      exact ⟨i,j,h,by simpa [Function.update_of_ne (outside i j h)] using hi,
        by simpa [Function.update_of_ne (outside j i h.symm)] using hj⟩

theorem removeAlarms {n : ℕ} (G : SimpleGraph (Fin n)) (edge : ∃ i j, G.Adj i j)
    (A : Finset (Fin n)) (s : ℕ) (isolated : ∀ i j, G.Adj i j → i ∉ A)
    (circuit : HasCircuitSize n (F G A) s) :
    ∃ r, r + A.card ≤ s ∧ HasCircuitSize n (F G ∅) r := by
  classical
  obtain ⟨u,v,uv⟩ := edge
  obtain ⟨n',rfl⟩ : ∃ t, n = t + 1 := ⟨n-1, by have := u.2; omega⟩
  induction A using Finset.strongInduction generalizing s with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with rfl | ⟨a,ha⟩
    · exact ⟨s,by simp,circuit⟩
    have ua : u ≠ a := by rintro rfl; exact isolated _ _ uv ha
    have enough := dep_lower_set _ (F G A) {u,a} (by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | h
      · exact F_dep G A _ v uv (isolated _ _ uv.symm)
      · simp only [Finset.mem_singleton] at h
        subst i
        exact F_dep_A G A a ha) s circuit
    rw [Finset.card_pair ua] at enough
    obtain ⟨t,rfl⟩ : ∃ t, s = t + 1 := ⟨s-1, by omega⟩
    have eqn : (fun x => F G A (Function.update x a false)) = F G (A.erase a) :=
      funext (zeroAlarm G A a ha isolated)
    have nonconstant := F_nc G (A.erase a) (Or.inr ⟨u,v,uv⟩)
    have step := one_gate_at n' (F G A) a false t (F_dep_A G A a ha) (by
      obtain ⟨x,y,h⟩ := nonconstant
      exact ⟨x,y,by rw [zeroAlarm G A a ha isolated, zeroAlarm G A a ha isolated]; exact h⟩) circuit
    rw [eqn] at step
    obtain ⟨r,hr,cr⟩ := ih (A.erase a) (Finset.erase_ssubset ha) t
      (fun i j h mem => isolated i j h (Finset.mem_of_mem_erase mem)) step
    have size := Finset.card_erase_add_one ha
    exact ⟨r, by omega, cr⟩

-- It is enough to check irreducible graphs in a subgraph-closed family.
theorem reduceToCore (P : ∀ n, SimpleGraph (Fin n) → Prop)
    (closed : ∀ {n} {G H : SimpleGraph (Fin n)}, P n G → H ≤ G → P n H)
    (terminal : ∀ {n} (G : SimpleGraph (Fin n)), P n G → ¬CanPeel G →
      (∃ i j, G.Adj i j) → ∀ k s, (∀ T, Cov G T → k ≤ T.card) →
      HasCircuitSize n (F G ∅) s → G.edgeSet.ncard + k ≤ s + 1) :
    ∀ (m n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (k s : ℕ),
    G.edgeSet.ncard = m → P n G → (∀ i j, G.Adj i j → i ∉ A) →
    (∀ T, Cov G T → k ≤ T.card) → (A.Nonempty ∨ ∃ i j, G.Adj i j) →
    HasCircuitSize n (F G A) s → A.card + m + k ≤ s + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n G A k s hm inside hinv hk hne hC
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · push Not at hE
    have hk0 : k ≤ (∅ : Finset (Fin n)).card := hk ∅ (fun i j h => absurd h (hE i j))
    have hm0 : m = 0 := by rw [← hm]; exact noedge_ncard G hE
    have := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    simp at hk0
    omega
  by_cases peel : CanPeel G
  swap
  · obtain ⟨r, cost, hc⟩ := removeAlarms G hE A s hinv hC
    have bound := terminal G inside peel hE k r hk hc
    omega
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := peel
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hdepl := F_dep G A l p hlp hpA
  have hdepp := F_dep G A p l hlp.symm hlA
  have hs1 : 2 ≤ s + 1 := by
    have := dep_lower_set _ (F G A) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hdepl
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact hdepp) s hC
    rwa [Finset.card_pair hlp.ne] at this
  set G0 := G.deleteEdges {s(l, p)} with hG0
  have hm0 : G0.edgeSet.ncard + 1 = m := by rw [← hm]; exact ncard_del1 G l p hlp
  have inside0 : P _ G0 := closed inside (deleteEdges_le _)
  have hinv0 : ∀ i j, G0.Adj i j → i ∉ A := fun i j h => hinv i j ((deleteEdges_adj).1 h).1
  have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  have hrf : (fun x => F G A (Function.update x l false)) = F G0 A :=
    funext (restrict_false G A l p hlA hleaf)
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · set G1 := G.deleteEdges {s(p, l), s(p, q)} with hG1
    by_cases h0 : A.Nonempty ∨ ∃ i j, G0.Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F G1 (insert p A) :=
        funext (restrict_true G A l p q hlA hlp hleaf hq)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc G0 A h0
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrf x
          have e2 := congrFun hrf y
          rw [e1, e2]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrt x
          have e2 := congrFun hrt y
          rw [e1, e2]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have hk0 : ∀ T, Cov G0 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS0 T hT)
          have := Finset.card_insert_le p T
          omega
        have := ih G0.edgeSet.ncard (by omega) _ G0 A (k - 1) s' rfl inside0 hinv0 hk0 h0 hC'
        omega
      · rw [hrt] at hC'
        have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
          intro e he
          rcases he with rfl | he
          · exact Sym2.mem_mk_left _ _
          · rw [Set.mem_singleton_iff] at he
            subst he
            exact Sym2.mem_mk_left _ _
        have hk1 : ∀ T, Cov G1 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS1 T hT)
          have := Finset.card_insert_le p T
          omega
        have inside1 : P _ G1 := closed inside (deleteEdges_le _)
        have hinv1 : ∀ i j, G1.Adj i j → i ∉ insert p A := by
          intro i j h hi
          rcases Finset.mem_insert.1 hi with heq | hi
          · exact del_p_adj G l p q hq i j h heq
          · exact hinv i j ((deleteEdges_adj).1 h).1 hi
        obtain ⟨hc1, hc2⟩ := ncard_del2 G l p q hlp
        rw [← hG1] at hc1 hc2
        have := ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k - 1) s' rfl inside1 hinv1
          hk1 (Or.inl (Finset.insert_nonempty _ _)) hC'
        rw [Finset.card_insert_of_notMem hpA] at this
        omega
    · push Not at h0
      obtain ⟨hA0, hG00⟩ := h0
      have hm1 : m = 1 := by
        have := noedge_ncard G0 hG00
        omega
      have hk1 : k ≤ ({p} : Finset (Fin (n' + 1))).card := by
        apply hk
        intro i j hij
        have h1 := hG00 i j
        rw [deleteEdges_adj] at h1
        push Not at h1
        have h2 := h1 hij
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
        rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (Finset.mem_singleton_self _)
        · exact Or.inl (Finset.mem_singleton_self _)
      rw [Finset.card_singleton] at hk1
      subst hA0
      simp only [Finset.card_empty]
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : G0.Adj p l' := (deleteEdges_adj).2 ⟨hpl', by
      simp [hl'l, hpl'.ne.symm]⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc G0 A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      have e1 := congrFun hrf x
      have e2 := congrFun hrf y
      rw [e1, e2]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have hk0 : ∀ T, Cov G0 T → k ≤ T.card := cov_swap G l p l' k hl'l hpl' hleaf' hk
    have := ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl inside0 hinv0 hk0
      (Or.inr ⟨p, l', hpl'0⟩) hC'
    omega

end Independent.CyclicCore
